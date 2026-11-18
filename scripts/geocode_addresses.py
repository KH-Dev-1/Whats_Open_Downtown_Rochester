"""Place each business on the map from its street address, using Olmsted County's official address points.

    py scripts/geocode_addresses.py             # geocode every business that has an address, write the files
    py scripts/geocode_addresses.py --dry-run   # show what would move, write nothing

Why: spreadsheet coordinates (and generic geocoders such as Mapbox or the Census) put a building on the street
centerline, often 10-40 m from the real entrance. The county's E911 address points sit on the building itself.

For each business with an "address" (the workbook's "Display address" column, loaded by load_business_data.py;
"Address from site" is not used):
  1. Olmsted County address points (public ArcGIS service, no key): the official E911 points on the buildings.
     Active, parent (non-unit) points are preferred.
  2. Nominatim (OpenStreetMap), as in the Geocoding notebook, when the county has no match. No key; the public server
     allows 1 request per second. Only results that match the street number are accepted.
  3. The US Census geocoder (street interpolation, less precise) as a last resort.
  Each business's "geocodeStatus" records which source placed it.
  4. If none match, the existing coordinates are kept and the business is listed so the address can be fixed.
Businesses without an address are left alone. The same data is re-embedded in index.html.
Uses only the Python standard library.
"""

import argparse
import json
import re
import ssl
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

from load_business_data import DATA_PATH, embed_in_index, load_data, render_data

COUNTY_URL = "https://public.gis.olmstedcounty.gov/arcgis/rest/services/Olmsted_Addressing/MapServer/1/query"
CENSUS_URL = "https://geocoding.geo.census.gov/geocoder/locations/onelineaddress"
NOMINATIM_URL = "https://nominatim.openstreetmap.org/search"
NOMINATIM_VIEWBOX = "-92.60,44.10,-92.35,43.90"  # greater Rochester, so "2nd St SW" can't match another town
NOMINATIM_STATUS = "Geocoded via Nominatim (OpenStreetMap)"
COUNTY_STATUS = "Geocoded from Olmsted County address points"
CENSUS_STATUS = "Geocoded via US Census (street interpolation)"
MIN_MOVE_M = 3  # smaller differences are not reported as a change

DIRECTIONS = {"N": "N", "S": "S", "E": "E", "W": "W", "NE": "NE", "NW": "NW", "SE": "SE", "SW": "SW",
              "NORTH": "N", "SOUTH": "S", "EAST": "E", "WEST": "W", "NORTHEAST": "NE", "NORTHWEST": "NW",
              "SOUTHEAST": "SE", "SOUTHWEST": "SW"}
STREET_TYPES = {"STREET": "ST", "ST": "ST", "AVENUE": "AVE", "AVE": "AVE", "DRIVE": "DR", "DR": "DR", "ROAD": "RD",
                "RD": "RD", "BOULEVARD": "BLVD", "BLVD": "BLVD", "LANE": "LN", "LN": "LN", "COURT": "CT", "CT": "CT",
                "PLACE": "PL", "PL": "PL", "PARKWAY": "PKWY", "PKWY": "PKWY", "CIRCLE": "CIR", "CIR": "CIR",
                "WAY": "WAY", "SQUARE": "SQ", "SQ": "SQ", "TRAIL": "TRL", "TRL": "TRL", "PLAZA": "PLZ", "PLZ": "PLZ"}
ORDINAL_WORDS = {"FIRST": "1", "SECOND": "2", "THIRD": "3", "FOURTH": "4", "FIFTH": "5", "SIXTH": "6",
                 "SEVENTH": "7", "EIGHTH": "8", "NINTH": "9", "TENTH": "10", "ELEVENTH": "11", "TWELFTH": "12"}
SUITE = re.compile(r"\b(?:suite|ste|unit|apt|floor|fl|room|rm)\b\.?\s*#?\s*\w+|#\s*\w+", re.I)


def parse_address(text):
    """'1117 2nd Street SW, Rochester, MN 55902' -> {number, pre_dir, name, type, post_dir, zip}; None if unparseable."""
    street, _, rest = text.partition(",")
    lead = rest.split(",")[0].strip().rstrip(".").upper()
    if lead in DIRECTIONS:  # "4 3rd St, SW, Suite 204": the direction got separated by a stray comma
        street += " " + lead
    street = SUITE.sub(" ", street)
    match = re.match(r"\s*(\d+)[A-Za-z]?\s+(.+?)\s*$", street)
    if not match:
        return None
    number, tokens = match.group(1), re.sub(r"[.]", "", match.group(2)).upper().split()
    pre_dir = post_dir = street_type = None
    if len(tokens) > 1 and tokens[-1] in DIRECTIONS:
        post_dir = DIRECTIONS[tokens.pop()]
    if len(tokens) > 1 and tokens[-1] in STREET_TYPES:
        street_type = STREET_TYPES[tokens.pop()]
    if len(tokens) > 1 and tokens[0] in DIRECTIONS and not post_dir:
        pre_dir = DIRECTIONS[tokens.pop(0)]
    name = " ".join(tokens)
    name = ORDINAL_WORDS.get(name, re.sub(r"^(\d+)(?:ST|ND|RD|TH)$", r"\1", name))
    zip_match = re.search(r"\b(\d{5})\b", rest)
    return {"number": number, "pre_dir": pre_dir, "name": name, "type": street_type, "post_dir": post_dir,
            "zip": zip_match.group(1) if zip_match else None}


def sql(value):
    return "'" + value.replace("'", "''") + "'"


def get_json(url, params):
    request = urllib.request.Request(url + "?" + urllib.parse.urlencode(params),
                                     headers={"User-Agent": "whats-open-geocoder"})
    for attempt in range(3):
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                return json.load(response)
        except ssl.SSLError as error:
            sys.exit(f"Could not verify the server's certificate ({error}). On a corporate network, run from a "
                     "machine without SSL inspection or ask IT to trust the service.")
        except (urllib.error.URLError, TimeoutError, ConnectionError):
            if attempt == 2:
                raise
            time.sleep(2 * (attempt + 1))


def county_match(parts):
    """Best county address point for the parsed address, or None.
    A direction matches on either side of the street name ('E Center St' is stored as 'Center St E'). The number,
    street name and direction are never loosened, and the match always stays in the ZIP or, failing that, the city of
    Rochester, so a miss can't land on the same street in another town. Only the street type (St/Ave) and a wrong
    ZIP are tolerated."""
    tries = []
    for use_type, use_zip in ((True, True), (False, True), (True, False), (False, False)):
        clauses = [f"ADDNO = {sql(parts['number'])}", f"ST_NAME = {sql(parts['name'])}"]
        if use_type and parts["type"]:
            clauses.append(f"ST_TYPE = {sql(parts['type'])}")
        for direction in (parts["pre_dir"], parts["post_dir"]):
            if direction:
                clauses.append(f"(PRE_DIR = {sql(direction)} OR POST_DIR = {sql(direction)})")
        if use_zip and parts["zip"]:
            clauses.append(f"ZIP5 = {sql(parts['zip'])}")
        elif parts["zip"]:  # sheet ZIPs are sometimes wrong: ignore the ZIP but stay in the city of Rochester
            clauses.append("CITY = 'ROCHESTER'")
        tries.append(" AND ".join(clauses))
    for where in dict.fromkeys(tries):  # skip repeats when the address had no ZIP or street type
        data = get_json(COUNTY_URL, {"where": where, "outFields": "EFF_STATUS,UNIT,PAR_CHILD,ZIP5,CITY",
                                     "outSR": 4326, "f": "json"})
        found = [f for f in data.get("features", []) if f.get("geometry")]
        if found:
            # Active points first, then ones without a unit number, then parent points (the building itself).
            found.sort(key=lambda f: (f["attributes"]["EFF_STATUS"] != "A", bool(f["attributes"]["UNIT"]),
                                      f["attributes"]["PAR_CHILD"] != "P"))
            best = found[0]
            return best["geometry"]["y"], best["geometry"]["x"]
    return None


def nominatim_match(address, number):
    """Nominatim (OpenStreetMap). Accepts a result only when it carries the same house number as the address, so a
    street or neighbourhood centre is never mistaken for the building."""
    data = get_json(NOMINATIM_URL, {"q": address, "format": "jsonv2", "limit": 3, "addressdetails": 1,
                                    "countrycodes": "us", "viewbox": NOMINATIM_VIEWBOX, "bounded": 1})
    for hit in data or []:
        if str(hit.get("address", {}).get("house_number", "")).upper() == number.upper():
            return float(hit["lat"]), float(hit["lon"])
    return None


def census_match(address):
    data = get_json(CENSUS_URL, {"address": address, "benchmark": "Public_AR_Current", "format": "json"})
    matches = data.get("result", {}).get("addressMatches", [])
    if matches:
        return matches[0]["coordinates"]["y"], matches[0]["coordinates"]["x"]
    return None


def meters_between(lat1, lng1, lat2, lng2):
    return (((lat2 - lat1) * 111_320) ** 2 + ((lng2 - lng1) * 111_320 * 0.7189) ** 2) ** 0.5  # ~44 deg N


def geocode_businesses(businesses, dry_run=False):
    """Set lat/lng/geocodeStatus on every business that has an address. Returns (moved, unmatched, no_address)."""
    moved, unmatched, no_address = [], [], 0
    cache = {}  # businesses that share an address share one lookup
    for business in businesses:
        address = (business.get("address") or "").strip()  # the workbook's "Display address" column
        if not address:
            no_address += 1
            continue
        if address not in cache:
            parts = parse_address(address)
            result = status = None
            if parts:
                result, status = county_match(parts), COUNTY_STATUS
            if not result and parts:
                result, status = nominatim_match(address, parts["number"]), NOMINATIM_STATUS
                time.sleep(1.1)  # Nominatim's usage policy: at most 1 request per second
            if not result:
                result, status = census_match(address), CENSUS_STATUS
            cache[address] = (result, status)
        result, status = cache[address]
        if not result:
            unmatched.append(f"{business['name']} ({address})")
            continue
        lat, lng = round(result[0], 6), round(result[1], 6)
        old = (business.get("lat"), business.get("lng"))
        shift = meters_between(*old, lat, lng) if None not in old else None
        if not dry_run:
            business["lat"], business["lng"], business["geocodeStatus"] = lat, lng, status
        if shift is None or shift >= MIN_MOVE_M:
            moved.append(f"{business['name']}: moved {'new' if shift is None else f'{shift:.0f} m'} [{status}]")
    return moved, unmatched, no_address


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--dry-run", action="store_true", help="show the changes without writing any file")
    args = parser.parse_args()

    header, data = load_data()
    moved, unmatched, no_address = geocode_businesses(data["businesses"], dry_run=args.dry_run)
    for line in moved:
        print("  " + line)
    for line in unmatched:
        print("  NO MATCH (kept existing coordinates): " + line)
    total = len(data["businesses"])
    print(f"{len(moved)} moved, {len(unmatched)} without a match, {no_address} without an address (left as is), {total} total")
    if args.dry_run:
        print("Dry run: no files written.")
        return
    js_text = render_data(header, data)
    DATA_PATH.write_text(js_text, encoding="utf-8", newline="")
    embed_in_index(js_text)
    print(f"Wrote {DATA_PATH.name} and re-embedded it in index.html")


if __name__ == "__main__":
    main()
