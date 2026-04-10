"""
generate_proposals.py
Generates proposals_b64.txt for meter_sim_v10.html.
Output: gzip+base64 JSON {terminalID: [lat, lon, addr]}
"""

import base64, gzip, json, csv, re, math, random
from pathlib import Path
from collections import Counter, defaultdict
import shapefile
from pyproj import Transformer

# ── Constants ──────────────────────────────────────────────────────────────────
LATM   = 111000   # meters per degree latitude
LONM   = 82500    # meters per degree longitude (Chicago ~41.9°N)
COMM_BUFFER_DEG = 0.0005   # ~55m bbox expansion for commercial zones (kept for near_comm_zone)
BIKE_EXCL_M  = 25          # exclude destinations within 25m of bike routes
PED_EXCL_M   = 0           # exclude if inside ped street polygon
EXIST_BLOCK_M = 30         # if existing non-flagged meter within 30m → block occupied

# Road class capacity fractions (transportation_20260316.geojson 'class' field)
# Class 2 = arterial (80%), 3 = minor arterial (40%), 4 = local/residential (20%)
# Classes 1,5,7,9,99,E,RIV,S = no meters allowed
CLASS_CAP_FRAC  = {'2': 0.80, '3': 0.40, '4': 0.20}
NO_PARK_CLASSES = {'1', '5', '7', '9', '99', 'E', 'RIV', 'S'}

# Standard parking rate tiers ($/hr). Relocated meters lose prior designation;
# estimated new rate = snap_to_tier(nbhd_avg_rate × lodes_job_factor).
RATE_TIERS = [0.50, 2.50, 4.75, 7.00, 14.00]
# Midpoints between consecutive tiers — boundary for snapping
_RATE_BREAKS = [1.50, 3.625, 5.875, 10.50]

# Per-tier price elasticity of demand.
# Lower tiers serve commuters/residents with few alternatives → inelastic.
# Higher tiers serve discretionary parkers who can substitute or avoid → elastic.
# These scale how aggressively each tier is pushed toward its rate cap.
TIER_ELASTICITY = {0.50: 0.10, 2.50: 0.20, 4.75: 0.35, 7.00: 0.50, 14.00: 0.65}

# Revenue target: slightly above SRSV ($386M) to leave a cushion.
# Per-tier factors are solved to hit this while keeping active spaces near 30,500.
TARGET_SYSTEM_REV = 405_000_000

# Chicago address grid: ~1m per address number (100 addr units ≈ one ~100m block).
# Used to convert address range half-span into a geographic offset when shifting the
# marker from the block midpoint toward the commercial-zone end of the block.
ADDR_TO_M = 1.0

# Non-arterial block parameters (class 3 and 4 scoring)
RES_RATE           = 1.50   # base hourly rate for class 3/4 not near commercial zone
RES_COMM_RATE_FRAC = 0.60   # class 3/4 near commercial: this fraction of nbhd avg rate
# Utilization for class 3/4 — tiered by parking scarcity:
#   ZONE:    permit zone nearby → parking is already constrained → paid meters get used
#   COMM:    near commercial zone but no permit zone → some destination demand
#   DEFAULT: neither → abundant free parking suppresses paid meter use
RES_UTIL_ZONE    = 0.50
RES_UTIL_COMM    = 0.30
RES_UTIL_DEFAULT = 0.15
RES_UTIL_JMAX    = 1.50     # cap on jfactor boost applied to residential util
RES_CAP_FRAC     = 0.20     # used only for permit zone meter_quota calculation
ZONE_SEARCH_M    = 150      # radius (m) to search for nearest permit zone centroid (class 4 only)
PERP_BONUS       = 1.5      # score multiplier for class 4 blocks perpendicular to permit zone street
# No-parking road exclusion (from lanes.json OSM data)
NO_PARK_LANES  = 4          # roads with this many lanes or more are assumed to have no parking
NO_PARK_EXCL_M = 25         # exclusion radius (m) around no-park road geometry points

# Business license density scoring
# Active business license count within BIZ_SEARCH_M replaces LODES job density.
# Directly measures operating commercial activity; captures small/informal businesses
# that WAC employment data misses. biz_factor = clip(sqrt(count / p75_count), min, max)
BIZ_MIN_FACTOR = 0.5   # floor: sparse areas still get some consideration
BIZ_MAX_FACTOR = 3.0   # ceiling: avoids loop/mag mile dominating everything
BIZ_SEARCH_M   = 200   # radius (m) to count active licenses near a destination block
JOB_GRID_CELL  = 0.005 # spatial grid cell ~550m (shared by biz, ped, and rate grids)

# Local rate estimation: search ALL meters (flagged + retained) within this radius.
# Area demand is stable at 400m regardless of which specific meters are relocated;
# rates of nearby meters (observed before moves) are the best available demand signal.
ALL_METER_RATE_SEARCH_M = 400  # radius (m) to search for nearby meters

# Pedestrian commercial street priority
# Class 2/3 roads that pass through a ped street zone are high-retail corridors.
# Destination blocks within this radius of such a road get a sort-tier boost.
PED_COMM_SEARCH_M = 150      # meters

# Chicago neighborhood bboxes (matches latLonToNbhd in v9)
NBHD = {
    'loop':       {'avgRate': 5.50, 'baseDensity': 1.10},
    'south_loop': {'avgRate': 3.60, 'baseDensity': 1.03},
    'near_west':  {'avgRate': 3.40, 'baseDensity': 1.01},
    'north_side': {'avgRate': 2.50, 'baseDensity': 0.97},
    'far_north':  {'avgRate': 2.50, 'baseDensity': 0.94},
    'northwest':  {'avgRate': 2.50, 'baseDensity': 0.91},
    'west_side':  {'avgRate': 2.50, 'baseDensity': 0.88},
    'southwest':  {'avgRate': 2.50, 'baseDensity': 0.87},
    'far_south':  {'avgRate': 2.50, 'baseDensity': 0.85},
}

# Better Streets for Buses corridors — loaded from BetterStreets_BusRoutes.shp
# (NAD83 Illinois State Plane East, US feet → WGS84 via pyproj).
BUS_EXCL_M = 30   # exclude destinations within 30m of a BSB route centerline
FREE_PARK_EXCL_M = 201   # 1/8 mile — exclude destinations within this radius of a free surface lot

# Road types that are NOT parkable (expressways, ramps, rail, etc.)
NON_PARKABLE_TYPES = {'EXPY', 'HWY', 'TOLL', 'XR', 'ER', 'SR', 'RL', 'ORD'}

# Street name lookup: populated from transportation_20260316.geojson during loading.
# Maps the centerline 'n' code (= transportation 'streetname' field) to a full street
# name string like "S YALE AVE". Used by side_addr() to produce readable addresses.
street_name_lookup: dict = {}

# Road class lookup: maps centerline 'n' code to road class string ('2','3','4', etc.)
road_class_lookup: dict = {}

# Business license spatial grid: cell → list of (lat, lon) for active licenses.
biz_grid: dict = {}
# Normalization baseline: 75th-percentile license count per BIZ_SEARCH_M circle
p75_biz_count: float = 1.0

# Pedestrian commercial grid: class 2/3 segment midpoints that fall inside a ped street polygon.
# Used to boost destination blocks near high-retail pedestrian corridors.
ped_comm_grid: dict = {}

# All-meter rate grid: spatial index of (lat, lon, rate) for ALL meters (flagged + retained).
# Area demand is stable within 400m of original meter locations; pre-move rates are
# the best available observed signal regardless of which specific meters are relocated.
all_meter_rate_grid: dict = {}

# ── Helper functions ───────────────────────────────────────────────────────────
def dist_m(lat1, lon1, lat2, lon2):
    dlat = (lat2 - lat1) * LATM
    dlon = (lon2 - lon1) * LONM
    return math.sqrt(dlat*dlat + dlon*dlon)

def lat_lon_to_nbhd(lat, lon):
    if lat > 41.97:                         return 'far_north'
    if lat > 41.92 and lon < -87.72:        return 'northwest'
    if lat > 41.92:                         return 'north_side'
    if lat > 41.88 and lon > -87.65:        return 'loop'
    if lat > 41.88 and lon < -87.70:        return 'west_side'
    if lat > 41.88:                         return 'near_west'
    if lat > 41.83 and lon < -87.70:        return 'southwest'
    if lat > 41.83:                         return 'south_loop'
    return 'far_south'

def base_util(rate):
    if rate >= 14:   return 0.55
    if rate >= 7:    return 0.72
    if rate >= 4.75: return 0.78
    if rate >= 2.5:  return 0.65
    return 0.50

def calc_util(rate, nbhd):
    bu = base_util(rate)
    nd = NBHD[nbhd]['baseDensity']
    return min(0.97, max(0.25, bu * nd * 1.05 * 1.02))

# Perpendicular offset from centerline so each side is visually distinct on the map.
# ~4.5m places the meter at curbside. Matches SNAP_OFFSET constants in v9 HTML.
SNAP_OFFSET_LAT = 4.5 / 111000   # degrees lat
SNAP_OFFSET_LON = 4.5 / 82500    # degrees lon at Chicago latitude

def side_offsets(d):
    """
    Returns (dlat, dlon) for LEFT side and RIGHT side given street direction d.
    Convention (US): traveling in direction d, left is to your left.
      d='N': left=west(-lon),  right=east(+lon)
      d='S': left=east(+lon),  right=west(-lon)
      d='E': left=north(+lat), right=south(-lat)
      d='W': left=south(-lat), right=north(+lat)
    """
    if d == 'N': return (0, -SNAP_OFFSET_LON), (0,  SNAP_OFFSET_LON)
    if d == 'S': return (0,  SNAP_OFFSET_LON), (0, -SNAP_OFFSET_LON)
    if d == 'E': return ( SNAP_OFFSET_LAT, 0), (-SNAP_OFFSET_LAT, 0)
    if d == 'W': return (-SNAP_OFFSET_LAT, 0), ( SNAP_OFFSET_LAT, 0)
    return (0, -SNAP_OFFSET_LON), (0, SNAP_OFFSET_LON)  # default N

def side_capacity(af, at_):
    """Capacity for ONE side of a block from its address range (used for zone quota calc).
    Formula: 90% usable block length / 5.8m per space (19ft), using 2.1m per address unit
    (empirical median from Chicago centerline geometry; theoretical grid value ~2.01m)."""
    if not (af and at_ and str(af).strip().isdigit() and str(at_).strip().isdigit()):
        return 0
    addr_span = min(abs(int(at_) - int(af)), 100)
    if addr_span <= 0:
        return 0
    return max(1, round(0.90 * addr_span * 2.1 / 5.8))

def physical_capacity(af, at_):
    """Usable physical parking capacity for one side (no class fraction applied).
    10% of block length is treated as unusable (driveways, hydrants, corners)."""
    if not (af and at_ and str(af).strip().isdigit() and str(at_).strip().isdigit()):
        return 0
    addr_span = min(abs(int(at_) - int(af)), 100)
    if addr_span <= 0:
        return 0
    return round(0.90 * addr_span * 2.1 / 5.8)

def addr_parity(af):
    """Return 'O' if af address is odd, 'E' if even, None if unknown."""
    try:
        return 'O' if int(str(af).strip()) % 2 == 1 else 'E'
    except (ValueError, TypeError, AttributeError):
        return None

def side_addr(seg, addr_from, addr_to, addr_num=None):
    """Build address string for one side of a block.

    addr_num: explicit address number to use (overrides midpoint calculation).
    Uses street_name_lookup (built from transportation_20260316.geojson) to convert
    the centerline 'n' internal code into a real street name (e.g. 'S YALE AVE').
    Falls back to the raw numeric code if the lookup misses.
    """
    if addr_num is not None:
        num = addr_num
    elif addr_from and addr_to and str(addr_from).strip().isdigit() and str(addr_to).strip().isdigit():
        num = round((int(addr_from) + int(addr_to)) / 2)
    else:
        num = ''
    n_code = str(seg.get('n') or '').strip()
    street_name = street_name_lookup.get(n_code)
    if street_name:
        parts = [str(x) for x in [num, street_name] if str(x).strip()]
    else:
        # Fallback: old format using raw fields
        parts = [str(x).strip() for x in [num, seg.get('d'), n_code, seg.get('t'), seg.get('s')]
                 if x and str(x).strip()]
    return ' '.join(parts)

# ── Point-in-polygon (ray casting) ────────────────────────────────────────────
def point_in_polygon(px, py, polygon):
    """polygon = list of [lon, lat] or (lon, lat). Returns True if (px,py) inside."""
    n = len(polygon)
    inside = False
    j = n - 1
    for i in range(n):
        xi, yi = polygon[i][0], polygon[i][1]
        xj, yj = polygon[j][0], polygon[j][1]
        if ((yi > py) != (yj > py)) and (px < (xj - xi) * (py - yi) / (yj - yi + 1e-15) + xi):
            inside = not inside
        j = i
    return inside

def point_in_any_polygon(px, py, polygons):
    """polygons = list of rings (each ring = list of [lon, lat])."""
    for ring in polygons:
        if point_in_polygon(px, py, ring):
            return True
    return False

# ── Distance from point to line segment ───────────────────────────────────────
def dist_point_to_segment(px, py, ax, ay, bx, by):
    """Approximate planar distance (degrees); scale by LATM/LONM for metres."""
    dx = (bx - ax) * LONM
    dy = (by - ay) * LATM
    qx = (px - ax) * LONM
    qy = (py - ay) * LATM
    seg_len2 = dx*dx + dy*dy
    if seg_len2 == 0:
        return math.sqrt(qx*qx + qy*qy)
    t = max(0, min(1, (qx*dx + qy*dy) / seg_len2))
    ex = qx - t*dx
    ey = qy - t*dy
    return math.sqrt(ex*ex + ey*ey)

# ── Bbox helpers ───────────────────────────────────────────────────────────────
def ring_bbox(ring):
    lons = [c[0] for c in ring]
    lats = [c[1] for c in ring]
    return min(lons), min(lats), max(lons), max(lats)

def expand_bbox(bbox, deg):
    return (bbox[0]-deg, bbox[1]-deg, bbox[2]+deg, bbox[3]+deg)

def in_bbox(lon, lat, bbox):
    return bbox[0] <= lon <= bbox[2] and bbox[1] <= lat <= bbox[3]

# ── Build spatial grid index ───────────────────────────────────────────────────
def build_grid(items_with_bbox, cell=0.002):
    """items_with_bbox = list of (item, (minlon, minlat, maxlon, maxlat))"""
    grid = {}
    for item, bbox in items_with_bbox:
        c0 = (int(bbox[0] / cell), int(bbox[1] / cell))
        c1 = (int(bbox[2] / cell), int(bbox[3] / cell))
        for gx in range(c0[0], c1[0]+1):
            for gy in range(c0[1], c1[1]+1):
                key = (gx, gy)
                if key not in grid:
                    grid[key] = []
                grid[key].append(item)
    return grid

def grid_query(grid, lon, lat, cell=0.002, radius=1):
    """Query grid cells within radius cells of (lon, lat)."""
    cx = int(lon / cell)
    cy = int(lat / cell)
    results = []
    for dx in range(-radius, radius+1):
        for dy in range(-radius, radius+1):
            results.extend(grid.get((cx+dx, cy+dy), []))
    return results

# ═══════════════════════════════════════════════════════════════════════════════
# LOAD DATA
# ═══════════════════════════════════════════════════════════════════════════════

print("Loading parking meters CSV...")
meters = []
with open('chicago_parking_meters.csv', newline='', encoding='utf-8') as f:
    for row in csv.DictReader(f):
        try:
            meters.append({
                'tid':   row['TerminalID'],
                'addr':  row['LocationAddress'],
                'lat':   float(row['Latitude']),
                'lon':   float(row['Longitude']),
                'rate':  float(row['FullRate']) if row['FullRate'] else 2.5,
                'sp':    int(row['NumberOfSpaces']) if row['NumberOfSpaces'] else 4,
            })
        except (ValueError, KeyError):
            pass
print(f"  {len(meters)} terminals loaded")

# Index ALL meters into rate grid immediately (before flagged/retained split).
# Pre-move rates are a valid area demand signal within ALL_METER_RATE_SEARCH_M
# regardless of which specific terminals are later relocated.
for _m in meters:
    _key = (int(_m['lon'] / JOB_GRID_CELL), int(_m['lat'] / JOB_GRID_CELL))
    if _key not in all_meter_rate_grid:
        all_meter_rate_grid[_key] = []
    all_meter_rate_grid[_key].append((_m['lat'], _m['lon'], _m['rate']))

# ── Extract flagged terminal IDs from v9 HTML ──────────────────────────────────
print("Extracting flagged terminal IDs from v10 HTML...")
with open('meter_sim_v10.html', 'r', encoding='utf-8', errors='replace') as f:
    html = f.read()

m = re.search(r'const BIKE_IDS\s*=\s*new Set\(\[([^\]]+)\]\)', html)
BIKE_IDS = set(x.strip().strip('"') for x in m.group(1).split(',')) if m else set()

m2 = re.search(r'PED_IDS\s*=\s*new Set\(\[([^\]]+)\]\)', html)
PED_IDS  = set(x.strip().strip('"') for x in m2.group(1).split(',')) if m2 else set()

FLAGGED_IDS = BIKE_IDS | PED_IDS
print(f"  BIKE_IDS: {len(BIKE_IDS)}, PED_IDS: {len(PED_IDS)}, total flagged: {len(FLAGGED_IDS)}")

# Split meters into flagged vs non-flagged
flagged_meters  = [m for m in meters if m['tid'] in FLAGGED_IDS]
retained_meters = [m for m in meters if m['tid'] not in FLAGGED_IDS]
print(f"  Flagged: {len(flagged_meters)}, Retained: {len(retained_meters)}")

# ── Load centerline ────────────────────────────────────────────────────────────
print("Loading centerline...")
with open('centerline_b64.txt') as f:
    raw = f.read().strip()
segs = json.loads(gzip.decompress(base64.b64decode(raw)).decode('utf-8').replace('\x60', ':'))
print(f"  {len(segs)} centerline segments")

# Filter out non-parkable road types, directional freeway lanes, segments outside Chicago
chicago_bounds = (-87.95, 41.64, -87.52, 42.05)
DIRECTIONAL_SUFFIXES = {'SB', 'NB', 'EB', 'WB', 'SB1', 'NB1', 'EB1', 'WB1'}
segs = [s for s in segs
        if s.get('t') not in NON_PARKABLE_TYPES
        and s.get('s') not in DIRECTIONAL_SUFFIXES
        and s.get('la') and s.get('lo')
        and in_bbox(s['lo'], s['la'], chicago_bounds)]
print(f"  {len(segs)} segments after filtering non-parkable types")

# ── Load commercial zones (B/C/D) ─────────────────────────────────────────────
print("Loading commercial zones...")
with open('Boundaries_-_Zoning_Districts_(current)_20260315.geojson') as f:
    zoning = json.load(f)

comm_rings = []       # list of (ring, expanded_bbox)
comm_class_rings = [] # list of (ring, expanded_bbox, zclass_letter) for zone-class lookup
for feat in zoning['features']:
    zclass = (feat['properties'].get('zone_class') or '').upper()
    # B, C, D zone classes (any subtype like B1, B2-3, C1, D3, etc.)
    if not (zclass.startswith('B') or zclass.startswith('C') or zclass.startswith('D')):
        continue
    geom = feat['geometry']
    if not geom:
        continue
    geom_type = geom['type']
    if geom_type == 'Polygon':
        polys = [geom['coordinates']]
    elif geom_type == 'MultiPolygon':
        polys = geom['coordinates']
    else:
        continue
    zclass_letter = zclass[0]  # 'B', 'C', or 'D'
    for poly in polys:
        outer = poly[0]  # exterior ring
        bbox = ring_bbox(outer)
        ebbox = expand_bbox(bbox, COMM_BUFFER_DEG)
        comm_rings.append((outer, ebbox))
        comm_class_rings.append((outer, ebbox, zclass_letter))

print(f"  {len(comm_rings)} commercial zone rings (B/C/D)")

# Build spatial grids of commercial zones for fast lookup
comm_grid = build_grid([(ring, ebbox) for ring, ebbox in comm_rings], cell=0.002)
# Zone-class grid stores (ring, zclass_letter) tuples for class lookup
comm_class_grid = build_grid([((ring, zclass_letter), ebbox)
                               for ring, ebbox, zclass_letter in comm_class_rings], cell=0.002)
print(f"  Commercial zone grid built")

def near_comm_zone(lon, lat):
    """True if (lon,lat) is within COMM_BUFFER of any B/C/D zone."""
    candidates = grid_query(comm_grid, lon, lat, cell=0.002)
    for ring in candidates:
        bbox = ring_bbox(ring)
        ebbox = expand_bbox(bbox, COMM_BUFFER_DEG)
        if in_bbox(lon, lat, ebbox):
            return True
    return False

def in_comm_zone(lon, lat):
    """True if (lon,lat) is inside any B/C/D zone polygon (strict check, no buffer)."""
    candidates = grid_query(comm_grid, lon, lat, cell=0.002)
    for ring in candidates:
        if point_in_polygon(lon, lat, ring):
            return True
    return False

def comm_zone_class_at(lon, lat):
    """Return zone class letter ('B', 'C', or 'D') if (lon, lat) is inside a commercial zone,
    or None if not inside any. Uses strict point-in-polygon (no buffer)."""
    candidates = grid_query(comm_class_grid, lon, lat, cell=0.002)
    for (ring, zclass_letter) in candidates:
        if point_in_polygon(lon, lat, ring):
            return zclass_letter
    return None

def comm_end_side(lat, lon, d, af, at_):
    """Find which end of a block is closest to a commercial zone.

    Returns (dlat_offset, dlon_offset, use_high_addr):
      - dlat_offset, dlon_offset: shift from segment midpoint toward the commercial end
      - use_high_addr: True = use max(af,at_) as address number
                       False = use min(af,at_)
                       None  = neither/both ends near commercial; keep midpoint

    Chicago address direction convention:
      d='N': higher address = further north (+lat)
      d='S': higher address = further south (-lat)
      d='E': higher address = further east  (+lon)
      d='W': higher address = further west  (-lon)
    """
    if not (af and at_ and str(af).strip().isdigit() and str(at_).strip().isdigit()):
        return 0.0, 0.0, None
    lo_addr = min(int(str(af).strip()), int(str(at_).strip()))
    hi_addr = max(int(str(af).strip()), int(str(at_).strip()))
    half_m = (hi_addr - lo_addr) / 2.0 * ADDR_TO_M
    if half_m <= 0:
        return 0.0, 0.0, None

    # Unit vector (per metre) from low-address end toward high-address end
    if d == 'N':   dlat_u, dlon_u =  1.0/LATM, 0.0
    elif d == 'S': dlat_u, dlon_u = -1.0/LATM, 0.0
    elif d == 'E': dlat_u, dlon_u = 0.0,  1.0/LONM
    else:          dlat_u, dlon_u = 0.0, -1.0/LONM   # d='W'

    hi_lat, hi_lon = lat + dlat_u * half_m, lon + dlon_u * half_m
    lo_lat, lo_lon = lat - dlat_u * half_m, lon - dlon_u * half_m

    hi_comm = near_comm_zone(hi_lon, hi_lat)
    lo_comm = near_comm_zone(lo_lon, lo_lat)

    if hi_comm and not lo_comm:
        return dlat_u * half_m, dlon_u * half_m, True
    elif lo_comm and not hi_comm:
        return -dlat_u * half_m, -dlon_u * half_m, False
    elif hi_comm and lo_comm:
        return dlat_u * half_m, dlon_u * half_m, True   # sandwiched — pick high end
    else:
        return 0.0, 0.0, None  # neither near commercial — keep midpoint

# ── Load ped street polygons ───────────────────────────────────────────────────
print("Loading ped street polygons...")
with open('zoning_pedstreet_20260315.geojson') as f:
    ped_gj = json.load(f)

# Pedestrian street type → sort tier (lower = higher priority).
# RETAIL is highest-demand; SIX-CORNER is mid; plain PEDESTRIAN STREET is lowest.
_PED_TYPE_TIER = {
    'PEDESTRIAN STREET RETAIL':     0,
    'PEDESTRIAN STREET SIX-CORNER': 1,
    'PEDESTRIAN STREET':            2,
}

ped_rings = []      # list of (outer, bbox) — used by on_ped_street exclusion
ped_type_rings = [] # list of (outer, tier) — used to look up zone tier for ped_comm_grid
for feat in ped_gj['features']:
    geom = feat['geometry']
    if not geom:
        continue
    if geom['type'] == 'Polygon':
        polys = [geom['coordinates']]
    elif geom['type'] == 'MultiPolygon':
        polys = geom['coordinates']
    else:
        continue
    _pname = feat.get('properties', {}).get('name', 'PEDESTRIAN STREET')
    _ptier = _PED_TYPE_TIER.get(_pname, 2)
    for poly in polys:
        outer = poly[0]
        bbox = ring_bbox(outer)
        ped_rings.append((outer, bbox))
        ped_type_rings.append((outer, _ptier))

ped_grid = build_grid([(ring, bbox) for ring, bbox in ped_rings], cell=0.001)
print(f"  {len(ped_rings)} ped street rings")

# ── Load CPD park polygons (replaces hard lakefront lon cutoff) ───────────────
# Excludes destination blocks inside any CPD park or within PARK_BUFFER_M of
# a park boundary. Covers lakefront parks (Grant, Lincoln, Jackson) and all
# interior parks. Buffer allows adjustment without re-running polygon math.
print("Loading CPD park polygons...")
with open('CPD_Parks_20260402.geojson', encoding='utf-8') as f:
    parks_gj = json.load(f)

PARK_BUFFER_M  = 10
_PARK_BUF_DEG  = PARK_BUFFER_M / min(LATM, LONM)

park_rings = []   # (outer_ring, expanded_bbox) — for point-in-polygon
park_segs  = []   # (ax, ay, bx, by, bbox) — for boundary-buffer check

for feat in parks_gj['features']:
    geom = feat.get('geometry')
    if not geom:
        continue
    polys = geom['coordinates'] if geom['type'] == 'Polygon' else (
            geom['coordinates'] if geom['type'] == 'MultiPolygon' else [])
    if geom['type'] == 'Polygon':
        polys = [polys]
    for poly in polys:
        outer = poly[0]
        bbox  = ring_bbox(outer)
        park_rings.append((outer, expand_bbox(bbox, _PARK_BUF_DEG)))
        for i in range(len(outer) - 1):
            ax, ay = outer[i][0],   outer[i][1]
            bx, by = outer[i+1][0], outer[i+1][1]
            seg_bbox = (min(ax,bx)-_PARK_BUF_DEG, min(ay,by)-_PARK_BUF_DEG,
                        max(ax,bx)+_PARK_BUF_DEG, max(ay,by)+_PARK_BUF_DEG)
            park_segs.append((ax, ay, bx, by, seg_bbox))

park_ring_grid = build_grid([(ring, ebbox) for ring, ebbox in park_rings], cell=0.002)
park_seg_grid  = build_grid([((ax,ay,bx,by), bbox) for ax,ay,bx,by,bbox in park_segs], cell=0.001)
print(f"  {len(park_rings)} park rings, {len(park_segs)} boundary segments")

def near_park(lon, lat):
    """True if (lon,lat) is inside or within PARK_BUFFER_M of any CPD park polygon."""
    for ring in grid_query(park_ring_grid, lon, lat, cell=0.002):
        if point_in_polygon(lon, lat, ring):
            return True
    for seg in grid_query(park_seg_grid, lon, lat, cell=0.001):
        ax, ay, bx, by = seg
        if dist_point_to_segment(lon, lat, ax, ay, bx, by) < PARK_BUFFER_M:
            return True
    return False

def ped_street_tier(lon, lat):
    """Return the tier of the ped zone containing (lon, lat), or None if not inside any."""
    for ring, tier in ped_type_rings:
        if point_in_polygon(lon, lat, ring):
            return tier
    return None

# Small offset for boundary check — catches segments running along polygon edges
_PED_DLAT = 5 / 111000
_PED_DLON = 5 / 82500

def on_ped_street(lon, lat):
    """True if (lon, lat) or any point within 5m is inside a ped street polygon."""
    for clat, clon in [
        (lat,              lon),
        (lat + _PED_DLAT,  lon),
        (lat - _PED_DLAT,  lon),
        (lat,              lon + _PED_DLON),
        (lat,              lon - _PED_DLON),
    ]:
        for ring in grid_query(ped_grid, clon, clat, cell=0.001):
            if point_in_polygon(clon, clat, ring):
                return True
    return False

# (LODES WAC job data removed — replaced by business license density scoring)

# ── Load BSB corridors from BetterStreets_BusRoutes.shp ──────────────────────
print("Loading Better Streets for Buses corridors from shapefile...")
_bsb_transformer = Transformer.from_crs('ESRI:102671', 'EPSG:4326', always_xy=True)
sf_bsb = shapefile.Reader('BetterStreets_BusRoutes.shp')
bus_segments = []   # list of (ax, ay, bx, by, bbox)  [lon, lat order]
buf = BUS_EXCL_M / min(LATM, LONM)
for shp in sf_bsb.shapes():
    if shp.shapeType == 0:
        continue
    parts = list(shp.parts) + [len(shp.points)]
    for i in range(len(parts) - 1):
        pts = shp.points[parts[i]:parts[i+1]]
        wgs = []
        for x, y in pts:
            lon, lat = _bsb_transformer.transform(x, y)
            if -88.5 < lon < -87.2 and 41.4 < lat < 42.5:
                wgs.append((lon, lat))
        for j in range(len(wgs) - 1):
            ax, ay = wgs[j]
            bx, by = wgs[j+1]
            bbox = (min(ax,bx)-buf, min(ay,by)-buf, max(ax,bx)+buf, max(ay,by)+buf)
            bus_segments.append((ax, ay, bx, by, bbox))

bus_grid = build_grid([((ax,ay,bx,by), bbox) for ax,ay,bx,by,bbox in bus_segments], cell=0.001)
print(f"  {len(bus_segments)} BSB route line segments")

# Encode BSB geometry for client-side geometry check (replaces pre-computed BSB_IDS)
_bsb_segs_data = [[round(ax,5), round(ay,5), round(bx,5), round(by,5)]
                  for ax, ay, bx, by, _ in bus_segments]
BSB_ROUTES_B64 = base64.b64encode(
    gzip.compress(json.dumps(_bsb_segs_data, separators=(',', ':')).encode())
).decode('ascii')
print(f"  BSB B64: {len(_bsb_segs_data):,} segments -> {len(BSB_ROUTES_B64):,} chars")

# ── Load transportation geojson for street name / road class lookups ──────────
print("Loading transportation network...")
with open('transportation_20260316.geojson') as f:
    trans_gj = json.load(f)

# ── Build street name and road class lookups from transportation features ──────
# The centerline 'n' field = transportation 'streetname' field (internal numeric code).
# transportation has pre_dir + street_nam + street_typ = human-readable name.
# The 'class' field gives road functional class (2=arterial, 3=minor arterial, 4=local, etc.)
for feat in trans_gj['features']:
    p = feat['properties']
    code = str(p.get('streetname') or '').strip()
    if not code:
        continue
    if code not in street_name_lookup:
        parts = [x for x in [p.get('pre_dir'), p.get('street_nam'), p.get('street_typ')] if x]
        if parts:
            street_name_lookup[code] = ' '.join(parts)
    if code not in road_class_lookup:
        rc = str(p.get('class') or '').strip()
        if rc:
            road_class_lookup[code] = rc

    # Ped commercial grid: class 2/3 segment midpoints inside a ped street zone.
    geom = feat.get('geometry')
    if geom:
        coords = geom.get('coordinates', [])
        if geom['type'] == 'LineString' and coords:
            mid = coords[len(coords) // 2]
        elif geom['type'] == 'MultiLineString' and coords and coords[0]:
            mid = coords[0][len(coords[0]) // 2]
        else:
            mid = None
        if mid:
            seg_lon, seg_lat = mid[0], mid[1]
            rc_feat = str(p.get('class') or '').strip()
            if rc_feat in ('2', '3'):
                _ptier = ped_street_tier(seg_lon, seg_lat)
                if _ptier is not None:
                    pc_cell = (int(seg_lon / JOB_GRID_CELL), int(seg_lat / JOB_GRID_CELL))
                    if pc_cell not in ped_comm_grid:
                        ped_comm_grid[pc_cell] = []
                    ped_comm_grid[pc_cell].append((seg_lat, seg_lon, _ptier))

print(f"  {len(street_name_lookup)} street name codes loaded from transportation")
print(f"  {len(road_class_lookup)} road class codes loaded from transportation")
print(f"  {sum(len(v) for v in ped_comm_grid.values())} ped commercial segment midpoints in "
      f"{len(ped_comm_grid)} cells")

# Reverse lookup: full street name → set of n_codes (for precise permit zone matching)
name_to_ncodes = defaultdict(set)
for _nc, _fn in street_name_lookup.items():
    name_to_ncodes[_fn].add(_nc)
print(f"  {len(name_to_ncodes)} unique street names in reverse lookup")

def lookup_biz_count(lat, lon):
    """Count active business licenses within BIZ_SEARCH_M of (lat, lon)."""
    cx = int(lon / JOB_GRID_CELL)
    cy = int(lat / JOB_GRID_CELL)
    count = 0
    for dx in range(-1, 2):
        for dy in range(-1, 2):
            for (blat, blon) in biz_grid.get((cx + dx, cy + dy), []):
                if dist_m(lat, lon, blat, blon) <= BIZ_SEARCH_M:
                    count += 1
    return count

def biz_score_factor(lat, lon):
    """Business license density as score multiplier, normalized to p75 count.
    Areas above p75 density get a boost; sparse areas get a penalty (floor=0.5)."""
    count = lookup_biz_count(lat, lon)
    raw = math.sqrt(count / p75_biz_count) if p75_biz_count > 0 else 1.0
    return max(BIZ_MIN_FACTOR, min(BIZ_MAX_FACTOR, raw))

def snap_to_tier(rate):
    """Snap a continuous rate estimate to the nearest standard parking tier."""
    for i, bp in enumerate(_RATE_BREAKS):
        if rate < bp:
            return RATE_TIERS[i]
    return RATE_TIERS[-1]

def nearest_ped_tier(lat, lon):
    """Return the best (lowest) ped street tier within PED_COMM_SEARCH_M, or 3 if none.
    Tier 0 = RETAIL (highest priority), 1 = SIX-CORNER, 2 = plain, 3 = not near any."""
    cx = int(lon / JOB_GRID_CELL)
    cy = int(lat / JOB_GRID_CELL)
    best = 3
    for dx in range(-1, 2):
        for dy in range(-1, 2):
            for (slat, slon, stier) in ped_comm_grid.get((cx + dx, cy + dy), []):
                if dist_m(lat, lon, slat, slon) <= PED_COMM_SEARCH_M:
                    if stier < best:
                        best = stier
    return best

def est_local_rate(lat, lon):
    """IDW average rate of all meters within ALL_METER_RATE_SEARCH_M.
    Uses pre-move rates from all terminals (flagged + retained) as an area demand signal.
    Returns None if no meters are nearby."""
    cx = int(lon / JOB_GRID_CELL)
    cy = int(lat / JOB_GRID_CELL)
    total_w, total_r = 0.0, 0.0
    for dx in range(-1, 2):
        for dy in range(-1, 2):
            for (mlat, mlon, mrate) in all_meter_rate_grid.get((cx + dx, cy + dy), []):
                d = dist_m(lat, lon, mlat, mlon)
                if d <= ALL_METER_RATE_SEARCH_M:
                    w = 1.0 / max(d, 10.0)
                    total_w += w
                    total_r += mrate * w
    return (total_r / total_w) if total_w > 0 else None

def near_bus_corridor(lon, lat):
    for seg in grid_query(bus_grid, lon, lat, cell=0.001):
        ax, ay, bx, by = seg
        if dist_point_to_segment(lon, lat, ax, ay, bx, by) < BUS_EXCL_M:
            return True
    return False

# ── Compute BSB_IDS: existing meters on BSB corridors ────────────────────────
# Mirrors how BIKE_IDS/PED_IDS work: flag source terminals for relocation.
# near_bus_corridor() is now available, so we can check current meter positions.
BSB_IDS = set()
for _m in meters:
    if near_bus_corridor(_m['lon'], _m['lat']):
        BSB_IDS.add(_m['tid'])
BSB_IDS -= FLAGGED_IDS   # don't double-count bike/ped terminals already flagged
FLAGGED_IDS |= BSB_IDS
# Re-split retained_meters: pull BSB terminals out and into flagged_meters
_bsb_new = [_m for _m in retained_meters if _m['tid'] in BSB_IDS]
retained_meters = [_m for _m in retained_meters if _m['tid'] not in BSB_IDS]
flagged_meters  = flagged_meters + _bsb_new
print(f"  BSB_IDS: {len(BSB_IDS)} terminals on BSB corridors flagged for relocation")
print(f"  Total flagged: {len(flagged_meters)}, Retained: {len(retained_meters)}")

# ── Load parking permit zones ─────────────────────────────────────────────────
print("Loading parking permit zones...")
# Direction mapping: permit zone STREET DIRECTION → which centerline d values represent same axis
#   N/S prefix → street runs N-S → centerline d in {'N','S'}
#   E/W prefix → street runs E-W → centerline d in {'E','W'}
PZ_AXIS = {'N': {'N','S'}, 'S': {'N','S'}, 'E': {'E','W'}, 'W': {'E','W'}}
# Perpendicular: preferred cross-street direction for meters near a zone
#   Zone on N-S street → prefer E-W cross streets (d in E/W)
#   Zone on E-W street → prefer N-S cross streets (d in N/S)
PZ_PERP = {'N': {'E','W'}, 'S': {'E','W'}, 'E': {'N','S'}, 'W': {'N','S'}}

pz_by_zone = defaultdict(list)   # zone_id -> list of parsed rows
with open('Parking_Permit_Zones_20260401.csv', newline='', encoding='utf-8-sig') as f:
    for row in csv.DictReader(f):
        if row.get('STATUS', '').strip().upper() != 'ACTIVE':
            continue
        zone_id = row.get('ZONE', '').strip()
        if not zone_id:
            continue
        d = row.get('STREET DIRECTION', '').strip().upper()
        if d not in PZ_AXIS:
            continue
        try:
            lo = int(row['ADDRESS RANGE - LOW'].strip())
            hi = int(row['ADDRESS RANGE - HIGH'].strip())
        except (ValueError, KeyError):
            continue
        odd_even = row.get('ODD_EVEN', '').strip().upper()   # 'O' or 'E'
        street_name_raw = row.get('STREET NAME', '').strip().upper()
        street_type_raw = row.get('STREET TYPE', '').strip().upper()
        full_name = ' '.join(x for x in [d, street_name_raw, street_type_raw] if x)
        span = min(abs(hi - lo), 100)
        cap  = max(0, round(0.90 * span * 2.1 / 5.8))
        pz_by_zone[zone_id].append({
            'lo': min(lo, hi), 'hi': max(lo, hi),
            'd': d, 'cap': cap,
            'odd_even': odd_even, 'full_name': full_name,
        })

# Load sticker counts from xlsx (zone_id str → count)
print("Loading permit zone sticker counts from xlsx...")
import openpyxl as _openpyxl
_wb = _openpyxl.load_workbook('Parking Zone Count.xlsx')
_ws = _wb.active
zone_sticker_counts = {}
for _row in _ws.iter_rows(min_row=2, values_only=True):
    if _row[0] is not None and _row[1] is not None:
        try:
            zone_sticker_counts[str(int(_row[0]))] = int(_row[1])
        except (ValueError, TypeError):
            pass
print(f"  {len(zone_sticker_counts)} zones with sticker counts")

# Compute per-zone metadata
zone_meta = {}   # zone_id -> {meter_quota, perp_dirs, used, total_cap}
for zone_id, rows in pz_by_zone.items():
    total_cap = sum(r['cap'] for r in rows)
    if total_cap == 0:
        continue
    dir_counts = Counter(r['d'] for r in rows)
    main_dir   = dir_counts.most_common(1)[0][0]
    stickers   = zone_sticker_counts.get(zone_id, 0)
    remaining  = max(0, total_cap - stickers)
    zone_meta[zone_id] = {
        'total_cap':   total_cap,
        'stickers':    stickers,
        'meter_quota': remaining,   # spaces available for meters after permit holders
        'axis_dirs':   PZ_AXIS[main_dir],     # centerline d values on same axis as zone street
        'perp_dirs':   PZ_PERP[main_dir],     # centerline d values perpendicular to zone street
        'used':        0,
    }
print(f"  {len(zone_meta)} active permit zones")
print(f"  Total zone physical capacity: {sum(z['total_cap'] for z in zone_meta.values())} spaces; "
      f"stickers: {sum(z['stickers'] for z in zone_meta.values())}; "
      f"available for meters: {sum(z['meter_quota'] for z in zone_meta.values())}")

# ── Match permit zone rows to centerline segments → zone centroids ─────────────
print("Computing permit zone centroids from centerline...")

# Index centerline segments by direction axis and address bucket (100-unit buckets)
# addr_bucket_index[(axis, bucket)] -> list of (seg, 'L'|'R', addr_lo, addr_hi)
# axis: 'NS' for d in N/S, 'EW' for d in E/W
addr_bucket_idx = defaultdict(list)
for seg in segs:
    d = seg.get('d') or 'N'
    axis = 'NS' if d in ('N', 'S') else 'EW'
    for side, af, at_ in [('L', 'lf', 'lt'), ('R', 'rf', 'rt')]:
        a0, a1 = seg.get(af), seg.get(at_)
        if a0 and a1 and str(a0).strip().isdigit() and str(a1).strip().isdigit():
            alo, ahi = int(str(a0).strip()), int(str(a1).strip())
            alo, ahi = min(alo, ahi), max(alo, ahi)
            for bucket in range((alo // 100) * 100, (ahi // 100) * 100 + 100, 100):
                addr_bucket_idx[(axis, bucket)].append((seg, side, alo, ahi))

def addr_overlap(lo1, hi1, lo2, hi2):
    return max(lo1, hi1) >= min(lo2, hi2) and min(lo1, hi1) <= max(lo2, hi2)

zone_locs = defaultdict(list)   # zone_id -> list of (lat, lon)
for zone_id, rows in pz_by_zone.items():
    if zone_id not in zone_meta:
        continue
    for row in rows:
        d_prefix = row['d']
        axis = 'NS' if d_prefix in ('N', 'S') else 'EW'
        lo, hi = row['lo'], row['hi']
        lo, hi = min(lo, hi), max(lo, hi)
        bucket = (lo // 100) * 100
        # Search the matching bucket(s)
        seen_segs = set()
        for bkt in range(bucket, (hi // 100) * 100 + 100, 100):
            for seg, side, alo, ahi in addr_bucket_idx.get((axis, bkt), []):
                sid = id(seg)
                if sid in seen_segs:
                    continue
                if addr_overlap(lo, hi, alo, ahi):
                    seen_segs.add(sid)
                    zone_locs[zone_id].append((seg['la'], seg['lo']))
                    break   # one match per zone row is enough for centroid
            if seen_segs:
                break

zone_centroids = {}   # zone_id -> (lat, lon)
for zone_id, locs in zone_locs.items():
    zone_centroids[zone_id] = (
        sum(l[0] for l in locs) / len(locs),
        sum(l[1] for l in locs) / len(locs),
    )
print(f"  {len(zone_centroids)}/{len(zone_meta)} zones matched to centerline locations")

# Build spatial grid of zone centroids
ZONE_CELL = 0.002
zone_centroid_grid = defaultdict(list)   # cell -> [(zone_id, lat, lon)]
for zone_id, (clat, clon) in zone_centroids.items():
    key = (int(clon / ZONE_CELL), int(clat / ZONE_CELL))
    zone_centroid_grid[key].append((zone_id, clat, clon))

def nearest_zone(lat, lon, max_m=ZONE_SEARCH_M):
    """Return (zone_id, dist_m) of nearest permit zone centroid within max_m, else (None, inf)."""
    cx = int(lon / ZONE_CELL)
    cy = int(lat / ZONE_CELL)
    best_id, best_d = None, float('inf')
    for dx in range(-2, 3):
        for dy in range(-2, 3):
            for zone_id, clat, clon in zone_centroid_grid.get((cx + dx, cy + dy), []):
                d = dist_m(lat, lon, clat, clon)
                if d < best_d:
                    best_d, best_id = d, zone_id
    return (best_id, best_d) if best_d <= max_m else (None, float('inf'))

# ── Build per-side meter capacity for permit zones ────────────────────────────
# For each zone, match centerline segment sides by address range + ODD_EVEN parity
# + street name. Compute remaining = total_phys - sticker_count, then distribute
# evenly across matched sides. If remaining/N < 2 (each side would get < 2 spaces),
# select the N_max best sides (by physical capacity) where N_max = remaining // 2
# and assign remaining // N_max each, so every selected side gets at least 2 spaces.
print("Computing per-side meter caps for permit zones...")

# zone_side_cap[(id(seg), 'L'|'R')] = assigned meter cap for this side in its zone.
# A value of 0 means the zone data says no meters on this side.
zone_side_cap = {}   # type: dict

_MIN_METERS_PER_SIDE = 2

_zones_with_sides = 0
_total_zone_meter_spaces = 0

for zone_id, zrows in pz_by_zone.items():
    if zone_id not in zone_meta:
        continue
    zm = zone_meta[zone_id]
    stickers = zm['stickers']

    # Collect all (seg, side, phys_cap) matched by address range + parity + street name
    matched = []   # list of (seg, side, phys_cap)
    seen_keys = set()

    for zrow in zrows:
        d_prefix = zrow['d']
        axis = 'NS' if d_prefix in ('N', 'S') else 'EW'
        lo, hi = zrow['lo'], zrow['hi']
        odd_even = zrow['odd_even']
        full_name = zrow['full_name']
        valid_ncodes = name_to_ncodes.get(full_name, set())

        for bkt in range((lo // 100) * 100, (hi // 100) * 100 + 100, 100):
            for seg, side, alo, ahi in addr_bucket_idx.get((axis, bkt), []):
                if not addr_overlap(lo, hi, alo, ahi):
                    continue
                # Street name filter (skip if we have name data and it doesn't match)
                if valid_ncodes:
                    n_code = str(seg.get('n') or '').strip()
                    if n_code not in valid_ncodes:
                        continue
                # Parity filter: match ODD_EVEN to this side's address range
                af = seg.get('lf' if side == 'L' else 'rf')
                if odd_even in ('O', 'E') and addr_parity(af) != odd_even:
                    continue
                key = (id(seg), side)
                if key in seen_keys:
                    continue
                seen_keys.add(key)
                pc = physical_capacity(
                    seg.get('lf' if side == 'L' else 'rf'),
                    seg.get('lt' if side == 'L' else 'rt')
                )
                matched.append((seg, side, pc))

    if not matched:
        continue

    total_phys = sum(pc for _, _, pc in matched)
    remaining = max(0, total_phys - stickers)
    N = len(matched)

    if remaining == 0:
        for seg, side, _ in matched:
            zone_side_cap[(id(seg), side)] = 0
        continue

    per_side = remaining / N
    if per_side >= _MIN_METERS_PER_SIDE:
        # Distribute evenly; give any leftover to highest-phys-cap sides
        sorted_m = sorted(matched, key=lambda x: -x[2])
        base = remaining // N
        extra = remaining % N
        for i, (seg, side, _) in enumerate(sorted_m):
            zone_side_cap[(id(seg), side)] = base + (1 if i < extra else 0)
    else:
        # Can only give >= 2 meters to a subset of sides
        max_sides = remaining // _MIN_METERS_PER_SIDE
        if max_sides == 0:
            for seg, side, _ in matched:
                zone_side_cap[(id(seg), side)] = 0
        else:
            # Pick best (highest phys cap) sides
            sorted_m = sorted(matched, key=lambda x: -x[2])
            selected = sorted_m[:max_sides]
            excluded = sorted_m[max_sides:]
            base = remaining // max_sides
            extra = remaining % max_sides
            for i, (seg, side, _) in enumerate(selected):
                zone_side_cap[(id(seg), side)] = base + (1 if i < extra else 0)
            for seg, side, _ in excluded:
                zone_side_cap[(id(seg), side)] = 0

    _zones_with_sides += 1
    _total_zone_meter_spaces += sum(
        zone_side_cap[(id(seg), side)] for seg, side, _ in matched
        if (id(seg), side) in zone_side_cap
    )

print(f"  {len(zone_side_cap)} side entries in {_zones_with_sides} zones "
      f"({_total_zone_meter_spaces} total meter spaces from zone data)")

# ── Post-process: enforce L/R balance for zone-assigned segment pairs ─────────
# When a zone assigns caps independently to L and R sides of the same segment
# (e.g. via the best-N_max path that selected one side but not the other),
# the pair can be lopsided. Rebalance so |left - right| <= max_diff, where
# max_diff = 2 for total <= 10 and 4 for total >= 11. The combined total is
# preserved; capacity is redistributed rather than added or removed.
_seg_sides = defaultdict(dict)
for (seg_id, side), cap in zone_side_cap.items():
    _seg_sides[seg_id][side] = cap

_rebalanced = 0
for seg_id, sides in _seg_sides.items():
    if 'L' not in sides or 'R' not in sides:
        continue  # only one side tracked in any zone; nothing to balance
    L_cap = sides['L']
    R_cap = sides['R']
    total = L_cap + R_cap
    if total == 0:
        continue
    max_diff = 2 if total <= 10 else 4
    if abs(L_cap - R_cap) <= max_diff:
        continue
    # Bring the higher side down to (total + max_diff) // 2 and give the rest
    # to the lower side, preserving total.
    max_high = (total + max_diff) // 2
    if L_cap > R_cap:
        zone_side_cap[(seg_id, 'L')] = max_high
        zone_side_cap[(seg_id, 'R')] = total - max_high
    else:
        zone_side_cap[(seg_id, 'R')] = max_high
        zone_side_cap[(seg_id, 'L')] = total - max_high
    _rebalanced += 1

print(f"  {_rebalanced} segment pairs rebalanced to satisfy L/R max-diff rule")

# ── Load bike routes ───────────────────────────────────────────────────────────
print("Loading bike routes...")
with open('Bike_Routes_20260316.geojson') as f:
    bike_gj = json.load(f)

# Extract all line segments from bike routes
bike_segments = []  # list of (ax, ay, bx, by, bbox)
for feat in bike_gj['features']:
    geom = feat['geometry']
    if not geom:
        continue
    if geom['type'] == 'LineString':
        lines = [geom['coordinates']]
    elif geom['type'] == 'MultiLineString':
        lines = geom['coordinates']
    else:
        continue
    for line in lines:
        for i in range(len(line)-1):
            ax, ay = line[i][0], line[i][1]
            bx, by = line[i+1][0], line[i+1][1]
            buf = BIKE_EXCL_M / min(LATM, LONM)
            bbox = (min(ax,bx)-buf, min(ay,by)-buf, max(ax,bx)+buf, max(ay,by)+buf)
            bike_segments.append((ax, ay, bx, by, bbox))

bike_grid = build_grid([((ax,ay,bx,by), bbox) for ax,ay,bx,by,bbox in bike_segments], cell=0.001)
print(f"  {len(bike_segments)} bike route line segments")

def near_bike_route(lon, lat):
    thresh_m = BIKE_EXCL_M
    candidates = grid_query(bike_grid, lon, lat, cell=0.001)
    for seg in candidates:
        ax, ay, bx, by = seg
        d = dist_point_to_segment(lon, lat, ax, ay, bx, by)
        if d < thresh_m:
            return True
    return False

# ── Load free surface parking lots ───────────────────────────────────────────
# OSM Overpass export (elements array). Only lots tagged fee=no are excluded;
# paid lots (fee=yes) and untagged lots are not restricted.
print("Loading free surface parking lots...")
with open('surface parking lots.json', encoding='utf-8') as f:
    _park_data = json.load(f)

FREE_PARK_CELL = 0.005  # ~550m grid cell for spatial lookup
free_park_grid: dict = {}
_free_lot_count = 0
for _el in _park_data.get('elements', []):
    if _el.get('tags', {}).get('fee') != 'no':
        continue
    b = _el.get('bounds')
    if not b:
        continue
    clat = (b['minlat'] + b['maxlat']) / 2.0
    clon = (b['minlon'] + b['maxlon']) / 2.0
    cell = (int(clon / FREE_PARK_CELL), int(clat / FREE_PARK_CELL))
    if cell not in free_park_grid:
        free_park_grid[cell] = []
    free_park_grid[cell].append((clat, clon))
    _free_lot_count += 1
print(f"  {_free_lot_count} free surface lots indexed")

def near_free_parking(lon, lat):
    """True if (lon, lat) is within FREE_PARK_EXCL_M of any free surface parking lot."""
    cx = int(lon / FREE_PARK_CELL)
    cy = int(lat / FREE_PARK_CELL)
    for dx in range(-1, 2):
        for dy in range(-1, 2):
            for (clat, clon) in free_park_grid.get((cx + dx, cy + dy), []):
                if dist_m(lat, lon, clat, clon) <= FREE_PARK_EXCL_M:
                    return True
    return False

# ── Load lanes.json for no-parking road exclusion ────────────────────────────
# Excludes destination blocks on roads that physically cannot have street parking:
#   - OSM ways with lanes >= NO_PARK_LANES (4+), or
#   - Ways with explicit parking:both/left/right = no tags
# Uses segment-based distance (same approach as bike/bus exclusions) because OSM
# geometry nodes can be spaced 100+ m apart on long straight arterials, so
# point-proximity alone misses blocks that are directly on the road.
print("Loading lanes data for no-parking exclusion...")
with open('lanes.json', encoding='utf-8') as f:
    _lanes_data = json.load(f)

_NO_PARK_BUF = NO_PARK_EXCL_M / min(LATM, LONM)
no_park_segments: list = []   # list of (ax, ay, bx, by, bbox)
_no_park_way_ct = 0
for _el in _lanes_data.get('elements', []):
    _tags = _el.get('tags', {})
    try:
        _n_lanes = int(_tags.get('lanes', 0))
    except (ValueError, TypeError):
        _n_lanes = 0
    _explicit_no_park = (
        _tags.get('parking:both') == 'no' or
        _tags.get('parking:left') == 'no' or
        _tags.get('parking:right') == 'no' or
        _tags.get('parking') == 'no'
    )
    if _n_lanes < NO_PARK_LANES and not _explicit_no_park:
        continue
    _pts = _el.get('geometry', [])
    if len(_pts) < 2:
        continue
    for _i in range(len(_pts) - 1):
        _ax, _ay = _pts[_i]['lon'],   _pts[_i]['lat']
        _bx, _by = _pts[_i+1]['lon'], _pts[_i+1]['lat']
        _bbox = (min(_ax,_bx)-_NO_PARK_BUF, min(_ay,_by)-_NO_PARK_BUF,
                 max(_ax,_bx)+_NO_PARK_BUF, max(_ay,_by)+_NO_PARK_BUF)
        no_park_segments.append((_ax, _ay, _bx, _by, _bbox))
    _no_park_way_ct += 1

no_park_seg_grid = build_grid(
    [((ax,ay,bx,by), bbox) for ax,ay,bx,by,bbox in no_park_segments], cell=0.001)
print(f"  {_no_park_way_ct} no-parking ways, {len(no_park_segments)} segments indexed")

def near_no_park_road(lon, lat, max_m=NO_PARK_EXCL_M):
    """True if (lon,lat) is within max_m of any no-parking road segment."""
    for seg in grid_query(no_park_seg_grid, lon, lat, cell=0.001):
        ax, ay, bx, by = seg
        if dist_point_to_segment(lon, lat, ax, ay, bx, by) < max_m:
            return True
    return False

# ── Load business licenses for demand scoring ─────────────────────────────────
# Active licenses with lat/lon. Used in place of LODES job density to score
# destination blocks by on-the-ground commercial activity.
#
# Source: City of Chicago Data Portal — Business Licenses
#   https://data.cityofchicago.org/Community-Economic-Development/Business-Licenses/r5kz-chrr
# Download the full CSV export and save as 'business_licenses_20260406.csv'
# (file is ~490MB and excluded from this repo due to GitHub size limits).
print("Loading business licenses...")
from datetime import datetime as _dt
_today = _dt(2026, 4, 6)
_biz_load_ct = 0
with open('business_licenses_20260406.csv', newline='', encoding='utf-8') as f:
    for row in csv.DictReader(f):
        if row.get('LICENSE STATUS') not in ('AAI', 'AAC'):
            continue
        exp = row.get('LICENSE TERM EXPIRATION DATE', '')
        try:
            if _dt.strptime(exp, '%m/%d/%Y') < _today:
                continue
        except (ValueError, TypeError):
            continue
        try:
            blat = float(row['LATITUDE'])
            blon = float(row['LONGITUDE'])
        except (ValueError, KeyError, TypeError):
            continue
        _cell = (int(blon / JOB_GRID_CELL), int(blat / JOB_GRID_CELL))
        if _cell not in biz_grid:
            biz_grid[_cell] = []
        biz_grid[_cell].append((blat, blon))
        _biz_load_ct += 1
print(f"  {_biz_load_ct} active business locations indexed in {len(biz_grid)} grid cells")

# Compute p75 normalization baseline by sampling biz_count at each grid cell centroid.
# This gives a distribution of counts across occupied Chicago areas.
_biz_sample = []
for (_gcx, _gcy), _pts in biz_grid.items():
    _clat = _gcy * JOB_GRID_CELL + JOB_GRID_CELL / 2
    _clon = _gcx * JOB_GRID_CELL + JOB_GRID_CELL / 2
    _biz_sample.append(lookup_biz_count(_clat, _clon))
_biz_sample.sort()
p75_biz_count = max(1.0, _biz_sample[int(len(_biz_sample) * 0.75)] if _biz_sample else 1.0)
print(f"  Biz count range: {min(_biz_sample) if _biz_sample else 0}–"
      f"{max(_biz_sample) if _biz_sample else 0} | p75={p75_biz_count:.0f}")

# ── Build spatial grid of retained meters (for occupied-block check) ──────────
print("Building retained meter spatial grid...")
TGRID = 0.0005  # ~55m
ret_grid = {}
for m in retained_meters:
    key = (int(m['lon'] / TGRID), int(m['lat'] / TGRID))
    if key not in ret_grid:
        ret_grid[key] = []
    ret_grid[key].append(m)

# all_meter_rate_grid is already built during initial meter loading (all meters, pre-split).

def block_has_retained_meter(lon, lat, thresh_m=EXIST_BLOCK_M):
    """True if any retained (non-flagged) meter is within thresh_m of (lon,lat)."""
    cx = int(lon / TGRID)
    cy = int(lat / TGRID)
    for dx in (-1, 0, 1):
        for dy in (-1, 0, 1):
            for m in ret_grid.get((cx+dx, cy+dy), []):
                if dist_m(lat, lon, m['lat'], m['lon']) < thresh_m:
                    return True
    return False

# ═══════════════════════════════════════════════════════════════════════════════
# FIND AND SCORE DESTINATION BLOCKS (unified by road class)
#
# Road class drives capacity fraction:
#   Class 2 (arterial):       80% of physical curb capacity, neighborhood rate
#   Class 3 (minor arterial): 40% of physical curb capacity, RES_RATE
#   Class 4 (local):          20% of physical curb capacity, RES_RATE
#   All other classes:        no meters allowed
#
# Total cap = floor((left_phys + right_phys) * fraction), split between L/R sides.
# Class 4 only: permit zone quota enforced; perpendicular cross-street bonus applied.
# ═══════════════════════════════════════════════════════════════════════════════
print("\nFinding destination blocks by road class...")

all_dest_blocks = []
class_counts_found = Counter()

for seg in segs:
    lon, lat = seg['lo'], seg['la']
    d = seg.get('d') or 'N'

    # Look up road class from transportation data via centerline 'n' code
    n_code = str(seg.get('n') or '').strip()
    road_class = road_class_lookup.get(n_code)
    if road_class not in CLASS_CAP_FRAC:
        continue

    cap_frac     = CLASS_CAP_FRAC[road_class]
    is_class4    = (road_class == '4')

    # Standard exclusions
    if near_bus_corridor(lon, lat):
        continue
    if on_ped_street(lon, lat):
        continue
    if near_bike_route(lon, lat):
        continue
    if block_has_retained_meter(lon, lat):
        continue
    if near_free_parking(lon, lat):
        continue
    if near_no_park_road(lon, lat):
        continue
    if near_park(lon, lat):
        continue

    # Permit zone lookup and perpendicular bonus (class 4 only)
    zone_id   = None
    perp_mult = 1.0
    if is_class4:
        zone_id, _ = nearest_zone(lat, lon)
        if zone_id and d in zone_meta[zone_id]['perp_dirs']:
            perp_mult = PERP_BONUS

    # Physical capacity per side (no fraction yet)
    phys_lcap = physical_capacity(seg.get('lf'), seg.get('lt'))
    phys_rcap = physical_capacity(seg.get('rf'), seg.get('rt'))

    # Compute per-side meter caps.
    # Class 4 (residential): use permit zone data where available; flat 20% otherwise.
    # Classes 2/3 (arterial/minor arterial): combined cap split randomly between sides.
    if is_class4:
        seg_id = id(seg)
        lkey = (seg_id, 'L')
        rkey = (seg_id, 'R')
        left_cap  = zone_side_cap[lkey] if lkey in zone_side_cap else int(phys_lcap * cap_frac)
        right_cap = zone_side_cap[rkey] if rkey in zone_side_cap else int(phys_rcap * cap_frac)
        if left_cap == 0 and right_cap == 0:
            continue
    else:
        total_cap = int((phys_lcap + phys_rcap) * cap_frac)
        if total_cap < 1:
            continue
        # Split total between L and R sides.
        # Max allowed |left - right|: 2 for total<=10, 4 for total>=11.
        # 50% of the time use an uneven split; otherwise even.
        max_diff  = 2 if total_cap <= 10 else 4
        max_extra = max_diff // 2
        base      = total_cap // 2
        if max_extra > 0 and total_cap > 1 and random.random() >= 0.5:
            extra = random.randint(1, max_extra)
            if random.random() < 0.5:
                left_cap  = base + extra
                right_cap = total_cap - left_cap
            else:
                right_cap = base + extra
                left_cap  = total_cap - right_cap
            left_cap  = max(0, left_cap)
            right_cap = max(0, right_cap)
        else:
            left_cap  = base
            right_cap = total_cap - base

    nbhd         = lat_lon_to_nbhd(lat, lon)
    is_near_comm = near_comm_zone(lon, lat)
    biz_factor   = biz_score_factor(lat, lon)
    zone_class   = comm_zone_class_at(lon, lat) or 'R'

    if road_class == '2':
        avg_rate = NBHD[nbhd]['avgRate']
        util     = calc_util(avg_rate, nbhd)
    else:
        # Rate: near-commercial blocks support higher rates than deep residential
        avg_rate = (NBHD[nbhd]['avgRate'] * RES_COMM_RATE_FRAC
                    if is_near_comm else RES_RATE)
        # Utilization: tiered by how constrained free parking alternatives are,
        # boosted by local business density (more businesses = more turnover demand).
        if zone_id is not None:
            _base_util = RES_UTIL_ZONE
        elif is_near_comm:
            _base_util = RES_UTIL_COMM
        else:
            _base_util = RES_UTIL_DEFAULT
        util = min(0.85, _base_util * min(RES_UTIL_JMAX, biz_factor))

    # Pedestrian commercial tier: 0=RETAIL, 1=SIX-CORNER, 2=plain, 3=none.
    # Only queried when near a commercial zone (the primary sort tier).
    ped_tier = nearest_ped_tier(lat, lon) if is_near_comm else 3

    # Estimated rate: IDW average of all nearby meters' pre-move rates anchors the
    # estimate. Business density can lift above that floor. Fallback to nbhd avg.
    _local_rate = est_local_rate(lat, lon)
    if _local_rate is not None:
        _seg_est_rate = snap_to_tier(_local_rate * max(1.0, biz_factor))
    else:
        _seg_est_rate = snap_to_tier(avg_rate * biz_factor)

    (left_dlat, left_dlon), (right_dlat, right_dlon) = side_offsets(d)

    # Shift marker toward the block end closest to the commercial zone.
    # Uses whichever side has address data; both sides run parallel so the
    # along-street offset is identical. The address number at that end is
    # used instead of the midpoint so the label matches the visual position.
    _ref_af = seg.get('lf') or seg.get('rf')
    _ref_at = seg.get('lt') or seg.get('rt')
    _cdlat, _cdlon, _use_hi = comm_end_side(lat, lon, d, _ref_af, _ref_at)

    def _end_addr_num(af, at_):
        """Return the address number at the commercial end, or None for midpoint."""
        if _use_hi is None or not (af and at_ and
                str(af).strip().isdigit() and str(at_).strip().isdigit()):
            return None
        lo = min(int(str(af).strip()), int(str(at_).strip()))
        hi = max(int(str(af).strip()), int(str(at_).strip()))
        return hi if _use_hi else lo

    if left_cap >= 1:
        all_dest_blocks.append({
            'lat':           lat + left_dlat + _cdlat,
            'lon':           lon + left_dlon + _cdlon,
            'addr':          side_addr(seg, seg.get('lf'), seg.get('lt'),
                                       addr_num=_end_addr_num(seg.get('lf'), seg.get('lt'))),
            'cap':           left_cap,
            'score':         avg_rate * util * left_cap * perp_mult * biz_factor,
            'nbhd':          nbhd,
            'side':          'L',
            'used':          0,
            'res':           is_class4,
            'zone_id':       zone_id,
            'class':         road_class,
            'near_comm':     is_near_comm,
            'ped_tier':      ped_tier,
            'avg_rate':      avg_rate,
            'biz_factor':    biz_factor,
            'est_rate':      _seg_est_rate,
            'zone_class':    zone_class,
        })

    if right_cap >= 1:
        all_dest_blocks.append({
            'lat':           lat + right_dlat + _cdlat,
            'lon':           lon + right_dlon + _cdlon,
            'addr':          side_addr(seg, seg.get('rf'), seg.get('rt'),
                                       addr_num=_end_addr_num(seg.get('rf'), seg.get('rt'))),
            'cap':           right_cap,
            'score':         avg_rate * util * right_cap * perp_mult * biz_factor,
            'nbhd':          nbhd,
            'side':          'R',
            'used':          0,
            'res':           is_class4,
            'zone_id':       zone_id,
            'class':         road_class,
            'near_comm':     is_near_comm,
            'ped_tier':      ped_tier,
            'avg_rate':      avg_rate,
            'biz_factor':    biz_factor,
            'est_rate':      _seg_est_rate,
            'zone_class':    zone_class,
        })
    class_counts_found[road_class] += 1

print(f"  {len(all_dest_blocks)} candidate block-sides found (before dedup)")
for rc in sorted(class_counts_found):
    print(f"    class {rc}: {class_counts_found[rc]} segments")

# Dedup by (lat rounded 4dp, lon rounded 4dp, side)
seen_keys = set()
deduped   = []
for b in all_dest_blocks:
    key = (round(b['lat'], 4), round(b['lon'], 4), b['side'])
    if key not in seen_keys:
        seen_keys.add(key)
        deduped.append(b)
all_dest_blocks = deduped
print(f"  {len(all_dest_blocks)} block-sides after dedup")

# Sort by composite key:
#   1. Commercial proximity (near B/C/D zone) — first priority
#   2. Ped commercial proximity (class 2/3 on ped street) — within near_comm tier
#   3. Road class (2 → 3 → 4) — within each proximity tier
#   4. Score descending — within each class tier
_CLASS_TIER = {'2': 0, '3': 1, '4': 2}
all_dest_blocks.sort(key=lambda b: (
    0 if b['near_comm'] else 1,
    b.get('ped_tier', 3),           # 0=RETAIL, 1=SIX-CORNER, 2=plain ped, 3=none
    _CLASS_TIER.get(b['class'], 3),
    -b['score']
))

near_comm_count = sum(1 for b in all_dest_blocks if b['near_comm'])
_ptier_counts = {0: 0, 1: 0, 2: 0}
for b in all_dest_blocks:
    t = b.get('ped_tier', 3)
    if t in _ptier_counts:
        _ptier_counts[t] += 1
print(f"  {near_comm_count} block-sides near commercial zones "
      f"(ped-retail={_ptier_counts[0]}, ped-sixcorner={_ptier_counts[1]}, "
      f"ped-plain={_ptier_counts[2]}), "
      f"{len(all_dest_blocks) - near_comm_count} not near commercial zones")

# Print top 20
print("\nTop 20 destination blocks by priority:")
for b in all_dest_blocks[:20]:
    _pt = b.get('ped_tier', 3)
    _plabel = ['retail','6corn','plain','--'][_pt] if _pt < 4 else '--'
    print(f"  comm={'Y' if b['near_comm'] else 'N'}"
          f"  ped={_plabel}"
          f"  class={b['class']}"
          f"  score={b['score']:.1f}"
          f"  cap={b['cap']}"
          f"  addr={b['addr']}")

# ── Pre-compute per-terminal candidates for client-side re-ranking ─────────────
# For each flagged terminal, find the best block of each zone class (B/C/D/R)
# that has sufficient raw capacity (ignoring shared usage). These are stored as
# alternative candidates so the JS can re-rank based on slider weights and zone
# filters without re-running the script.
print("\nPre-computing per-terminal alternative candidates...")
_comm_cands_by_class = {'B': [], 'C': [], 'D': [], 'R': []}
for b in all_dest_blocks:
    zc = b.get('zone_class', 'R')
    if zc in _comm_cands_by_class:
        _comm_cands_by_class[zc].append(b)

def _make_cand(b):
    return [round(b['lat'], 5), round(b['lon'], 5), b['addr'], b['est_rate'],
            b.get('zone_class', 'R'), b.get('ped_tier', 3), round(b.get('biz_factor', 1.0), 2)]

def find_zone_candidates(terminal_sp):
    """Find best block of each zone class with cap >= terminal_sp."""
    result = {}
    for zc, blist in _comm_cands_by_class.items():
        for b in blist:
            if b['cap'] >= terminal_sp:
                result[zc] = b
                break
    return result

terminal_candidates = {}
for m in flagged_meters:
    zone_cands = find_zone_candidates(m['sp'])
    terminal_candidates[m['tid']] = {zc: _make_cand(b) for zc, b in zone_cands.items()}

print(f"  Done — {len(terminal_candidates)} terminals have pre-computed candidates")

# ═══════════════════════════════════════════════════════════════════════════════
# CLUSTER FLAGGED TERMINALS BY CURRENT PROXIMITY
# Terminals within CLUSTER_RADIUS_M of each other currently share a block-side
# and should ideally move together to the same destination.
# ═══════════════════════════════════════════════════════════════════════════════
print(f"\nClustering {len(flagged_meters)} flagged terminals by current proximity...")

CLUSTER_RADIUS_M = 50   # ~half a block; terminals this close are treated as a group

CLUSTER_CELL = CLUSTER_RADIUS_M / min(LATM, LONM)
cgrid: dict = defaultdict(list)
for i, fm in enumerate(flagged_meters):
    key = (int(fm['lat'] / CLUSTER_CELL), int(fm['lon'] / CLUSTER_CELL))
    cgrid[key].append(i)

assigned_cid = [None] * len(flagged_meters)
clusters: list = []

for seed_i in range(len(flagged_meters)):
    if assigned_cid[seed_i] is not None:
        continue
    cid = len(clusters)
    clusters.append([])
    queue = [seed_i]
    while queue:
        i = queue.pop()
        if assigned_cid[i] is not None:
            continue
        assigned_cid[i] = cid
        clusters[cid].append(flagged_meters[i])
        cx = int(flagged_meters[i]['lat'] / CLUSTER_CELL)
        cy = int(flagged_meters[i]['lon'] / CLUSTER_CELL)
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for j in cgrid.get((cx + dx, cy + dy), []):
                    if (assigned_cid[j] is None
                            and dist_m(flagged_meters[i]['lat'], flagged_meters[i]['lon'],
                                       flagged_meters[j]['lat'], flagged_meters[j]['lon'])
                                < CLUSTER_RADIUS_M):
                        queue.append(j)

# Sort clusters largest-first so big groups get placed before tiny stragglers
clusters.sort(key=lambda g: sum(m['sp'] for m in g), reverse=True)

total_sp_to_move = sum(m['sp'] for m in flagged_meters)
print(f"  {len(clusters)} clusters, {total_sp_to_move} total spaces to relocate")
print(f"  Cluster sizes (spaces): "
      f"max={max(sum(m['sp'] for m in g) for g in clusters)}, "
      f"median={sorted(sum(m['sp'] for m in g) for g in clusters)[len(clusters)//2]}, "
      f"mean={total_sp_to_move/len(clusters):.1f}")

# ═══════════════════════════════════════════════════════════════════════════════
# ASSIGN TERMINALS TO BLOCKS (cluster-aware, space-capacity matching)
#
# Terminals are ordered in cluster sequence so co-located meters stay adjacent.
# Within each cluster, sort smallest-sp first so the smallest terminals fill
# the last slivers of each block's capacity.
#
# For each terminal we walk the score-sorted block list and assign it to the
# first block with (cap - space_used) >= terminal.sp.  Because we walk the list
# in the SAME order for every terminal, consecutive terminals from the same
# cluster naturally land on the same block until it fills up, then overflow to
# the next block — preserving group cohesion without complex bin-packing.
# ═══════════════════════════════════════════════════════════════════════════════
print(f"\nAssigning {len(flagged_meters)} flagged terminals to blocks...")

all_blocks = all_dest_blocks  # sorted: (near_comm desc, class asc, score desc)

# Initialise per-block space tracker
for b in all_blocks:
    b['space_used'] = 0

# Near-commercial class 4 blocks (residential cross streets adjacent to B/C/D zones)
# are given first priority for small-sp terminals — they fill cross-street parking
# before arterials absorb everything.  All other blocks use the composite sort order.
nc_class4  = [b for b in all_blocks if b['class'] == '4' and b['near_comm']]
other_blocks = [b for b in all_blocks if not (b['class'] == '4' and b['near_comm'])]
# other_blocks retains the composite sort: near-comm class 2 → near-comm class 3 →
# non-comm class 2 → non-comm class 3 → non-comm class 4

max_nc4_cap = max((b['cap'] for b in nc_class4), default=0)
print(f"  Near-commercial class 4 blocks: {len(nc_class4)}, max cap: {max_nc4_cap}")
print(f"  Other blocks: {len(other_blocks)}")

def try_assign(m, block_list):
    """Try to assign terminal m to the first eligible block in block_list. Returns True if placed."""
    for b in block_list:
        remaining = b['cap'] - b['space_used']
        if remaining >= m['sp']:
            proposals[m['tid']] = [
                round(b['lat'], 5), round(b['lon'], 5), b['addr'], b['est_rate'],
                b.get('zone_class', 'R'), b.get('ped_tier', 3), round(b.get('biz_factor', 1.0), 2),
            ]
            b['used']       += 1
            b['space_used'] += m['sp']
            if b['res'] and b['zone_id']:
                zone_meta[b['zone_id']]['used'] += 1
            return True
    return False

# Build ordered terminal list: clusters in score order, terminals within each
# cluster sorted smallest-sp first so small terminals fill leftover capacity.
ordered_terminals = []
for grp in clusters:
    ordered_terminals.extend(sorted(grp, key=lambda m: m['sp']))

proposals = {}
placed    = 0

for m in ordered_terminals:
    assigned = False
    # Small terminals: try near-commercial class 4 cross streets first, then everything else.
    # Large terminals (sp > max class 4 cap): skip straight to the composite-sorted list.
    if m['sp'] <= max_nc4_cap:
        assigned = try_assign(m, nc_class4)
    if not assigned:
        assigned = try_assign(m, other_blocks)
    if assigned:
        placed += 1

unplaced = len(ordered_terminals) - placed

placed_by_class = Counter(b['class'] for b in all_blocks if b['used'] > 0)
class_detail = ', '.join(f"class{rc}={placed_by_class[rc]}" for rc in sorted(placed_by_class))
print(f"  Placed: {placed} ({class_detail}), Unplaced: {unplaced}")

# Neighborhood distribution
nbhd_counts = Counter()
for b in all_blocks:
    if b['used'] > 0:
        nbhd_counts[b['nbhd']] += b['used']
print("\nPlacements by neighborhood:")
for nbhd, count in nbhd_counts.most_common():
    print(f"  {nbhd}: {count}")

# Permit zone quota usage
zones_used = [(zid, zm) for zid, zm in zone_meta.items() if zm['used'] > 0]
zones_used.sort(key=lambda x: -x[1]['used'])
print(f"\nPermit zones used: {len(zones_used)} zones")
for zid, zm in zones_used[:10]:
    print(f"  zone {zid}: {zm['used']}/{zm['meter_quota']} terminals placed "
          f"(total zone cap {zm['total_cap']} spaces)")

# ═══════════════════════════════════════════════════════════════════════════════
# OUTPUT
# ═══════════════════════════════════════════════════════════════════════════════
# Build final output: per terminal, a list of candidates.
# Index 0 = greedy-assigned result (capacity-aware, best overall).
# Additional entries = best alternative of each remaining zone class for client-side re-ranking.
output_proposals = {}
for m in flagged_meters:
    tid = m['tid']
    greedy = proposals.get(tid)                      # [lat, lon, addr, rate, zc, pt, jf] or None
    zone_cands = terminal_candidates.get(tid, {})    # {zc: [lat, lon, addr, rate, zc, pt, jf]}

    if greedy:
        greedy_zc = greedy[4]
        cands = [greedy]
        # Append best candidates of other zone classes not already covered by greedy
        for zc in ['B', 'C', 'D', 'R']:
            if zc == greedy_zc:
                continue
            alt = zone_cands.get(zc)
            if alt and (abs(alt[0] - greedy[0]) > 0.0001 or abs(alt[1] - greedy[1]) > 0.0001):
                cands.append(alt)
        output_proposals[tid] = cands
    elif zone_cands:
        # No greedy result — use best available candidates in priority order
        output_proposals[tid] = [zone_cands[zc] for zc in ['B', 'C', 'D', 'R'] if zc in zone_cands]

# ── Build permit zone utilization data for map layer ──────────────────────────
# Physical capacity is from the address-range formula, but CPM meters already occupy
# some of those curb spaces. Effective permit capacity = physical_cap - meter_spaces.
# util_rate = stickers / effective_cap (can exceed 1.0 = oversubscribed).
# Output: [[lat, lon, util_rate, total_cap, stickers, meter_spaces], ...]

# Build spatial grid of ALL meter spaces for zone-meter matching.
# Cell ~55m; for each segment location in a zone, sum meter spaces within 30m.
_MZONE_TGRID = 0.0005
_mzone_grid: dict = {}   # cell -> list of (lat, lon, spaces)
for _m in meters:
    _k = (int(_m['lon'] / _MZONE_TGRID), int(_m['lat'] / _MZONE_TGRID))
    if _k not in _mzone_grid:
        _mzone_grid[_k] = []
    _mzone_grid[_k].append((_m['lat'], _m['lon'], _m['sp']))

def _count_meter_spaces_near(lat, lon, radius_m=EXIST_BLOCK_M):
    cx = int(lon / _MZONE_TGRID)
    cy = int(lat / _MZONE_TGRID)
    total = 0
    for dx in (-1, 0, 1):
        for dy in (-1, 0, 1):
            for (mlat, mlon, msp) in _mzone_grid.get((cx+dx, cy+dy), []):
                if dist_m(lat, lon, mlat, mlon) < radius_m:
                    total += msp
    return total

zone_util_data = []
for zone_id, zm in zone_meta.items():
    if zone_id not in zone_centroids:
        continue
    clat, clon = zone_centroids[zone_id]
    total_cap = zm['total_cap']
    stickers  = zm['stickers']
    # Sum meter spaces at each segment location matched to this zone
    meter_spaces = 0
    seen_locs = set()
    for (slat, slon) in zone_locs.get(zone_id, []):
        loc_key = (round(slat, 4), round(slon, 4))
        if loc_key in seen_locs:
            continue
        seen_locs.add(loc_key)
        meter_spaces += _count_meter_spaces_near(slat, slon)
    effective_cap = max(1, total_cap - meter_spaces)
    util_rate = round(stickers / effective_cap, 3)
    zone_util_data.append([round(clat, 5), round(clon, 5), util_rate,
                           total_cap, stickers, meter_spaces])

zone_util_gz  = gzip.compress(json.dumps(zone_util_data, separators=(',', ':')).encode('utf-8'))
zone_util_b64 = base64.b64encode(zone_util_gz).decode('ascii')
print(f"  Zone utilization: {len(zone_util_data)} zones encoded ({len(zone_util_b64):,} chars)")

# ═══════════════════════════════════════════════════════════════════════════════
# POST-PROCESSING: Floor removal → least-productive removal → rate minimization
# ═══════════════════════════════════════════════════════════════════════════════
# ── Rate elasticity helpers (used in post-processing) ─────────────────────────
def snap_to_tier(rate):
    return min(RATE_TIERS, key=lambda t: abs(t - rate))

_avg_inv_eps = sum(1.0 / e for e in TIER_ELASTICITY.values()) / len(TIER_ELASTICITY)

def get_tier_factor(base_factor, tier):
    """Return the tier-specific factor, scaled inversely by elasticity.
    Inelastic tiers (low price) get pushed harder; elastic tiers get lighter touch."""
    eps = TIER_ELASTICITY.get(tier, 0.35)
    return min(1.0, base_factor * (1.0 / eps) / _avg_inv_eps)

def elast_rev(base_rev, base_rate, new_rate, tier):
    """Revenue adjusted for demand response: Rev ~ base_rev * (new_rate/base_rate)^(1-eps).
    When eps=0 this reduces to simple linear scaling; higher eps adds demand penalty."""
    if base_rate <= 0 or new_rate <= 0:
        return base_rev
    eps = TIER_ELASTICITY.get(tier, 0.35)
    return base_rev * ((new_rate / base_rate) ** (1.0 - eps))

print("\nPost-processing scenario removals and rate minimization...")

# ── Constants (match meter_sim_v10.html) ──────────────────────────────────────
SRSV        = 386_661_383   # Settlement System Revenue Value
CPI_FACTOR  = 1.382         # matches HTML constant
RATE_TIERS  = [0.50, 2.50, 4.75, 7.00, 14.00]

def get_rate_cap(orig_rate):
    """Mirror getRateCap() from the JS."""
    tier = min(RATE_TIERS, key=lambda t: abs(t - orig_rate))
    return (tier + 0.25) * CPI_FACTOR

# ── Decode full meter data (with REV, HRS, DAYS, SP) from HTML B64 ─────────────
# Fields: [id, addr, lat, lon, rate, sp, hrs, days, util, rev, nbhd, clz]
FI = {'ID':0,'ADDR':1,'LAT':2,'LON':3,'RATE':4,'SP':5,'HRS':6,'DAYS':7,'UTIL':8,'REV':9,'NBHD':10,'CLZ':11}

b64_m = re.search(r'const B64\s*=\s*`([^`]+)`', html)
if not b64_m:
    print("  WARNING: B64 constant not found — skipping post-processing")
    raw_data = []
else:
    raw_data = json.loads(gzip.decompress(base64.b64decode(b64_m.group(1))).decode('utf-8'))
    print(f"  Decoded {len(raw_data)} meters from HTML B64 data")

if raw_data:
    # Build lookup
    raw_by_tid = {str(row[FI['ID']]): row for row in raw_data}

    # Set of bike/ped TIDs without a proposal → already treated as removed
    bp_removed = {tid for tid in FLAGGED_IDS if tid not in output_proposals}

    # ── Compute after-scenario revenue at MAX rate cap (with elasticity) ─────────
    # All active meters (retained and relocated) scale from their base to cap.
    # Elasticity is applied so floor-removal threshold reflects real demand response.
    after_rev_max = {}
    prop_base_rate = {}   # pRate for each relocated terminal (used in Step 3)
    for row in raw_data:
        tid = str(row[FI['ID']])
        sp  = row[FI['SP']]
        if tid in bp_removed:
            after_rev_max[tid] = 0.0
            continue
        if tid in FLAGGED_IDS and tid in output_proposals:
            prop  = output_proposals[tid]
            cand  = prop[0] if isinstance(prop[0], list) else prop
            prate = cand[3] if (len(cand) > 3 and cand[3] is not None) else row[FI['RATE']]
            cap_rate = get_rate_cap(prate)
            tier     = snap_to_tier(prate)
            orig_rev  = row[FI['REV']]
            orig_rate = row[FI['RATE']]
            base_rev  = (orig_rev * prate / orig_rate) if orig_rate > 0 else orig_rev
            after_rev_max[tid] = elast_rev(base_rev, prate, cap_rate, tier)
            prop_base_rate[tid] = prate
        else:
            orig_rate = row[FI['RATE']]
            cap_rate  = get_rate_cap(orig_rate)
            tier      = snap_to_tier(orig_rate)
            orig_rev  = row[FI['REV']]
            after_rev_max[tid] = elast_rev(orig_rev, orig_rate, cap_rate, tier)

    # ── JS demand model (mirrors calcUtil / NBHD in meter_sim_v10.html) ──────────
    JS_NBHD_DENSITY = {
        'loop': 1.10, 'south_loop': 1.03, 'near_west': 1.01,
        'north_side': 0.97, 'far_north': 0.94, 'northwest': 0.91,
        'west_side': 0.88, 'southwest': 0.87, 'far_south': 0.85,
    }

    def js_base_util(rate):
        if rate >= 14:   return 0.55
        if rate >= 7:    return 0.72
        if rate >= 4.75: return 0.78
        if rate >= 2.5:  return 0.65
        return 0.50

    def js_calc_util(rate, nbhd):
        bu = js_base_util(rate)
        nd = JS_NBHD_DENSITY.get(nbhd, 0.90)
        return min(0.97, max(0.25, bu * nd * 1.05 * 1.02))

    def js_annual_rev(row, applied_rate):
        """JS-equivalent annual revenue: sp * rate * calcUtil(rate, nbhd) * hrs * days."""
        nbhd = row[FI['NBHD']]
        sp   = row[FI['SP']]
        hrs  = row[FI['HRS']]
        days = row[FI['DAYS']]
        util = js_calc_util(applied_rate, nbhd)
        return sp * applied_rate * util * hrs * days

    def applied_rate_for(row, tid, base_f):
        """Compute the rate applied to a terminal at a given base_factor."""
        if tid in FLAGGED_IDS and tid in prop_base_rate:
            prate    = prop_base_rate[tid]
            cap_rate = get_rate_cap(prate)
            tier     = snap_to_tier(prate)
            return prate + (cap_rate - prate) * get_tier_factor(base_f, tier)
        else:
            orig_rate = row[FI['RATE']]
            cap_rate  = get_rate_cap(orig_rate)
            tier      = snap_to_tier(orig_rate)
            return orig_rate + (cap_rate - orig_rate) * get_tier_factor(base_f, tier)

    def system_rev_at(base_f, removed_set):
        """JS-model system revenue at a given base_factor, excluding removed_set.
        Uses calcUtil step function to match what the JS simulator displays."""
        total = 0.0
        for row in raw_data:
            tid = str(row[FI['ID']])
            if tid in removed_set:
                continue
            arate = applied_rate_for(row, tid, base_f)
            total += js_annual_rev(row, arate)
        return total

    def solve_base_factor(removed_set, target_rev):
        """Binary search for base_factor that achieves target_rev given removed_set."""
        lo, hi = 0.0, 1.0
        for _ in range(60):
            mid = (lo + hi) / 2.0
            if system_rev_at(mid, removed_set) < target_rev:
                lo = mid
            else:
                hi = mid
        return (lo + hi) / 2.0

    # ── STEP 0: Initial base_factor solve with only bp_removed ────────────────
    print("  Step 0: Initial base_factor solve (JS model)...")
    init_base_factor = solve_base_factor(bp_removed, TARGET_SYSTEM_REV)
    print(f"    Initial base_factor: {init_base_factor:.4f}  "
          f"(${system_rev_at(init_base_factor, bp_removed):,.0f})")

    # ── STEP 1: Remove meters below $2K/space/yr using JS calcUtil at actual rates
    # Compute applied rate for each active terminal at init_base_factor, then use
    # JS demand model to estimate utilization → JS-equivalent revenue → floor check.
    TARGET_SPACES = 30_500

    below_floor = set()
    for row in raw_data:
        tid = str(row[FI['ID']])
        if tid in bp_removed:
            continue
        sp = row[FI['SP']]
        if sp <= 0:
            continue
        arate = applied_rate_for(row, tid, init_base_factor)
        js_rev = js_annual_rev(row, arate)
        if (js_rev / sp) < 2000:
            below_floor.add(tid)

    print(f"  Step 1: Below $2K/space/yr floor: {len(below_floor)} terminals removed")
    for tid in below_floor:
        if tid in output_proposals:
            del output_proposals[tid]

    # ── STEP 2: Trim to ~TARGET_SPACES active spaces by removing least-productive ─
    after_step1 = bp_removed | below_floor
    active_rows = [r for r in raw_data if str(r[FI['ID']]) not in after_step1]
    total_active_spaces = sum(r[FI['SP']] for r in active_rows)
    print(f"  Step 2: Active spaces after floor removal: {total_active_spaces:,}")

    least_productive = set()
    if total_active_spaces > TARGET_SPACES:
        # Score each active terminal by JS rev/space at init_base_factor
        scored = []
        for row in active_rows:
            tid   = str(row[FI['ID']])
            sp    = row[FI['SP']]
            if sp <= 0:
                continue
            arate = applied_rate_for(row, tid, init_base_factor)
            js_rev = js_annual_rev(row, arate)
            scored.append((js_rev / sp, sp, tid))
        scored.sort()   # ascending: remove least-productive first

        spaces_to_cut = total_active_spaces - TARGET_SPACES
        cut_so_far = 0
        for _, sp, tid in scored:
            if cut_so_far >= spaces_to_cut:
                break
            least_productive.add(tid)
            cut_so_far += sp
            if tid in output_proposals:
                del output_proposals[tid]
        remaining = total_active_spaces - cut_so_far
        print(f"    Removed {len(least_productive)} terminals ({cut_so_far:,} spaces) "
              f"-> {remaining:,} active spaces")
    else:
        print(f"    Already at or below {TARGET_SPACES:,} spaces — no trimming needed")

    # ── STEP 3: Re-solve per-tier rate factors targeting TARGET_SYSTEM_REV ───────
    all_removed = after_step1 | least_productive
    print(f"  Step 3: Re-solving base_factor with {len(all_removed)} total removed terminals...")
    base_factor = solve_base_factor(all_removed, TARGET_SYSTEM_REV)
    achieved_rev = system_rev_at(base_factor, all_removed)

    per_tier_factors = {str(tier): round(get_tier_factor(base_factor, tier), 4)
                        for tier in RATE_TIERS}

    print(f"    Base factor: {base_factor:.4f}  |  Target: ${TARGET_SYSTEM_REV:,.0f}  |  "
          f"Achieved: ${achieved_rev:,.0f}")
    print(f"    Per-tier factors:")
    for tier in RATE_TIERS:
        tf  = per_tier_factors[str(tier)]
        cap = get_rate_cap(tier)
        new = round(tier + (cap - tier) * tf, 2)
        print(f"      ${tier:.2f}/hr  ->  ${new:.2f}/hr  (factor {tf})")

    rate_factor = round(base_factor, 4)  # kept for backward compat display

    # ── Restructure output to v2 format ───────────────────────────────────────
    output_proposals = {
        'v': 2,
        'proposals': output_proposals,
        'removed': sorted(below_floor | least_productive),
        'rate_factor': rate_factor,          # base factor (for backward compat)
        'rate_factors': per_tier_factors,    # per-tier factors keyed by tier string
    }
    print(f"\n  V2 output: {len(output_proposals['proposals'])} relocations, "
          f"{len(output_proposals['removed'])} additional removals, "
          f"base_factor={rate_factor:.4f}")

print(f"\nWriting proposals_b64.txt...")
compressed = gzip.compress(json.dumps(output_proposals, separators=(',', ':')).encode('utf-8'))
encoded    = base64.b64encode(compressed).decode('ascii')
with open('proposals_b64.txt', 'w') as f:
    f.write(encoded)
print(f"  Done. File size: {len(encoded):,} chars")

# ── Embed into meter_sim_v10.html ─────────────────────────────────────────────
HTML_FILE = 'meter_sim_v10.html'
print(f"\nEmbedding into {HTML_FILE}...")
with open(HTML_FILE, 'r', encoding='utf-8', errors='replace') as f:
    html = f.read()

# Embed PROPOSALS_B64
new_html, n = re.subn(
    r'(const PROPOSALS_B64\s*=\s*`)([^`]*?)(`)',
    lambda m: m.group(1) + encoded + m.group(3),
    html, count=1, flags=re.DOTALL
)
if n == 0:
    print("  WARNING: PROPOSALS_B64 constant not found in HTML — skipping embed.")
else:
    print(f"  PROPOSALS_B64 updated ({len(encoded):,} chars).")

# Embed N_TO_NAME street name lookup so snapToCenter produces real addresses.
# Format: const N_TO_NAME = {"code":"S YALE AVE", ...};
n_to_name_js = json.dumps(street_name_lookup, separators=(',', ':'))
new_html, n2 = re.subn(
    r'(const N_TO_NAME\s*=\s*)\{[^;]*\};',
    lambda m: m.group(1) + n_to_name_js + ';',
    new_html, count=1
)
if n2 == 0:
    print("  WARNING: N_TO_NAME constant not found in HTML — skipping embed.")
else:
    print(f"  N_TO_NAME updated ({len(n_to_name_js):,} chars, {len(street_name_lookup)} entries).")

# Embed ZONE_UTIL_B64
new_html, n3 = re.subn(
    r'(const ZONE_UTIL_B64\s*=\s*`)([^`]*?)(`)',
    lambda m: m.group(1) + zone_util_b64 + m.group(3),
    new_html, count=1, flags=re.DOTALL
)
if n3 == 0:
    print("  WARNING: ZONE_UTIL_B64 constant not found in HTML — skipping embed.")
else:
    print(f"  ZONE_UTIL_B64 updated ({len(zone_util_b64):,} chars).")

# Embed BSB_ROUTES_B64 (geometry-based check replaces pre-computed BSB_IDS list)
new_html, n4 = re.subn(
    r'(const BSB_ROUTES_B64\s*=\s*`)([^`]*?)(`)',
    lambda m: m.group(1) + BSB_ROUTES_B64 + m.group(3),
    new_html, count=1, flags=re.DOTALL
)
if n4 == 0:
    print("  WARNING: BSB_ROUTES_B64 constant not found in HTML — skipping embed.")
else:
    print(f"  BSB_ROUTES_B64 updated ({len(BSB_ROUTES_B64):,} chars).")

if n > 0 or n2 > 0 or n3 > 0 or n4 > 0:
    with open(HTML_FILE, 'w', encoding='utf-8') as f:
        f.write(new_html)
    print(f"  {HTML_FILE} saved.")

# ── Embed into meter_sim_v11.html ─────────────────────────────────────────────
HTML_FILE_V11 = 'meter_sim_v11.html'
print(f"\nEmbedding into {HTML_FILE_V11}...")
with open(HTML_FILE_V11, 'r', encoding='utf-8', errors='replace') as f:
    html11 = f.read()

v11_n = 0

# Embed PROPOSALS_B64
html11, _n = re.subn(
    r'(const PROPOSALS_B64\s*=\s*`)([^`]*?)(`)',
    lambda m: m.group(1) + encoded + m.group(3),
    html11, count=1, flags=re.DOTALL
)
v11_n += _n
if _n == 0:
    print("  WARNING: PROPOSALS_B64 not found in v11 — skipping.")
else:
    print(f"  PROPOSALS_B64 updated ({len(encoded):,} chars).")

# Embed BSB_ROUTES_B64
html11, _n = re.subn(
    r'(const BSB_ROUTES_B64\s*=\s*`)([^`]*?)(`)',
    lambda m: m.group(1) + BSB_ROUTES_B64 + m.group(3),
    html11, count=1, flags=re.DOTALL
)
v11_n += _n
if _n == 0:
    print("  WARNING: BSB_ROUTES_B64 not found in v11 — skipping.")
else:
    print(f"  BSB_ROUTES_B64 updated ({len(BSB_ROUTES_B64):,} chars).")

# Embed ZONE_UTIL_B64
html11, _n = re.subn(
    r'(const ZONE_UTIL_B64\s*=\s*`)([^`]*?)(`)',
    lambda m: m.group(1) + zone_util_b64 + m.group(3),
    html11, count=1, flags=re.DOTALL
)
v11_n += _n
if _n == 0:
    print("  WARNING: ZONE_UTIL_B64 not found in v11 — skipping.")
else:
    print(f"  ZONE_UTIL_B64 updated ({len(zone_util_b64):,} chars).")

if v11_n > 0:
    with open(HTML_FILE_V11, 'w', encoding='utf-8') as f:
        f.write(html11)
    print(f"  {HTML_FILE_V11} saved.")

print("\nProposals generation complete.")

