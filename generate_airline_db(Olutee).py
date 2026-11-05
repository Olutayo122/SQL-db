#!/usr/bin/env python3
"""
generate_airline_db.py
======================

WHY THIS TOPIC?
---------------
An airline gives a naturally relational design (airports -> routes -> flights ->
bookings -> passengers) and has every measurement scale the brief asks for,
plus realistic cause-and-effect between columns (weather -> delays, booking
lead time -> fare, cabin -> satisfaction). That makes the data useful for later
analysis (regression, classification, association rules) instead of being
uniform noise.

NOTHING IS DOWNLOADED
---------------------
Every row is generated here. A small amount of general public knowledge was typed
in by hand (airport codes, approximate coordinates and elevations, typical
aircraft seat counts and ranges, typical monthly temperatures). No dataset, API
or file from anybody else is used. All passengers are invented.

MEASUREMENT SCALES (brief: >= 1 column of each; >= 7 columns)
-------------------------------------------------------------
NOMINAL  : weather_condition, payment_method, booking_channel, home_country,
           flight_status, booking_status, route_category, extra_name,
           extra_category, region, manufacturer, engine_type, iata_code
ORDINAL  : cabin_class (Economy < Premium Economy < Business),
           loyalty_tier (Standard < Silver < Gold < Platinum),
           satisfaction_rating (1 to 5)
INTERVAL : origin_temperature_c (0 C is arbitrary), scheduled_departure,
           scheduled_arrival, booking_date, signup_date, birth_year,
           year_built, elevation_m (zero = sea level, an arbitrary datum)
RATIO    : fare_gbp, checked_baggage_kg, departure_delay_min, arrival_delay_min,
           distance_km, seats_capacity, base_fare_gbp, quantity,
           unit_price_paid, weekly_frequency, range_km, cruise_speed_kmh

KEYS (extra marks for foreign and compound keys across tables)
--------------------------------------------------------------
Compound PRIMARY KEYS : flight_cabins(flight_id, cabin_class)
                        booking_extras(booking_id, extra_id)
Compound UNIQUE keys  : routes(origin, destination)
                        flights(flight_number, scheduled_departure)
                        bookings(flight_id, seat_number)  -> no seat sold twice
COMPOSITE FOREIGN KEY : bookings(flight_id, cabin_class) ->
                        flight_cabins(flight_id, cabin_class)
                        (a passenger can only hold a cabin that the flight sells)
Simple foreign keys   : everywhere else (see CREATE TABLE statements)
"""

import bisect
import math
import random
import sqlite3
from datetime import date, datetime, time, timedelta
from pathlib import Path

# =============================================================================
# 0. GLOBAL SETTINGS
# =============================================================================
# A fixed seed makes the database exactly reproducible, so the report, the
# screenshots and the marker's run of this script all agree.
SEED = 2026
random.seed(SEED)

DB_PATH = Path("kestrel_air.db")

# The airline operates through calendar 2026. SNAPSHOT is the day the database
# was "extracted": flights up to and including that day are history (with
# weather, delays and ratings); later flights are only "Scheduled" and have
# partial bookings. Having a future section makes NULLs and statuses realistic.
FLIGHTS_FROM = date(2026, 1, 1)
FLIGHTS_TO = date(2026, 12, 31)
SNAPSHOT = date(2026, 10, 29)
SALES_OPEN = date(2025, 9, 1)         # tickets go on sale four months before launch
SIGNUP_FROM = date(2025, 6, 1)        # website / loyalty scheme launch

N_PASSENGERS = 50_000                 # many people fly once or twice, a few fly a lot
SCHEDULE_SCALE = 0.10                 # thins the weekly schedule to a small regional airline
MIN_TURNAROUND = timedelta(minutes=45)


# =============================================================================
# 1. REFERENCE DATA (typed in from general knowledge, approximate on purpose)
# =============================================================================
# (iata, name, city, country, region, lat, lon, elevation_m, is_hub, mean_temp_c, seasonal_amp_c)
# mean_temp_c / seasonal_amp_c describe a typical annual temperature cycle and are
# used only to simulate the temperature column; they are NOT stored in the DB.
AIRPORTS = [
    ("MAN", "Manchester Airport", "Manchester", "United Kingdom", "UK", 53.354, -2.275, 78, 1, 10.0, 6.5),
    ("EDI", "Edinburgh Airport", "Edinburgh", "United Kingdom", "UK", 55.950, -3.373, 41, 1, 9.0, 6.0),
    ("LGW", "London Gatwick", "London", "United Kingdom", "UK", 51.148, -0.190, 62, 0, 11.5, 7.0),
    ("BHX", "Birmingham Airport", "Birmingham", "United Kingdom", "UK", 52.454, -1.748, 99, 0, 10.5, 6.8),
    ("BFS", "Belfast International", "Belfast", "United Kingdom", "UK", 54.657, -6.216, 81, 0, 9.5, 5.5),
    ("ABZ", "Aberdeen Airport", "Aberdeen", "United Kingdom", "UK", 57.202, -2.198, 65, 0, 8.5, 5.8),
    ("INV", "Inverness Airport", "Inverness", "United Kingdom", "UK", 57.542, -4.047, 9, 0, 8.5, 5.8),
    ("DUB", "Dublin Airport", "Dublin", "Ireland", "Ireland", 53.421, -6.270, 74, 0, 10.0, 5.5),
    ("CDG", "Paris Charles de Gaulle", "Paris", "France", "Western Europe", 49.010, 2.548, 119, 0, 12.0, 8.0),
    ("AMS", "Amsterdam Schiphol", "Amsterdam", "Netherlands", "Western Europe", 52.309, 4.764, -3, 0, 10.5, 7.5),
    ("FRA", "Frankfurt Airport", "Frankfurt", "Germany", "Central Europe", 50.033, 8.571, 111, 0, 10.5, 9.0),
    ("BER", "Berlin Brandenburg", "Berlin", "Germany", "Central Europe", 52.362, 13.501, 48, 0, 10.0, 9.5),
    ("GVA", "Geneva Airport", "Geneva", "Switzerland", "Central Europe", 46.238, 6.109, 430, 0, 10.0, 9.0),
    ("MAD", "Madrid Barajas", "Madrid", "Spain", "Southern Europe", 40.472, -3.563, 610, 0, 15.0, 9.5),
    ("BCN", "Barcelona El Prat", "Barcelona", "Spain", "Southern Europe", 41.297, 2.078, 4, 0, 16.0, 7.5),
    ("PMI", "Palma de Mallorca", "Palma", "Spain", "Southern Europe", 39.552, 2.739, 8, 0, 18.0, 8.0),
    ("AGP", "Malaga Airport", "Malaga", "Spain", "Southern Europe", 36.675, -4.499, 16, 0, 18.5, 6.0),
    ("ALC", "Alicante Airport", "Alicante", "Spain", "Southern Europe", 38.282, -0.558, 43, 0, 18.5, 7.0),
    ("TFS", "Tenerife South", "Tenerife", "Spain", "Atlantic Islands", 28.045, -16.572, 64, 0, 21.0, 3.5),
    ("LIS", "Lisbon Airport", "Lisbon", "Portugal", "Southern Europe", 38.774, -9.134, 114, 0, 17.5, 5.5),
    ("FAO", "Faro Airport", "Faro", "Portugal", "Southern Europe", 37.017, -7.966, 8, 0, 18.0, 5.5),
    ("FCO", "Rome Fiumicino", "Rome", "Italy", "Southern Europe", 41.800, 12.239, 5, 0, 16.0, 8.0),
    ("ATH", "Athens Airport", "Athens", "Greece", "Southern Europe", 37.936, 23.947, 94, 0, 18.5, 9.5),
    ("KEF", "Keflavik Airport", "Reykjavik", "Iceland", "Nordic", 63.985, -22.606, 52, 0, 4.5, 5.5),
    ("CPH", "Copenhagen Airport", "Copenhagen", "Denmark", "Nordic", 55.618, 12.656, 5, 0, 9.0, 8.0),
    ("OSL", "Oslo Gardermoen", "Oslo", "Norway", "Nordic", 60.194, 11.100, 204, 0, 6.0, 10.0),
]

# (model, manufacturer, engine_type, economy, premium, business, range_km, cruise_kmh)
AIRCRAFT_TYPES = [
    ("ATR 72-600", "ATR", "Turboprop", 72, 0, 0, 1500, 510),
    ("Embraer E190", "Embraer", "Turbofan", 92, 8, 0, 4500, 820),
    ("Airbus A320neo", "Airbus", "Turbofan", 156, 12, 0, 6300, 830),
    ("Airbus A321neo", "Airbus", "Turbofan", 192, 18, 12, 7400, 840),
]
# Seat letters per row (2-2 layout for regional aircraft, 3-3 for narrow-bodies).
SEAT_LETTERS = {"ATR 72-600": "ACDF", "Embraer E190": "ACDF",
                "Airbus A320neo": "ABCDEF", "Airbus A321neo": "ABCDEF"}
FLEET_PLAN = [("ATR 72-600", 2), ("Embraer E190", 2), ("Airbus A320neo", 3), ("Airbus A321neo", 1)]

# Hand-designed hub-and-spoke network: (hub, destination, category, weekly flights each way).
# The category drives seasonality, weekday pattern, pricing and load factor.
NETWORK = [
    ("MAN", "DUB", "Mixed", 7), ("MAN", "CDG", "Business", 5), ("MAN", "AMS", "Business", 6),
    ("MAN", "BCN", "Leisure", 4), ("MAN", "PMI", "Leisure", 4), ("MAN", "AGP", "Leisure", 4),
    ("MAN", "FAO", "Leisure", 3), ("MAN", "ALC", "Leisure", 3), ("MAN", "TFS", "Leisure", 3),
    ("MAN", "LIS", "Mixed", 3), ("MAN", "FCO", "Mixed", 3), ("MAN", "ATH", "Leisure", 2),
    ("MAN", "GVA", "Business", 2), ("MAN", "KEF", "Mixed", 2), ("MAN", "BFS", "Domestic", 5),
    ("MAN", "ABZ", "Domestic", 2), ("MAN", "INV", "Domestic", 2), ("MAN", "MAD", "Mixed", 3),
    ("EDI", "DUB", "Mixed", 4), ("EDI", "CDG", "Business", 3), ("EDI", "AMS", "Business", 4),
    ("EDI", "BCN", "Leisure", 2), ("EDI", "PMI", "Leisure", 2), ("EDI", "KEF", "Mixed", 3),
    ("EDI", "CPH", "Business", 3), ("EDI", "OSL", "Business", 3), ("EDI", "BER", "Business", 2),
    ("EDI", "FRA", "Business", 3), ("EDI", "BHX", "Domestic", 3), ("EDI", "LGW", "Domestic", 7),
]

# Seasonal multipliers on the number of flights (index = month 1..12).
# Leisure routes are cut hard in winter; business routes dip in August.
SEASON_FREQ = {
    "Leisure":  [0, .55, .55, .80, 1.00, 1.10, 1.40, 1.60, 1.60, 1.30, 1.00, .60, .80],
    "Business": [0, .90, 1.00, 1.05, 1.00, 1.05, 1.00, .85, .70, 1.05, 1.10, 1.10, .80],
}
SEASON_FREQ["Domestic"] = [(a + b) / 2 for a, b in zip(SEASON_FREQ["Leisure"], SEASON_FREQ["Business"])]
SEASON_FREQ["Mixed"] = SEASON_FREQ["Domestic"]
# Weekday pattern (Mon..Sun). Business traffic is weekday-heavy, leisure is weekend-heavy.
DOW_FREQ = {
    "Business": [1.25, 1.20, 1.20, 1.25, 1.15, 0.50, 0.45],
    "Leisure":  [0.85, 0.65, 0.80, 1.00, 1.40, 1.25, 1.35],
    "Domestic": [1.15, 1.00, 1.00, 1.10, 1.20, 0.65, 0.90],
    "Mixed":    [1.00, 0.90, 0.95, 1.05, 1.20, 1.00, 1.10],
}
# Additive monthly load-factor adjustment (summer, Christmas high; Jan/Feb low).
SEASON_LOAD = [0, -.07, -.06, -.02, .01, .03, .06, .11, .12, .05, .01, -.04, .05]
# Base load factor by route category.
BASE_LOAD = {"Business": 0.78, "Domestic": 0.74, "Mixed": 0.72, "Leisure": 0.70}
# Fare level by route category (business routes are priced higher, leisure lower) and by month.
ROUTE_FARE_FACTOR = {"Business": 1.15, "Domestic": 1.00, "Mixed": 1.00, "Leisure": 0.95}
SEASON_FARE = [0, .90, .90, .95, 1.00, 1.05, 1.15, 1.35, 1.40, 1.10, 1.00, .95, 1.20]

# Departure hours 06..21 and how popular each is (morning, midday and evening banks).
DEP_HOURS = list(range(6, 22))
DEP_HOUR_W = [8, 12, 10, 7, 5, 6, 8, 7, 6, 6, 8, 10, 8, 5, 3, 2]

# Weather effects. Delays and cancellations are driven by weather, hour of day and
# randomness, so later analysis can discover genuine relationships.
WEATHER_DELAY_PROB = {"Clear": 0.00, "Cloudy": 0.02, "Rain": 0.06, "Fog": 0.15,
                      "Snow": 0.25, "Strong Wind": 0.12, "Thunderstorm": 0.22}
WEATHER_DELAY_EXTRA_MIN = {"Clear": 0, "Cloudy": 1, "Rain": 4, "Fog": 14,
                           "Snow": 30, "Strong Wind": 12, "Thunderstorm": 25}
WEATHER_CANCEL_PROB = {"Clear": 0.002, "Cloudy": 0.002, "Rain": 0.004, "Fog": 0.020,
                       "Snow": 0.050, "Strong Wind": 0.025, "Thunderstorm": 0.060}

CABINS = ["Economy", "Premium Economy", "Business"]       # ordinal, lowest first
CABIN_FARE_MULT = {"Economy": 1.00, "Premium Economy": 1.75, "Business": 2.90}
CABIN_FARE_ADD = {"Economy": 0.0, "Premium Economy": 15.0, "Business": 40.0}
CABIN_LOAD_MULT = {"Economy": 1.00, "Premium Economy": 0.78, "Business": 0.55}
CABIN_SATISFACTION_BONUS = {"Economy": 0.00, "Premium Economy": 0.30, "Business": 0.50}

# (extra_name, category, list_price_gbp)
EXTRAS = [
    ("Checked bag 20kg", "Baggage", 24.99), ("Sports equipment", "Baggage", 35.00),
    ("Extra legroom seat", "Seat", 17.50), ("Seat selection", "Seat", 6.99),
    ("Priority boarding", "Boarding", 9.99), ("Hot meal", "Food & Drink", 11.50),
    ("Snack box", "Food & Drink", 6.50), ("Drink", "Food & Drink", 4.50),
    ("Lounge access", "Airport Services", 28.00), ("Fast track security", "Airport Services", 8.00),
    ("Travel insurance", "Insurance", 15.00), ("Carbon offset", "Sustainability", 3.50),
]
EXTRA_ID = {name: i for i, (name, _, _) in enumerate(EXTRAS, start=1)}
EXTRA_PRICE = {name: price for name, _, price in EXTRAS}

PAYMENT = {"Credit Card": 36, "Debit Card": 31, "PayPal": 14, "Apple Pay": 11,
           "Bank Transfer": 3, "Airline Voucher": 5}
CHANNEL = {"Website": 44, "Mobile App": 30, "Travel Agent": 12, "Call Centre": 4, "Corporate Portal": 10}
HOME_COUNTRY = {"United Kingdom": 62, "Ireland": 6, "France": 4, "Germany": 4, "Spain": 4,
                "Netherlands": 3, "Italy": 3, "Poland": 3, "Portugal": 2, "Norway": 2,
                "Denmark": 2, "Iceland": 1, "Greece": 1, "Switzerland": 1, "Belgium": 2}

FIRST = ["Oliver", "Amelia", "Muhammad", "Aisha", "Harry", "Fatima", "Jack", "Sophie", "Ali", "Emily",
         "Noah", "Priya", "Liam", "Zainab", "Ethan", "Chloe", "Omar", "Grace", "Daniel", "Hannah",
         "Arjun", "Megan", "Bilal", "Lucy", "Callum", "Sara", "Rhys", "Ayesha", "Owen", "Isla",
         "Tariq", "Ffion", "Samuel", "Maryam", "Joshua", "Ella", "Hassan", "Cerys", "Leo", "Nadia",
         "Marta", "Lukas", "Elena", "Mateo", "Ingrid", "Pierre", "Sofia", "Jan", "Anna", "Tomas"]
LAST = ["Smith", "Jones", "Williams", "Taylor", "Brown", "Davies", "Evans", "Khan", "Thomas", "Roberts",
        "Johnson", "Patel", "Hughes", "Ahmed", "Wright", "Morgan", "Hussain", "Edwards", "Walker", "Lewis",
        "Clarke", "Singh", "Griffiths", "Ali", "Jenkins", "Bennett", "Rees", "Malik", "Phillips", "Shah",
        "Price", "Cooper", "Iqbal", "Powell", "Ward", "Baker", "Chaudhry", "Lloyd", "Hall", "Begum",
        "Murphy", "Walsh", "Dubois", "Muller", "Garcia", "Rossi", "Jensen", "Nowak", "Silva", "Kowalski"]


# =============================================================================
# 2. DATABASE SCHEMA
# =============================================================================
# Design notes (the same reasoning is repeated in the written report):
#  * Third normal form: each fact is stored once (airport details are not repeated
#    on every flight; passenger details are not repeated on every booking).
#  * PRAGMA foreign_keys = ON is set on the connection, so SQLite enforces every
#    REFERENCES clause below instead of silently ignoring it.
#  * CHECK constraints restrict each attribute to its valid domain, so impossible
#    values (rating 9, negative fare, 5-letter airport code) cannot be inserted.
#  * Nullable columns (delays, rating, seat, baggage, weather) are NULL only where the
#    value is genuinely unknown, giving realistic missing data for later cleaning.
#  * Dates/times are ISO-8601 text ("2026-03-14 07:35"), which sorts correctly.
SCHEMA = """
CREATE TABLE airports (
    airport_id    INTEGER PRIMARY KEY,
    iata_code     TEXT    NOT NULL UNIQUE CHECK (length(iata_code) = 3),
    airport_name  TEXT    NOT NULL,
    city          TEXT    NOT NULL,
    country       TEXT    NOT NULL,
    region        TEXT    NOT NULL CHECK (region IN ('UK','Ireland','Western Europe','Central Europe',
                                                     'Southern Europe','Nordic','Atlantic Islands')),
    latitude      REAL    NOT NULL CHECK (latitude  BETWEEN -90  AND 90),
    longitude     REAL    NOT NULL CHECK (longitude BETWEEN -180 AND 180),
    elevation_m   INTEGER NOT NULL CHECK (elevation_m BETWEEN -50 AND 4000),
    is_hub        INTEGER NOT NULL CHECK (is_hub IN (0,1))
);

CREATE TABLE aircraft_types (
    aircraft_type_id INTEGER PRIMARY KEY,
    model            TEXT    NOT NULL UNIQUE,
    manufacturer     TEXT    NOT NULL,
    engine_type      TEXT    NOT NULL CHECK (engine_type IN ('Turboprop','Turbofan')),
    seats_economy    INTEGER NOT NULL CHECK (seats_economy >= 0),
    seats_premium    INTEGER NOT NULL CHECK (seats_premium >= 0),
    seats_business   INTEGER NOT NULL CHECK (seats_business >= 0),
    range_km         INTEGER NOT NULL CHECK (range_km > 0),
    cruise_speed_kmh INTEGER NOT NULL CHECK (cruise_speed_kmh > 0)
);

CREATE TABLE aircraft (
    aircraft_id      INTEGER PRIMARY KEY,
    registration     TEXT    NOT NULL UNIQUE,
    aircraft_type_id INTEGER NOT NULL REFERENCES aircraft_types(aircraft_type_id),
    year_built       INTEGER NOT NULL CHECK (year_built BETWEEN 2005 AND 2026)
);

CREATE TABLE routes (
    route_id               INTEGER PRIMARY KEY,
    origin_airport_id      INTEGER NOT NULL REFERENCES airports(airport_id),
    destination_airport_id INTEGER NOT NULL REFERENCES airports(airport_id),
    distance_km            INTEGER NOT NULL CHECK (distance_km > 0),
    route_category         TEXT    NOT NULL CHECK (route_category IN ('Domestic','Business','Leisure','Mixed')),
    weekly_frequency       INTEGER NOT NULL CHECK (weekly_frequency > 0),
    CHECK (origin_airport_id <> destination_airport_id),
    UNIQUE (origin_airport_id, destination_airport_id)          -- compound key: one row per directed route
);

CREATE TABLE flights (
    flight_id            INTEGER PRIMARY KEY,
    flight_number        TEXT    NOT NULL,
    route_id             INTEGER NOT NULL REFERENCES routes(route_id),
    aircraft_id          INTEGER NOT NULL REFERENCES aircraft(aircraft_id),
    scheduled_departure  TEXT    NOT NULL,
    scheduled_arrival    TEXT    NOT NULL,
    origin_temperature_c REAL    CHECK (origin_temperature_c BETWEEN -40 AND 50),
    weather_condition    TEXT    CHECK (weather_condition IN ('Clear','Cloudy','Rain','Fog','Snow',
                                                              'Strong Wind','Thunderstorm')),
    flight_status        TEXT    NOT NULL CHECK (flight_status IN ('Scheduled','Completed','Cancelled','Diverted')),
    departure_delay_min  INTEGER CHECK (departure_delay_min BETWEEN 0 AND 600),
    arrival_delay_min    INTEGER CHECK (arrival_delay_min   BETWEEN 0 AND 900),
    UNIQUE (flight_number, scheduled_departure)                  -- compound key: a flight number runs once per departure
);

CREATE TABLE flight_cabins (
    flight_id      INTEGER NOT NULL REFERENCES flights(flight_id),
    cabin_class    TEXT    NOT NULL CHECK (cabin_class IN ('Economy','Premium Economy','Business')),
    seats_capacity INTEGER NOT NULL CHECK (seats_capacity > 0),
    base_fare_gbp  REAL    NOT NULL CHECK (base_fare_gbp > 0),
    PRIMARY KEY (flight_id, cabin_class)                         -- compound primary key
);

CREATE TABLE passengers (
    passenger_id     INTEGER PRIMARY KEY,
    first_name       TEXT    NOT NULL,
    last_name        TEXT    NOT NULL,
    email            TEXT    NOT NULL UNIQUE,
    home_country     TEXT    NOT NULL,
    birth_year       INTEGER NOT NULL CHECK (birth_year BETWEEN 1920 AND 2008),   -- account holders are adults
    signup_date      TEXT    NOT NULL,
    loyalty_tier     TEXT    NOT NULL CHECK (loyalty_tier IN ('Standard','Silver','Gold','Platinum')),
    marketing_opt_in INTEGER NOT NULL CHECK (marketing_opt_in IN (0,1))
);

CREATE TABLE extras (
    extra_id      INTEGER PRIMARY KEY,
    extra_name    TEXT    NOT NULL UNIQUE,
    extra_category TEXT   NOT NULL,
    list_price_gbp REAL   NOT NULL CHECK (list_price_gbp > 0)
);

CREATE TABLE bookings (
    booking_id          INTEGER PRIMARY KEY,
    passenger_id        INTEGER NOT NULL REFERENCES passengers(passenger_id),
    flight_id           INTEGER NOT NULL REFERENCES flights(flight_id),
    cabin_class         TEXT    NOT NULL,
    booking_date        TEXT    NOT NULL,
    booking_channel     TEXT    NOT NULL CHECK (booking_channel IN ('Website','Mobile App','Travel Agent',
                                                                    'Call Centre','Corporate Portal')),
    payment_method      TEXT    NOT NULL CHECK (payment_method IN ('Credit Card','Debit Card','PayPal',
                                                                   'Apple Pay','Bank Transfer','Airline Voucher')),
    seat_number         TEXT,                                    -- NULL once a passenger cancels (seat released)
    fare_gbp            REAL    NOT NULL CHECK (fare_gbp > 0),
    checked_baggage_kg  REAL    CHECK (checked_baggage_kg >= 0), -- NULL until the passenger actually checks in
    booking_status      TEXT    NOT NULL CHECK (booking_status IN ('Booked','Flown','No-show','Cancelled','Refunded')),
    satisfaction_rating INTEGER CHECK (satisfaction_rating BETWEEN 1 AND 5),  -- NULL: survey not answered
    FOREIGN KEY (flight_id, cabin_class) REFERENCES flight_cabins(flight_id, cabin_class),  -- composite FK
    UNIQUE (flight_id, seat_number)                              -- compound key: a seat is sold once per flight
);

CREATE TABLE booking_extras (
    booking_id      INTEGER NOT NULL REFERENCES bookings(booking_id),
    extra_id        INTEGER NOT NULL REFERENCES extras(extra_id),
    quantity        INTEGER NOT NULL CHECK (quantity > 0),
    unit_price_paid REAL    NOT NULL CHECK (unit_price_paid >= 0),   -- price at purchase (promotions vary it)
    PRIMARY KEY (booking_id, extra_id)                           -- compound primary key (basket-style table)
);

CREATE INDEX idx_flights_route      ON flights(route_id);
CREATE INDEX idx_flights_aircraft   ON flights(aircraft_id);
CREATE INDEX idx_flights_departure  ON flights(scheduled_departure);
CREATE INDEX idx_bookings_passenger ON bookings(passenger_id);
CREATE INDEX idx_bookings_flight    ON bookings(flight_id);
CREATE INDEX idx_bookings_date      ON bookings(booking_date);
CREATE INDEX idx_extras_extra       ON booking_extras(extra_id);
"""


# =============================================================================
# 3. SMALL HELPERS
# =============================================================================
def wchoice(mapping):
    """Weighted random choice from {value: weight}."""
    return random.choices(list(mapping), list(mapping.values()))[0]


def haversine_km(lat1, lon1, lat2, lon2):
    """Great-circle distance, so route distances are consistent with coordinates."""
    r = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    a = (math.sin((p2 - p1) / 2) ** 2
         + math.cos(p1) * math.cos(p2) * math.sin(math.radians(lon2 - lon1) / 2) ** 2)
    return int(round(2 * r * math.asin(math.sqrt(a))))


def iso_dt(dt):
    return dt.strftime("%Y-%m-%d %H:%M")


# =============================================================================
# 4. REFERENCE TABLES: airports, aircraft types, fleet, routes
# =============================================================================
def build_reference():
    airports = []
    clim = {}
    code_to_id = {}
    for i, (iata, name, city, country, region, lat, lon, elev, hub, mean_t, amp) in enumerate(AIRPORTS, start=1):
        airports.append((i, iata, name, city, country, region, lat, lon, elev, hub))
        clim[i] = (mean_t, amp)
        code_to_id[iata] = i
    coords = {a[0]: (a[6], a[7]) for a in airports}

    types = [(i,) + t for i, t in enumerate(AIRCRAFT_TYPES, start=1)]
    type_by_model = {t[1]: t for t in types}

    fleet = []
    letters = "ABCDEFGHIJ"
    for model, count in FLEET_PLAN:
        for _ in range(count):
            reg = "G-KST" + letters[len(fleet)]                  # G-KSTA, G-KSTB, ...
            fleet.append((len(fleet) + 1, reg, type_by_model[model][0], random.randint(2013, 2025)))

    # Each pair in NETWORK becomes TWO directed routes (outbound and return).
    routes, route_meta = [], {}
    rid = 1
    for hub, dest, cat, weekly in NETWORK:
        for o, d in ((hub, dest), (dest, hub)):
            oi, di = code_to_id[o], code_to_id[d]
            dist = haversine_km(*coords[oi], *coords[di])
            routes.append((rid, oi, di, dist, cat, weekly))
            route_meta[rid] = {"origin": oi, "dest": di, "dist": dist, "cat": cat, "weekly": weekly}
            rid += 1
    return airports, clim, types, fleet, routes, route_meta


# =============================================================================
# 5. FLIGHTS (schedule, aircraft rotation, weather, delays, cabins)
# =============================================================================
def seat_map(model, n_business, n_premium, n_economy):
    """Seat labels per cabin, front-to-back: business rows first, then premium, then economy."""
    letters = SEAT_LETTERS[model]
    out, row = {}, 1
    for cabin, n in (("Business", n_business), ("Premium Economy", n_premium), ("Economy", n_economy)):
        seats = []
        for _ in range(n // len(letters)):
            seats += [f"{row}{ch}" for ch in letters]
            row += 1
        out[cabin] = seats
    return out


def simulate_weather(temp, mean_t):
    """Pick a weather condition that is plausible for the temperature and climate."""
    w = {"Clear": 38, "Cloudy": 28, "Rain": 19, "Fog": 4, "Snow": 0, "Strong Wind": 7, "Thunderstorm": 2}
    if temp <= 1.0:
        w.update(Snow=16, Rain=6, Fog=7)
    elif temp <= 4.0:
        w.update(Snow=4, Fog=7)
    if temp >= 20.0:
        w.update(Thunderstorm=6, Fog=1, Rain=9, Clear=55)
    if mean_t >= 15.5:                                           # Mediterranean climates are sunnier
        w["Clear"] += 14
        w["Rain"] = max(3, w["Rain"] - 8)
    return wchoice(w)


def build_flights(airports, clim, types, fleet, routes, route_meta):
    ap_coords = {a[0]: a for a in airports}
    type_row = {t[0]: t for t in types}
    ac_state = {a[0]: {"free_at": datetime(2000, 1, 1), "loc": None,
                       "usable_range": type_row[a[2]][7] * 0.80,   # keep 20% fuel reserve margin
                       "capacity": type_row[a[2]][4] + type_row[a[2]][5] + type_row[a[2]][6],
                       "type": a[2]} for a in fleet}
    hub_ids = [a[0] for a in airports if a[9] == 1]
    for i, aid in enumerate(ac_state):
        ac_state[aid]["loc"] = hub_ids[i % len(hub_ids)]         # fleet starts spread across the hubs

    # 5a. candidate departures: how many flights does each route run each day?
    cands = []
    day = FLIGHTS_FROM
    while day <= FLIGHTS_TO:
        for r in routes:
            cat = r[4]
            expected = (r[5] * SCHEDULE_SCALE * SEASON_FREQ[cat][day.month]
                        * DOW_FREQ[cat][day.weekday()] / 7.0)
            n = int(expected) + (1 if random.random() < expected - int(expected) else 0)
            n = min(n, 2)
            for slot in range(n):
                # With two flights, one goes in the first half of the day and one in the second.
                hours = DEP_HOURS if n == 1 else (DEP_HOURS[:8] if slot == 0 else DEP_HOURS[8:])
                weights = DEP_HOUR_W if n == 1 else (DEP_HOUR_W[:8] if slot == 0 else DEP_HOUR_W[8:])
                h = random.choices(hours, weights)[0]
                m = random.choice([0, 5, 10, 15, 20, 25, 30, 35, 40, 45, 50, 55])
                cands.append((datetime.combine(day, time(h, m)), r[0], slot))
        day += timedelta(days=1)
    cands.sort(key=lambda c: c[0])

    # 5b. assign aircraft in time order so no aircraft is in two places at once.
    flights, cabins = [], []
    dropped = 0
    for dep_dt, rid, slot in cands:
        meta = route_meta[rid]
        dist = meta["dist"]
        free = [a for a, s in ac_state.items() if s["usable_range"] >= dist * 1.1 and s["free_at"] <= dep_dt]
        if not free:
            dropped += 1                                         # schedule trimmed: no aircraft available
            continue
        at_origin = [a for a in free if ac_state[a]["loc"] == meta["origin"]]
        pool = at_origin or free                                 # prefer an aircraft already at the origin
        # Busy routes get bigger aircraft, thin routes smaller ones.
        exp = 1 if meta["weekly"] >= 5 else (0 if meta["weekly"] >= 3 else -1)
        aid = random.choices(pool, [ac_state[a]["capacity"] ** exp for a in pool])[0]
        tid = ac_state[aid]["type"]
        trow = type_row[tid]
        duration = int(round((dist / trow[8] * 60 + 25) / 5.0) * 5)   # cruise time + 25 min taxi/climb
        arr_dt = dep_dt + timedelta(minutes=duration)
        ac_state[aid]["free_at"] = arr_dt + MIN_TURNAROUND
        ac_state[aid]["loc"] = meta["dest"]

        # Weather, delay and status only exist for flights that already happened.
        temp = weather = dep_delay = arr_delay = None
        if dep_dt.date() > SNAPSHOT:
            status = "Scheduled"
        else:
            mean_t, amp = clim[meta["origin"]]
            doy = dep_dt.timetuple().tm_yday
            temp = round(mean_t + amp * math.sin(2 * math.pi * (doy - 110) / 365) + random.gauss(0, 3.2), 1)
            weather = simulate_weather(temp, mean_t)
            if random.random() < WEATHER_CANCEL_PROB[weather]:
                status = "Cancelled"
            else:
                status = "Diverted" if random.random() < (0.012 if weather in ("Fog", "Thunderstorm") else 0.003) else "Completed"
                p_delay = min(0.9, 0.28 + 0.018 * (dep_dt.hour - 6) + WEATHER_DELAY_PROB[weather])
                if random.random() < p_delay:
                    dep_delay = min(420, 1 + int(random.expovariate(1.0 / (16 + WEATHER_DELAY_EXTRA_MIN[weather]))))
                else:
                    dep_delay = 0                                # on time: zero is a meaningful ratio value
                if status == "Diverted":
                    arr_delay = dep_delay + random.randint(45, 180)
                else:
                    arr_delay = max(0, dep_delay + int(random.gauss(-3, 9)))   # pilots can make up a little time

        flights.append({"rid": rid, "aid": aid, "tid": tid, "dep": dep_dt, "arr": arr_dt, "slot": slot,
                        "temp": temp, "weather": weather, "status": status,
                        "dep_delay": dep_delay, "arr_delay": arr_delay})

    # 5c. numbering: flight_id follows departure time; flight_number = KST + route code + slot
    for i, f in enumerate(flights, start=1):
        f["id"] = i
        f["number"] = f"KST{f['rid'] * 10 + f['slot']}"
        meta = route_meta[f["rid"]]
        trow = type_row[f["tid"]]
        f["dist"], f["cat"] = meta["dist"], meta["cat"]
        # Price list for this flight: grows with distance, varies by route type, season and weekday.
        base = ((24 + 0.078 * meta["dist"]) * ROUTE_FARE_FACTOR[meta["cat"]]
                * SEASON_FARE[f["dep"].month] * (1.08 if f["dep"].weekday() in (4, 6) else 1.0))
        sm = seat_map(trow[1], trow[6], trow[5], trow[4])
        f["seats"] = sm
        for cabin in CABINS:
            if sm[cabin]:
                price = round(base * CABIN_FARE_MULT[cabin] + CABIN_FARE_ADD[cabin], 2)
                cabins.append((f["id"], cabin, len(sm[cabin]), price))
        f["base"] = {c[1]: c[3] for c in cabins[-3:] if c[0] == f["id"]}
    print(f"  schedule: {len(flights):,} flights built, {dropped} candidate flights dropped (no aircraft free)")
    return flights, cabins


# =============================================================================
# 6. PASSENGERS
# =============================================================================
def build_passengers():
    span = (date(2026, 10, 25) - SIGNUP_FROM).days
    rows = []
    for pid in range(1, N_PASSENGERS + 1):
        first, last = random.choice(FIRST), random.choice(LAST)
        # Triangular: sign-ups accelerate as the airline grows (mode at ~75% of the period).
        signup = SIGNUP_FROM + timedelta(days=int(random.triangular(0, span, span * 0.75)))
        rows.append({"id": pid, "first": first, "last": last,
                     "email": f"{first}.{last}{pid}@example.com".lower(),   # unique + reserved domain
                     "country": wchoice(HOME_COUNTRY),
                     "birth": int(random.triangular(1940, 2008, 1984)),     # 18+ and centred on mid-adults
                     "signup": signup.isoformat(),
                     "optin": 1 if random.random() < 0.46 else 0,
                     "tier": "Standard"})                                   # recomputed after bookings exist
    # Sort by signup so a passenger can be chosen from "everyone who had already signed up".
    rows.sort(key=lambda p: p["signup"])
    return rows


# =============================================================================
# 7. EXTRAS (ancillary purchases with deliberate co-purchase patterns)
# =============================================================================
def pick_extras(cabin, category, duration_min, dist_km, has_hot_meal_service):
    """
    Choose which add-ons one booking buys. The probabilities are deliberately linked
    (bag -> priority boarding, lounge -> fast track, hot meal -> drink ...) so that
    association-rule mining later finds real rules with lift > 1.
    Returns {extra_name: quantity}.
    """
    chosen = {}
    p_bag = {"Economy": 0.38, "Premium Economy": 0.60, "Business": 0.0}[cabin]   # business bags are included
    has_bag = random.random() < p_bag
    if has_bag:
        chosen["Checked bag 20kg"] = 2 if random.random() < 0.15 else 1
        if random.random() < 0.015:
            chosen["Sports equipment"] = 1
    if random.random() < (0.30 if has_bag else 0.07):
        chosen["Priority boarding"] = 1
    if cabin == "Economy" and random.random() < 0.45:
        chosen["Seat selection"] = 1
    if random.random() < (0.10 if has_bag else 0.04):
        chosen["Extra legroom seat"] = 1
        chosen.pop("Seat selection", None)                       # legroom seat already includes selection
    hot = has_hot_meal_service and random.random() < 0.22
    if hot:
        chosen["Hot meal"] = 1
    elif random.random() < 0.20:
        chosen["Snack box"] = 1
    if random.random() < (0.55 if hot else 0.15):
        chosen["Drink"] = 1
    lounge = random.random() < (0.55 if cabin == "Business" else 0.06)
    if lounge:
        chosen["Lounge access"] = 1
    if random.random() < (0.60 if lounge else 0.09):
        chosen["Fast track security"] = 1
    if random.random() < (0.14 if category == "Leisure" else 0.05):
        chosen["Travel insurance"] = 1
    if random.random() < (0.16 if cabin == "Business" else 0.06) + (0.10 if "Travel insurance" in chosen else 0):
        chosen["Carbon offset"] = 1
    return chosen


def satisfaction(cabin, arr_delay, n_extras):
    """Survey answer 1-5, or None if the passenger ignored the survey (about two thirds do)."""
    if random.random() > 0.33 + (0.12 if arr_delay >= 60 else 0.0):   # unhappy people answer more
        return None
    score = (4.15 + CABIN_SATISFACTION_BONUS[cabin] - 0.013 * min(arr_delay, 240)
             + 0.05 * min(n_extras, 4) + random.gauss(0, 0.85))
    return max(1, min(5, int(round(score))))


# =============================================================================
# 8. BOOKINGS (one row = one passenger holding one seat on one flight)
# =============================================================================
def build_bookings(flights, passengers):
    signup_strs = [p["signup"] for p in passengers]
    # Frequent-flyer behaviour: a heavy-tailed activity weight (log-normal) so a few
    # passengers book many flights and most book one or two.
    cum, total = [], 0.0
    for _ in passengers:
        total += random.lognormvariate(0, 1.05)
        cum.append(total)

    def pick_passenger(booking_day, taken):
        k = bisect.bisect_right(signup_strs, booking_day.isoformat())   # only people already signed up
        if k == 0:
            return None
        for _ in range(6):
            idx = bisect.bisect_left(cum, random.random() * cum[k - 1], 0, k)
            if idx not in taken:
                return idx
        return None

    bookings = []
    for f in flights:
        dep_day = f["dep"].date()
        month_load = (BASE_LOAD[f["cat"]] + SEASON_LOAD[dep_day.month]
                      + (0.04 if dep_day.weekday() in (4, 6) else (-0.05 if dep_day.weekday() in (1, 2) else 0.0)))
        load = max(0.35, min(0.97, month_load + random.gauss(0, 0.06)))
        hot_service = f["dist"] >= 700 and f["tid"] >= 3             # hot meals only on longer jet flights
        taken_pass = set()
        for cabin in CABINS:
            seats = list(f["seats"][cabin])
            if not seats:
                continue
            random.shuffle(seats)                                    # random seat allocation
            n_sell = int(round(len(seats) * min(0.99, load * CABIN_LOAD_MULT[cabin] * (1.2 if (cabin == "Business" and f["cat"] == "Business") else 1.0))))
            n_sell = min(len(seats), max(0, n_sell + random.randint(-2, 2)))
            seat_i = 0
            for _ in range(n_sell):
                # Booking lead time: log-normal around three weeks, capped by when sales opened.
                max_lead = (dep_day - SALES_OPEN).days
                lead = min(max_lead, 330, int(random.lognormvariate(math.log(22), 0.9)))
                b_day = dep_day - timedelta(days=lead)
                if b_day > SNAPSHOT:
                    continue                                         # not booked yet at extraction time
                pidx = pick_passenger(b_day, taken_pass)
                if pidx is None:
                    continue
                taken_pass.add(pidx)

                # Status depends on whether the flight has happened.
                if f["status"] == "Scheduled":
                    status = "Cancelled" if random.random() < 0.03 else "Booked"
                elif f["status"] == "Cancelled":
                    status = "Refunded"
                else:
                    r = random.random()
                    status = "Flown" if r < 0.945 else ("No-show" if r < 0.97 else "Cancelled")

                # Price: cheaper when booked early, dearer close to departure (+ small noise).
                demand = 0.82 + 0.90 * math.exp(-lead / 25.0)
                fare = max(14.99, round(f["base"][cabin] * demand * random.gauss(1.0, 0.05), 2))

                extras = {}
                if status not in ("Cancelled",):
                    extras = pick_extras(cabin, f["cat"], 0, f["dist"], hot_service)

                seat = None
                if status != "Cancelled":                            # a cancelled booking releases its seat
                    seat = seats[seat_i]
                    seat_i += 1

                # Checked baggage is only weighed at check-in, so unflown bookings stay NULL.
                bag_kg = None
                if status == "Flown":
                    n_bags = (random.choices([0, 1, 2], [5, 60, 35])[0] if cabin == "Business"
                              else extras.get("Checked bag 20kg", 0))
                    bag_kg = round(sum(random.triangular(7, 23, 16) for _ in range(n_bags)), 1)

                rating = None
                if status == "Flown":
                    rating = satisfaction(cabin, f["arr_delay"] or 0, len(extras))

                # Business bookings more often come from a corporate portal.
                channel = wchoice({"Corporate Portal": 40, "Website": 30, "Mobile App": 15, "Travel Agent": 10,
                                   "Call Centre": 5}) if cabin == "Business" else wchoice(CHANNEL)

                bookings.append({"pidx": pidx, "fid": f["id"], "cabin": cabin, "bdate": b_day.isoformat(),
                                 "channel": channel, "pay": wchoice(PAYMENT), "seat": seat, "fare": fare,
                                 "bag": bag_kg, "status": status, "rating": rating, "extras": extras})
    # booking_id follows booking date (chronological, like a real system's auto-increment).
    bookings.sort(key=lambda b: (b["bdate"], random.random()))
    for i, b in enumerate(bookings, start=1):
        b["id"] = i
    return bookings


# =============================================================================
# 9. LOYALTY TIERS (derived from behaviour, not random)
# =============================================================================
def assign_tiers(passengers, bookings):
    flown = {}
    for b in bookings:
        if b["status"] == "Flown":
            flown[b["pidx"]] = flown.get(b["pidx"], 0) + 1
    for idx, p in enumerate(passengers):
        n = flown.get(idx, 0)
        p["tier"] = "Platinum" if n >= 10 else "Gold" if n >= 6 else "Silver" if n >= 3 else "Standard"


# =============================================================================
# 10. WRITE EVERYTHING TO SQLITE AND VALIDATE
# =============================================================================
def main():
    DB_PATH.unlink(missing_ok=True)
    print("Building reference data ...")
    airports, clim, types, fleet, routes, route_meta = build_reference()
    print("Simulating flights ...")
    flights, cabins = build_flights(airports, clim, types, fleet, routes, route_meta)
    print("Creating passengers ...")
    passengers = build_passengers()
    print("Selling seats and extras ...")
    bookings = build_bookings(flights, passengers)
    assign_tiers(passengers, bookings)

    con = sqlite3.connect(DB_PATH)
    con.execute("PRAGMA foreign_keys = ON")                      # make SQLite enforce the foreign keys
    con.executescript(SCHEMA)

    passenger_rows = [(i, p["first"], p["last"], p["email"], p["country"], p["birth"], p["signup"], p["tier"], p["optin"])
                      for i, p in enumerate(passengers, start=1)]
    # NOTE: after sorting by signup the list position + 1 is a valid unique passenger_id,
    # so passenger_id also increases with signup date (like a real auto-increment).

    con.executemany("INSERT INTO airports VALUES (?,?,?,?,?,?,?,?,?,?)", airports)
    con.executemany("INSERT INTO aircraft_types VALUES (?,?,?,?,?,?,?,?,?)", types)
    con.executemany("INSERT INTO aircraft VALUES (?,?,?,?)", fleet)
    con.executemany("INSERT INTO routes VALUES (?,?,?,?,?,?)", routes)
    con.executemany("INSERT INTO flights VALUES (?,?,?,?,?,?,?,?,?,?,?)",
                    [(f["id"], f["number"], f["rid"], f["aid"], iso_dt(f["dep"]), iso_dt(f["arr"]),
                      f["temp"], f["weather"], f["status"], f["dep_delay"], f["arr_delay"]) for f in flights])
    con.executemany("INSERT INTO flight_cabins VALUES (?,?,?,?)", cabins)
    con.executemany("INSERT INTO passengers VALUES (?,?,?,?,?,?,?,?,?)", passenger_rows)
    con.executemany("INSERT INTO extras VALUES (?,?,?,?)",
                    [(i, n, c, p) for i, (n, c, p) in enumerate(EXTRAS, start=1)])
    con.executemany("INSERT INTO bookings VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                    [(b["id"], b["pidx"] + 1, b["fid"], b["cabin"], b["bdate"], b["channel"], b["pay"],
                      b["seat"], b["fare"], b["bag"], b["status"], b["rating"]) for b in bookings])
    extra_rows = []
    for b in bookings:
        for name, qty in b["extras"].items():
            # Occasional promotions (10-20% off) mean the price paid is not always the list price.
            disc = random.choice([0, 0, 0, 0, 0.10, 0.20])
            extra_rows.append((b["id"], EXTRA_ID[name], qty, round(EXTRA_PRICE[name] * (1 - disc), 2)))
    con.executemany("INSERT INTO booking_extras VALUES (?,?,?,?)", extra_rows)
    con.commit()

    # ---------------------------------------------------------------- validation
    print("\n=== VALIDATION ===")
    for t in ("airports", "aircraft_types", "aircraft", "routes", "flights", "flight_cabins",
              "passengers", "extras", "bookings", "booking_extras"):
        n_rows = con.execute(f"SELECT COUNT(*) FROM {t}").fetchone()[0]
        n_cols = len(con.execute(f"PRAGMA table_info({t})").fetchall())
        print(f"{t:15s} {n_rows:>9,} rows  {n_cols:>2} columns")
    print("foreign key violations:", len(con.execute("PRAGMA foreign_key_check").fetchall()))
    print("integrity_check       :", con.execute("PRAGMA integrity_check").fetchone()[0])
    bad = con.execute("""SELECT COUNT(*) FROM bookings b JOIN passengers p USING (passenger_id)
                         WHERE b.booking_date < p.signup_date""").fetchone()[0]
    print("bookings before signup:", bad)
    bad = con.execute("""SELECT COUNT(*) FROM bookings b JOIN flights f USING (flight_id)
                         WHERE b.booking_date > substr(f.scheduled_departure,1,10)""").fetchone()[0]
    print("bookings after departure:", bad)
    bad = con.execute("""SELECT COUNT(*) FROM (SELECT flight_id, cabin_class, COUNT(*) n FROM bookings
                         WHERE seat_number IS NOT NULL GROUP BY flight_id, cabin_class) x
                         JOIN flight_cabins c USING (flight_id, cabin_class) WHERE x.n > c.seats_capacity""").fetchone()[0]
    print("over-capacity cabins  :", bad)

    print("\n=== NULLs that are deliberate (unknown, not-applicable or not-yet-happened) ===")
    for tbl, col in (("flights", "departure_delay_min"), ("flights", "weather_condition"),
                     ("bookings", "satisfaction_rating"), ("bookings", "seat_number"),
                     ("bookings", "checked_baggage_kg")):
        n_null = con.execute(f"SELECT COUNT(*) FROM {tbl} WHERE {col} IS NULL").fetchone()[0]
        n_all = con.execute(f"SELECT COUNT(*) FROM {tbl}").fetchone()[0]
        print(f"{tbl}.{col:22s} {n_null:>8,} NULL of {n_all:,}")

    print("\n=== Distributions (sanity check that the data looks realistic) ===")
    print("loyalty tiers :", dict(con.execute("SELECT loyalty_tier, COUNT(*) FROM passengers GROUP BY 1").fetchall()))
    print("flight status :", dict(con.execute("SELECT flight_status, COUNT(*) FROM flights GROUP BY 1").fetchall()))
    print("booking status:", dict(con.execute("SELECT booking_status, COUNT(*) FROM bookings GROUP BY 1").fetchall()))
    print("avg delay by weather (min):")
    for w, a, n in con.execute("""SELECT weather_condition, ROUND(AVG(departure_delay_min),1), COUNT(*) FROM flights
                                  WHERE departure_delay_min IS NOT NULL GROUP BY 1 ORDER BY 2 DESC"""):
        print(f"   {w:13s} {a:>5}  (n={n})")
    print("avg fare by cabin (GBP):",
          dict(con.execute("SELECT cabin_class, ROUND(AVG(fare_gbp),2) FROM bookings GROUP BY 1").fetchall()))
    print("avg rating by cabin    :",
          dict(con.execute("SELECT cabin_class, ROUND(AVG(satisfaction_rating),2) FROM bookings GROUP BY 1").fetchall()))

    print("\n=== Association rules preview: add-ons bought together (support / confidence / lift) ===")
    rows = con.execute("""
        WITH n AS (SELECT COUNT(DISTINCT booking_id) AS total FROM booking_extras),
             f AS (SELECT extra_id, COUNT(*) AS cnt FROM booking_extras GROUP BY extra_id)
        SELECT ea.extra_name, eb.extra_name,
               ROUND(COUNT(*) * 1.0 / (SELECT total FROM n), 4)                                    AS support,
               ROUND(COUNT(*) * 1.0 / fa.cnt, 3)                                                   AS confidence,
               ROUND((COUNT(*) * 1.0 / fa.cnt) / (fb.cnt * 1.0 / (SELECT total FROM n)), 2)        AS lift
        FROM booking_extras a
        JOIN booking_extras b ON a.booking_id = b.booking_id AND a.extra_id <> b.extra_id
        JOIN f fa ON fa.extra_id = a.extra_id
        JOIN f fb ON fb.extra_id = b.extra_id
        JOIN extras ea ON ea.extra_id = a.extra_id
        JOIN extras eb ON eb.extra_id = b.extra_id
        GROUP BY a.extra_id, b.extra_id
        HAVING support >= 0.01
        ORDER BY lift DESC LIMIT 6""").fetchall()
    for a, b, s, c, l in rows:
        print(f"   {a} -> {b}: support={s}, confidence={c}, lift={l}")

    con.close()
    print(f"\nDone. Database written to {DB_PATH.resolve()}  ({DB_PATH.stat().st_size / 1e6:.1f} MB)")


if __name__ == "__main__":
    main()
