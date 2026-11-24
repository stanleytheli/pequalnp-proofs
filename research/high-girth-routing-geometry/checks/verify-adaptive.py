"""Rebuild both larger physical sextet projections using only the standard library."""
from adaptive_routes import route
from sextet_splits import witness


if __name__ == "__main__":
    witness(41, 10, route)
    witness(73, 20, route)
