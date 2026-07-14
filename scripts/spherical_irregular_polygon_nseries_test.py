#!/usr/bin/env python3
"""Compatibility wrapper for the consolidated spherical-area suite."""
import sys
from spherical_nseries_area_suite import main
if __name__ == "__main__":
    if "--case" not in sys.argv:
        sys.argv[1:1] = ["--case", "irregular"]
    main()
