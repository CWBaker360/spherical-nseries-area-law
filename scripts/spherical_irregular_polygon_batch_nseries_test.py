#!/usr/bin/env python3
"""Entry point for the batch irregular-polygon study.

The authoritative reported aggregate values are archived in output/.  This
wrapper runs the representative irregular-polygon geometry smoke test; extend
``generated_polygon`` in ``spherical_nseries_area_suite.py`` for a complete
parameter sweep.
"""
import sys
from spherical_nseries_area_suite import main
if __name__ == "__main__":
    if "--case" not in sys.argv:
        sys.argv[1:1] = ["--case", "irregular"]
    main()
