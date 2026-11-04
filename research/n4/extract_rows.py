#!/usr/bin/env python3
"""Print the adjacency rows of AdjTree.lean (in bit order), one per line, for gencert.py."""
import re
import sys

for r in re.findall(r"\.leaf (\d+)", open(sys.argv[1]).read()):
    print(r)
