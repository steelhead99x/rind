#!/bin/sh
set -e
for d in driver.*.py ; do
  # driver.narrow.py reads the `_alt` routines the other drivers write, and
  # admin/regenerate deletes them first, so it runs last.
  [ "$d" = driver.narrow.py ] && continue
  python3 $d
done
python3 driver.narrow.py
