"""Prints whether pyrind VERSION is below, within, or past
pyrind-cryptography's pyrind requirement.

Usage: python3 pin.py VERSION
"""

import pathlib
import sys
import tomllib

from packaging.requirements import Requirement
from packaging.version import Version


def place(version: str, requirement: str) -> str:
    """Where pyrind `version` falls against `requirement`."""
    spec = Requirement(requirement).specifier
    # Only the >= and < bounds the pin uses, so no other form is misread.
    if any(s.operator not in (">=", "<") for s in spec):
        raise ValueError(f"only >= and < bounds are read, not {requirement}")
    v = Version(version)
    if v in spec:
        return "within"
    if any(v < Version(s.version) for s in spec if s.operator == ">="):
        return "below"
    return "past"


if __name__ == "__main__":
    pyproject = pathlib.Path(__file__).with_name("pyproject.toml")
    with open(pyproject, "rb") as f:
        deps = tomllib.load(f)["project"]["dependencies"]
    [requirement] = [d for d in deps if Requirement(d).name == "pyrind"]
    print(place(sys.argv[1], requirement))
