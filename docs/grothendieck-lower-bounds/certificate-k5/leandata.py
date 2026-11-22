"""Read the witness data from the Lean sources, where they are stored once.

The tables are `def <name> : Array String := #["...", ...]`, one comma-separated row of
integers per string; single rows are `def <name> : String := "..."`.
"""
from pathlib import Path
import re

LEAN = Path(__file__).resolve().parents[3] / "lean" / "Lemmata" / "GrothendieckLowerBounds"


def _source(module):
    return (LEAN / f"{module}.lean").read_text(encoding="utf-8")


def table(module, name):
    match = re.search(r"def " + name + r" : Array String := #\[(.*?)\]", _source(module), re.S)
    assert match, f"{name} not found in {module}.lean"
    return [[int(t) for t in row.split(",")] for row in re.findall(r'"([^"]*)"', match.group(1))]


def row(module, name):
    match = re.search(r'def ' + name + r' : String := "([^"]*)"', _source(module))
    assert match, f"{name} not found in {module}.lean"
    return [int(t) for t in match.group(1).split(",")]


def matrix_text(rows):
    """The certified text form: single spaces between entries, a line feed after every row."""
    return "".join(" ".join(map(str, r)) + "\n" for r in rows)
