"""
Print the list of lean files in the MIL folder that do not import Mathlib.Tactic
"""
from pathlib import Path

for path in (Path(__file__).parent.parent/"MIL").glob("**/*.lean"):
    if not any([l == "import Mathlib.Tactic" for l in path.read_text().split("\n")]):
        print(path)
