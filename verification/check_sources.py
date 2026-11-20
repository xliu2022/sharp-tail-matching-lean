#!/usr/bin/env python3
"""Conservative source scan; the Lean axiom audit is the authoritative check."""
from pathlib import Path
import re
import json
import sys

root = Path(__file__).resolve().parents[1]
files = [root / "SharpTailMatching.lean", root / "Solution.lean", *sorted((root / "SharpTailMatching").rglob("*.lean"))]

def code_without_comments(text: str) -> str:
    result = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                result.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif in_string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                in_string = False
                i += 1
            else:
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            in_string = True
            i += 1
        else:
            result.append(text[i])
            i += 1
    return "".join(result)

forbidden = re.compile(r"\b(?:sorry|admit|axiom|sorryAx|native_decide|ofReduceBool|unsafe)\b")
problems = []
theorems = definitions = lines = 0
for path in files:
    text = path.read_text(encoding="utf-8")
    code = code_without_comments(text)
    lines += len(text.splitlines())
    theorems += len(re.findall(r"\b(?:theorem|lemma)\s+[A-Za-z_]", code))
    definitions += len(re.findall(r"\b(?:def|structure|abbrev)\s+[A-Za-z_]", code))
    for match in forbidden.finditer(code):
        problems.append(f"{path.relative_to(root)}: forbidden token {match.group(0)!r}")

config = json.loads((root / "comparator.json").read_text())
targets = json.loads((root / "verification" / "targets.json").read_text())
if config["theorem_names"] != targets["headline"]:
    problems.append("Comparator targets differ from the recorded headline target list")
challenge = code_without_comments((root / "Challenge.lean").read_text())
if len(re.findall(r"\bsorry\b", challenge)) != len(targets["headline"]):
    problems.append("Unexpected number of deliberate Challenge statement holes")
for path in files:
    code = code_without_comments(path.read_text())
    if re.search(r"(?m)^\s*(?:public\s+)?import\s+Challenge(?:\s|$)", code):
        problems.append(f"{path.relative_to(root)} imports Challenge")

print(f"Lean source files: {len(files)} (including the aggregate import file)")
print(f"Source lines, including comments and blank lines: {lines}")
print(f"Named theorem/lemma declarations: {theorems}")
print(f"Definitions/structures/abbreviations: {definitions}")
if problems:
    print("\n".join(problems))
    sys.exit(1)
print("PASS: no proof placeholders, extra axioms, native_decide, or unsafe declarations in project sources.")
print("Challenge.lean is excluded: its nine deliberate statement holes are checked against Solution by Comparator.")
print("This textual check supplements, and does not replace, Lean's kernel and #print axioms checks.")

