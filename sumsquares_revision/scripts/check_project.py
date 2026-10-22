#!/usr/bin/env python3
"""Source/preflight checks; the Lean comparator performs proof verification."""

from pathlib import Path
import json
import re
import sys


ROOT = Path(__file__).resolve().parents[1]


def fail(message: str) -> None:
    raise ValueError(message)


def lean_code(text: str) -> str:
    """Mask strings and nested Lean comments, preserving source line numbers."""
    result = list(text)
    index = 0
    depth = 0
    string = False
    while index < len(text):
        if depth:
            width = 2 if text.startswith(("/-", "-/"), index) else 1
            if text.startswith("/-", index):
                depth += 1
            elif text.startswith("-/", index):
                depth -= 1
        elif string:
            width = 2 if text[index] == "\\" and index + 1 < len(text) else 1
            if text[index] == '"':
                string = False
        elif text.startswith("--", index):
            end = text.find("\n", index)
            width = (len(text) if end < 0 else end) - index
        elif text.startswith("/-", index):
            depth = 1
            width = 2
        elif text[index] == '"':
            string = True
            width = 1
        else:
            index += 1
            continue
        for cursor in range(index, min(index + width, len(text))):
            if text[cursor] != "\n":
                result[cursor] = " "
        index += width
    if depth or string:
        fail("unterminated Lean comment or string")
    return "".join(result)


def main() -> None:
    required = [
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "RequestProject/Main.lean", "Challenge.lean", "Solution.lean",
        "comparator.json", "formalization.yaml",
    ]
    missing = [name for name in required if not (ROOT / name).is_file()]
    if missing:
        fail("missing required project files: " + ", ".join(missing))
    if (ROOT / "RequestProject ").exists():
        fail("remove the trailing space from the RequestProject directory")

    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    if config.get("challenge_module") != "Challenge" or config.get("solution_module") != "Solution":
        fail("comparator must compare Challenge with Solution")
    names = config.get("theorem_names", [])
    if not isinstance(names, list) or not names or not all(isinstance(n, str) for n in names):
        fail("comparator theorem_names must be a nonempty list of names")
    if len(names) != len(set(names)):
        fail("duplicate comparator theorem name")
    if set(config.get("permitted_axioms", [])) != {"propext", "Quot.sound", "Classical.choice"}:
        fail("the permitted axioms must be exactly propext, Quot.sound, and Classical.choice")
    if config.get("definition_names", []):
        fail("this paper challenge must not leave definition holes")

    sources = list((ROOT / "RequestProject").rglob("*.lean")) + [ROOT / "Solution.lean"]
    if (ROOT / "RequestProject.lean").is_file():
        sources.append(ROOT / "RequestProject.lean")
    forbidden = re.compile(r"(?<![\w'])\b(?:sorry|admit|axiom|sorryAx|native_decide|implemented_by)\b(?![\w'])")
    for path in sources:
        code = lean_code(path.read_text(encoding="utf-8"))
        for match in forbidden.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            fail(f"{path.relative_to(ROOT)}:{line}: forbidden proof-source token {match.group()}")

    for module in ("Challenge", "Solution"):
        code = lean_code((ROOT / f"{module}.lean").read_text(encoding="utf-8"))
        if not re.search(r"^namespace\s+Paper\s*$", code, flags=re.MULTILINE):
            fail(f"{module}.lean must expose its statements in namespace Paper")
        declarations = re.findall(r"^theorem\s+([\w']+)", code, flags=re.MULTILINE)
        actual = {"Paper." + name for name in declarations}
        if len(declarations) != len(actual) or actual != set(names):
            fail(f"{module}.lean and comparator.json have different theorem inventories: "
                 f"missing={sorted(set(names) - actual)}, extra={sorted(actual - set(names))}")
        if module == "Challenge":
            imports = re.findall(r"^(?:public\s+)?import\s+([^\n]+)", code, flags=re.MULTILINE)
            if [value.strip() for value in imports] != ["Mathlib"]:
                fail("Challenge.lean must import only Mathlib, independently of the proof development")
            if re.search(r"(?<![\w'])\b(?:axiom|implemented_by)\b(?![\w'])", code):
                fail("Challenge.lean contains an axiom or implemented_by declaration")

    print(f"OK: {len(names)} named statements in each interface; proof sources contain no placeholders or extra axioms.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, TypeError) as error:
        print(f"error: {error}", file=sys.stderr)
        sys.exit(1)
