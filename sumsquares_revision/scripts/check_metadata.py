#!/usr/bin/env python3
"""Validate formalization.yaml against the pinned upstream v0.4 schema."""

from pathlib import Path
import json
import sys

try:
    import jsonschema
    import yaml
except ImportError as error:
    raise SystemExit("Install the metadata validator with: python3 -m pip install -r scripts/requirements.txt") from error

ROOT = Path(__file__).resolve().parents[1]
schema = json.loads((ROOT / "scripts/schema/formalization-v0.4.schema.json").read_text(encoding="utf-8"))
data = yaml.safe_load((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
if not isinstance(data, dict) or data.get("version") != "v0.4":
    raise SystemExit('error: formalization.yaml must declare version: "v0.4"')
jsonschema.Draft7Validator.check_schema(schema)
errors = list(jsonschema.Draft7Validator(schema).iter_errors(data))
if errors:
    for error in errors:
        location = ".".join(map(str, error.absolute_path)) or "<root>"
        print(f"error: {location}: {error.message}", file=sys.stderr)
    raise SystemExit(1)
print("OK: formalization.yaml conforms to the pinned v0.4 schema.")
