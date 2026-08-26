#!/usr/bin/env python3
"""Translate the balanced-eight JSON artifacts into auditable Lean constants."""

from fractions import Fraction
from functools import reduce
import json
from math import gcd, lcm
from pathlib import Path
import sys


def profile_expr(values):
    names = ("n20", "n12", "n4", "n16", "n8", "n0")
    return "{ " + ", ".join(f"{name} := {value}" for name, value in zip(names, values)) + " }"


def table_expr(values):
    names = ("a", "b", "c", "d", "e", "f", "g", "h", "i")
    return "{ " + ", ".join(f"{name} := {value}" for name, value in zip(names, values)) + " }"


def int_list(values):
    return "[" + ", ".join(str(value) for value in values) + "]"


def cleared_vector(values):
    rationals = [Fraction(value) for value in values]
    denominator = reduce(lcm, (value.denominator for value in rationals), 1)
    numerators = [value.numerator * (denominator // value.denominator) for value in rationals]
    common = reduce(gcd, (abs(value) for value in numerators), denominator)
    return denominator // common, [value // common for value in numerators]


def main():
    if len(sys.argv) != 4:
        raise SystemExit("usage: generate_balanced8_certificate_data.py TABLES FARKAS OUTPUT")
    table_path, farkas_path, output_path = map(Path, sys.argv[1:])
    tables = json.loads(table_path.read_text(encoding="utf-8"))
    farkas = json.loads(farkas_path.read_text(encoding="utf-8"))

    lines = [
        "import Mathlib",
        "",
        "namespace LeanCipher.BalancedEightCertificates",
        "",
        "structure Profile where",
        "  n20 : Nat",
        "  n12 : Nat",
        "  n4 : Nat",
        "  n16 : Nat",
        "  n8 : Nat",
        "  n0 : Nat",
        "  deriving DecidableEq, Repr, Ord",
        "",
        "structure LocalTable where",
        "  a : Nat",
        "  b : Nat",
        "  c : Nat",
        "  d : Nat",
        "  e : Nat",
        "  f : Nat",
        "  g : Nat",
        "  h : Nat",
        "  i : Nat",
        "  deriving DecidableEq, Repr, Ord",
        "",
        "structure Family where",
        "  weight : Nat",
        "  profile : Profile",
        "  rows : List LocalTable",
        "  deriving DecidableEq, Repr",
        "",
        "structure IntCertificate where",
        "  profile : Profile",
        "  scale : Nat",
        "  z : List Int",
        "  deriving DecidableEq, Repr",
        "",
        "/- Generated mechanically from tables.json. -/",
        "def declaredFamilies : List Family := [",
    ]
    families = []
    for weight in (59, 61, 63):
        for key, rows in sorted(tables[str(weight)].items(), key=lambda item: tuple(map(int, item[0].split(",")))):
            profile = tuple(map(int, key.split(",")))
            row_text = ",\n      ".join(table_expr(row) for row in rows)
            families.append(
                f"  {{ weight := {weight}, profile := {profile_expr(profile)}, rows := [\n"
                f"      {row_text}\n    ] }}"
            )
    lines.append(",\n".join(families))
    lines.extend([
        "]",
        "",
        "/- Rational vectors from global_farkas_69.json, cleared to primitive integers. -/",
        "def declaredCertificates : List IntCertificate := [",
    ])
    certificates = []
    for item in farkas["certificates"]:
        scale, z = cleared_vector(item["y"])
        certificates.append(
            f"  {{ profile := {profile_expr(item['profile'])}, scale := {scale}, z := {int_list(z)} }}"
        )
    lines.append(",\n".join(certificates))
    lines.extend([
        "]",
        "",
        "def declaredSurvivors : List Profile := [",
        ",\n".join(f"  {profile_expr(profile)}" for profile in farkas["survivors"]),
        "]",
        "",
        "end LeanCipher.BalancedEightCertificates",
        "",
    ])
    output_path.write_text("\n".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()
