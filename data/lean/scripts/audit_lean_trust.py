#!/usr/bin/env python3
"""Reject admissions and audit the axioms of the public complete theorems."""

from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
AXIOM_AUDIT = ROOT / "scripts" / "AxiomAudit.lean"

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ORDINARY_THEOREMS = {
    "CryptoFrontierAtlas.tu_deng_conjecture_complete",
    "CryptoFrontierAtlas.VectorialNonlinearityComplete.vectorial_nonlinearity_is_minimum_component",
    "CryptoFrontierAtlas.VectorialNonlinearityComplete.vectorial_nonlinearity_min_component_spec",
    "CryptoFrontierAtlas.VectorialNonlinearityComplete.uniform_vectorial_nonlinearity_bound",
    "CryptoFrontierAtlas.BalancedEightNonlinearityComplete.balanced_eight_nonlinearity_is_affine_distance",
}
NATIVE_THEOREMS = {
    "CryptoFrontierAtlas.BalancedEightNonlinearityComplete.balanced_eight_nonlinearity_le_116",
    "CryptoFrontierAtlas.BalancedEightNonlinearityComplete.balanced_eight_bound_is_sharp",
}
EXPECTED_THEOREMS = ORDINARY_THEOREMS | NATIVE_THEOREMS

FORBIDDEN_WORD = re.compile(r"\b(?:sorry|sorryAx|admit|axiom|unsafe|opaque|partial)\b")
CONSTANT_DECLARATION = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable|local)\s+)*constant\b"
)
FORBIDDEN_OPTION_SETTINGS = (
    (
        re.compile(r"\bset_option\s+checkBinderAnnotations\s+false\b"),
        "set_option checkBinderAnnotations false",
    ),
    (
        re.compile(r"\bset_option\s+warningAsError\s+false\b"),
        "set_option warningAsError false",
    ),
)
AXIOM_REPORT = re.compile(r"'([^']+)' depends on axioms:\s*\[(.*?)\]", re.DOTALL)


def strip_comments_and_strings(source: str) -> str:
    """Remove nested Lean comments and strings while retaining line breaks."""
    result = []
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    while index < len(source):
        current = source[index]
        following = source[index + 1] if index + 1 < len(source) else ""

        if in_line_comment:
            if current == "\n":
                in_line_comment = False
                result.append("\n")
            else:
                result.append(" ")
            index += 1
            continue

        if block_depth:
            if current == "/" and following == "-":
                block_depth += 1
                result.extend("  ")
                index += 2
            elif current == "-" and following == "/":
                block_depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if current == "\n" else " ")
                index += 1
            continue

        if in_string:
            result.append("\n" if current == "\n" else " ")
            if escaped:
                escaped = False
            elif current == "\\":
                escaped = True
            elif current == '"':
                in_string = False
            index += 1
            continue

        if current == "-" and following == "-":
            in_line_comment = True
            result.extend("  ")
            index += 2
        elif current == "/" and following == "-":
            block_depth = 1
            result.extend("  ")
            index += 2
        elif current == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(current)
            index += 1

    if block_depth:
        raise ValueError("unterminated block comment")
    if in_string:
        raise ValueError("unterminated string literal")
    return "".join(result)


def source_location(source: str, offset: int) -> int:
    return source.count("\n", 0, offset) + 1


def self_check_source_audit() -> None:
    for pattern, directive in FORBIDDEN_OPTION_SETTINGS:
        live_directive = "\n\t".join(directive.split())
        inert_directives = (
            f"-- {directive}\n",
            f"/- outer /- {directive} -/ comment -/",
            f'"{directive}"',
        )
        if not pattern.search(strip_comments_and_strings(live_directive)) or any(
            pattern.search(strip_comments_and_strings(source))
            for source in inert_directives
        ):
            raise RuntimeError(f"source audit self-check failed for {directive!r}")


def audit_sources() -> None:
    failures = []
    files = sorted(
        path for path in ROOT.rglob("*.lean") if ".lake" not in path.parts
    )
    for path in files:
        source = path.read_text(encoding="utf-8")
        try:
            code = strip_comments_and_strings(source)
        except ValueError as error:
            failures.append(f"{path.relative_to(ROOT)}: {error}")
            continue
        for pattern in (FORBIDDEN_WORD, CONSTANT_DECLARATION):
            for match in pattern.finditer(code):
                failures.append(
                    f"{path.relative_to(ROOT)}:{source_location(code, match.start())}: "
                    f"forbidden token {match.group(0).strip()!r}"
                )
        for pattern, directive in FORBIDDEN_OPTION_SETTINGS:
            for match in pattern.finditer(code):
                failures.append(
                    f"{path.relative_to(ROOT)}:{source_location(code, match.start())}: "
                    f"forbidden option setting {directive!r}"
                )

    if failures:
        raise RuntimeError("forbidden Lean source constructs:\n" + "\n".join(failures))
    print(f"source audit PASS: {len(files)} Lean files, no forbidden constructs")


def parse_axioms(output: str) -> dict[str, set[str]]:
    reports = {}
    for theorem, body in AXIOM_REPORT.findall(output):
        reports[theorem] = {item.strip() for item in body.split(",") if item.strip()}
    return reports


def audit_axioms() -> None:
    completed = subprocess.run(
        ["lake", "env", "lean", str(AXIOM_AUDIT)],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    output = completed.stdout + completed.stderr
    print(output, end="" if output.endswith("\n") else "\n")
    if completed.returncode:
        raise RuntimeError(f"Lean axiom audit failed with exit code {completed.returncode}")

    reports = parse_axioms(output)
    missing_reports = EXPECTED_THEOREMS - reports.keys()
    extra_reports = reports.keys() - EXPECTED_THEOREMS
    if missing_reports or extra_reports:
        raise RuntimeError(
            f"unexpected axiom reports; missing={sorted(missing_reports)}, "
            f"extra={sorted(extra_reports)}"
        )

    for theorem in sorted(ORDINARY_THEOREMS):
        if reports[theorem] != STANDARD_AXIOMS:
            raise RuntimeError(
                f"{theorem} crossed the ordinary-kernel trust boundary: "
                f"{sorted(reports[theorem])}"
            )

    for theorem in sorted(NATIVE_THEOREMS):
        axioms = reports[theorem]
        native_axioms = {
            name
            for name in axioms
            if name.startswith("LeanCipher.") and "._native.native_decide.ax_" in name
        }
        unexpected = axioms - STANDARD_AXIOMS - native_axioms
        if unexpected or not native_axioms or not STANDARD_AXIOMS.issubset(axioms):
            raise RuntimeError(
                f"{theorem} has an unexpected trust boundary: "
                f"unexpected={sorted(unexpected)}, native={sorted(native_axioms)}"
            )

    sharp = reports[
        "CryptoFrontierAtlas.BalancedEightNonlinearityComplete.balanced_eight_bound_is_sharp"
    ]
    if not any(".witness_weight." in name for name in sharp) or not any(
        ".witness_maximumWalshMagnitude." in name for name in sharp
    ):
        raise RuntimeError("sharpness theorem is missing its two native witness checks")

    print("axiom audit PASS: ordinary proofs use only standard axioms; Balanced-eight extras are native_decide")


def main() -> None:
    self_check_source_audit()
    audit_sources()
    audit_axioms()


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, ValueError) as error:
        print(f"trust audit FAILED: {error}", file=sys.stderr)
        raise SystemExit(1)
