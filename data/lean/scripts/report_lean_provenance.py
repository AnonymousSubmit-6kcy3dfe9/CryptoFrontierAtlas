#!/usr/bin/env python3
"""Print reproducible toolchain and Lean source-tree provenance as JSON."""

import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_files() -> list[Path]:
    return sorted(
        (path for path in ROOT.rglob("*.lean") if ".lake" not in path.parts),
        key=lambda path: path.relative_to(ROOT).as_posix(),
    )


def tree_sha256(files: list[Path]) -> str:
    digest = hashlib.sha256()
    for path in files:
        relative = path.relative_to(ROOT).as_posix().encode("utf-8")
        digest.update(relative)
        digest.update(b"\0")
        digest.update(hashlib.sha256(path.read_bytes()).digest())
        digest.update(b"\n")
    return digest.hexdigest()


def git_commit() -> str:
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    return completed.stdout.strip()


def main() -> None:
    manifest_path = ROOT / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    files = source_files()
    report = {
        "repository_commit": git_commit(),
        "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean_toolchain_file_sha256": file_sha256(ROOT / "lean-toolchain"),
        "lake_manifest_sha256": file_sha256(manifest_path),
        "mathlib_input_revision": mathlib["inputRev"],
        "mathlib_commit": mathlib["rev"],
        "lean_source_file_count": len(files),
        "lean_source_tree_sha256": tree_sha256(files),
        "source_tree_hash_algorithm": "sha256(path_utf8 + NUL + sha256(file_bytes) + LF), sorted by path",
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
