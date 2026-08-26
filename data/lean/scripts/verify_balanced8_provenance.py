#!/usr/bin/env python3
"""Verify and replay the checked Balanced-eight certificate-data provenance."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile


ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = ROOT / "provenance" / "balanced8" / "manifest.json"


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def checked_path(relative_path: str) -> Path:
    path = (ROOT / relative_path).resolve()
    if ROOT.resolve() not in path.parents:
        raise ValueError(f"path escapes Lean project: {relative_path}")
    return path


def verify_record(record: dict) -> bytes:
    path = checked_path(record["path"])
    data = path.read_bytes()
    actual_hash = sha256(data)
    if actual_hash != record["sha256"] or len(data) != record["bytes"]:
        raise RuntimeError(
            f"provenance mismatch for {record['path']}: "
            f"sha256={actual_hash}, bytes={len(data)}"
        )
    return data


def verify_original_zip(zip_path: Path, manifest: dict, inputs: dict[str, bytes]) -> None:
    archive_bytes = zip_path.read_bytes()
    archive = manifest["source_artifact"]
    if sha256(archive_bytes) != archive["sha256"] or len(archive_bytes) != archive["bytes"]:
        raise RuntimeError(f"source artifact hash or size mismatch: {zip_path}")

    with zipfile.ZipFile(zip_path) as bundle:
        for record in manifest["inputs"]:
            member_data = bundle.read(record["source_member"])
            if member_data != inputs[record["path"]]:
                raise RuntimeError(
                    f"checked input differs from ZIP member {record['source_member']}"
                )
    print(f"source artifact PASS: {zip_path}")


def replay_generator(manifest: dict) -> None:
    generator = checked_path(manifest["generator"]["path"])
    tables = checked_path(manifest["inputs"][0]["path"])
    farkas = checked_path(manifest["inputs"][1]["path"])
    expected = checked_path(manifest["output"]["path"]).read_bytes()

    with tempfile.TemporaryDirectory(prefix="balanced8-lean-") as temporary_directory:
        regenerated = Path(temporary_directory) / "BalancedEightCertificateData.lean"
        completed = subprocess.run(
            [sys.executable, str(generator), str(tables), str(farkas), str(regenerated)],
            cwd=ROOT,
            check=False,
        )
        if completed.returncode:
            raise RuntimeError(f"generator failed with exit code {completed.returncode}")
        actual = regenerated.read_bytes()

    if actual != expected:
        raise RuntimeError(
            "generator output differs from LeanCipher/BalancedEightCertificateData.lean; "
            f"expected sha256={sha256(expected)}, actual sha256={sha256(actual)}"
        )
    print(f"generator replay PASS: sha256={sha256(actual)}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--artifact-zip",
        type=Path,
        help="optionally verify the original balanced8_nl118_iacr_artifact.zip",
    )
    arguments = parser.parse_args()

    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    if manifest.get("schema_version") != "1.0":
        raise RuntimeError("unsupported provenance manifest version")

    input_records = {record["path"]: record for record in manifest["inputs"]}
    inputs = {path: verify_record(record) for path, record in input_records.items()}
    verify_record(manifest["output"])
    if arguments.artifact_zip:
        verify_original_zip(arguments.artifact_zip.resolve(), manifest, inputs)
    replay_generator(manifest)


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, RuntimeError, ValueError, zipfile.BadZipFile) as error:
        print(f"Balanced-eight provenance FAILED: {error}", file=sys.stderr)
        raise SystemExit(1)
