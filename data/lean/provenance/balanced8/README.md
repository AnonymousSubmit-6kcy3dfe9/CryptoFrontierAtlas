# Balanced-eight generator inputs

`tables.json` and `global_farkas_69.json` are the exact input bytes used to
generate `../../LeanCipher/BalancedEightCertificateData.lean`. Their hashes,
sizes, original artifact member names, and the deterministic generator command
are recorded in [`manifest.json`](manifest.json).

The checked-in inputs are sufficient to replay the Lean data file; the original
submission ZIP is not required. When that ZIP is available, pass its path to
`../../scripts/verify_balanced8_provenance.py --artifact-zip` to verify the
member-level provenance as well.
