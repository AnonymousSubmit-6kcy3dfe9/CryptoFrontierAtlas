# Lean verification artifacts

This directory is a standalone Lean 4 project for three principal applications
in the accompanying submission. The environment is fixed by `lean-toolchain`
at Lean 4.29.1 and by `lake-manifest.json` at mathlib commit
`5e932f97dd25535344f80f9dd8da3aab83df0fe6` (input tag `v4.29.1`).

## Replay

From a clean checkout, install Elan and run the following from this directory.
`lake build` consumes the checked lockfile; `lake update` is not part of the
reproducible replay. The package configuration passes
`-DwarningAsError=true`, so every ordinary Lake build also enforces a
warning-free source tree.

    lake build CryptoFrontierAtlas

The aggregate module imports all three application modules. Individual files
can also be checked with:

    lake env lean CryptoFrontierAtlas/TuDengComplete.lean
    lake env lean CryptoFrontierAtlas/TuDeng.lean
    lake env lean CryptoFrontierAtlas/VectorialNonlinearityComplete.lean
    lake env lean CryptoFrontierAtlas/VectorialNonlinearity.lean
    lake env lean CryptoFrontierAtlas/BalancedEightNonlinearityComplete.lean
    lake env lean CryptoFrontierAtlas/BalancedEightNonlinearity.lean
    lake env lean LeanCipher/BooleanNonlinearity.lean

The same checks used in CI are:

    python3 scripts/audit_lean_trust.py
    python3 scripts/verify_balanced8_provenance.py
    python3 scripts/report_lean_provenance.py

The CI workflow uses `leanprover/lean-action` pinned to commit
`38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9` (release `v1.5.0`). After the
Lake build it runs the bundled independent checker explicitly as
`LEAN_NUM_THREADS=1 lake env leanchecker CryptoFrontierAtlas`; the module
argument is required because the Lake package name differs from the aggregate
library target. Serial replay keeps the checker within public-runner memory
limits without changing the modules or declarations it rechecks.

The first command lexically rejects `sorry`, `sorryAx`, `admit`, user-written
axioms/constants, `opaque`, `unsafe`, and `partial` declarations in the project
sources. It also rejects the option settings
`set_option checkBinderAnnotations false` and
`set_option warningAsError false`, including variants separated by arbitrary
whitespace, while ignoring comments and string literals. These rules keep every
declaration under Lean's default instance-binder validation and prevent source
files from locally bypassing the package's warning-as-error policy. The command
then runs `#print axioms` on the complete public theorems and checks the output
against the trust boundary below. CI also runs Lean's independent `leanchecker`
environment check.

## Nonlinearity semantics

`LeanCipher/BooleanNonlinearity.lean` defines Hamming distance, affine Boolean
functions, maximum Walsh magnitude, and scalar nonlinearity for every input
dimension, including dimension zero. It proves that the spectral definition
`(2^n - max_a |W_f(a)|) / 2` equals the minimum Hamming distance from `f` to
an affine Boolean function. `LeanCipher/VectorialNonlinearity.lean` proves, for
every positive output dimension, that its joint spectral definition equals
the minimum scalar nonlinearity among all nonzero components `v . F`, and
exhibits a nonzero component attaining that minimum. Thus the
public vectorial and balanced-eight bounds use the same formally connected
coding-theoretic notion of nonlinearity as the manuscript.

## Exact scope

| Module | Mechanically checked | Outside this artifact |
| --- | --- | --- |
| TuDengComplete.lean plus its `LeanCipher` modules | The pair-count definition and the uniform Tu--Deng inequality for every `k >= 2` and `1 <= t <= 2^k - 2`, via greatest cyclic carries, a pivotal-subcube partition, and Russo/profile comparison | The optional equality characterization and equality-residue count are not part of this theorem |
| TuDeng.lean | A smaller native-replayable finite regression check through `k <= 8` | The all-parameter proof is in `TuDengComplete.lean`, not in this finite-check file |
| VectorialNonlinearityComplete.lean plus its `LeanCipher` modules | For every `k >= 3`, `k < m < 2k`, and `F : F_2^(2k) -> F_2^m`, a nonzero component has Walsh magnitude at least `2^k + 4`, hence `NL(F) <= 2^(2k-1) - 2^(k-1) - 2`; `NL(F)` is proved equal to the minimum scalar nonlinearity of the nonzero components; Walsh inversion, Parseval, Nyberg's bound, the bent hyperplane, normalization, and odd fibres are all proved internally | Tightness of the bound and the separate exhaustive value at `(n,m)=(4,3)` are outside this theorem |
| VectorialNonlinearity.lean | The reusable integer row-moment and odd-fibre contradiction at the end of the critical case | The full theorem is in `VectorialNonlinearityComplete.lean` |
| BalancedEightNonlinearityComplete.lean plus its `LeanCipher` modules | Every balanced `f : F_2^8 -> F_2` has `NL(f) <= 116`, and an explicit balanced function attains 116; the proof includes the local enumeration, 69 integer Farkas certificates, all 13 terminal profile exclusions, and the normalization and semantic bridges | Claims outside the balanced eight-variable case are outside this theorem |
| BalancedEightNonlinearity.lean | A smaller standalone replay of the 13 terminal profiles and the explicit balanced witness | The full theorem is in `BalancedEightNonlinearityComplete.lean` |

All three records may therefore cite their `Complete` modules as complete
formalizations of the displayed scoped theorems.

## Trust boundary

The complete Tu--Deng and vectorial theorems use ordinary Lean/mathlib proof
checking. Their `#print axioms` output contains only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. The finite Tu--Deng checks and parts of
the complete balanced-eight proof use `native_decide` for fixed finite
enumeration, certificate, parity, normalization, and witness checks; the
complete Balanced-eight theorem therefore additionally contains generated
`._native.native_decide.ax_*` declarations and trusts Lean's compiled native
evaluator. The surrounding reductions and soundness bridges are proved in
Lean. No project source contains an admission, user-declared axiom, opaque
replacement, unsafe declaration, disabled binder-annotation validation, or a
local warning-as-error bypass.

## Balanced-eight certificate provenance

The exact `tables.json` and `global_farkas_69.json` bytes used to generate
`LeanCipher/BalancedEightCertificateData.lean` are checked in under
`provenance/balanced8/`. `manifest.json` records their original ZIP member
names, SHA-256 hashes, sizes, the source artifact hash, the generator command,
and the generated Lean file hash. Rebuild and byte-compare the generated file
without changing the working tree by running:

    python3 scripts/verify_balanced8_provenance.py

Given the original `balanced8_nl118_iacr_artifact.zip`, also verify that the
checked inputs are byte-for-byte copies of its members:

    python3 scripts/verify_balanced8_provenance.py --artifact-zip /path/to/balanced8_nl118_iacr_artifact.zip

`scripts/report_lean_provenance.py` prints the Git commit, exact toolchain and
mathlib revisions, lockfile hash, and a deterministic digest of every Lean
source file. Each public problem record binds that complete source-tree digest
and file count to the immutable commit used by its GitHub link; `npm run
check:data` verifies the committed tree, the checked-out tree, and the public
wrapper digest agree. The CI log records the provenance report for every
checked commit.

The Lean source is licensed under Apache-2.0 with the repository software.
