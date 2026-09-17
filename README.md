# CryptoFrontierAtlas

CryptoFrontierAtlas collects research problems on block ciphers and their
mathematical foundations. This is the anonymous artifact repository accompanying
EUROCRYPT submission #81.

Deployed web interface:
[Browse the problem collection](https://anonymoussubmit-6kcy3dfe9.github.io/CryptoFrontierAtlas/).

## Setup

Requirements: Git, Node.js 20 or later, and npm. Use a clone with the full
repository history and run the following from its root:

```bash
npm ci
npm run check:data
npm run dev
```

To build and preview the production site locally:

```bash
npm run build
npm run preview
```

## Lean proofs

The three principal formalizations have the following theorem entry points:

| Result | Lean entry point |
| --- | --- |
| Tu–Deng inequality | [TuDengComplete.lean](data/lean/CryptoFrontierAtlas/TuDengComplete.lean) |
| Vectorial nonlinearity bound beyond the Nyberg threshold | [VectorialNonlinearityComplete.lean](data/lean/CryptoFrontierAtlas/VectorialNonlinearityComplete.lean) |
| Optimal nonlinearity of eight-variable balanced Boolean functions: 116 | [BalancedEightNonlinearityComplete.lean](data/lean/CryptoFrontierAtlas/BalancedEightNonlinearityComplete.lean) |

Proof implementations are in [`data/lean/LeanCipher/`](data/lean/LeanCipher/).

To check all three formalizations, install [elan](https://github.com/leanprover/elan#installation)
and run the following from the repository root:

```bash
cd data/lean
lake build CryptoFrontierAtlas
```

The project uses Lean 4.29.1, fixed by [`lean-toolchain`](data/lean/lean-toolchain),
with dependencies pinned in [`lake-manifest.json`](data/lean/lake-manifest.json).
Further replay instructions and verification trust assumptions are documented in
[`data/lean/README.md`](data/lean/README.md).

License: [Apache-2.0](LICENSE) for code and Lean proofs;
[CC BY 4.0](LICENSE-DATA.md) for problem data.
