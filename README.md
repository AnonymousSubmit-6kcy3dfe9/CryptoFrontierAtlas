# CryptoFrontierAtlas

CryptoFrontierAtlas is a public, source-aware atlas of open questions in
cryptography. Its taxonomy reserves symmetric cryptography, asymmetric
cryptography, and other cryptographic research as top-level areas; the current
release populates symmetric cryptography only. It indexes formal problem
statements, public literature progress, scope boundaries, and evidence status
in a static site designed for GitHub Pages.

The public release contains 49 English problem records and three explicitly
cleared, scoped Lean applications under data/lean. They completely formalize
the uniform Tu--Deng inequality, the stated vectorial-nonlinearity bound beyond
the Nyberg threshold, and the sharp balanced eight-variable maximum of 116.
Other private solutions and uncleared manuscripts remain out of the repository.

Anonymous or unpublished internal progress is not represented in the public
timeline. The public timeline contains source statements and identifiable
literature or verification events only.

## Local development

The website requires Node.js 20 or newer.

```bash
npm install
npm run check:data
npm run dev
```

The production build is:

```bash
npm run build
npm run preview
```

The data contract is [`data/schema/problem.schema.json`](data/schema/problem.schema.json),
the release manifest is [`data/manifest.json`](data/manifest.json),
and the inclusion, disclosure, taxonomy, and release policy is documented in
[`DESIGN.md`](DESIGN.md).

The Lean artifacts can be replayed independently of the website:

    cd data/lean
    lake build CryptoFrontierAtlas

The project records its Lean toolchain and mathlib lockfile. The complete
replay and trust-boundary checks are documented in
[`data/lean/README.md`](data/lean/README.md); finite checks that use
`native_decide` are documented there with that evaluator's trust boundary.

## Contribution boundary

New records require a public source citation, an auditable scope, status and
disclosure fields, and license review. Do not add local absolute paths,
private proof text, answer-bearing filenames, or Lean artifacts that have not
been explicitly cleared for publication and scoped in the metadata.

## License

Metadata and dataset text are released under CC BY 4.0; the website and
validation code are released under Apache-2.0. See `LICENSE-DATA.md` and
`LICENSE`.
