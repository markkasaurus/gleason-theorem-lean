# Gleason's Theorem: A Lean 4 Formalization

This repository formalizes Gleason's theorem for separable real and complex
Hilbert spaces of dimension at least three.

## Main theorem

The public statement is defined in `GleasonStatement.lean`, which imports only
Mathlib. The proof entry point is:

```lean
ClassicalGleason.Separable.gleason_theorem_verified
```

For `𝕜 = ℝ` and `𝕜 = ℂ`, every nonnegative, countably additive finite measure
on the orthogonal projections of a separable Hilbert space `H`, with
`3 ≤ Module.rank 𝕜 H`, has a unique representing positive trace-class
operator. Representation is expressed by basis-independent diagonal sums on
the range of each projection.

The proof follows the projection/frame-function route and establishes the
required continuity and quadraticity through finite-dimensional harmonic
analysis and an oscillation argument.

## Mathematical source

A. M. Gleason, "Measures on the Closed Subspaces of a Hilbert Space,"
*Journal of Mathematics and Mechanics* **6** (1957), 885-893.
[doi:10.1512/iumj.1957.6.56050](https://doi.org/10.1512/iumj.1957.6.56050)

## Environment

The project pins Lean `4.26.0` and Mathlib `v4.26.0`. From a fresh checkout:

```sh
lake exe cache get
lake build
```

## Verification

```sh
./scripts/verify.sh
```

The verification routine builds the project, checks the reported axiom
dependencies, and rejects placeholders, custom axioms, unsafe declarations,
known development-artifact patterns, and build warnings.

The repository also contains a manually triggered comparator workflow. It
constructs a trusted challenge from `GleasonStatement.lean` at runtime and
compares it with `GleasonVerification.lean` on Linux. No challenge containing a
placeholder is committed to the repository.

See `docs/THEOREM.md`, `docs/ARCHITECTURE.md`, and `docs/VERIFICATION.md` for
the precise statement and verification boundary.

## License

Copyright 2026 Mark J. Soares. Licensed under the Apache License 2.0.
