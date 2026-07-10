# Theorem

## Public statement

The exact public proposition is `ClassicalGleason.Separable.GleasonStatement`,
defined in `GleasonStatement.lean`. The verified theorem is:

```lean
theorem ClassicalGleason.Separable.gleason_theorem_verified :
    GleasonStatement ℝ ∧ GleasonStatement ℂ
```

For either scalar field `𝕜`, the proposition quantifies over a separable
complete inner-product space `H` satisfying

```lean
(3 : Cardinal) ≤ Module.rank 𝕜 H
```

and a `ProjectionMeasure 𝕜 H`. Such a measure assigns a nonnegative real number
to each orthogonal projection and is countably additive whenever a pairwise
orthogonal family converges pointwise to its strong sum.

The conclusion gives a unique continuous linear operator `T` satisfying:

- `T.IsPositive`;
- the diagonal of `T` sums to `m.μ 1` in every Hilbert basis;
- on every projection `P`, the diagonal sum over a Hilbert basis of
  `LinearMap.range P` equals `m.μ P`.

For a positive operator, the finite basis-independent diagonal sum is the
trace-class condition. The range-basis sum is the trace pairing with `P`.

## Scope

The statement covers separable real and complex Hilbert spaces and does not
assume finite dimensionality. It includes uniqueness of the representing
operator. The finite-dimensional complex theorem used internally is also
available as `ClassicalGleason.finite_gleason_statement_from_oscillation`.

## Mathematical source

A. M. Gleason, "Measures on the Closed Subspaces of a Hilbert Space,"
*Journal of Mathematics and Mechanics* **6** (1957), 885-893.
[doi:10.1512/iumj.1957.6.56050](https://doi.org/10.1512/iumj.1957.6.56050)
