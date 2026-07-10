# Proof Architecture

The formalization is organized into four layers.

## Projection and quadratic foundations

`Gleason/Finite/` defines finite-dimensional projection frame functions,
rank-one projections, their associated quadratic function, polarization, and
the operator and trace reconstruction steps.

## Continuity and harmonic analysis

`Gleason/Continuity/`, `Gleason/Harmonic/`, and `SphericalHarmonics/` establish
continuity and quadraticity of nonnegative frame functions on the sphere. The
argument combines near-infimum oscillation control, rotation-equivariant
spherical harmonic projections, exclusion of higher harmonic sectors, and the
global parallelogram identity.

## Finite-dimensional theorem

`Gleason/Finite/Theorem.lean` assembles the complex finite-dimensional
projection theorem from the continuity result and the polarization/trace
pipeline.

## Separable extension

`Gleason/Separable/` restricts a projection measure to finite-dimensional
subspaces, constructs compatible local quadratic data, obtains the real and
complex representing operators, proves basis-independent trace formulas, and
establishes uniqueness. `Gleason/Separable/Theorem.lean` combines the real and
complex results.

`GleasonStatement.lean` is deliberately independent of all proof modules, and
`GleasonVerification.lean` is the sole public bridge from that statement to the
implementation theorem.
