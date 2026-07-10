import Mathlib

/-!
# Gleason's Theorem on Separable Hilbert Spaces

This file contains the public mathematical statement and the definitions needed
to express it. It has no dependency on the proof implementation.

For a positive operator, finiteness and basis-independence of its diagonal sum
is the standard characterization of trace class. This formulation is used
because Mathlib does not yet provide a general trace-class operator API.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe u v

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A bundled orthogonal projection. -/
abbrev OrthogonalProjection (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] :=
  {P : H →L[𝕜] H // IsStarProjection P}

instance : Zero (OrthogonalProjection 𝕜 H) :=
  ⟨⟨0, IsStarProjection.zero (H →L[𝕜] H)⟩⟩

instance : One (OrthogonalProjection 𝕜 H) :=
  ⟨⟨1, IsStarProjection.one (H →L[𝕜] H)⟩⟩

/-- A finite measure on the orthogonal projections which is additive for
countable orthogonal strong sums. This is equivalent to a countably additive
finite measure on the closed subspaces of a Hilbert space. -/
structure ProjectionMeasure (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] where
  μ : OrthogonalProjection 𝕜 H → ℝ
  nonneg : ∀ P, 0 ≤ μ P
  countably_additive :
    ∀ {ι : Type v} [Countable ι]
      (P : ι → OrthogonalProjection 𝕜 H) (Q : OrthogonalProjection 𝕜 H),
      Pairwise (fun i j => (P i).1 * (P j).1 = 0) →
      (∀ x : H, HasSum (fun i => (P i).1 x) (Q.1 x)) →
      HasSum (fun i => μ (P i)) (μ Q)

/-- The diagonal of `T` has sum `r` in every Hilbert basis. For positive
operators this is the basis-independent trace relation. -/
def HasDiagonalTrace (T : H →L[𝕜] H) (r : ℝ) : Prop :=
  ∀ {ι : Type v} (b : HilbertBasis ι 𝕜 H),
    HasSum (fun i => RCLike.re (inner 𝕜 (b i) (T (b i)))) r

/-- The trace pairing of `T` with `P` has value `r`. The sum is taken over an
arbitrary Hilbert basis of the range of `P`, making basis independence explicit. -/
def HasProjectionTrace (T : H →L[𝕜] H)
    (P : OrthogonalProjection 𝕜 H) (r : ℝ) : Prop :=
  ∀ {ι : Type v} (b : HilbertBasis ι 𝕜 (LinearMap.range P.1)),
    HasSum
      (fun i =>
        RCLike.re
          (inner 𝕜 ((b i : LinearMap.range P.1) : H)
            (T ((b i : LinearMap.range P.1) : H))))
      r

/-- A positive trace-class operator represents a projection measure by the
trace pairing. -/
def Represents (m : ProjectionMeasure 𝕜 H) (T : H →L[𝕜] H) : Prop :=
  T.IsPositive ∧
  HasDiagonalTrace T (m.μ 1) ∧
  ∀ P : OrthogonalProjection 𝕜 H, HasProjectionTrace T P (m.μ P)

/-- Gleason's theorem for separable real or complex Hilbert spaces of
dimension at least three. -/
def GleasonStatement (𝕜 : Type u) [RCLike 𝕜] : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H],
    (3 : Cardinal) ≤ Module.rank 𝕜 H →
    ∀ m : ProjectionMeasure 𝕜 H,
      ∃! T : H →L[𝕜] H, Represents m T

end ClassicalGleason.Separable
