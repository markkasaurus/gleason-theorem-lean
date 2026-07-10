import Gleason.Separable.ComplexOperator
import Gleason.Separable.BasisDecomposition

/-!
# Trace Representation over the Complex Field

Countable additivity along Hilbert bases identifies the diagonal sums of the
representing operator with the projection measure.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ProjectionMeasure

theorem measure_rankOne_eq_inner_representingOperator
    (m : ProjectionMeasure ℂ H) (hdim : (3 : Cardinal) ≤ Module.rank ℂ H)
    (u : H) (hu : ‖u‖ = 1) :
    m.μ (OrthogonalProjection.rankOne (𝕜 := ℂ) u) =
      (inner ℂ u (m.representingOperator hdim u)).re := by
  have h := m.quadraticValue_eq_inner_representingOperator hdim u
  simpa [quadraticValue, hu] using h

theorem representingOperator_hasProjectionTrace
    [TopologicalSpace.SeparableSpace H]
    (m : ProjectionMeasure ℂ H) (hdim : (3 : Cardinal) ≤ Module.rank ℂ H)
    (P : OrthogonalProjection ℂ H) :
    HasProjectionTrace (m.representingOperator hdim) P (m.μ P) := by
  intro ι b
  letI : CompleteSpace (LinearMap.range P.1) :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      P.2.isIdempotentElem).completeSpace_coe
  letI : TopologicalSpace.SeparableSpace (LinearMap.range P.1) := by infer_instance
  letI : Countable ι := HilbertBasis.index_countable b
  let R : ι → OrthogonalProjection ℂ H := fun i =>
    OrthogonalProjection.rankOne
      ((b i : LinearMap.range P.1) : H)
  have hmeasure : HasSum (fun i => m.μ (R i)) (m.μ P) :=
    m.countably_additive R P
      (OrthogonalProjection.rankOne_basis_pairwise b)
      (OrthogonalProjection.hasSum_rankOne_range P b)
  have hfun :
      (fun i => m.μ (R i)) =
        (fun i =>
          RCLike.re (inner ℂ ((b i : LinearMap.range P.1) : H)
            (m.representingOperator hdim
              ((b i : LinearMap.range P.1) : H)))) := by
    funext i
    simpa only [RCLike.re_eq_complex_re] using
      m.measure_rankOne_eq_inner_representingOperator hdim _
        (b.orthonormal.norm_eq_one i)
  rw [← hfun]
  exact hmeasure

theorem representingOperator_hasDiagonalTrace
    [TopologicalSpace.SeparableSpace H]
    (m : ProjectionMeasure ℂ H) (hdim : (3 : Cardinal) ≤ Module.rank ℂ H) :
    HasDiagonalTrace (m.representingOperator hdim) (m.μ 1) := by
  intro ι b
  letI : Countable ι := HilbertBasis.index_countable b
  let R : ι → OrthogonalProjection ℂ H := fun i =>
    OrthogonalProjection.rankOne (b i)
  have hmeasure : HasSum (fun i => m.μ (R i)) (m.μ 1) :=
    m.countably_additive R 1
      (OrthogonalProjection.rankOne_hilbertBasis_pairwise b)
      (by
        intro x
        simpa using OrthogonalProjection.hasSum_rankOne_hilbertBasis b x)
  have hfun :
      (fun i => m.μ (R i)) =
        (fun i => RCLike.re
          (inner ℂ (b i) (m.representingOperator hdim (b i)))) := by
    funext i
    simpa only [RCLike.re_eq_complex_re] using
      m.measure_rankOne_eq_inner_representingOperator hdim _
        (b.orthonormal.norm_eq_one i)
  rw [← hfun]
  exact hmeasure

theorem representingOperator_represents
    [TopologicalSpace.SeparableSpace H]
    (m : ProjectionMeasure ℂ H) (hdim : (3 : Cardinal) ≤ Module.rank ℂ H) :
    Represents m (m.representingOperator hdim) :=
  ⟨m.representingOperator_isPositive hdim,
    m.representingOperator_hasDiagonalTrace hdim,
    m.representingOperator_hasProjectionTrace hdim⟩

end ProjectionMeasure

end ClassicalGleason.Separable
