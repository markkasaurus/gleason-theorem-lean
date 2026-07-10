import Gleason.Separable.RealOperator
import Gleason.Separable.BasisDecomposition

/-!
# Trace Representation over the Real Field

Countable additivity along Hilbert bases identifies the diagonal sums of the
real representing operator with the projection measure.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace ProjectionMeasure

theorem measure_rankOne_eq_inner_realRepresentingOperator
    (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H)
    (u : H) (hu : ‖u‖ = 1) :
    m.μ (OrthogonalProjection.rankOne (𝕜 := ℝ) u) =
      inner ℝ (m.realRepresentingOperator hdim u) u := by
  have h := m.quadraticValue_eq_inner_realRepresentingOperator hdim u
  simpa [quadraticValue, hu] using h

theorem realRepresentingOperator_hasProjectionTrace
    [TopologicalSpace.SeparableSpace H]
    (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H)
    (P : OrthogonalProjection ℝ H) :
    HasProjectionTrace (m.realRepresentingOperator hdim) P (m.μ P) := by
  intro ι b
  letI : CompleteSpace (LinearMap.range P.1) :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      P.2.isIdempotentElem).completeSpace_coe
  letI : TopologicalSpace.SeparableSpace (LinearMap.range P.1) := by
    infer_instance
  letI : Countable ι := HilbertBasis.index_countable b
  let R : ι → OrthogonalProjection ℝ H := fun i =>
    OrthogonalProjection.rankOne
      ((b i : LinearMap.range P.1) : H)
  have hmeasure : HasSum (fun i => m.μ (R i)) (m.μ P) :=
    m.countably_additive R P
      (OrthogonalProjection.rankOne_basis_pairwise b)
      (OrthogonalProjection.hasSum_rankOne_range P b)
  have hfun :
      (fun i => m.μ (R i)) =
        (fun i =>
          RCLike.re
            (inner ℝ ((b i : LinearMap.range P.1) : H)
              (m.realRepresentingOperator hdim
                ((b i : LinearMap.range P.1) : H)))) := by
    funext i
    simpa [R, real_inner_comm] using
      m.measure_rankOne_eq_inner_realRepresentingOperator hdim _
        (b.orthonormal.norm_eq_one i)
  rw [← hfun]
  exact hmeasure

theorem realRepresentingOperator_hasDiagonalTrace
    [TopologicalSpace.SeparableSpace H]
    (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H) :
    HasDiagonalTrace (m.realRepresentingOperator hdim) (m.μ 1) := by
  intro ι b
  letI : Countable ι := HilbertBasis.index_countable b
  let R : ι → OrthogonalProjection ℝ H := fun i =>
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
          (inner ℝ (b i) (m.realRepresentingOperator hdim (b i)))) := by
    funext i
    simpa [R, real_inner_comm] using
      m.measure_rankOne_eq_inner_realRepresentingOperator hdim _
        (b.orthonormal.norm_eq_one i)
  rw [← hfun]
  exact hmeasure

theorem realRepresentingOperator_represents
    [TopologicalSpace.SeparableSpace H]
    (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H) :
    Represents m (m.realRepresentingOperator hdim) :=
  ⟨m.realRepresentingOperator_isPositive hdim,
    m.realRepresentingOperator_hasDiagonalTrace hdim,
    m.realRepresentingOperator_hasProjectionTrace hdim⟩

end ProjectionMeasure

end ClassicalGleason.Separable
