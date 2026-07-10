import Gleason.Finite.Projection
import Mathlib

noncomputable section

namespace RankOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- Rank-one projection onto `ℂ ∙ x` as an element of `Projection H` (the subtype from `F1`). -/
def rankOneProjection (x : H) (_hx : x ≠ 0) : Projection H := by
  classical
  haveI : CompleteSpace (↥(ℂ ∙ x : Submodule ℂ H)) := by infer_instance
  haveI : (ℂ ∙ x : Submodule ℂ H).HasOrthogonalProjection := by infer_instance
  let K : Submodule ℂ H := (ℂ ∙ x)
  refine ⟨K.starProjection, ?_, ?_⟩
  ·
    have hId : IsIdempotentElem K.starProjection := by
      simpa using (Submodule.isIdempotentElem_starProjection (K := K))
    simpa [IsIdempotentElem] using hId
  ·
    intro u v
    have hv : v - K.starProjection v ∈ Kᗮ := by
      simpa using (Submodule.sub_starProjection_mem_orthogonal (K := K) v)
    have hu : K.starProjection u ∈ K := by
      simpa using (Submodule.starProjection_apply_mem (U := K) u)
    have hv0 :
        ∀ w ∈ K, inner (𝕜 := ℂ) w (v - K.starProjection v) = (0 : ℂ) :=
      (Submodule.mem_orthogonal (K := K) (v := v - K.starProjection v)).1 hv
    exact hv0 (K.starProjection u) hu

end RankOne
