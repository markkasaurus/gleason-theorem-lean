import Gleason.Separable.ProjectionMeasure

/-!
# Trace on Rank-One Projections

The trace pairing with the projection onto a unit vector is its diagonal
matrix coefficient. This identifies projection trace data with quadratic-form
data and is the basis of uniqueness.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe u v

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem orthonormal_const_unit (u : H) (hu : ‖u‖ = 1) :
    Orthonormal 𝕜 (fun _ : Unit => u) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hij : i = j := Subsingleton.elim i j
  subst j
  simp [inner_self_eq_norm_sq_to_K, hu]

theorem hasProjectionTrace_rankOne_eq_inner
    (T : H →L[𝕜] H) (u : H) (hu : ‖u‖ = 1) (r : ℝ)
    (htrace : HasProjectionTrace T
      (OrthogonalProjection.rankOne (𝕜 := 𝕜) u) r) :
    r = RCLike.re (inner 𝕜 u (T u)) := by
  classical
  let P : OrthogonalProjection 𝕜 H := OrthogonalProjection.rankOne (𝕜 := 𝕜) u
  let v : Unit → H := fun _ => u
  let s : Finset Unit := {default}
  have hv : Orthonormal 𝕜 v := orthonormal_const_unit u hu
  let S : Submodule 𝕜 H := Submodule.span 𝕜 (s.image v : Set H)
  letI : CompleteSpace (LinearMap.range P.1) :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      P.2.isIdempotentElem).completeSpace_coe
  have hS : S = 𝕜 ∙ u := by
    simp [S, s, v]
  have hRange : LinearMap.range P.1 = 𝕜 ∙ u := by
    dsimp [P]
    exact Submodule.range_starProjection (𝕜 ∙ u)
  let L : S ≃ₗᵢ[𝕜] LinearMap.range P.1 :=
    LinearIsometryEquiv.ofEq S (LinearMap.range P.1) (hS.trans hRange.symm)
  let b0 : OrthonormalBasis ↥s 𝕜 S := OrthonormalBasis.span hv s
  let b : HilbertBasis (ULift.{v} ↥s) 𝕜 (LinearMap.range P.1) :=
    ((b0.map L).reindex (Equiv.ulift.symm)).toHilbertBasis
  have hb_apply (i : ULift.{v} ↥s) :
      ((b i : LinearMap.range P.1) : H) = u := by
    simp [b, b0, L, S, s, v]
  have hsum := htrace b
  have hfinite := hasSum_fintype
    (fun i : ULift.{v} ↥s =>
      RCLike.re
        (inner 𝕜 ((b i : LinearMap.range P.1) : H)
          (T ((b i : LinearMap.range P.1) : H))))
  have hr := hsum.unique hfinite
  calc
    r = ∑ i : ULift.{v} ↥s,
        RCLike.re
          (inner 𝕜 ((b i : LinearMap.range P.1) : H)
            (T ((b i : LinearMap.range P.1) : H))) := hr
    _ = RCLike.re (inner 𝕜 u (T u)) := by
      simp [hb_apply, s]

end ClassicalGleason.Separable
