import Gleason.Harmonic.GreatCircle.GreatCirclePointStandard

noncomputable section

open Complex InnerProductSpace

def stdGreatCirclePointConstraintSubmodule : Submodule ℝ C(spherePoint3, ℝ) :=
  LinearMap.ker stdGreatCirclePointConstraintLinear

@[simp] theorem mem_stdGreatCirclePointConstraintSubmodule_iff
    (f : C(spherePoint3, ℝ)) :
    f ∈ stdGreatCirclePointConstraintSubmodule ↔
      stdGreatCirclePointConstraintLinear f = 0 := by
  rfl

theorem continuousSphereGreatCirclePointConstraintSubmodule_le_stdGreatCirclePointConstraintSubmodule :
    continuousSphereGreatCirclePointConstraintSubmodule ≤ stdGreatCirclePointConstraintSubmodule := by
  intro f hf
  rw [mem_stdGreatCirclePointConstraintSubmodule_iff]
  change
    greatCirclePointConstraintLinear sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3 f = 0
  exact hf sphereE1 sphereE2 sphereE3
    sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3

theorem le_continuousSphereGreatCirclePointConstraintSubmodule_of_invariant_and_le_std
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGinv :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGstd : G ≤ stdGreatCirclePointConstraintSubmodule) :
    G ≤ continuousSphereGreatCirclePointConstraintSubmodule := by
  intro f hf
  apply mem_continuousSphereGreatCirclePointConstraintSubmodule_of_forall_spherePrecomp
  intro e
  have hmem_map : spherePrecomp e f ∈ G.map (spherePrecompLinearEquiv e).toLinearMap := by
    exact ⟨f, hf, rfl⟩
  have hmemG : spherePrecomp e f ∈ G := by
    simpa [hGinv e] using hmem_map
  exact hGstd hmemG
