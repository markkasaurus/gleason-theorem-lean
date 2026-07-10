import Gleason.Harmonic.Sphere.SphereQuadraticEndpoint

noncomputable section

open Complex InnerProductSpace

def sphereQuadraticSubmodule : Submodule ℝ (spherePoint3 → ℝ) where
  carrier := {g | ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ, ∀ p : spherePoint3, g p = Q p.1}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro p
    simp
  add_mem' := by
    intro g h hg hh
    rcases hg with ⟨Qg, hQg⟩
    rcases hh with ⟨Qh, hQh⟩
    refine ⟨Qg + Qh, ?_⟩
    intro p
    simp [hQg p, hQh p]
  smul_mem' := by
    intro c g hg
    rcases hg with ⟨Q, hQ⟩
    refine ⟨c • Q, ?_⟩
    intro p
    simp [hQ p]

theorem harmonicSphereDegreeSup_zero_two_le_sphereQuadraticSubmodule :
    harmonicSphereDegreeSubmodule 0 ⊔ harmonicSphereDegreeSubmodule 2 ≤ sphereQuadraticSubmodule := by
  intro g hg
  rcases exists_quadraticMap_of_mem_harmonicSphereDegreeSubmodule_sup_zero_two hg with ⟨Q, hQ⟩
  exact ⟨Q, hQ⟩

theorem eq_sup_zero_two_imp_le_sphereQuadraticSubmodule
    {F : Submodule ℝ (spherePoint3 → ℝ)}
    (hF : F = harmonicSphereDegreeSubmodule 0 ⊔ harmonicSphereDegreeSubmodule 2) :
    F ≤ sphereQuadraticSubmodule := by
  rw [hF]
  exact harmonicSphereDegreeSup_zero_two_le_sphereQuadraticSubmodule
