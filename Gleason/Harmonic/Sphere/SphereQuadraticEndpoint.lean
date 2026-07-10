import Gleason.Harmonic.Sphere.SphereSectors
import Gleason.Harmonic.Auxiliary.QuadraticBridge

noncomputable section

open Complex InnerProductSpace

def constantSphereBilin (c : ℝ) :
    LinearMap.BilinMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ :=
  LinearMap.mk₂' ℝ ℝ
    (fun x y : WithLp 2 (ℂ × ℝ) => c * inner (𝕜 := ℝ) x y)
    (by
      intro x1 x2 y
      simp [inner_add_left, mul_add])
    (by
      intro a x y
      ring_nf
      simp [inner_smul_left]
      ring)
    (by
      intro x y1 y2
      simp [inner_add_right, left_distrib])
    (by
      intro a x y
      ring_nf
      simp [inner_smul_right]
      ring)

def constantSphereQuadraticMap (c : ℝ) : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ :=
  LinearMap.BilinMap.toQuadraticMap (constantSphereBilin c)

lemma constantSphereQuadraticMap_apply_unit (c : ℝ) (p : spherePoint3) :
    constantSphereQuadraticMap c p.1 = c := by
  have hnorm_sq : ‖p.1‖ ^ 2 = 1 := by
    nlinarith [p.2]
  have hinner : inner (𝕜 := ℝ) p.1 p.1 = ‖p.1‖ ^ 2 := by
    simpa [inner_self_eq_norm_sq_to_K]
  calc
    constantSphereQuadraticMap c p.1
      = c * inner (𝕜 := ℝ) p.1 p.1 := by
          change (constantSphereBilin c p.1) p.1 = c * inner (𝕜 := ℝ) p.1 p.1
          rfl
    _ = c * ‖p.1‖ ^ 2 := by rw [hinner]
    _ = c := by rw [hnorm_sq, mul_one]

theorem exists_quadraticMap_of_mem_harmonicSphereDegreeSubmodule_zero
    {g : spherePoint3 → ℝ} (hg : g ∈ harmonicSphereDegreeSubmodule 0) :
    ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ, ∀ p : spherePoint3, g p = Q p.1 := by
  rcases hg with ⟨f, hf, rfl⟩
  rcases hf with ⟨_, hfHom⟩
  let c : ℝ := f 0
  refine ⟨constantSphereQuadraticMap c, ?_⟩
  intro p
  have hconst : f p.1 = c := by
    simpa [c] using (hfHom 0 p.1).symm
  calc
    f p.1 = c := hconst
    _ = constantSphereQuadraticMap c p.1 := (constantSphereQuadraticMap_apply_unit c p).symm

theorem exists_quadraticMap_of_mem_harmonicSphereDegreeSubmodule_two
    {g : spherePoint3 → ℝ} (hg : g ∈ harmonicSphereDegreeSubmodule 2) :
    ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ, ∀ p : spherePoint3, g p = Q p.1 := by
  rcases hg with ⟨f, hf, rfl⟩
  rcases exists_quadraticMap_of_harmonicHomogeneousDegree_two hf with ⟨Q, hQ⟩
  exact ⟨Q, fun p => hQ p.1⟩

theorem exists_quadraticMap_of_mem_harmonicSphereDegreeSubmodule_sup_zero_two
    {g : spherePoint3 → ℝ}
    (hg : g ∈ harmonicSphereDegreeSubmodule 0 ⊔ harmonicSphereDegreeSubmodule 2) :
    ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ, ∀ p : spherePoint3, g p = Q p.1 := by
  rcases Submodule.mem_sup.mp hg with ⟨g0, hg0, g2, hg2, rfl⟩
  rcases exists_quadraticMap_of_mem_harmonicSphereDegreeSubmodule_zero hg0 with ⟨Q0, hQ0⟩
  rcases exists_quadraticMap_of_mem_harmonicSphereDegreeSubmodule_two hg2 with ⟨Q2, hQ2⟩
  refine ⟨Q0 + Q2, ?_⟩
  intro p
  simp [hQ0 p, hQ2 p]
