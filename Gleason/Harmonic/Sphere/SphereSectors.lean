import Gleason.Harmonic.Auxiliary.SectorGlue

noncomputable section

open Complex InnerProductSpace

abbrev spherePoint3 := {p : WithLp 2 (ℂ × ℝ) // ‖p‖ = 1}

def sphereRestrictionLinear :
    (WithLp 2 (ℂ × ℝ) → ℝ) →ₗ[ℝ] (spherePoint3 → ℝ) where
  toFun f := fun p => f p.1
  map_add' := by
    intro f g
    funext p
    rfl
  map_smul' := by
    intro c f
    funext p
    rfl

def harmonicSphereDegreeSubmodule (n : ℕ) : Submodule ℝ (spherePoint3 → ℝ) :=
  (harmonicHomogeneousDegreeSubmodule n).map sphereRestrictionLinear

def equatorSpherePoint (θ : ℝ) : spherePoint3 :=
  ⟨WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), (0 : ℝ)), by
    have hsq :
        ‖WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), (0 : ℝ))‖ ^ 2 = 1 := by
      rw [WithLp.norm_toLp_fst]
      rw [Complex.sq_norm]
      have hnormSq :
          Complex.normSq ((Real.cos θ : ℂ) + Complex.I * Real.sin θ) =
            Real.cos θ ^ 2 + Real.sin θ ^ 2 := by
        simpa [mul_comm] using Complex.normSq_add_mul_I (Real.cos θ) (Real.sin θ)
      rw [hnormSq]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    nlinarith [norm_nonneg (WithLp.toLp 2
      (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), (0 : ℝ)))]
  ⟩

def equatorRestrictionFromSphereLinear :
    (spherePoint3 → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun f := fun θ => f (equatorSpherePoint θ)
  map_add' := by
    intro f g
    funext θ
    rfl
  map_smul' := by
    intro c f
    funext θ
    rfl

lemma equatorRestrictionFromSphere_sphereRestriction
    (f : WithLp 2 (ℂ × ℝ) → ℝ) :
    equatorRestrictionFromSphereLinear (sphereRestrictionLinear f) = equatorRestrictionL2 f := by
  funext θ
  rfl

theorem not_harmonicSphereDegreeSubmodule_le_frameAdmissible {n : ℕ} (hn : 2 < n) :
    ¬ harmonicSphereDegreeSubmodule n ≤
        (frameAdmissibleCircleSubmodule.comap equatorRestrictionFromSphereLinear) := by
  intro hle
  have hambient :
      harmonicHomogeneousDegreeSubmodule n ≤
        frameAdmissibleCircleSubmodule.comap equatorRestrictionLinear := by
    intro f hf
    have hsphere : sphereRestrictionLinear f ∈ harmonicSphereDegreeSubmodule n := by
      exact ⟨f, hf, rfl⟩
    have hframe :
        sphereRestrictionLinear f ∈
          frameAdmissibleCircleSubmodule.comap equatorRestrictionFromSphereLinear :=
      hle hsphere
    simpa [equatorRestrictionFromSphere_sphereRestriction] using hframe
  exact not_harmonicHomogeneousDegreeSubmodule_le_frameAdmissible hn hambient

theorem harmonicSphereDegreeSubmodule_ne_bot {n : ℕ} (hn : 2 < n) :
    harmonicSphereDegreeSubmodule n ≠ ⊥ := by
  rcases exists_explicit_harmonic_surface_mode_not_circleFrame hn with
    ⟨f, hfHarm, hfHom, hnot⟩
  let hf : WithLp 2 (ℂ × ℝ) → ℝ := f
  have hmem : hf ∈ harmonicHomogeneousDegreeSubmodule n := ⟨hfHarm, hfHom⟩
  intro hbot
  have hresZero : sphereRestrictionLinear hf = 0 := by
    have hbotMem :
        sphereRestrictionLinear hf ∈ (⊥ : Submodule ℝ (spherePoint3 → ℝ)) := by
      rw [← hbot]
      exact ⟨hf, hmem, rfl⟩
    simpa using hbotMem
  have heqZero : equatorRestrictionL2 hf = 0 := by
    funext θ
    have hθ := congrFun hresZero (equatorSpherePoint θ)
    simpa [equatorRestrictionFromSphere_sphereRestriction] using hθ
  have hframe : circleFrameFunction (equatorRestrictionL2 hf) := by
    simpa [heqZero] using circleFrameFunction_const (0 : ℝ)
  exact hnot hframe
