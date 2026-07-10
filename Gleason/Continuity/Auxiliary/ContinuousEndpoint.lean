import Gleason.Harmonic.Auxiliary.GlobalOscillationBridge
import Gleason.Continuity.Auxiliary.FrameEndpoint

noncomputable section

open Complex InnerProductSpace

def continuousHarmonicSphereDegreeSubmodule (n : ℕ) : Submodule ℝ C(spherePoint3, ℝ) :=
  (harmonicSphereDegreeSubmodule n).comap (ContinuousMap.coeFnLinearMap ℝ)

def continuousSphereQuadraticSubmodule : Submodule ℝ C(spherePoint3, ℝ) :=
  sphereQuadraticSubmodule.comap (ContinuousMap.coeFnLinearMap ℝ)

lemma continuous_sphereRestriction_of_harmonicHomogeneousDegree
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ}
    (hf : HarmonicHomogeneousDegree n f) :
    Continuous (sphereRestrictionLinear f) := by
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.2 ?_
    intro p
    exact (hf.1 p).1.continuousAt
  simpa [sphereRestrictionLinear] using hcont.comp continuous_subtype_val

lemma continuous_of_mem_harmonicSphereDegreeSubmodule
    {n : ℕ} {g : spherePoint3 → ℝ}
    (hg : g ∈ harmonicSphereDegreeSubmodule n) :
    Continuous g := by
  rcases hg with ⟨f, hf, rfl⟩
  exact continuous_sphereRestriction_of_harmonicHomogeneousDegree hf

theorem continuousHarmonicSphereDegreeSubmodule_ne_bot (n : ℕ) :
    continuousHarmonicSphereDegreeSubmodule n ≠ ⊥ := by
  let f : WithLp 2 (ℂ × ℝ) → ℝ := surfaceModeAL2 n
  let g : C(spherePoint3, ℝ) :=
    ⟨sphereRestrictionLinear f,
      continuous_sphereRestriction_of_harmonicHomogeneousDegree
        ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩⟩
  have hg : g ∈ continuousHarmonicSphereDegreeSubmodule n := by
    show sphereRestrictionLinear f ∈ harmonicSphereDegreeSubmodule n
    exact ⟨f, ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩, rfl⟩
  intro hbot
  have hg0 : g = 0 := by
    simpa [hbot] using hg
  have hval : g sphereE1 = 0 := by
    simpa using congrArg (fun h : C(spherePoint3, ℝ) => h sphereE1) hg0
  simp [g, f, sphereRestrictionLinear, surfaceModeAL2, sphereE1] at hval

theorem continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereFrameSubmodule :
    continuousHarmonicSphereDegreeSubmodule 0 ≤ continuousSphereFrameSubmodule := by
  intro f hf
  exact harmonicSphereDegreeSubmodule_zero_le_sphereFrameSubmodule hf

theorem continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereFrameSubmodule :
    continuousHarmonicSphereDegreeSubmodule 2 ≤ continuousSphereFrameSubmodule := by
  intro f hf
  exact harmonicSphereDegreeSubmodule_two_le_sphereFrameSubmodule hf

theorem not_continuousHarmonicSphereDegreeSubmodule_one_le_continuousSphereFrameSubmodule :
    ¬ continuousHarmonicSphereDegreeSubmodule 1 ≤ continuousSphereFrameSubmodule := by
  intro hle
  have hle' : harmonicSphereDegreeSubmodule 1 ≤ sphereFrameSubmodule := by
    intro g hg
    let gC : C(spherePoint3, ℝ) := ⟨g, continuous_of_mem_harmonicSphereDegreeSubmodule hg⟩
    have hgC : gC ∈ continuousHarmonicSphereDegreeSubmodule 1 := hg
    exact hle hgC
  exact not_harmonicSphereDegreeSubmodule_one_le_sphereFrameSubmodule hle'

theorem not_continuousHarmonicSphereDegreeSubmodule_gt_two_le_continuousSphereFrameSubmodule
    {n : ℕ} (hn : 2 < n) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤ continuousSphereFrameSubmodule := by
  intro hle
  have hle' : harmonicSphereDegreeSubmodule n ≤ sphereFrameSubmodule := by
    intro g hg
    let gC : C(spherePoint3, ℝ) := ⟨g, continuous_of_mem_harmonicSphereDegreeSubmodule hg⟩
    have hgC : gC ∈ continuousHarmonicSphereDegreeSubmodule n := hg
    exact hle hgC
  exact not_harmonicSphereDegreeSubmodule_gt_two_le_sphereFrameSubmodule hn hle'

theorem continuousSphereFrameSubmodule_eq_sup_zero_two_of_independent_sector_decomposition
    (hQind : iSupIndep continuousHarmonicSphereDegreeSubmodule)
    (hQnontriv : ∀ n, continuousHarmonicSphereDegreeSubmodule n ≠ ⊥)
    {s : Set ℕ}
    (hF : continuousSphereFrameSubmodule = ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i) :
    continuousSphereFrameSubmodule =
      continuousHarmonicSphereDegreeSubmodule 0 ⊔
        continuousHarmonicSphereDegreeSubmodule 2 := by
  refine eq_sup_zero_two_of_independent_sector_decomposition
    (Q := continuousHarmonicSphereDegreeSubmodule) hQind hQnontriv hF
    continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereFrameSubmodule
    continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereFrameSubmodule ?_ ?_
  · exact not_continuousHarmonicSphereDegreeSubmodule_one_le_continuousSphereFrameSubmodule
  · intro n hn
    exact not_continuousHarmonicSphereDegreeSubmodule_gt_two_le_continuousSphereFrameSubmodule hn

theorem continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereQuadraticSubmodule :
    continuousHarmonicSphereDegreeSubmodule 0 ≤ continuousSphereQuadraticSubmodule := by
  intro f hf
  rcases exists_quadraticMap_of_mem_harmonicSphereDegreeSubmodule_zero hf with ⟨Q, hQ⟩
  exact ⟨Q, hQ⟩

theorem continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereQuadraticSubmodule :
    continuousHarmonicSphereDegreeSubmodule 2 ≤ continuousSphereQuadraticSubmodule := by
  intro f hf
  rcases exists_quadraticMap_of_mem_harmonicSphereDegreeSubmodule_two hf with ⟨Q, hQ⟩
  exact ⟨Q, hQ⟩

theorem continuousHarmonicSphereDegreeSup_zero_two_le_continuousSphereQuadraticSubmodule :
    continuousHarmonicSphereDegreeSubmodule 0 ⊔
        continuousHarmonicSphereDegreeSubmodule 2 ≤
      continuousSphereQuadraticSubmodule := by
  rw [sup_le_iff]
  exact
    ⟨continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereQuadraticSubmodule,
      continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereQuadraticSubmodule⟩

theorem eq_sup_zero_two_imp_le_continuousSphereQuadraticSubmodule
    {F : Submodule ℝ C(spherePoint3, ℝ)}
    (hF :
      F =
        continuousHarmonicSphereDegreeSubmodule 0 ⊔
          continuousHarmonicSphereDegreeSubmodule 2) :
    F ≤ continuousSphereQuadraticSubmodule := by
  rw [hF]
  exact continuousHarmonicSphereDegreeSup_zero_two_le_continuousSphereQuadraticSubmodule

theorem continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_sector_decomposition
    (hQind : iSupIndep continuousHarmonicSphereDegreeSubmodule)
    (hQnontriv : ∀ n, continuousHarmonicSphereDegreeSubmodule n ≠ ⊥)
    {s : Set ℕ}
    (hF : continuousSphereFrameSubmodule = ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i) :
    continuousSphereFrameSubmodule ≤ continuousSphereQuadraticSubmodule := by
  apply eq_sup_zero_two_imp_le_continuousSphereQuadraticSubmodule
  exact continuousSphereFrameSubmodule_eq_sup_zero_two_of_independent_sector_decomposition
    hQind hQnontriv hF

theorem coordSphereFrameContinuousMap_mem_continuousSphereQuadraticSubmodule_of_sector_decomposition
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (hQind : iSupIndep continuousHarmonicSphereDegreeSubmodule)
    (hQnontriv : ∀ n, continuousHarmonicSphereDegreeSubmodule n ≠ ⊥)
    {s : Set ℕ}
    (hF : continuousSphereFrameSubmodule = ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i)
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic μ p = 0) :
    coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
      continuousSphereQuadraticSubmodule := by
  apply continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_sector_decomposition
    hQind hQnontriv hF
  exact coordSphereFrameContinuousMap_mem_continuousSphereFrameSubmodule_of_zero_at_p
    (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hp0

theorem continuousSphereFrameSubmodule_eq_sup_zero_two_of_sector_decomposition
    (hQind : iSupIndep continuousHarmonicSphereDegreeSubmodule)
    {s : Set ℕ}
    (hF : continuousSphereFrameSubmodule = ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i) :
    continuousSphereFrameSubmodule =
      continuousHarmonicSphereDegreeSubmodule 0 ⊔
        continuousHarmonicSphereDegreeSubmodule 2 := by
  exact continuousSphereFrameSubmodule_eq_sup_zero_two_of_independent_sector_decomposition
    hQind continuousHarmonicSphereDegreeSubmodule_ne_bot hF

theorem continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_decomposition
    (hQind : iSupIndep continuousHarmonicSphereDegreeSubmodule)
    {s : Set ℕ}
    (hF : continuousSphereFrameSubmodule = ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i) :
    continuousSphereFrameSubmodule ≤ continuousSphereQuadraticSubmodule := by
  exact continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_sector_decomposition
    hQind continuousHarmonicSphereDegreeSubmodule_ne_bot hF

theorem coordSphereFrameContinuousMap_mem_continuousSphereQuadraticSubmodule_of_decomposition
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (hQind : iSupIndep continuousHarmonicSphereDegreeSubmodule)
    {s : Set ℕ}
    (hF : continuousSphereFrameSubmodule = ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i)
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic μ p = 0) :
    coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
      continuousSphereQuadraticSubmodule := by
  exact coordSphereFrameContinuousMap_mem_continuousSphereQuadraticSubmodule_of_sector_decomposition
    hQind continuousHarmonicSphereDegreeSubmodule_ne_bot hF hdim μ hu hv hp huv hup hvp hp0

theorem exists_quadraticMap_of_coordSphereFrameFun_of_sector_decomposition
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (hQind : iSupIndep continuousHarmonicSphereDegreeSubmodule)
    (hQnontriv : ∀ n, continuousHarmonicSphereDegreeSubmodule n ≠ ⊥)
    {s : Set ℕ}
    (hF : continuousSphereFrameSubmodule = ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i)
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic μ p = 0) :
    ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ,
      ∀ x : spherePoint3, coordSphereFrameFun μ u v p x = Q x.1 := by
  have hmem :
      coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
        continuousSphereQuadraticSubmodule :=
    coordSphereFrameContinuousMap_mem_continuousSphereQuadraticSubmodule_of_sector_decomposition
      hQind hQnontriv hF hdim μ hu hv hp huv hup hvp hp0
  exact hmem

theorem exists_quadraticMap_of_coordSphereFrameFun_of_decomposition
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (hQind : iSupIndep continuousHarmonicSphereDegreeSubmodule)
    {s : Set ℕ}
    (hF : continuousSphereFrameSubmodule = ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i)
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic μ p = 0) :
    ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ,
      ∀ x : spherePoint3, coordSphereFrameFun μ u v p x = Q x.1 := by
  exact exists_quadraticMap_of_coordSphereFrameFun_of_sector_decomposition
    hQind continuousHarmonicSphereDegreeSubmodule_ne_bot hF hdim μ hu hv hp huv hup hvp hp0
