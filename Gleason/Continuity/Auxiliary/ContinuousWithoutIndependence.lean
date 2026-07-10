import Gleason.Continuity.Auxiliary.ContinuousEndpoint

noncomputable section

open Complex InnerProductSpace

theorem continuousHarmonicSphereDegreeSubmodule_zero_not_le_two :
    ¬ continuousHarmonicSphereDegreeSubmodule 0 ≤
        continuousHarmonicSphereDegreeSubmodule 2 := by
  intro hle
  have hone_mem :
      (1 : C(spherePoint3, ℝ)) ∈ continuousHarmonicSphereDegreeSubmodule 0 := by
    show ((1 : C(spherePoint3, ℝ)) : spherePoint3 → ℝ) ∈ harmonicSphereDegreeSubmodule 0
    refine ⟨surfaceModeAL2 0, ⟨surfaceModeAL2_harmonicAt 0, surfaceModeAL2_homogeneous 0⟩, ?_⟩
    ext x
    simp [sphereRestrictionLinear, surfaceModeAL2]
  have hone_two :
      (1 : C(spherePoint3, ℝ)) ∈ continuousHarmonicSphereDegreeSubmodule 2 :=
    hle hone_mem
  rcases hone_two with ⟨f, hf, hres⟩
  have hsum :=
    sum_harmonicHomogeneousDegree_two_on_orthogonal_sphere_triple_zero
      hf sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  have h1 : f sphereE1.1 = 1 := by
    simpa [sphereRestrictionLinear] using congrFun hres sphereE1
  have h2 : f sphereE2.1 = 1 := by
    simpa [sphereRestrictionLinear] using congrFun hres sphereE2
  have h3 : f sphereE3.1 = 1 := by
    simpa [sphereRestrictionLinear] using congrFun hres sphereE3
  linarith

theorem continuousHarmonicSphereDegreeSubmodule_two_not_le_zero :
    ¬ continuousHarmonicSphereDegreeSubmodule 2 ≤
        continuousHarmonicSphereDegreeSubmodule 0 := by
  intro hle
  let g : C(spherePoint3, ℝ) :=
    ⟨sphereRestrictionLinear (surfaceModeAL2 2),
      continuous_sphereRestriction_of_harmonicHomogeneousDegree
        ⟨surfaceModeAL2_harmonicAt 2, surfaceModeAL2_homogeneous 2⟩⟩
  have hg_mem : g ∈ continuousHarmonicSphereDegreeSubmodule 2 := by
    show sphereRestrictionLinear (surfaceModeAL2 2) ∈ harmonicSphereDegreeSubmodule 2
    exact ⟨surfaceModeAL2 2, ⟨surfaceModeAL2_harmonicAt 2, surfaceModeAL2_homogeneous 2⟩, rfl⟩
  have hg_zero : g ∈ continuousHarmonicSphereDegreeSubmodule 0 := hle hg_mem
  rcases hg_zero with ⟨f, hf0, hres⟩
  have he1 : f sphereE1.1 = f 0 := by
    simpa using (hf0.2 0 sphereE1.1).symm
  have he2 : f sphereE2.1 = f 0 := by
    simpa using (hf0.2 0 sphereE2.1).symm
  have hf_eq : f sphereE1.1 = f sphereE2.1 := he1.trans he2.symm
  have hg1 : g sphereE1 = 1 := by
    simp [g, sphereRestrictionLinear, surfaceModeAL2, sphereE1]
  have hg2 : g sphereE2 = -1 := by
    simp [g, sphereRestrictionLinear, surfaceModeAL2, sphereE2]
  have hf1 : f sphereE1.1 = g sphereE1 := by
    simpa [g, sphereRestrictionLinear] using congrFun hres sphereE1
  have hf2 : f sphereE2.1 = g sphereE2 := by
    simpa [g, sphereRestrictionLinear] using congrFun hres sphereE2
  rw [hf1, hf2] at hf_eq
  rw [hg1, hg2] at hf_eq
  norm_num at hf_eq

theorem continuousSphereFrameSubmodule_eq_sup_zero_two_of_sector_decomposition_noindep
    {s : Set ℕ}
    (hF : continuousSphereFrameSubmodule = ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i) :
    continuousSphereFrameSubmodule =
      continuousHarmonicSphereDegreeSubmodule 0 ⊔
        continuousHarmonicSphereDegreeSubmodule 2 := by
  have hs_subset : s ⊆ ({0, 2} : Set ℕ) := by
    intro n hn
    have hQn : continuousHarmonicSphereDegreeSubmodule n ≤ continuousSphereFrameSubmodule := by
      rw [hF]
      exact le_iSup (fun i : s => continuousHarmonicSphereDegreeSubmodule i) ⟨n, hn⟩
    cases n with
    | zero =>
        simp
    | succ n =>
        cases n with
        | zero =>
            exact (not_continuousHarmonicSphereDegreeSubmodule_one_le_continuousSphereFrameSubmodule
              hQn).elim
        | succ n' =>
            cases n' with
            | zero =>
                simp
            | succ n'' =>
                have hgt : 2 < Nat.succ (Nat.succ (Nat.succ n'')) := by omega
                exact
                  (not_continuousHarmonicSphereDegreeSubmodule_gt_two_le_continuousSphereFrameSubmodule
                    hgt hQn).elim
  have hs0 : 0 ∈ s := by
    by_contra h0
    have hFle : continuousSphereFrameSubmodule ≤ continuousHarmonicSphereDegreeSubmodule 2 := by
      rw [hF]
      refine iSup_le ?_
      intro i
      have hi02 : (i : ℕ) = 0 ∨ (i : ℕ) = 2 := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hs_subset i.2
      rcases hi02 with hi | hi
      · exact False.elim (h0 (hi ▸ i.2))
      · simpa [hi]
    exact continuousHarmonicSphereDegreeSubmodule_zero_not_le_two <|
      continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereFrameSubmodule.trans hFle
  have hs2 : 2 ∈ s := by
    by_contra h2
    have hFle : continuousSphereFrameSubmodule ≤ continuousHarmonicSphereDegreeSubmodule 0 := by
      rw [hF]
      refine iSup_le ?_
      intro i
      have hi02 : (i : ℕ) = 0 ∨ (i : ℕ) = 2 := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hs_subset i.2
      rcases hi02 with hi | hi
      · simpa [hi]
      · exact False.elim (h2 (hi ▸ i.2))
    exact continuousHarmonicSphereDegreeSubmodule_two_not_le_zero <|
      continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereFrameSubmodule.trans hFle
  have hs_eq : s = ({0, 2} : Set ℕ) := by
    ext n
    constructor
    · intro hn
      exact hs_subset hn
    · intro hn
      rcases hn with rfl | rfl
      · exact hs0
      · exact hs2
  rw [hF, hs_eq]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    rintro ⟨i, hi⟩
    rcases hi with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · rw [sup_le_iff]
    constructor
    · exact le_iSup (fun i : ({0, 2} : Set ℕ) => continuousHarmonicSphereDegreeSubmodule i)
        ⟨0, by simp⟩
    · exact le_iSup (fun i : ({0, 2} : Set ℕ) => continuousHarmonicSphereDegreeSubmodule i)
        ⟨2, by simp⟩

theorem continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_decomposition_noindep
    {s : Set ℕ}
    (hF : continuousSphereFrameSubmodule = ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i) :
    continuousSphereFrameSubmodule ≤ continuousSphereQuadraticSubmodule := by
  apply eq_sup_zero_two_imp_le_continuousSphereQuadraticSubmodule
  exact continuousSphereFrameSubmodule_eq_sup_zero_two_of_sector_decomposition_noindep hF

theorem coordSphereFrameContinuousMap_mem_continuousSphereQuadraticSubmodule_of_decomposition_noindep
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
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
  apply continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_decomposition_noindep
    hF
  exact coordSphereFrameContinuousMap_mem_continuousSphereFrameSubmodule_of_zero_at_p
    (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hp0

theorem exists_quadraticMap_of_coordSphereFrameFun_of_decomposition_noindep
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
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
    coordSphereFrameContinuousMap_mem_continuousSphereQuadraticSubmodule_of_decomposition_noindep
      hF hdim μ hu hv hp huv hup hvp hp0
  exact hmem
