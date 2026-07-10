import Gleason.Harmonic.GreatCircle.GreatCircleExclusionA
import Gleason.Harmonic.Sectors.HarmonicBHomogeneous

noncomputable section

open Complex InnerProductSpace Real

lemma northEquatorAverage_surfaceModeBL2_zero_of_gt_two {n : ℕ} (hn : 2 < n) :
    northEquatorAverageLinear
      ⟨sphereRestrictionLinear (surfaceModeBL2 n),
        continuous_sphereRestriction_of_harmonicHomogeneousDegree
          (n := n) ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩⟩ = 0 := by
  rw [northEquatorAverageLinear_apply]
  change
    (2 * Real.pi)⁻¹ *
      ∫ θ in 0..2 * Real.pi,
        surfaceModeBL2 n (WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), 0)) =
      0
  have hn2 : 2 ≤ n := by
    omega
  simp_rw [surfaceModeBL2_equator hn2]
  have hpos : 0 < n - 2 := by
    omega
  have hn0 : ((n - 2 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) (a := 0) (b := 2 * Real.pi)
    (c := ((n - 2 : ℕ) : ℝ)) hn0]
  rw [smul_eq_mul]
  have hI :
      ∫ x in (((n - 2 : ℕ) : ℝ)) * 0..(((n - 2 : ℕ) : ℝ)) * (2 * Real.pi), Real.cos x = 0 := by
    rw [integral_cos]
    simp [sin_nat_mul_two_pi']
  rw [hI]
  ring

lemma surfaceModeBL2_sphereE2_mod_two_gt_two {n : ℕ} (hn : 2 < n) (hmod : n % 4 = 2) :
    sphereRestrictionLinear (surfaceModeBL2 n) sphereE2 = 1 := by
  have hn2 : 2 ≤ n := by
    omega
  rw [show sphereRestrictionLinear (surfaceModeBL2 n) sphereE2 =
      Real.cos ((((n - 2 : ℕ) : ℝ) * (Real.pi / 2))) by
    simpa [sphereRestrictionLinear, sphereE2] using surfaceModeBL2_equator hn2 (Real.pi / 2)]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 4 * k + 2 := by
    refine ⟨n / 4, ?_⟩
    omega
  have hk' : n - 2 = 4 * k := by
    omega
  rw [hk']
  have hang : (((4 * k : ℕ) : ℝ) * (Real.pi / 2)) = (k : ℝ) * (2 * Real.pi) := by
    norm_num [Nat.cast_mul]
    ring
  rw [hang, Real.cos_nat_mul_two_pi]

lemma surfaceModeBL2_not_mem_continuousSphereGreatCircleConstraintSubmodule_of_mod_eq_two
    {n : ℕ} (hn : 2 < n) (hmod : n % 4 = 2) :
    let g : C(spherePoint3, ℝ) :=
      ⟨sphereRestrictionLinear (surfaceModeBL2 n),
        continuous_sphereRestriction_of_harmonicHomogeneousDegree
          ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩⟩
    g ∉ continuousSphereGreatCircleConstraintSubmodule := by
  intro g hg
  have havg : northEquatorAverageLinear g = 0 := by
    simpa [g] using northEquatorAverage_surfaceModeBL2_zero_of_gt_two hn
  have hg1 : g sphereE1 = 1 := by
    simp [g, sphereRestrictionLinear, surfaceModeBL2, sphereE1]
  have hg2 : g sphereE2 = 1 := by
    simpa [g] using surfaceModeBL2_sphereE2_mod_two_gt_two hn hmod
  have hg3 : g sphereE3 = 0 := by
    have hpos : 0 < n - 2 := by
      omega
    simp [g, sphereRestrictionLinear, surfaceModeBL2, sphereE3, zero_pow (Nat.ne_of_gt hpos)]
  have hstd :=
    (mem_continuousSphereGreatCircleConstraintSubmodule_iff g).1 hg
      sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  rw [greatCircleAverageLinear_std] at hstd
  have havg_centered :
      northEquatorAverageLinear (sphereFrameCentered g) = -sphereFrameCenter g := by
    calc
      northEquatorAverageLinear (sphereFrameCentered g)
        =
          northEquatorAverageLinear g -
            northEquatorAverageLinear (ContinuousMap.const _ (sphereFrameCenter g)) := by
              simp [sphereFrameCentered, map_sub]
      _ = 0 - sphereFrameCenter g := by
            rw [havg, northEquatorAverageLinear_const]
      _ = -sphereFrameCenter g := by
            ring
  have hval_centered : (sphereFrameCentered g) sphereE3 = -sphereFrameCenter g := by
    simp [sphereFrameCentered, hg3]
  rw [havg_centered, hval_centered] at hstd
  have hcenter_zero : sphereFrameCenter g = 0 := by
    linarith
  have hcenter_two_thirds : sphereFrameCenter g = 2 / 3 := by
    simp [sphereFrameCenter, hg1, hg2, hg3]
    norm_num
  linarith

theorem not_continuousHarmonicSphereDegreeSubmodule_le_continuousSphereGreatCircleConstraintSubmodule_of_mod_eq_two
    {n : ℕ} (hn : 2 < n) (hmod : n % 4 = 2) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤ continuousSphereGreatCircleConstraintSubmodule := by
  intro hle
  let g : C(spherePoint3, ℝ) :=
    ⟨sphereRestrictionLinear (surfaceModeBL2 n),
      continuous_sphereRestriction_of_harmonicHomogeneousDegree
        ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩⟩
  have hg : g ∈ continuousHarmonicSphereDegreeSubmodule n := by
    show sphereRestrictionLinear (surfaceModeBL2 n) ∈ harmonicSphereDegreeSubmodule n
    exact ⟨surfaceModeBL2 n,
      ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩, rfl⟩
  exact
    surfaceModeBL2_not_mem_continuousSphereGreatCircleConstraintSubmodule_of_mod_eq_two
      hn hmod (hle hg)
