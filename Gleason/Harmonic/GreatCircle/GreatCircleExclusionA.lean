import Gleason.Harmonic.GreatCircle.GreatCircleConstraints
import Gleason.Continuity.Auxiliary.ContinuousEndpoint
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Complex InnerProductSpace Real

lemma sin_nat_mul_two_pi' (n : ℕ) : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
  simpa [Nat.cast_mul, mul_assoc, two_mul, mul_left_comm, mul_comm] using
    Real.sin_nat_mul_pi (2 * n)

lemma std_sphereTripleIsometryEquiv_eq_refl :
    sphereTripleIsometryEquiv sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3 =
    LinearIsometryEquiv.refl ℝ sphereAmbient3 := by
  ext v
  calc
    sphereTripleIsometryEquiv sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3 v
      =
        sphereTripleIsometryEquiv sphereE1 sphereE2 sphereE3
          sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
          (∑ i, (sphereStdBasis.repr v) i • sphereStdBasis i) := by
            rw [sphereStdBasis.sum_repr]
    _ =
        ∑ i, (sphereStdBasis.repr v) i •
          sphereTripleIsometryEquiv sphereE1 sphereE2 sphereE3
            sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
            (sphereStdBasis i) := by
          simp
    _ = ∑ i, (sphereStdBasis.repr v) i • sphereStdBasis i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          fin_cases i <;> simp [sphereStdBasis_apply, sphereTripleVec]
    _ = v := by rw [sphereStdBasis.sum_repr]

lemma greatCircleAverageLinear_std
    (f : C(spherePoint3, ℝ)) :
    greatCircleAverageLinear sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3 f =
      northEquatorAverageLinear f := by
  rw [greatCircleAverageLinear_apply]
  congr 1
  ext x
  simp [spherePrecomp_apply, sphereMap, std_sphereTripleIsometryEquiv_eq_refl]

lemma northEquatorAverage_surfaceModeAL2_zero_of_pos {n : ℕ} (hn : 0 < n) :
    northEquatorAverageLinear
      ⟨sphereRestrictionLinear (surfaceModeAL2 n),
        continuous_sphereRestriction_of_harmonicHomogeneousDegree
          ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩⟩ = 0 := by
  rw [northEquatorAverageLinear_apply]
  change
    (2 * Real.pi)⁻¹ *
      ∫ θ in 0..2 * Real.pi,
        surfaceModeAL2 n (WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), 0)) =
      0
  simp_rw [surfaceModeAL2_equator]
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) (a := 0) (b := 2 * Real.pi)
    (c := (n : ℝ)) hn0]
  rw [smul_eq_mul]
  have hI : ∫ x in (n : ℝ) * 0..(n : ℝ) * (2 * Real.pi), Real.cos x = 0 := by
    rw [integral_cos]
    simp [sin_nat_mul_two_pi']
  rw [hI]
  ring

lemma surfaceModeAL2_sphereE2_mod_zero (n : ℕ) (hmod : n % 4 = 0) :
    sphereRestrictionLinear (surfaceModeAL2 n) sphereE2 = 1 := by
  rw [show sphereRestrictionLinear (surfaceModeAL2 n) sphereE2 = ((Complex.I ^ n).re) by
    simp [sphereRestrictionLinear, surfaceModeAL2, sphereE2]]
  rw [Complex.I_pow_eq_pow_mod, hmod]
  norm_num [pow_two]

lemma surfaceModeAL2_sphereE2_mod_one (n : ℕ) (hmod : n % 4 = 1) :
    sphereRestrictionLinear (surfaceModeAL2 n) sphereE2 = 0 := by
  rw [show sphereRestrictionLinear (surfaceModeAL2 n) sphereE2 = ((Complex.I ^ n).re) by
    simp [sphereRestrictionLinear, surfaceModeAL2, sphereE2]]
  rw [Complex.I_pow_eq_pow_mod, hmod]
  norm_num [pow_two, pow_succ]

lemma surfaceModeAL2_sphereE2_mod_three (n : ℕ) (hmod : n % 4 = 3) :
    sphereRestrictionLinear (surfaceModeAL2 n) sphereE2 = 0 := by
  rw [show sphereRestrictionLinear (surfaceModeAL2 n) sphereE2 = ((Complex.I ^ n).re) by
    simp [sphereRestrictionLinear, surfaceModeAL2, sphereE2]]
  rw [Complex.I_pow_eq_pow_mod, hmod]
  norm_num [pow_two, pow_succ]

lemma surfaceModeAL2_not_mem_continuousSphereGreatCircleConstraintSubmodule_of_mod_ne_two
    {n : ℕ} (hn : 0 < n) (hmod : n % 4 ≠ 2) :
    let g : C(spherePoint3, ℝ) :=
      ⟨sphereRestrictionLinear (surfaceModeAL2 n),
        continuous_sphereRestriction_of_harmonicHomogeneousDegree
          ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩⟩
    g ∉ continuousSphereGreatCircleConstraintSubmodule := by
  intro g hg
  have havg : northEquatorAverageLinear g = 0 := by
    simpa [g] using northEquatorAverage_surfaceModeAL2_zero_of_pos hn
  have hg1 : g sphereE1 = 1 := by
    simp [g, sphereRestrictionLinear, surfaceModeAL2, sphereE1]
  have hg3 : g sphereE3 = 0 := by
    change ((0 : ℂ) ^ n).re = 0
    rw [zero_pow (Nat.ne_of_gt hn)]
    simp
  have hg2_ne_neg_one : g sphereE2 ≠ -1 := by
    by_cases h0 : n % 4 = 0
    · have hg2 : g sphereE2 = 1 := by
        simpa [g] using surfaceModeAL2_sphereE2_mod_zero n h0
      linarith
    by_cases h1 : n % 4 = 1
    · have hg2 : g sphereE2 = 0 := by
        simpa [g] using surfaceModeAL2_sphereE2_mod_one n h1
      linarith
    have h3 : n % 4 = 3 := by
      omega
    have hg2 : g sphereE2 = 0 := by
      simpa [g] using surfaceModeAL2_sphereE2_mod_three n h3
    linarith
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
  have hsum_zero : g sphereE1 + g sphereE2 + g sphereE3 = 0 := by
    have h' := congrArg (fun t : ℝ => 3 * t) hcenter_zero
    simp [sphereFrameCenter] at h'
    exact h'
  have hg2 : g sphereE2 = -1 := by
    linarith
  exact hg2_ne_neg_one hg2

theorem not_continuousHarmonicSphereDegreeSubmodule_le_continuousSphereGreatCircleConstraintSubmodule_of_mod_ne_two
    {n : ℕ} (hn : 0 < n) (hmod : n % 4 ≠ 2) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤ continuousSphereGreatCircleConstraintSubmodule := by
  intro hle
  let g : C(spherePoint3, ℝ) :=
    ⟨sphereRestrictionLinear (surfaceModeAL2 n),
      continuous_sphereRestriction_of_harmonicHomogeneousDegree
        ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩⟩
  have hg : g ∈ continuousHarmonicSphereDegreeSubmodule n := by
    show sphereRestrictionLinear (surfaceModeAL2 n) ∈ harmonicSphereDegreeSubmodule n
    exact ⟨surfaceModeAL2 n, ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩, rfl⟩
  exact
    surfaceModeAL2_not_mem_continuousSphereGreatCircleConstraintSubmodule_of_mod_ne_two
      hn hmod (hle hg)
