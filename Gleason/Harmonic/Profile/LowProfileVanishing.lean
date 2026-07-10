import Gleason.Harmonic.Profile.LowProfileDerivatives

noncomputable section

open Complex InnerProductSpace

set_option maxHeartbeats 800000

private lemma cast_two_add_two_mul (k : ℕ) :
    (((2 + k * 2 : ℕ)) : ℝ) = 2 + 2 * (k : ℝ) := by
  exact_mod_cast (by ring : 2 + k * 2 = 2 + 2 * k)

private lemma cast_two_add_two_mul_sub_one (k : ℕ) :
    (((2 + k * 2 - 1 : ℕ)) : ℝ) = 1 + 2 * (k : ℝ) := by
  exact_mod_cast (by omega : 2 + k * 2 - 1 = 1 + 2 * k)

theorem eq_zero_of_even_degree_gt_two_of_sphere_low_profile
    {k : ℕ} (hk : 1 ≤ k)
    {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree (2 * (k + 1)) f)
    (hfg : sphereRestrictionLinear f = g)
    {a b : ℝ}
    (hrep : ∀ x : spherePoint3, g x = a + b * sphereCoordZ x ^ 2) :
    g = 0 := by
  have hsum1 := harmonicAt_second_directional_sum_zero (p := complexOneVec) (hf.1 complexOneVec)
  have hpath11 :
      iteratedDeriv 2 (fun s : ℝ => f (complexOneVec + s • complexOneVec)) 0 =
        a * ((2 * (k + 1) : ℕ) : ℝ) * ((2 * (k + 1) - 1 : ℕ) : ℝ) := by
    have hfun :
        (fun s : ℝ => f (complexOneVec + s • complexOneVec)) =
          fun s : ℝ => a * (1 + s) ^ (2 * (k + 1)) := by
      funext s
      exact even_degree_eval_complexOne_add_smul_complexOneVec hf hfg hrep s
    rw [hfun, iteratedDeriv_two_axis_even_degree]
  have hpath12 :
      iteratedDeriv 2 (fun s : ℝ => f (complexOneVec + s • complexIVec)) 0 =
        2 * a * (k + 1) := by
    have hfun :
        (fun s : ℝ => f (complexOneVec + s • complexIVec)) =
          fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1) := by
      funext s
      exact even_degree_eval_complexOne_add_smul_complexIVec hf hfg hrep s
    rw [hfun, iteratedDeriv_two_normsq_even_degree]
  have hpath13 :
      iteratedDeriv 2 (fun s : ℝ => f (complexOneVec + s • realUnitVec)) 0 =
        2 * a * (k + 1) + 2 * b := by
    have hfun :
        (fun s : ℝ => f (complexOneVec + s • realUnitVec)) =
          fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1) + b * s ^ 2 * (1 + s ^ 2) ^ k := by
      funext s
      exact even_degree_eval_complexOne_add_smul_realUnitVec hf hfg hrep s
    rw [hfun, iteratedDeriv_two_equator_low_profile]
  rw [hpath11, hpath12, hpath13] at hsum1
  have hEq1 := hsum1
  ring_nf at hEq1

  have hsum2 := harmonicAt_second_directional_sum_zero (p := realUnitVec) (hf.1 realUnitVec)
  have hpath21 :
      iteratedDeriv 2 (fun s : ℝ => f (realUnitVec + s • complexOneVec)) 0 =
        2 * a * (k + 1) + 2 * b * k := by
    have hfun :
        (fun s : ℝ => f (realUnitVec + s • complexOneVec)) =
          fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1) + b * (1 + s ^ 2) ^ k := by
      funext s
      exact even_degree_eval_realUnit_add_smul_complexOneVec hf hfg hrep s
    rw [hfun, iteratedDeriv_two_pole_low_profile]
  have hpath22 :
      iteratedDeriv 2 (fun s : ℝ => f (realUnitVec + s • complexIVec)) 0 =
        2 * a * (k + 1) + 2 * b * k := by
    have hfun :
        (fun s : ℝ => f (realUnitVec + s • complexIVec)) =
          fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1) + b * (1 + s ^ 2) ^ k := by
      funext s
      exact even_degree_eval_realUnit_add_smul_complexIVec hf hfg hrep s
    rw [hfun, iteratedDeriv_two_pole_low_profile]
  have hpath23 :
      iteratedDeriv 2 (fun s : ℝ => f (realUnitVec + s • realUnitVec)) 0 =
        (a + b) * ((2 * (k + 1) : ℕ) : ℝ) * ((2 * (k + 1) - 1 : ℕ) : ℝ) := by
    have hfun :
        (fun s : ℝ => f (realUnitVec + s • realUnitVec)) =
          fun s : ℝ => (a + b) * (1 + s) ^ (2 * (k + 1)) := by
      funext s
      exact even_degree_eval_realUnit_add_smul_realUnitVec hf hfg hrep s
    rw [hfun, iteratedDeriv_two_axis_even_degree]
  rw [hpath21, hpath22, hpath23] at hsum2
  have hEq2 := hsum2
  ring_nf at hEq2

  have hEq1' : a * (4 * (k : ℝ) ^ 2 + 10 * k + 6) + 2 * b = 0 := by
    rw [cast_two_add_two_mul, cast_two_add_two_mul_sub_one] at hEq1
    nlinarith [hEq1]
  have hEq2' : a * (4 * (k : ℝ) ^ 2 + 10 * k + 6) + b * (4 * (k : ℝ) ^ 2 + 10 * k + 2) = 0 := by
    rw [cast_two_add_two_mul, cast_two_add_two_mul_sub_one] at hEq2
    nlinarith [hEq2]
  have hbk : b * (4 * (k : ℝ) ^ 2 + 10 * k) = 0 := by
    linarith [hEq1', hEq2']
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 < (k : ℝ) := by linarith
  have hcoeffb : 4 * (k : ℝ) ^ 2 + 10 * k ≠ 0 := by
    have hpos : 0 < 4 * (k : ℝ) ^ 2 + 10 * k := by
      have hkSq : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg (k : ℝ)
      nlinarith
    exact ne_of_gt hpos
  have hb : b = 0 := (mul_eq_zero.mp hbk).resolve_right hcoeffb

  have hEq1'' := hEq1'
  rw [hb] at hEq1''
  ring_nf at hEq1''
  have hak : a * (4 * (k : ℝ) ^ 2 + 10 * k + 6) = 0 := by
    linarith [hEq1'']
  have hcoeffa : 4 * (k : ℝ) ^ 2 + 10 * k + 6 ≠ 0 := by
    have hpos : 0 < 4 * (k : ℝ) ^ 2 + 10 * k + 6 := by
      have hkSq : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg (k : ℝ)
      nlinarith
    exact ne_of_gt hpos
  have ha : a = 0 := (mul_eq_zero.mp hak).resolve_right hcoeffa

  ext x
  rw [hrep x, ha, hb]
  simp

theorem eq_zero_of_mem_continuousHarmonicSphereDegreeSubmodule_gt_two_of_northZonal_mem_sup_zero_two
    {n : ℕ} (hn : 2 < n) {g : C(spherePoint3, ℝ)}
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hgz : IsNorthZonal g)
    (hgsup :
      g ∈ continuousHarmonicSphereDegreeSubmodule 0 ⊔
        continuousHarmonicSphereDegreeSubmodule 2) :
    g = 0 := by
  by_cases hnEven : Even n
  · rcases hnEven with ⟨m, hm⟩
    have hm' : n = 2 * m := by simpa [two_mul] using hm
    rw [hm'] at hn hg
    have hm2 : 2 ≤ m := by omega
    rcases hg with ⟨f, hf, hfg⟩
    have hgquad :
        g ∈ continuousSphereQuadraticSubmodule :=
      continuousHarmonicSphereDegreeSup_zero_two_le_continuousSphereQuadraticSubmodule hgsup
    rcases exists_const_add_sq_of_isNorthZonal_mem_quadratic_pointConstraint hgquad hgpc hgz
      with ⟨a, b, hrep⟩
    have hk : 1 ≤ m - 1 := by omega
    have hm1 : 1 ≤ m := by omega
    simpa [Nat.sub_add_cancel hm1] using
      eq_zero_of_even_degree_gt_two_of_sphere_low_profile (k := m - 1) hk
        (by simpa [Nat.sub_add_cancel hm1] using hf) hfg hrep
  · exact
      eq_zero_of_odd_of_mem_continuousHarmonicSphereDegreeSubmodule_of_northZonal_pointConstraint
        (Nat.not_even_iff_odd.mp hnEven) hg hgpc hgz
