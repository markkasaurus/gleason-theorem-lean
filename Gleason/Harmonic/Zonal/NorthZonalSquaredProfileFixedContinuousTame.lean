import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileDynamics
import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientFixedContinuous

noncomputable section
set_option maxHeartbeats 800000

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

def oneUnitIcc : unitIcc := ⟨1, by constructor <;> norm_num⟩

lemma sqProfileLinearPart_apply_one (p : ℝ[X]) :
    sqProfileLinearPart p oneUnitIcc = p.coeff 1 := by
  simp [sqProfileLinearPart, oneUnitIcc]

lemma dist_sqProfileLinearPart_eq_abs_sub
    (a b : ℝ) :
    dist ((C a * X).toContinuousMapOn unitIcc)
        ((C b * X).toContinuousMapOn unitIcc) = |a - b| := by
  let f : C(unitIcc, ℝ) := (C (a - b) * X).toContinuousMapOn unitIcc
  have hsub :
      ((C a * X).toContinuousMapOn unitIcc) -
          ((C b * X).toContinuousMapOn unitIcc) = f := by
    ext u
    simp [f]
    ring
  have hle :
      dist ((C a * X).toContinuousMapOn unitIcc)
          ((C b * X).toContinuousMapOn unitIcc) ≤ |a - b| := by
    rw [dist_eq_norm, hsub]
    haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
    refine (ContinuousMap.norm_le_of_nonempty
      (f := f)
      (M := |a - b|)).2 ?_
    intro u
    rw [Real.norm_eq_abs]
    calc
      |((C (a - b) * X : ℝ[X]).eval u.1)| = |(a - b) * u.1| := by simp
      _ = |a - b| * |u.1| := by rw [abs_mul]
      _ ≤ |a - b| * 1 := by
            gcongr
            simpa [abs_of_nonneg u.2.1] using u.2.2
      _ = |a - b| := by ring
  have hge :
      |a - b| ≤
        dist ((C a * X).toContinuousMapOn unitIcc)
          ((C b * X).toContinuousMapOn unitIcc) := by
    have hpt : ‖f oneUnitIcc‖ ≤ ‖f‖ := f.norm_coe_le_norm oneUnitIcc
    rw [dist_eq_norm, hsub]
    calc
      |a - b| = ‖f oneUnitIcc‖ := by
        simp [f, oneUnitIcc, Real.norm_eq_abs]
      _ ≤ ‖f‖ := hpt
  exact le_antisymm hle hge

lemma sum_geom_nonneg (m : ℕ) :
    0 ≤ Finset.sum (Finset.range m) (fun j => (2 : ℝ) ^ j) := by
  positivity

lemma sqProfile_tame_small_div_le_eighth (d S : ℝ)
    (hd : 0 < d) (hS : 0 ≤ S) :
    3 * S * (d / (8 * (3 * S + 1))) ≤ d / 8 := by
  have hden : 0 < 8 * (3 * S + 1) := by
    nlinarith
  have hdiv :
      (3 * S : ℝ) / (3 * S + 1) ≤ 1 := by
    have hpos : 0 < 3 * S + 1 := by nlinarith
    exact (div_le_one hpos).2 (by linarith)
  have hfac :
      3 * S * (d / (8 * (3 * S + 1))) = (d / 8) * ((3 * S) / (3 * S + 1)) := by
    field_simp [show (3 * S + 1 : ℝ) ≠ 0 by linarith]
  rw [hfac]
  have hd8 : 0 ≤ d / 8 := by linarith
  nlinarith

lemma zeroUnitIcc_mem_closure_positiveUnitIcc :
    zeroUnitIcc ∈ closure ({u : unitIcc | 0 < u.1} : Set unitIcc) := by
  rw [mem_closure_iff_nhds]
  intro t ht
  rcases Metric.mem_nhds_iff.mp ht with ⟨ε, hε, hball⟩
  let u : unitIcc := ⟨min (ε / 2) 1, by
    constructor
    · positivity
    · exact min_le_right _ _⟩
  refine ⟨u, hball ?_, ?_⟩
  · change dist u zeroUnitIcc < ε
    change |u.1 - (0 : ℝ)| < ε
    have hu_nonneg : 0 ≤ u.1 := u.2.1
    rw [sub_zero]
    rw [abs_of_nonneg hu_nonneg]
    have hlt : u.1 ≤ ε / 2 := by
      simpa [u] using (min_le_left (ε / 2) (1 : ℝ))
    have hhalf : ε / 2 < ε := by
      nlinarith
    exact lt_of_le_of_lt hlt hhalf
  · have hmin_pos : 0 < min (ε / 2) 1 := by
      refine lt_min ?_ zero_lt_one
      positivity
    change 0 < u.1
    simpa [u] using hmin_pos

lemma sqMulContinuousMap_injective :
    Function.Injective sqMulContinuousMap := by
  intro q₁ q₂ hq
  have hEqPos : Set.EqOn q₁ q₂ ({u : unitIcc | 0 < u.1} : Set unitIcc) := by
    intro u hu
    have hval := congrArg (fun f : C(unitIcc, ℝ) => f u) hq
    change u.1 * q₁ u = u.1 * q₂ u at hval
    have hu' : 0 < u.1 := hu
    exact mul_left_cancel₀ (show u.1 ≠ 0 by linarith) hval
  ext u
  by_cases hu0 : u.1 = 0
  · have huz : u = zeroUnitIcc := by
      apply Subtype.ext
      simp [zeroUnitIcc, hu0]
    subst huz
    exact Set.EqOn.closure hEqPos q₁.continuous q₂.continuous
      zeroUnitIcc_mem_closure_positiveUnitIcc
  · exact hEqPos (lt_of_le_of_ne u.2.1 (Ne.symm hu0))

theorem northZonalSqProfileAverage_eq_linear_of_fixed_of_sqquotient_factor
    (r : C(unitIcc, ℝ))
    (hfix : northZonalSqProfileAverage r = r)
    (q : C(unitIcc, ℝ))
    (hq : r = sqMulContinuousMap q) :
    r = (C (q zeroUnitIcc) * X).toContinuousMapOn unitIcc := by
  let c : ℝ := q zeroUnitIcc
  have hfixq : northZonalSqQuotientAverage q = q := by
    apply sqMulContinuousMap_injective
    calc
      sqMulContinuousMap (northZonalSqQuotientAverage q)
          = northZonalSqProfileAverage (sqMulContinuousMap q) := by
              symm
              exact northZonalSqProfileAverage_sqMulContinuousMap q
      _ = northZonalSqProfileAverage r := by rw [hq]
      _ = r := hfix
      _ = sqMulContinuousMap q := hq
  have hconst :
      q = ContinuousMap.const _ c :=
    northZonalSqQuotientAverage_eq_const_of_fixed q hfixq
  have hlin : r = (C c * X).toContinuousMapOn unitIcc := by
    rw [hq, hconst]
    ext u
    simp [sqMulContinuousMap_apply]
    ring
  simpa [c] using hlin

theorem northZonalSqProfileAverage_eq_linear_of_fixed_of_eval_zero_of_tameApprox
    (r : C(unitIcc, ℝ))
    (hfix : northZonalSqProfileAverage r = r)
    (hzero : r zeroUnitIcc = 0)
    (htame :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfilePolynomialMap p) r <
            η / (8 * (((Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * 3) + 1)) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8) :
    r = (C (r oneUnitIcc) * X).toContinuousMapOn unitIcc := by
  let c : C(unitIcc, ℝ) := (C (r oneUnitIcc) * X).toContinuousMapOn unitIcc
  by_contra hne
  have hdpos : 0 < dist r c := by
    exact dist_pos.mpr hne
  rcases htame (η := dist r c) hdpos with ⟨p, m, hp0, hpr, htail⟩
  let S : ℝ := Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j
  have hSnonneg : 0 ≤ S := sum_geom_nonneg m
  have hpr' : dist (sqProfilePolynomialMap p) r < dist r c / 8 := by
    have hbound :
        dist r c / (8 * (3 * S + 1)) ≤ dist r c / 8 := by
      calc
        dist r c / (8 * (3 * S + 1))
            = (dist r c / 8) / (3 * S + 1) := by
                field_simp [show (3 * S + 1 : ℝ) ≠ 0 by linarith]
        _ ≤ dist r c / 8 := by
              refine div_le_self ?_ ?_
              · linarith
              · nlinarith
    have hprS : dist (sqProfilePolynomialMap p) r < dist r c / (8 * (3 * S + 1)) := by
      simpa [S, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, left_distrib, right_distrib]
        using hpr
    exact lt_of_lt_of_le hprS hbound
  have hdefect :
      sqProfilePolynomialDefect p ≤
        3 * (dist (sqProfilePolynomialMap p) r) := by
    calc
      sqProfilePolynomialDefect p
        = dist (northZonalSqProfileAverage (sqProfilePolynomialMap p))
            (sqProfilePolynomialMap p) := by
              rfl
      _ ≤ dist (northZonalSqProfileAverage (sqProfilePolynomialMap p))
            (northZonalSqProfileAverage r) +
          dist r (sqProfilePolynomialMap p) := by
            simpa [hfix] using
              dist_triangle
                (northZonalSqProfileAverage (sqProfilePolynomialMap p))
                (northZonalSqProfileAverage r)
                (sqProfilePolynomialMap p)
      _ ≤ 2 * dist (sqProfilePolynomialMap p) r +
          dist r (sqProfilePolynomialMap p) := by
            gcongr
            exact dist_northZonalSqProfileAverage_le _ _
      _ = 3 * dist (sqProfilePolynomialMap p) r := by
            rw [dist_comm]
            ring
  have hnearLinear :
      dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) < dist r c / 4 := by
    have hnorm :
        ‖sqProfilePolynomialMap p - sqProfileLinearPart p‖
          ≤
            S *
                sqProfilePolynomialDefect p +
              (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p :=
      norm_polynomial_sub_linear_le_of_sqprofile_almost_fixed p m hp0
    have hsumlt :
        S * sqProfilePolynomialDefect p +
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < dist r c / 4 := by
      have hprS : dist (sqProfilePolynomialMap p) r < dist r c / (8 * (3 * S + 1)) := by
        simpa [S, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm, left_distrib, right_distrib]
          using hpr
      have hdefect' :
          sqProfilePolynomialDefect p < 3 * (dist r c / (8 * (3 * S + 1))) := by
        nlinarith [hdefect, hprS]
      have hSbound :
          S * sqProfilePolynomialDefect p < dist r c / 8 := by
        by_cases hSzero : S = 0
        · simp [hSzero, hdpos]
        · have hSpos : 0 < S := lt_of_le_of_ne hSnonneg (Ne.symm hSzero)
          have haux :
              S * sqProfilePolynomialDefect p <
                S * (3 * (dist r c / (8 * (3 * S + 1)))) := by
            exact mul_lt_mul_of_pos_left hdefect' hSpos
          have hfrac :
              S * (3 * (dist r c / (8 * (3 * S + 1)))) ≤ dist r c / 8 := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              sqProfile_tame_small_div_le_eighth (dist r c) S hdpos hSnonneg
          exact lt_of_lt_of_le haux hfrac
      have htail' : (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < dist r c / 8 := htail
      nlinarith
    have : dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) < dist r c / 4 := by
      exact lt_of_le_of_lt (by simpa [dist_eq_norm] using hnorm) hsumlt
    exact this
  have hlineClose :
      dist (sqProfileLinearPart p) c < 3 * dist r c / 8 := by
    have hAtOne :
        dist (sqProfileLinearPart p) c =
          |(sqProfileLinearPart p) oneUnitIcc - c oneUnitIcc| := by
      change
        dist ((C (p.coeff 1) * X).toContinuousMapOn unitIcc)
          ((C (r oneUnitIcc) * X).toContinuousMapOn unitIcc) =
            |(sqProfileLinearPart p) oneUnitIcc - c oneUnitIcc|
      rw [dist_sqProfileLinearPart_eq_abs_sub]
      have hline :
          (sqProfileLinearPart p) oneUnitIcc = p.coeff 1 := by
        simp [sqProfileLinearPart, oneUnitIcc]
      have hc : c oneUnitIcc = r oneUnitIcc := by
        simp [c, oneUnitIcc]
      rw [hline, hc]
    have h1 :
        |(sqProfileLinearPart p) oneUnitIcc - (sqProfilePolynomialMap p) oneUnitIcc|
          ≤ dist (sqProfileLinearPart p) (sqProfilePolynomialMap p) := by
      simpa [dist_eq_norm, ContinuousMap.sub_apply, Real.norm_eq_abs, abs_sub_comm] using
        ((sqProfileLinearPart p - sqProfilePolynomialMap p).norm_coe_le_norm oneUnitIcc)
    have h2 :
        |(sqProfilePolynomialMap p) oneUnitIcc - r oneUnitIcc|
          ≤ dist (sqProfilePolynomialMap p) r := by
      simpa [dist_eq_norm, ContinuousMap.sub_apply, Real.norm_eq_abs, abs_sub_comm] using
        ((sqProfilePolynomialMap p - r).norm_coe_le_norm oneUnitIcc)
    have hsum :
        |(sqProfileLinearPart p) oneUnitIcc - c oneUnitIcc|
          ≤ |(sqProfileLinearPart p) oneUnitIcc - (sqProfilePolynomialMap p) oneUnitIcc| +
              |(sqProfilePolynomialMap p) oneUnitIcc - r oneUnitIcc| := by
      have hc : c oneUnitIcc = r oneUnitIcc := by
        simp [c, oneUnitIcc]
      rw [hc]
      exact abs_sub_le _ _ _
    rw [hAtOne]
    have hnearLinear' : dist (sqProfileLinearPart p) (sqProfilePolynomialMap p) < dist r c / 4 := by
      simpa [dist_comm] using hnearLinear
    linarith
  have hfinal :
      dist r c < dist r c := by
    calc
      dist r c ≤ dist r (sqProfilePolynomialMap p) +
          dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) +
          dist (sqProfileLinearPart p) c := by
            nlinarith [dist_triangle r (sqProfilePolynomialMap p) c,
              dist_triangle (sqProfilePolynomialMap p) (sqProfileLinearPart p) c]
      _ < dist r c / 8 + dist r c / 4 + 3 * dist r c / 8 := by
            have hpr'' : dist r (sqProfilePolynomialMap p) < dist r c / 8 := by
              simpa [dist_comm] using hpr'
            nlinarith [hpr'', hnearLinear, hlineClose]
      _ < dist r c := by
            nlinarith [hdpos]
  exact (not_lt_of_ge le_rfl) hfinal
