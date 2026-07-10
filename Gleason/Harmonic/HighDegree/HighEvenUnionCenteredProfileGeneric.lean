import Gleason.Harmonic.HighDegree.HighEvenUnionCenteredProfileAlmostFixed

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

private lemma northZonalScalarPolynomial_sub_const
    (p : ℝ[X]) (a : ℝ) :
    northZonalScalarPolynomial (p - Polynomial.C a) =
      northZonalScalarPolynomial p - Polynomial.C (2 * a) := by
  ext n
  cases n with
  | zero =>
      simp [coeff_northZonalScalarPolynomial, northZonalScalarCoeff_zero]
      ring_nf
  | succ n =>
      simp [coeff_northZonalScalarPolynomial]

private theorem northZonal_average_diff_le
    {f g : C(spherePoint3, ℝ)} (r : Set.Icc (0 : ℝ) 1) :
    |2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi,
          (northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ -
            northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩))|
      ≤ 2 * ‖northZonalContinuousMap f - northZonalContinuousMap g‖ := by
  let k : C(Set.Icc (-1 : ℝ) 1, ℝ) := northZonalContinuousMap f - northZonalContinuousMap g
  let path : ℝ → Set.Icc (-1 : ℝ) 1 := fun θ => ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpath : Continuous path := by continuity
  have hInt1 :
      IntervalIntegrable (fun θ : ℝ => ‖k (path θ)‖) volume 0 (2 * Real.pi) := by
    exact ((continuous_norm.comp (k.continuous.comp hpath))).intervalIntegrable 0 (2 * Real.pi)
  have hInt2 :
      IntervalIntegrable (fun _ : ℝ => ‖k‖) volume 0 (2 * Real.pi) := by
    exact (continuous_const : Continuous fun _ : ℝ => ‖k‖).intervalIntegrable 0 (2 * Real.pi)
  calc
    |2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi,
          (northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ -
            northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩))|
      = ‖2 * (((2 * Real.pi)⁻¹ : ℝ) * ∫ θ in 0..2 * Real.pi, k (path θ))‖ := by
          simp [k, path, Real.norm_eq_abs, ContinuousMap.sub_apply, northZonalContinuousMap_apply]
    _ = (2 * (2 * Real.pi)⁻¹) * ‖∫ θ in 0..2 * Real.pi, k (path θ)‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          rw [abs_of_pos, abs_of_pos]
          · ring_nf
          · positivity
          · positivity
    _ ≤ (2 * (2 * Real.pi)⁻¹) * ∫ θ in 0..2 * Real.pi, ‖k (path θ)‖ := by
          gcongr
          exact intervalIntegral.norm_integral_le_integral_norm hpi.le
    _ ≤ (2 * (2 * Real.pi)⁻¹) * ∫ θ in 0..2 * Real.pi, ‖k‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine intervalIntegral.integral_mono_on hpi.le hInt1 hInt2 ?_
          intro θ hθ
          exact k.norm_coe_le_norm _
    _ = 2 * ‖k‖ := by
          have hpi' : (2 * Real.pi : ℝ) ≠ 0 := by positivity
          rw [intervalIntegral.integral_const]
          field_simp [hpi']
          ring_nf
          simp [k, mul_assoc, mul_left_comm, mul_comm]
    _ = 2 * ‖northZonalContinuousMap f - northZonalContinuousMap g‖ := by
          rfl

set_option maxHeartbeats 800000 in
theorem exists_centeredProfile_poly_almost_fixed_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ h : C(spherePoint3, ℝ), ∃ c : ℝ[X],
        h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
        IsNorthZonal h ∧
        (∀ z : Set.Icc (-1 : ℝ) 1,
          centeredNorthZonalProfile h z = c.eval z.1) ∧
        ‖northZonalContinuousMap h - northZonalContinuousMap g‖ < ε ∧
        ∀ r : Set.Icc (0 : ℝ) 1,
          |(northZonalScalarPolynomial c).eval r.1 - c.eval r.1| < 4 * ε := by
  intro ε hε
  rcases exists_northZonal_mem_highEvenUnion_close_of_mem_topologicalClosure_highEvenUnion_of_isNorthZonal
      hg.1 hgz hε with
    ⟨h, hhHigh, hhz, hhdist⟩
  have hmono : Directed (· ≤ ·) highEvenBoundedHarmonicPolyHomogeneousImageSubmodule := by
    intro N M
    exact ⟨max N M,
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_left _ _),
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _)⟩
  rw [highEvenUnionHarmonicPolyHomogeneousImageSubmodule] at hhHigh
  rcases (Submodule.mem_iSup_of_directed highEvenBoundedHarmonicPolyHomogeneousImageSubmodule hmono).mp hhHigh with
    ⟨N, hhN⟩
  have hhEven :
      h ∈ evenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule N hhN
  rcases exists_even_mvPolynomial_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule hhEven with
    ⟨q, hqEval, hqEven⟩
  let p : ℝ[X] := northMeridianPolynomial q
  let c : ℝ[X] := p - Polynomial.C (p.eval 0)
  have hpEval : ∀ z : Set.Icc (-1 : ℝ) 1, northZonalProfile h z = p.eval z.1 := by
    intro z
    simpa [p] using northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal hhz hqEval z
  have hprofdist :
      ‖northZonalContinuousMap h - northZonalContinuousMap g‖ < ε := by
    calc
      ‖northZonalContinuousMap h - northZonalContinuousMap g‖
        ≤ ‖h - g‖ := norm_northZonalContinuousMap_sub_le h g
      _ < ε := by simpa using hhdist
  refine ⟨h, c, hhHigh, hhz, ?_, hprofdist, ?_⟩
  · intro z
    calc
      centeredNorthZonalProfile h z = northZonalProfile h z - northZonalProfile h zeroIcc := by
        rfl
      _ = p.eval z.1 - p.eval 0 := by
        rw [hpEval z]
        congr 1
        have hzero := hpEval zeroIcc
        simpa [zeroIcc] using hzero
      _ = c.eval z.1 := by
        simp [c]
  · intro r
    have hframeEq :
        2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) =
          northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc := by
      have hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
        rw [continuousSphereGreatCirclePointConstraintSubmodule_eq_continuousSphereFrameSubmodule]
        exact hg.2
      exact northZonalProfile_special_equation_of_mem_pointConstraint hgpc hgz r
    have hpAvg :
        (northZonalScalarPolynomial p).eval r.1 =
          2 * (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi,
              northZonalProfile h ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) := by
      calc
        (northZonalScalarPolynomial p).eval r.1
          = 2 * (((2 * Real.pi)⁻¹ : ℝ) *
              ∫ θ in 0..2 * Real.pi, p.eval (r.1 * Real.cos θ)) := by
                exact (special_average_polynomial_eval p r).symm
        _ = 2 * (((2 * Real.pi)⁻¹ : ℝ) *
              ∫ θ in 0..2 * Real.pi,
                northZonalProfile h ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) := by
              refine congrArg (fun t : ℝ => 2 * (((2 * Real.pi)⁻¹ : ℝ) * t)) ?_
              apply intervalIntegral.integral_congr_ae
              filter_upwards with θ hθ
              simpa using (hpEval ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩).symm
    have havgDiff :
        |(northZonalScalarPolynomial p).eval r.1 -
            (northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc)| <
          2 * ε := by
      have hle := northZonal_average_diff_le (f := h) (g := g) r
      rw [hpAvg, ← hframeEq]
      have hIntH :
          IntervalIntegrable
            (fun θ : ℝ => northZonalProfile h ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
            volume 0 (2 * Real.pi) := by
        let path : ℝ → Set.Icc (-1 : ℝ) 1 := fun θ => ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩
        have hpath : Continuous path := by continuity
        simpa [path, northZonalProfile] using
          ((continuous_northZonalProfile h).comp hpath).intervalIntegrable 0 (2 * Real.pi)
      have hIntG :
          IntervalIntegrable
            (fun θ : ℝ => northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
            volume 0 (2 * Real.pi) := by
        let path : ℝ → Set.Icc (-1 : ℝ) 1 := fun θ => ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩
        have hpath : Continuous path := by continuity
        simpa [path, northZonalProfile] using
          ((continuous_northZonalProfile g).comp hpath).intervalIntegrable 0 (2 * Real.pi)
      have hsub :
          2 * (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi,
              northZonalProfile h ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
          2 * (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi,
              northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
            =
          2 * (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi,
              (northZonalProfile h ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ -
                northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)) := by
        rw [intervalIntegral.integral_sub hIntH hIntG]
        ring_nf
      rw [hsub]
      exact lt_of_le_of_lt hle (by linarith [hprofdist])
    have hvalNonneg :
        |northZonalProfile g (nonnegIccToIcc r) - northZonalProfile h (nonnegIccToIcc r)| < ε := by
      have hle :
          |northZonalProfile g (nonnegIccToIcc r) - northZonalProfile h (nonnegIccToIcc r)|
            ≤ ‖northZonalContinuousMap h - northZonalContinuousMap g‖ := by
        simpa [ContinuousMap.sub_apply, northZonalContinuousMap_apply, Real.norm_eq_abs, abs_sub_comm] using
          ((northZonalContinuousMap h - northZonalContinuousMap g).norm_coe_le_norm (nonnegIccToIcc r))
      exact lt_of_le_of_lt hle hprofdist
    have hvalZero :
        |northZonalProfile g zeroIcc - northZonalProfile h zeroIcc| < ε := by
      have hle :
          |northZonalProfile g zeroIcc - northZonalProfile h zeroIcc|
            ≤ ‖northZonalContinuousMap h - northZonalContinuousMap g‖ := by
        simpa [ContinuousMap.sub_apply, northZonalContinuousMap_apply, Real.norm_eq_abs, abs_sub_comm] using
          ((northZonalContinuousMap h - northZonalContinuousMap g).norm_coe_le_norm zeroIcc)
      exact lt_of_le_of_lt hle hprofdist
    have hmain :
        |(northZonalScalarPolynomial p).eval r.1 - (p.eval r.1 + p.eval 0)|
          ≤ |(northZonalScalarPolynomial p).eval r.1 -
              (northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc)| +
            |northZonalProfile g (nonnegIccToIcc r) - p.eval r.1| +
            |northZonalProfile g zeroIcc - p.eval 0| := by
      have htri :
          |(northZonalScalarPolynomial p).eval r.1 - (p.eval r.1 + p.eval 0)|
            ≤ |(northZonalScalarPolynomial p).eval r.1 -
                  (northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc)| +
                |(northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc) -
                  (p.eval r.1 + p.eval 0)| := by
            exact abs_sub_le _ _ _
      refine htri.trans ?_
      have hsplit :
          |(northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc) -
              (p.eval r.1 + p.eval 0)|
            ≤ |northZonalProfile g (nonnegIccToIcc r) - p.eval r.1| +
                |northZonalProfile g zeroIcc - p.eval 0| := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Real.norm_eq_abs] using
          (norm_add_le
            (northZonalProfile g (nonnegIccToIcc r) - p.eval r.1)
            (northZonalProfile g zeroIcc - p.eval 0))
      linarith
    have hpolyNonneg :
        |northZonalProfile h (nonnegIccToIcc r) - p.eval r.1| = 0 := by
      rw [hpEval (nonnegIccToIcc r)]
      simp
    have hpolyZero :
        |northZonalProfile h zeroIcc - p.eval 0| = 0 := by
      have hz : (zeroIcc : ℝ) = 0 := by simp [zeroIcc]
      rw [hpEval zeroIcc, hz]
      simp
    have hcompNonneg :
        |northZonalProfile g (nonnegIccToIcc r) - p.eval r.1|
          ≤ |northZonalProfile g (nonnegIccToIcc r) - northZonalProfile h (nonnegIccToIcc r)| := by
      rw [hpEval (nonnegIccToIcc r)]
      simp
    have hcompZero :
        |northZonalProfile g zeroIcc - p.eval 0|
          ≤ |northZonalProfile g zeroIcc - northZonalProfile h zeroIcc| := by
      have hz : (zeroIcc : ℝ) = 0 := by simp [zeroIcc]
      rw [← hz, hpEval zeroIcc]
    have hbound :
        |(northZonalScalarPolynomial p).eval r.1 - (p.eval r.1 + p.eval 0)|
          < 4 * ε := by
      calc
        |(northZonalScalarPolynomial p).eval r.1 - (p.eval r.1 + p.eval 0)|
          ≤ |(northZonalScalarPolynomial p).eval r.1 -
              (northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc)| +
            |northZonalProfile g (nonnegIccToIcc r) - p.eval r.1| +
            |northZonalProfile g zeroIcc - p.eval 0| := hmain
        _ ≤ |(northZonalScalarPolynomial p).eval r.1 -
              (northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc)| +
            |northZonalProfile g (nonnegIccToIcc r) - northZonalProfile h (nonnegIccToIcc r)| +
            |northZonalProfile g zeroIcc - northZonalProfile h zeroIcc| := by
              gcongr
        _ < (2 * ε) + ε + ε := by
              nlinarith [havgDiff, hvalNonneg, hvalZero]
        _ = 4 * ε := by ring_nf
    have hcalc :
        (northZonalScalarPolynomial c).eval r.1 - c.eval r.1 =
          (northZonalScalarPolynomial p).eval r.1 - (p.eval r.1 + p.eval 0) := by
      rw [show c = p - Polynomial.C (p.eval 0) by rfl]
      rw [northZonalScalarPolynomial_sub_const]
      simp
      ring_nf
    rw [hcalc]
    exact hbound
