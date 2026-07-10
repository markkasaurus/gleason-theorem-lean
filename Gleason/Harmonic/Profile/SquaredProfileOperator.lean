import Gleason.Harmonic.HighDegree.HighEvenUnionProfileApprox
import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientEndpoint

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real

abbrev unitIccSq := Set.Icc (0 : ℝ) 1

def sqMulContinuousMap (q : C(unitIcc, ℝ)) : C(unitIcc, ℝ) :=
  ⟨fun u => u.1 * q u, continuous_subtype_val.mul q.continuous⟩

@[simp] theorem sqMulContinuousMap_apply (q : C(unitIcc, ℝ)) (u : unitIcc) :
    sqMulContinuousMap q u = u.1 * q u := by
  rfl

def northZonalSqProfileOrbit (r : C(unitIcc, ℝ)) (θ : ℝ) : C(unitIcc, ℝ) :=
  r.comp (sqMulCosSelfContinuous θ)

@[simp] theorem northZonalSqProfileOrbit_apply
    (r : C(unitIcc, ℝ)) (θ : ℝ) (u : unitIcc) :
    northZonalSqProfileOrbit r θ u = r (sqMulCosSelfMap θ u) := by
  simp [northZonalSqProfileOrbit, sqMulCosSelfContinuous]

lemma northZonalSqProfileOrbitContinuous (r : C(unitIcc, ℝ)) :
    Continuous (fun θ : ℝ => northZonalSqProfileOrbit r θ) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have harg : Continuous fun p : ℝ × unitIcc => sqMulCosSelfMap p.1 p.2 := by
    exact Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_snd).mul
        ((Real.continuous_cos.comp continuous_fst).pow 2))
      (fun p => mul_cos_sq_mem_Icc p.2 p.1)
  simpa [northZonalSqProfileOrbit, sqMulCosSelfContinuous] using r.continuous.comp harg

lemma northZonalSqProfileOrbit_intervalIntegrable (r : C(unitIcc, ℝ)) :
    IntervalIntegrable (fun θ : ℝ => northZonalSqProfileOrbit r θ)
      volume 0 (2 * Real.pi) := by
  exact (northZonalSqProfileOrbitContinuous r).intervalIntegrable 0 (2 * Real.pi)

def northZonalSqProfileAverage (r : C(unitIcc, ℝ)) : C(unitIcc, ℝ) :=
  (2 * ((2 * Real.pi)⁻¹ : ℝ)) •
    ∫ θ in 0..2 * Real.pi, northZonalSqProfileOrbit r θ

@[simp] theorem northZonalSqProfileAverage_apply (r : C(unitIcc, ℝ)) (u : unitIcc) :
    northZonalSqProfileAverage r u =
      2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, r (sqMulCosSelfMap θ u)) := by
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hInt :
      Integrable (fun θ : ℝ => northZonalSqProfileOrbit r θ)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    exact (northZonalSqProfileOrbitContinuous r).integrableOn_Ioc
  rw [northZonalSqProfileAverage, ContinuousMap.smul_apply, smul_eq_mul]
  rw [intervalIntegral_eq_integral_uIoc]
  simp [hpi]
  rw [ContinuousMap.integral_apply hInt u]
  simp [intervalIntegral_eq_integral_uIoc, hpi, northZonalSqProfileOrbit,
    sqMulCosSelfContinuous]
  ring_nf

theorem norm_northZonalSqProfileAverage_le_two_mul (r : C(unitIcc, ℝ)) :
    ‖northZonalSqProfileAverage r‖ ≤ 2 * ‖r‖ := by
  haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
  refine (ContinuousMap.norm_le_of_nonempty
    (f := northZonalSqProfileAverage r) (M := 2 * ‖r‖)).2 ?_
  intro u
  rw [northZonalSqProfileAverage_apply]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hInt1 :
      IntervalIntegrable (fun θ : ℝ => ‖r (sqMulCosSelfMap θ u)‖)
        volume 0 (2 * Real.pi) := by
    have hcont : Continuous (fun θ : ℝ => ‖r (sqMulCosSelfMap θ u)‖) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  have hInt2 :
      IntervalIntegrable (fun _ : ℝ => ‖r‖) volume 0 (2 * Real.pi) := by
    have hcont : Continuous (fun _ : ℝ => ‖r‖) := by continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  calc
    ‖2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, r (sqMulCosSelfMap θ u))‖
      = (2 * (2 * Real.pi)⁻¹) *
          ‖∫ θ in 0..2 * Real.pi, r (sqMulCosSelfMap θ u)‖ := by
            rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
            rw [abs_of_pos, abs_of_pos]
            · ring
            · positivity
            · positivity
    _ ≤ (2 * (2 * Real.pi)⁻¹) *
          ∫ θ in 0..2 * Real.pi, ‖r (sqMulCosSelfMap θ u)‖ := by
          gcongr
          exact intervalIntegral.norm_integral_le_integral_norm hpi.le
    _ ≤ (2 * (2 * Real.pi)⁻¹) * ∫ θ in 0..2 * Real.pi, ‖r‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine intervalIntegral.integral_mono_on hpi.le hInt1 hInt2 ?_
          intro θ hθ
          exact r.norm_coe_le_norm _
    _ = 2 * ‖r‖ := by
          have hpi' : (2 * Real.pi : ℝ) ≠ 0 := by positivity
          rw [intervalIntegral.integral_const]
          field_simp [hpi']
          ring_nf
          simp [mul_assoc, mul_left_comm, mul_comm]

theorem dist_northZonalSqProfileAverage_le
    (r s : C(unitIcc, ℝ)) :
    dist (northZonalSqProfileAverage r) (northZonalSqProfileAverage s) ≤
      2 * dist r s := by
  have hsub :
      northZonalSqProfileAverage (r - s) =
        northZonalSqProfileAverage r - northZonalSqProfileAverage s := by
    ext u
    have hr :
        IntervalIntegrable (fun θ : ℝ => r (sqMulCosSelfMap θ u)) volume 0 (2 * Real.pi) := by
      have hcont : Continuous (fun θ : ℝ => r (sqMulCosSelfMap θ u)) := by
        continuity
      exact hcont.intervalIntegrable _ _
    have hs :
        IntervalIntegrable (fun θ : ℝ => s (sqMulCosSelfMap θ u)) volume 0 (2 * Real.pi) := by
      have hcont : Continuous (fun θ : ℝ => s (sqMulCosSelfMap θ u)) := by
        continuity
      exact hcont.intervalIntegrable _ _
    simp [northZonalSqProfileAverage_apply, intervalIntegral.integral_sub hr hs]
    ring
  calc
    dist (northZonalSqProfileAverage r) (northZonalSqProfileAverage s)
      = ‖northZonalSqProfileAverage r - northZonalSqProfileAverage s‖ := by
          simp [dist_eq_norm]
    _ = ‖northZonalSqProfileAverage (r - s)‖ := by rw [hsub]
    _ ≤ 2 * ‖r - s‖ := norm_northZonalSqProfileAverage_le_two_mul (r - s)
    _ = 2 * dist r s := by simp [dist_eq_norm]

theorem northZonalSqProfileAverage_sqMulContinuousMap
    (q : C(unitIcc, ℝ)) :
    northZonalSqProfileAverage (sqMulContinuousMap q) =
      sqMulContinuousMap (northZonalSqQuotientAverage q) := by
  ext u
  rw [northZonalSqProfileAverage_apply, sqMulContinuousMap_apply]
  simp [sqMulContinuousMap_apply, northZonalSqQuotientAverage_apply]
  have hconst :
      ∫ θ in 0..2 * Real.pi, u.1 * Real.cos θ ^ 2 * q (sqMulCosSelfMap θ u) =
        u.1 * ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * q (sqMulCosSelfMap θ u) := by
    have htmp :
        ∫ θ in 0..2 * Real.pi, u.1 * (Real.cos θ ^ 2 * q (sqMulCosSelfMap θ u)) =
          u.1 * ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * q (sqMulCosSelfMap θ u) := by
      rw [intervalIntegral.integral_const_mul]
    simpa [mul_assoc] using htmp
  rw [hconst]
  ring

theorem northZonalSqProfileAverage_sqCenteredNorthZonalContinuousMap_of_mem_frame
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (hfz : IsNorthZonal f) :
    northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap f) =
      sqCenteredNorthZonalContinuousMap f := by
  ext u
  rw [northZonalSqProfileAverage_apply]
  have hmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
    rw [continuousSphereGreatCirclePointConstraintSubmodule_eq_continuousSphereFrameSubmodule]
    exact hf
  simpa [sqCenteredNorthZonalContinuousMap, ContinuousMap.coe_mk] using
    sqCenteredNorthZonalProfile_special_equation_of_mem_pointConstraint hmem hfz u
