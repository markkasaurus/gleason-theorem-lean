import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileFixedContinuousTame

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

def sqScaleMap (a : unitIcc) (u : unitIcc) : unitIcc :=
  ⟨a.1 * u.1, by
    constructor
    · exact mul_nonneg a.2.1 u.2.1
    · nlinarith [a.2.1, a.2.2, u.2.1, u.2.2]⟩

@[simp] theorem sqScaleMap_apply (a u : unitIcc) :
    (sqScaleMap a u : ℝ) = a.1 * u.1 := by
  rfl

lemma sqScaleMap_sqMulCosSelfMap (a : unitIcc) (θ : ℝ) (u : unitIcc) :
    sqScaleMap a (sqMulCosSelfMap θ u) = sqMulCosSelfMap θ (sqScaleMap a u) := by
  apply Subtype.ext
  simp [sqScaleMap, sqMulCosSelfMap, mul_assoc]

def sqProfileRescale (a : unitIcc) (ha : 0 < a.1) (r : C(unitIcc, ℝ)) : C(unitIcc, ℝ) :=
  ⟨fun u => r (sqScaleMap a u) / a.1,
    by
      have hcontScaleVal : Continuous fun u : unitIcc => (sqScaleMap a u : ℝ) := by
        simpa [sqScaleMap] using (continuous_const.mul continuous_subtype_val)
      have hcontScale : Continuous fun u : unitIcc => sqScaleMap a u := by
        exact Continuous.subtype_mk hcontScaleVal (fun u => (sqScaleMap a u).2)
      exact (r.continuous.comp hcontScale).div continuous_const (fun _ => ne_of_gt ha)⟩

@[simp] theorem sqProfileRescale_apply (a : unitIcc) (ha : 0 < a.1)
    (r : C(unitIcc, ℝ)) (u : unitIcc) :
    sqProfileRescale a ha r u = r (sqScaleMap a u) / a.1 := by
  rfl

lemma northZonalSqProfileAverage_sqProfileRescale
    (a : unitIcc) (ha : 0 < a.1) (r : C(unitIcc, ℝ)) :
    northZonalSqProfileAverage (sqProfileRescale a ha r) =
      sqProfileRescale a ha (northZonalSqProfileAverage r) := by
  ext u
  rw [northZonalSqProfileAverage_apply, sqProfileRescale_apply, northZonalSqProfileAverage_apply]
  simp_rw [sqProfileRescale_apply]
  have ha0 : (a.1 : ℝ) ≠ 0 := ne_of_gt ha
  have hleft :
      ∫ θ in 0..2 * Real.pi, r (sqScaleMap a (sqMulCosSelfMap θ u)) / a.1
        = (1 / a.1) * ∫ θ in 0..2 * Real.pi, r (sqScaleMap a (sqMulCosSelfMap θ u)) := by
    rw [show (fun θ : ℝ => r (sqScaleMap a (sqMulCosSelfMap θ u)) / a.1) =
        fun θ : ℝ => (1 / a.1) * r (sqScaleMap a (sqMulCosSelfMap θ u)) by
          funext θ
          field_simp [ha0]]
    rw [intervalIntegral.integral_const_mul]
  have hright :
      ∫ θ in 0..2 * Real.pi, r (sqMulCosSelfMap θ (sqScaleMap a u))
        = ∫ θ in 0..2 * Real.pi, r (sqScaleMap a (sqMulCosSelfMap θ u)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with θ hθ
    rw [sqScaleMap_sqMulCosSelfMap]
  rw [hleft, hright]
  field_simp [ha0]

theorem sqProfileRescale_fixed
    (a : unitIcc) (ha : 0 < a.1) {r : C(unitIcc, ℝ)}
    (hfix : northZonalSqProfileAverage r = r) :
    northZonalSqProfileAverage (sqProfileRescale a ha r) =
      sqProfileRescale a ha r := by
  rw [northZonalSqProfileAverage_sqProfileRescale, hfix]

theorem sqProfileRescale_zero
    (a : unitIcc) (ha : 0 < a.1) {r : C(unitIcc, ℝ)}
    (hzero : r zeroUnitIcc = 0) :
    sqProfileRescale a ha r zeroUnitIcc = 0 := by
  rw [sqProfileRescale_apply]
  have hscale0 : sqScaleMap a zeroUnitIcc = zeroUnitIcc := by
    apply Subtype.ext
    simp [sqScaleMap, zeroUnitIcc]
  rw [hscale0, hzero]
  simp

theorem sqProfileRescale_linear
    (a : unitIcc) (ha : 0 < a.1) (c : ℝ) :
    sqProfileRescale a ha ((C c * X).toContinuousMapOn unitIcc) =
      (C c * X).toContinuousMapOn unitIcc := by
  ext u
  rw [sqProfileRescale_apply]
  change (((C c * X : ℝ[X]).eval (a.1 * u.1)) / a.1) = ((C c * X : ℝ[X]).eval u.1)
  field_simp [show (a.1 : ℝ) ≠ 0 by exact ne_of_gt ha]
  change ((C c * X : ℝ[X]).eval (a.1 * u.1)) = a.1 * ((C c * X : ℝ[X]).eval u.1)
  simp [Polynomial.eval_mul]
  ring

theorem dist_sqProfileRescale_le_div
    (a : unitIcc) (ha : 0 < a.1) (r s : C(unitIcc, ℝ)) :
    dist (sqProfileRescale a ha r) (sqProfileRescale a ha s) ≤ dist r s / a.1 := by
  rw [dist_eq_norm]
  rw [dist_eq_norm]
  have ha0 : (a.1 : ℝ) ≠ 0 := ne_of_gt ha
  haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
  refine (ContinuousMap.norm_le_of_nonempty
    (f := sqProfileRescale a ha r - sqProfileRescale a ha s)
    (M := ‖r - s‖ / a.1)).2 ?_
  intro u
  rw [ContinuousMap.sub_apply, sqProfileRescale_apply, sqProfileRescale_apply, Real.norm_eq_abs]
  have hpoint :
      |(r - s) (sqScaleMap a u)| ≤ ‖r - s‖ := by
    simpa [ContinuousMap.sub_apply, Real.norm_eq_abs] using
      (r - s).norm_coe_le_norm (sqScaleMap a u)
  calc
    |r (sqScaleMap a u) / a.1 - s (sqScaleMap a u) / a.1|
      = |((r - s) (sqScaleMap a u)) / a.1| := by
          have hsub :
              r (sqScaleMap a u) / a.1 - s (sqScaleMap a u) / a.1 =
                (r (sqScaleMap a u) - s (sqScaleMap a u)) / a.1 := by
            field_simp [ha0]
          rw [hsub]
          simp [ContinuousMap.sub_apply]
    _ = |(r - s) (sqScaleMap a u)| / a.1 := by
          rw [abs_div, abs_of_pos ha]
    _ ≤ ‖r - s‖ / a.1 := by
          exact div_le_div_of_nonneg_right hpoint (le_of_lt ha)
