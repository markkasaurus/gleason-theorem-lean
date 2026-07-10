import Gleason.Harmonic.Auxiliary.PoleAverage
import Gleason.Harmonic.Profile.SquaredProfileOperator
import Gleason.Harmonic.HighDegree.HighEvenUnionProfilePolyApprox

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real

namespace GleasonS2Bridge

private lemma centeredNorthZonalProfile_sqrt_mul_cos_sq_eq_of_isNorthZonal_of_antipode_even
    {f : C(spherePoint3, ℝ)}
    (hfz : IsNorthZonal f)
    (hanti : ∀ x : spherePoint3, f (sphereAntipode x) = f x)
    (u : Set.Icc (0 : ℝ) 1) (θ : ℝ) :
    centeredNorthZonalProfile f
      ⟨Real.sqrt u.1 * Real.cos θ, mul_cos_mem_Icc
        ⟨Real.sqrt u.1, by
          constructor
          · exact Real.sqrt_nonneg u.1
          · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := by
              exact Real.sq_sqrt u.2.1
            have hle : Real.sqrt u.1 ≤ 1 := by
              nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
            simpa using hle⟩ θ⟩
      =
    sqCenteredNorthZonalProfile f ⟨u.1 * Real.cos θ ^ 2, mul_cos_sq_mem_Icc u θ⟩ := by
  let r : Set.Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt u.1, by
      constructor
      · exact Real.sqrt_nonneg u.1
      · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := by
          exact Real.sq_sqrt u.2.1
        have hle : Real.sqrt u.1 ≤ 1 := by
          nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
        simpa using hle⟩
  have hsqrt_mul :
      Real.sqrt (u.1 * Real.cos θ ^ 2) = |Real.sqrt u.1 * Real.cos θ| := by
    calc
      Real.sqrt (u.1 * Real.cos θ ^ 2)
          = Real.sqrt u.1 * Real.sqrt (Real.cos θ ^ 2) := by
              rw [Real.sqrt_mul u.2.1]
      _ = Real.sqrt u.1 * |Real.cos θ| := by
            rw [Real.sqrt_sq_eq_abs]
      _ = |Real.sqrt u.1| * |Real.cos θ| := by
            rw [abs_of_nonneg (Real.sqrt_nonneg u.1)]
      _ = |Real.sqrt u.1 * Real.cos θ| := by
            rw [abs_mul]
  calc
    centeredNorthZonalProfile f
      ⟨Real.sqrt u.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩
      = centeredNorthZonalProfile f
          ⟨|Real.sqrt u.1 * Real.cos θ|, by
            constructor
            · nlinarith [abs_nonneg (Real.sqrt u.1 * Real.cos θ)]
            · rw [abs_le]
              constructor <;> nlinarith [r.2.1, r.2.2, Real.neg_one_le_cos θ, Real.cos_le_one θ]⟩ := by
                by_cases hnonneg : 0 ≤ Real.sqrt u.1 * Real.cos θ
                · have habs : |Real.sqrt u.1 * Real.cos θ| = Real.sqrt u.1 * Real.cos θ :=
                    abs_of_nonneg hnonneg
                  have hz :
                      (⟨|Real.sqrt u.1 * Real.cos θ|, by
                        constructor
                        · nlinarith [abs_nonneg (Real.sqrt u.1 * Real.cos θ)]
                        · rw [abs_le]
                          constructor <;>
                            nlinarith [r.2.1, r.2.2, Real.neg_one_le_cos θ, Real.cos_le_one θ]⟩
                        : Set.Icc (-1 : ℝ) 1) =
                      ⟨Real.sqrt u.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ := by
                    apply Subtype.ext
                    simp [habs]
                  rw [hz]
                · have habs :
                    |Real.sqrt u.1 * Real.cos θ| = -(Real.sqrt u.1 * Real.cos θ) :=
                      abs_of_neg (lt_of_not_ge hnonneg)
                  have hz :
                      (⟨|Real.sqrt u.1 * Real.cos θ|, by
                        constructor
                        · nlinarith [abs_nonneg (Real.sqrt u.1 * Real.cos θ)]
                        · rw [abs_le]
                          constructor <;>
                            nlinarith [r.2.1, r.2.2, Real.neg_one_le_cos θ, Real.cos_le_one θ]⟩
                        : Set.Icc (-1 : ℝ) 1) =
                      negIcc ⟨Real.sqrt u.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ := by
                    apply Subtype.ext
                    simp [negIcc, habs]
                  rw [hz]
                  symm
                  exact
                    centeredNorthZonalProfile_even_of_isNorthZonal_of_antipode_even
                      hfz hanti ⟨Real.sqrt u.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩
    _ = centeredNorthZonalProfile f
          ⟨Real.sqrt (u.1 * Real.cos θ ^ 2), by
            constructor
            · nlinarith [Real.sqrt_nonneg (u.1 * Real.cos θ ^ 2)]
            · have hsq : (Real.sqrt (u.1 * Real.cos θ ^ 2)) ^ 2 = u.1 * Real.cos θ ^ 2 := by
                exact Real.sq_sqrt (mul_cos_sq_mem_Icc u θ |>.1)
              have hle : Real.sqrt (u.1 * Real.cos θ ^ 2) ≤ 1 := by
                nlinarith [mul_cos_sq_mem_Icc u θ |>.2, Real.sqrt_nonneg (u.1 * Real.cos θ ^ 2), hsq]
              simpa using hle⟩ := by
                have hz :
                    (⟨|Real.sqrt u.1 * Real.cos θ|, by
                      constructor
                      · nlinarith [abs_nonneg (Real.sqrt u.1 * Real.cos θ)]
                      · rw [abs_le]
                        constructor <;>
                          nlinarith [r.2.1, r.2.2, Real.neg_one_le_cos θ, Real.cos_le_one θ]⟩
                      : Set.Icc (-1 : ℝ) 1) =
                    ⟨Real.sqrt (u.1 * Real.cos θ ^ 2), by
                      constructor
                      · nlinarith [Real.sqrt_nonneg (u.1 * Real.cos θ ^ 2)]
                      · have hsq : (Real.sqrt (u.1 * Real.cos θ ^ 2)) ^ 2 = u.1 * Real.cos θ ^ 2 := by
                          exact Real.sq_sqrt (mul_cos_sq_mem_Icc u θ |>.1)
                        have hle : Real.sqrt (u.1 * Real.cos θ ^ 2) ≤ 1 := by
                          nlinarith [mul_cos_sq_mem_Icc u θ |>.2, Real.sqrt_nonneg (u.1 * Real.cos θ ^ 2), hsq]
                        simpa using hle⟩ := by
                  apply Subtype.ext
                  simp [hsqrt_mul]
                rw [hz]
    _ = sqCenteredNorthZonalProfile f ⟨u.1 * Real.cos θ ^ 2, mul_cos_sq_mem_Icc u θ⟩ := by
          simp [sqCenteredNorthZonalProfile]

theorem northZonalSqProfileAverage_apply_eq_two_mul_poleAverageLinear_sub_zero_of_isNorthZonal_of_antipode_even
    {f : C(spherePoint3, ℝ)}
    (hfz : IsNorthZonal f)
    (hanti : ∀ x : spherePoint3, f (sphereAntipode x) = f x)
    (u : unitIcc) :
    northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap f) u =
      2 * poleAverageLinear f
        (specialZPoint
          ⟨Real.sqrt u.1, by
            constructor
            · exact Real.sqrt_nonneg u.1
            · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := by
                exact Real.sq_sqrt u.2.1
              have hle : Real.sqrt u.1 ≤ 1 := by
                nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
              simpa using hle⟩) -
      2 * northZonalProfile f zeroIcc := by
  let r : Set.Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt u.1, by
      constructor
      · exact Real.sqrt_nonneg u.1
      · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := by
          exact Real.sq_sqrt u.2.1
        have hle : Real.sqrt u.1 ≤ 1 := by
          nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
        simpa using hle⟩
  rw [northZonalSqProfileAverage_apply]
  have hfun :
      (fun θ : ℝ => sqCenteredNorthZonalContinuousMap f (sqMulCosSelfMap θ u)) =
        (fun θ : ℝ =>
          centeredNorthZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) := by
    funext θ
    dsimp [sqCenteredNorthZonalContinuousMap]
    simpa [r, sqMulCosSelfMap] using
      centeredNorthZonalProfile_sqrt_mul_cos_sq_eq_of_isNorthZonal_of_antipode_even
        hfz hanti u θ |>.symm
  rw [hfun]
  have hbase :
      poleAverageLinear f (specialZPoint r) =
        ((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ := by
    rw [poleAverageLinear_eq_greatCircleAverageLinear
      f (specialXPoint r) sphereE2 (specialZPoint r)
      (specialXPoint_inner_sphereE2 r)
      (specialXPoint_inner_specialZPoint r)
      (sphereE2_inner_specialZPoint r)]
    exact greatCircleAverageLinear_special_of_isNorthZonal hfz r
  have hconst :
      (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, northZonalProfile f zeroIcc) =
        northZonalProfile f zeroIcc := by
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hconstInt :
        (∫ θ in 0..2 * Real.pi, northZonalProfile f zeroIcc) =
          (2 * Real.pi) * northZonalProfile f zeroIcc := by
      simp
    rw [hconstInt]
    field_simp [hpi]
  have hInt1 :
      IntervalIntegrable
        (fun θ : ℝ => northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
        volume 0 (2 * Real.pi) := by
    let path : ℝ → Set.Icc (-1 : ℝ) 1 := fun θ => ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩
    have hpath : Continuous path := by continuity
    simpa [path] using
      ((continuous_northZonalProfile f).comp hpath).intervalIntegrable 0 (2 * Real.pi)
  have hInt2 :
      IntervalIntegrable (fun θ : ℝ => northZonalProfile f zeroIcc)
        volume 0 (2 * Real.pi) := by
    simpa using
      (continuous_const : Continuous fun _ : ℝ => northZonalProfile f zeroIcc).intervalIntegrable
        0 (2 * Real.pi)
  calc
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi,
          centeredNorthZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
      =
        2 * ((((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
          (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi, northZonalProfile f zeroIcc)) := by
            congr 2
            calc
              (((2 * Real.pi)⁻¹ : ℝ) *
                  ∫ θ in 0..2 * Real.pi,
                    centeredNorthZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
                  =
                (((2 * Real.pi)⁻¹ : ℝ) *
                  ((∫ θ in 0..2 * Real.pi,
                    northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
                    (∫ θ in 0..2 * Real.pi, northZonalProfile f zeroIcc))) := by
                      congr 1
                      have hcenteredInt :
                          (∫ θ in 0..2 * Real.pi,
                            centeredNorthZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) =
                          (∫ θ in 0..2 * Real.pi,
                            northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
                          (∫ θ in 0..2 * Real.pi, northZonalProfile f zeroIcc) := by
                            have hfunCentered :
                                (fun θ : ℝ =>
                                  centeredNorthZonalProfile f
                                    ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) =
                                (fun θ : ℝ =>
                                  northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ -
                                    northZonalProfile f zeroIcc) := by
                                      funext θ
                                      simp [centeredNorthZonalProfile]
                            rw [hfunCentered, intervalIntegral.integral_sub hInt1 hInt2]
                      exact hcenteredInt
              _ =
                (((2 * Real.pi)⁻¹ : ℝ) *
                  ∫ θ in 0..2 * Real.pi,
                    northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
                (((2 * Real.pi)⁻¹ : ℝ) *
                  ∫ θ in 0..2 * Real.pi, northZonalProfile f zeroIcc) := by
                    rw [mul_sub]
    _ = 2 * ((((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
          (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi, northZonalProfile f zeroIcc)) := by
            rfl
    _ = 2 * (((((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
          northZonalProfile f zeroIcc)) := by
            rw [hconst]
    _ = 2 * poleAverageLinear f (specialZPoint r) - 2 * northZonalProfile f zeroIcc := by
            rw [hbase]
            ring

end GleasonS2Bridge
