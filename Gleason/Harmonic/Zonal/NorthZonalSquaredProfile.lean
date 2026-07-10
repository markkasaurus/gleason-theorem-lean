import Gleason.Harmonic.Zonal.NorthZonalEven

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real

def sqCenteredNorthZonalProfile (f : C(spherePoint3, ℝ)) :
    Set.Icc (0 : ℝ) 1 → ℝ :=
  fun u =>
    centeredNorthZonalProfile f
      ⟨Real.sqrt u.1, by
        constructor
        · have : 0 ≤ Real.sqrt u.1 := Real.sqrt_nonneg u.1
          nlinarith
        · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := by
            exact Real.sq_sqrt u.2.1
          have hle : Real.sqrt u.1 ≤ 1 := by
            nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
          simpa using hle⟩

@[simp] lemma sqCenteredNorthZonalProfile_apply
    (f : C(spherePoint3, ℝ)) (u : Set.Icc (0 : ℝ) 1) :
    sqCenteredNorthZonalProfile f u =
      centeredNorthZonalProfile f
        ⟨Real.sqrt u.1, by
          constructor
          · have : 0 ≤ Real.sqrt u.1 := Real.sqrt_nonneg u.1
            nlinarith
          · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := by
              exact Real.sq_sqrt u.2.1
            have hle : Real.sqrt u.1 ≤ 1 := by
              nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
            simpa using hle⟩ := by
  rfl

lemma mul_cos_sq_mem_Icc (u : Set.Icc (0 : ℝ) 1) (θ : ℝ) :
    u.1 * Real.cos θ ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have hcosSq : 0 ≤ Real.cos θ ^ 2 := sq_nonneg (Real.cos θ)
    nlinarith [u.2.1, hcosSq]
  · have hcos : Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (Real.cos θ), Real.neg_one_le_cos θ, Real.cos_le_one θ]
    nlinarith [u.2.1, u.2.2, hcos]

lemma centeredNorthZonalProfile_sqrt_mul_cos_sq_eq
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
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
                · have habs : |Real.sqrt u.1 * Real.cos θ| = -(Real.sqrt u.1 * Real.cos θ) := abs_of_neg (lt_of_not_ge hnonneg)
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
                  exact centeredNorthZonalProfile_even_of_mem_pointConstraint hfmem hfz
                    ⟨Real.sqrt u.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩
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

theorem sqCenteredNorthZonalProfile_special_equation_of_mem_pointConstraint
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (u : Set.Icc (0 : ℝ) 1) :
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
      ∫ θ in 0..2 * Real.pi,
        sqCenteredNorthZonalProfile f ⟨u.1 * Real.cos θ ^ 2, mul_cos_sq_mem_Icc u θ⟩) =
      sqCenteredNorthZonalProfile f u := by
  let r : Set.Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt u.1, by
      constructor
      · exact Real.sqrt_nonneg u.1
      · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := by
          exact Real.sq_sqrt u.2.1
        have hle : Real.sqrt u.1 ≤ 1 := by
          nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
        simpa using hle⟩
  have hbase :=
    centeredNorthZonalProfile_special_equation_of_mem_pointConstraint hfmem hfz r
  have hfun :
      (fun θ : ℝ =>
        centeredNorthZonalProfile f
          ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) =
      (fun θ : ℝ =>
        sqCenteredNorthZonalProfile f ⟨u.1 * Real.cos θ ^ 2, mul_cos_sq_mem_Icc u θ⟩) := by
    funext θ
    simpa [r, sqCenteredNorthZonalProfile, Real.sq_sqrt u.2.1, mul_pow] using
      centeredNorthZonalProfile_sqrt_mul_cos_sq_eq hfmem hfz u θ
  rw [hfun] at hbase
  simpa [sqCenteredNorthZonalProfile, r, nonnegIccToIcc, Real.sq_sqrt u.2.1] using hbase
