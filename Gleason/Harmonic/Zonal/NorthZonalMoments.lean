import Gleason.Harmonic.Zonal.NorthZonalConstraint
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real

def northZonalScalarCoeff (n : ℕ) : ℝ :=
  2 * (((2 * Real.pi)⁻¹ : ℝ) *
    ∫ θ in 0..2 * Real.pi, Real.cos θ ^ n)

lemma integral_cos_odd_eq_zero (m : ℕ) :
    ∫ θ in 0..2 * Real.pi, Real.cos θ ^ (2 * m + 1) = 0 := by
  simpa using
    (integral_sin_pow_mul_cos_pow_odd (a := (0 : ℝ)) (b := 2 * Real.pi) 0 m)

lemma integral_cos_even_succ (m : ℕ) :
    ∫ θ in 0..2 * Real.pi, Real.cos θ ^ (2 * m + 2) =
      (((2 * m + 1 : ℕ) : ℝ) / (((2 * m + 2 : ℕ) : ℝ))) *
        ∫ θ in 0..2 * Real.pi, Real.cos θ ^ (2 * m) := by
  simpa using
    (integral_cos_pow (a := (0 : ℝ)) (b := 2 * Real.pi) (n := 2 * m))

@[simp] lemma northZonalScalarCoeff_zero :
    northZonalScalarCoeff 0 = 2 := by
  unfold northZonalScalarCoeff
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  calc
    2 * (((2 * Real.pi)⁻¹ : ℝ) * ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 0)
      = 2 * (((2 * Real.pi)⁻¹ : ℝ) * (2 * Real.pi)) := by simp
    _ = 2 := by
      field_simp [hpi]

@[simp] lemma northZonalScalarCoeff_two :
    northZonalScalarCoeff 2 = 1 := by
  unfold northZonalScalarCoeff
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  calc
    2 * (((2 * Real.pi)⁻¹ : ℝ) * ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2)
      = 2 * (((2 * Real.pi)⁻¹ : ℝ) * Real.pi) := by simp
    _ = 1 := by
      field_simp [hpi]

@[simp] lemma northZonalScalarCoeff_odd (m : ℕ) :
    northZonalScalarCoeff (2 * m + 1) = 0 := by
  unfold northZonalScalarCoeff
  rw [integral_cos_odd_eq_zero]
  ring

lemma northZonalScalarCoeff_even_succ (m : ℕ) :
    northZonalScalarCoeff (2 * m + 2) =
      (((2 * m + 1 : ℕ) : ℝ) / (((2 * m + 2 : ℕ) : ℝ))) *
        northZonalScalarCoeff (2 * m) := by
  unfold northZonalScalarCoeff
  rw [integral_cos_even_succ]
  ac_rfl

lemma northZonalScalarCoeff_even_pos (m : ℕ) :
    0 < northZonalScalarCoeff (2 * m) := by
  induction m with
  | zero =>
      norm_num [northZonalScalarCoeff_zero]
  | succ m hm =>
      rw [show 2 * Nat.succ m = 2 * m + 2 by omega, northZonalScalarCoeff_even_succ]
      positivity

lemma northZonalScalarCoeff_even_gt_two_lt_one_aux (k : ℕ) :
    northZonalScalarCoeff (2 * (k + 2)) < 1 := by
  induction k with
  | zero =>
      rw [show 2 * (0 + 2) = 2 * 1 + 2 by norm_num, northZonalScalarCoeff_even_succ,
        northZonalScalarCoeff_two]
      norm_num
  | succ k hk =>
      rw [show 2 * (Nat.succ k + 2) = 2 * (k + 2) + 2 by omega, northZonalScalarCoeff_even_succ]
      have hfac_pos : 0 < ((((2 * (k + 2) + 1 : ℕ) : ℝ) / (((2 * (k + 2) + 2 : ℕ) : ℝ)))) := by
        positivity
      have hfac_lt : ((((2 * (k + 2) + 1 : ℕ) : ℝ) / (((2 * (k + 2) + 2 : ℕ) : ℝ)))) < 1 := by
        have hden : (0 : ℝ) < (((2 * (k + 2) + 2 : ℕ) : ℝ)) := by positivity
        have hnum : (((2 * (k + 2) + 1 : ℕ) : ℝ)) < (((2 * (k + 2) + 2 : ℕ) : ℝ)) := by
          norm_num
        exact (div_lt_one hden).2 hnum
      have hcoeff_nonneg : 0 ≤ northZonalScalarCoeff (2 * (k + 2)) := by
        exact le_of_lt (northZonalScalarCoeff_even_pos (k + 2))
      have hmul_lt_fac :
          ((((2 * (k + 2) + 1 : ℕ) : ℝ) / (((2 * (k + 2) + 2 : ℕ) : ℝ))) *
            northZonalScalarCoeff (2 * (k + 2))) <
          (((2 * (k + 2) + 1 : ℕ) : ℝ) / (((2 * (k + 2) + 2 : ℕ) : ℝ))) := by
        simpa using (mul_lt_mul_of_pos_left hk hfac_pos)
      calc
        ((((2 * (k + 2) + 1 : ℕ) : ℝ) / (((2 * (k + 2) + 2 : ℕ) : ℝ))) *
            northZonalScalarCoeff (2 * (k + 2)))
            < (((2 * (k + 2) + 1 : ℕ) : ℝ) / (((2 * (k + 2) + 2 : ℕ) : ℝ))) := hmul_lt_fac
        _ < 1 := hfac_lt

lemma monomial_special_average_eq_coeff_mul (n : ℕ) (r : Set.Icc (0 : ℝ) 1) :
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
      ∫ θ in 0..2 * Real.pi, (r.1 * Real.cos θ) ^ n) =
      northZonalScalarCoeff n * r.1 ^ n := by
  unfold northZonalScalarCoeff
  rw [show (fun θ : ℝ => (r.1 * Real.cos θ) ^ n) =
      (fun θ : ℝ => r.1 ^ n * Real.cos θ ^ n) by
      funext θ
      rw [mul_pow]]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem monomial_special_fixed_iff (n : ℕ) :
    (∀ r : Set.Icc (0 : ℝ) 1,
      2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, (r.1 * Real.cos θ) ^ n) =
          r.1 ^ n) ↔ n = 2 := by
  constructor
  · intro hfix
    let r1 : Set.Icc (0 : ℝ) 1 := ⟨1, by constructor <;> norm_num⟩
    have hcoeff :
        northZonalScalarCoeff n = 1 := by
      have hfix1 := hfix r1
      rw [monomial_special_average_eq_coeff_mul] at hfix1
      simpa [r1] using hfix1
    cases Nat.even_or_odd n with
    | inl hEven =>
        rcases hEven with ⟨m, rfl⟩
        cases m with
        | zero =>
            simp at hcoeff
        | succ m =>
            cases m with
            | zero =>
                rfl
            | succ m =>
                have hlt :
                    northZonalScalarCoeff (2 * (m + 2)) < 1 := by
                  exact northZonalScalarCoeff_even_gt_two_lt_one_aux m
                have hlt' :
                    northZonalScalarCoeff (m + 1 + 1 + (m + 1 + 1)) < 1 := by
                  simpa [two_mul, add_assoc, add_left_comm, add_comm] using hlt
                linarith
    | inr hOdd =>
        rcases hOdd with ⟨m, rfl⟩
        simp at hcoeff
  · intro hn
    subst hn
    intro r
    rw [monomial_special_average_eq_coeff_mul, northZonalScalarCoeff_two]
    simp
