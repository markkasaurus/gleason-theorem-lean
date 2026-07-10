import Mathlib
import Gleason.Finite.Polarization.BoundedQuadraticForm
import Gleason.Finite.Polarization.Definition
import Gleason.Finite.Polarization.Symmetry
import Gleason.Finite.Polarization.LeftScalar
import Gleason.Finite.Polarization.RightScalar

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

open scoped ComplexConjugate

/-- Robust inequality: `‖z‖ ≤ |re z| + |im z|` for `z : ℂ`. -/
private lemma complex_norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  have zrep : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    simpa using (Complex.re_add_im z)
  have hz : ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by
    simpa using congrArg (fun w : ℂ => ‖w‖) zrep
  have hle : ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ :=
    norm_add_le _ _
  have hre : ‖(z.re : ℂ)‖ = |z.re| := by simp [Complex.norm_real]
  have him : ‖(z.im : ℂ) * Complex.I‖ = |z.im| := by
    calc
      ‖(z.im : ℂ) * Complex.I‖ = ‖(z.im : ℂ)‖ * ‖(Complex.I : ℂ)‖ := by
        simpa using (norm_mul (z.im : ℂ) (Complex.I : ℂ))
      _ = |z.im| := by simp [Complex.norm_real, Complex.norm_I]
  calc
    ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := hz
    _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := hle
    _ = |z.re| + |z.im| := by simp [hre, him]

/-- Real abs triangle inequality via `norm_add_le`. -/
private lemma abs_add_le' (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  simpa [Real.norm_eq_abs] using (norm_add_le a b)

/-- Unit bound: if `‖x‖=‖y‖=1` then `‖polarization q x y‖ ≤ 4*C0`. -/
private lemma polarization_bound_unit
    (q : H → ℝ) (C0 : ℝ) (hC0 : 0 ≤ C0) (hC : ∀ z : H, |q z| ≤ C0 * ‖z‖ ^ 2)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖polarization q x y‖ ≤ 4 * C0 := by
  have hsum2 : (‖x‖ + ‖y‖ : ℝ) = 2 := by
    have : (1:ℝ) + 1 = 2 := by norm_num
    simpa [hx, hy] using this
  have h_add : ‖x + y‖ ≤ (2 : ℝ) := by
    calc
      ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
      _ = 2 := hsum2
  have h_sub : ‖x - y‖ ≤ (2 : ℝ) := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ = 2 := hsum2
  have hIy : ‖(Complex.I : ℂ) • y‖ = ‖y‖ := by
    calc
      ‖(Complex.I : ℂ) • y‖ = ‖(Complex.I : ℂ)‖ * ‖y‖ := by simpa using (norm_smul Complex.I y)
      _ = ‖y‖ := by simp [Complex.norm_I]
  have h_iadd : ‖x + (Complex.I : ℂ) • y‖ ≤ (2 : ℝ) := by
    calc
      ‖x + (Complex.I : ℂ) • y‖ ≤ ‖x‖ + ‖(Complex.I : ℂ) • y‖ := norm_add_le _ _
      _ = 2 := by simpa [hIy] using hsum2
  have h_isub : ‖x - (Complex.I : ℂ) • y‖ ≤ (2 : ℝ) := by
    calc
      ‖x - (Complex.I : ℂ) • y‖ ≤ ‖x‖ + ‖(Complex.I : ℂ) • y‖ := norm_sub_le _ _
      _ = 2 := by simpa [hIy] using hsum2

  have hsq (z : H) (hz : ‖z‖ ≤ (2 : ℝ)) : ‖z‖ ^ 2 ≤ (4 : ℝ) := by
    have hmul : ‖z‖ * ‖z‖ ≤ (2 : ℝ) * 2 := mul_le_mul hz hz (norm_nonneg z) (by norm_num)
    have : ‖z‖ * ‖z‖ ≤ 4 := by simpa [show (2:ℝ)*2 = 4 by norm_num] using hmul
    simpa [pow_two] using this

  have q_add : |q (x + y)| ≤ 4 * C0 := by
    have h1 : |q (x + y)| ≤ C0 * ‖x + y‖ ^ 2 := hC (x + y)
    have h2 : C0 * ‖x + y‖ ^ 2 ≤ C0 * 4 := mul_le_mul_of_nonneg_left (hsq _ h_add) hC0
    have : |q (x + y)| ≤ C0 * 4 := le_trans h1 h2
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have q_sub : |q (x - y)| ≤ 4 * C0 := by
    have h1 : |q (x - y)| ≤ C0 * ‖x - y‖ ^ 2 := hC (x - y)
    have h2 : C0 * ‖x - y‖ ^ 2 ≤ C0 * 4 := mul_le_mul_of_nonneg_left (hsq _ h_sub) hC0
    have : |q (x - y)| ≤ C0 * 4 := le_trans h1 h2
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have q_iadd : |q (x + (Complex.I : ℂ) • y)| ≤ 4 * C0 := by
    have h1 : |q (x + (Complex.I : ℂ) • y)| ≤ C0 * ‖x + (Complex.I : ℂ) • y‖ ^ 2 := hC _
    have h2 : C0 * ‖x + (Complex.I : ℂ) • y‖ ^ 2 ≤ C0 * 4 :=
      mul_le_mul_of_nonneg_left (hsq _ h_iadd) hC0
    have : |q (x + (Complex.I : ℂ) • y)| ≤ C0 * 4 := le_trans h1 h2
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have q_isub : |q (x - (Complex.I : ℂ) • y)| ≤ 4 * C0 := by
    have h1 : |q (x - (Complex.I : ℂ) • y)| ≤ C0 * ‖x - (Complex.I : ℂ) • y‖ ^ 2 := hC _
    have h2 : C0 * ‖x - (Complex.I : ℂ) • y‖ ^ 2 ≤ C0 * 4 :=
      mul_le_mul_of_nonneg_left (hsq _ h_isub) hC0
    have : |q (x - (Complex.I : ℂ) • y)| ≤ C0 * 4 := le_trans h1 h2
    simpa [mul_assoc, mul_left_comm, mul_comm] using this

  have hre_eq : (polarization q x y).re = (q (x + y) - q (x - y)) / 4 := by simp [polarization]
  have him_eq : (polarization q x y).im = (q (x + Complex.I • y) - q (x - Complex.I • y)) / 4 := by simp [polarization]

  have habs_re : |q (x + y) - q (x - y)| ≤ |q (x + y)| + |q (x - y)| := by
    simpa [sub_eq_add_neg] using abs_add_le' (q (x + y)) (-(q (x - y)))
  have hsum_re : |q (x + y)| + |q (x - y)| ≤ 8 * C0 := by
    have : |q (x + y)| + |q (x - y)| ≤ 4 * C0 + 4 * C0 := add_le_add q_add q_sub
    simpa [show 4 * C0 + 4 * C0 = 8 * C0 by ring] using this

  have hre : |(polarization q x y).re| ≤ 2 * C0 := by
    have hdiv : |q (x + y) - q (x - y)| / 4 ≤ (8 * C0) / 4 := by nlinarith [habs_re, hsum_re]
    have hdiv' : |(q (x + y) - q (x - y)) / 4| ≤ (8 * C0) / 4 := by simpa [abs_div] using hdiv
    have : |(polarization q x y).re| ≤ (8 * C0) / 4 := by simpa [hre_eq] using hdiv'
    simpa [show (8 * C0) / 4 = 2 * C0 by ring] using this

  have habs_im : |q (x + Complex.I • y) - q (x - Complex.I • y)|
      ≤ |q (x + Complex.I • y)| + |q (x - Complex.I • y)| := by
    simpa [sub_eq_add_neg] using abs_add_le' (q (x + Complex.I • y)) (-(q (x - Complex.I • y)))
  have hsum_im : |q (x + Complex.I • y)| + |q (x - Complex.I • y)| ≤ 8 * C0 := by
    have : |q (x + Complex.I • y)| + |q (x - Complex.I • y)| ≤ 4 * C0 + 4 * C0 := add_le_add q_iadd q_isub
    simpa [show 4 * C0 + 4 * C0 = 8 * C0 by ring] using this
  have him : |(polarization q x y).im| ≤ 2 * C0 := by
    have hdiv : |q (x + Complex.I • y) - q (x - Complex.I • y)| / 4 ≤ (8 * C0) / 4 := by nlinarith [habs_im, hsum_im]
    have hdiv' : |(q (x + Complex.I • y) - q (x - Complex.I • y)) / 4| ≤ (8 * C0) / 4 := by simpa [abs_div] using hdiv
    have : |(polarization q x y).im| ≤ (8 * C0) / 4 := by simpa [him_eq] using hdiv'
    simpa [show (8 * C0) / 4 = 2 * C0 by ring] using this

  have hnorm : ‖polarization q x y‖ ≤ |(polarization q x y).re| + |(polarization q x y).im| :=
    complex_norm_le_abs_re_add_abs_im (polarization q x y)
  have : ‖polarization q x y‖ ≤ 4 * C0 := by
    have : |(polarization q x y).re| + |(polarization q x y).im| ≤ 4 * C0 := by linarith [hre, him]
    exact le_trans hnorm this
  simpa using this

theorem polarization_le_norm_mul_norm (q : H → ℝ) (hq : IsBoundedQuadraticForm q) :
    ∃ C, ∀ x y : H, ‖polarization q x y‖ ≤ C * ‖x‖ * ‖y‖ := by
  classical
  rcases hq.bounded with ⟨C, hC⟩
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hCle : C ≤ C0 := le_max_left _ _
  have hC' : ∀ z : H, |q z| ≤ C0 * ‖z‖ ^ 2 := by
    intro z
    have hz := hC z
    have hz' : C * ‖z‖ ^ 2 ≤ C0 * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hCle (pow_nonneg (norm_nonneg z) 2)
    exact le_trans hz hz'

  refine ⟨4 * C0, ?_⟩
  intro x y
  by_cases hx : x = 0
  · subst hx
    simp [polarization_zero_left q hq y]
  by_cases hy : y = 0
  · subst hy
    simp [polarization_zero_right q hq x]

  have hnx : (‖x‖ : ℂ) ≠ 0 := by
    have : ‖x‖ ≠ 0 := by simpa [norm_eq_zero] using hx
    exact_mod_cast this
  have hny : (‖y‖ : ℂ) ≠ 0 := by
    have : ‖y‖ ≠ 0 := by simpa [norm_eq_zero] using hy
    exact_mod_cast this

  let x0 : H := ((‖x‖ : ℂ)⁻¹) • x
  let y0 : H := ((‖y‖ : ℂ)⁻¹) • y

  have hx0 : ‖x0‖ = 1 := by
    calc
      ‖x0‖ = ‖((‖x‖ : ℂ)⁻¹)‖ * ‖x‖ := by simp [x0, norm_smul]
      _ = (‖(‖x‖ : ℂ)‖)⁻¹ * ‖x‖ := by simp
      _ = (‖x‖)⁻¹ * ‖x‖ := by simp [Complex.norm_real]
      _ = 1 := by simpa using inv_mul_cancel₀ (by simpa [norm_eq_zero] using hx)

  have hy0 : ‖y0‖ = 1 := by
    calc
      ‖y0‖ = ‖((‖y‖ : ℂ)⁻¹)‖ * ‖y‖ := by simp [y0, norm_smul]
      _ = (‖(‖y‖ : ℂ)‖)⁻¹ * ‖y‖ := by simp
      _ = (‖y‖)⁻¹ * ‖y‖ := by simp [Complex.norm_real]
      _ = 1 := by simpa using inv_mul_cancel₀ (by simpa [norm_eq_zero] using hy)

  have hxexpr : x = (‖x‖ : ℂ) • x0 := by simp [x0, smul_smul, hnx]
  have hyexpr : y = (‖y‖ : ℂ) • y0 := by simp [y0, smul_smul, hny]

  have hunit : ‖polarization q x0 y0‖ ≤ 4 * C0 :=
    polarization_bound_unit q C0 hC0 hC' x0 y0 hx0 hy0

  have hright : polarization q x y = conj (‖y‖ : ℂ) * polarization q x y0 := by
    rw [hyexpr]
    -- `simp` sometimes prefers `↑‖‖y‖ • y0‖` over `↑‖y‖`; normalize it using `hy0`.
    have hy_scale : ‖‖y‖ • y0‖ = ‖y‖ := by
      calc
        ‖‖y‖ • y0‖ = ‖(‖y‖ : ℝ)‖ * ‖y0‖ := by
          simpa using (norm_smul (‖y‖ : ℝ) y0)
        _ = ‖y‖ * ‖y0‖ := by
          simp [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
        _ = ‖y‖ := by simpa [hy0]
    simpa [hy_scale] using (polarization_smul_right q hq (‖y‖ : ℂ) x y0)
  have hleft : polarization q x y0 = (‖x‖ : ℂ) * polarization q x0 y0 := by
    rw [hxexpr]
    -- Same normalization for the left scalar factor using `hx0`.
    have hx_scale : ‖‖x‖ • x0‖ = ‖x‖ := by
      calc
        ‖‖x‖ • x0‖ = ‖(‖x‖ : ℝ)‖ * ‖x0‖ := by
          simpa using (norm_smul (‖x‖ : ℝ) x0)
        _ = ‖x‖ * ‖x0‖ := by
          simp [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
        _ = ‖x‖ := by simpa [hx0]
    simpa [hx_scale] using (polarization_smul_left q hq (‖x‖ : ℂ) x0 y0)

  have : ‖polarization q x y‖ ≤ (4 * C0) * ‖x‖ * ‖y‖ := by
    calc
      ‖polarization q x y‖
          = ‖conj (‖y‖ : ℂ)‖ * ‖(‖x‖ : ℂ)‖ * ‖polarization q x0 y0‖ := by
              simp [hright, hleft, norm_mul, mul_assoc]
      _ ≤ ‖conj (‖y‖ : ℂ)‖ * ‖(‖x‖ : ℂ)‖ * (4 * C0) := by
              have hn : 0 ≤ ‖conj (‖y‖ : ℂ)‖ * ‖(‖x‖ : ℂ)‖ :=
                mul_nonneg (norm_nonneg _) (norm_nonneg _)
              exact mul_le_mul_of_nonneg_left hunit hn
      _ = (4 * C0) * ‖x‖ * ‖y‖ := by
              simp [Complex.norm_real, mul_assoc, mul_left_comm, mul_comm]
  simpa [mul_assoc, mul_left_comm, mul_comm] using this
