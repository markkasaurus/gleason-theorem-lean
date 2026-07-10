import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic

noncomputable section

open Real

/-- The circle frame-function condition in angular coordinates. -/
def circleFrameFunction (f : ℝ → ℝ) : Prop :=
  ∃ W : ℝ, ∀ θ : ℝ, f θ + f (θ + π / 2) = W

/-- The `n`th cosine mode on the unit circle. -/
def circleCosMode (n : ℕ) : ℝ → ℝ :=
  fun θ => Real.cos ((n : ℝ) * θ)

lemma circleFrameFunction_const (c : ℝ) : circleFrameFunction (fun _ : ℝ => c) := by
  refine ⟨2 * c, ?_⟩
  intro θ
  ring

lemma circleFrameFunction_add {f g : ℝ → ℝ}
    (hf : circleFrameFunction f) (hg : circleFrameFunction g) :
    circleFrameFunction (fun θ => f θ + g θ) := by
  rcases hf with ⟨Wf, hWf⟩
  rcases hg with ⟨Wg, hWg⟩
  refine ⟨Wf + Wg, ?_⟩
  intro θ
  linarith [hWf θ, hWg θ]

lemma circleFrameFunction_neg {f : ℝ → ℝ}
    (hf : circleFrameFunction f) :
    circleFrameFunction (fun θ => -f θ) := by
  rcases hf with ⟨W, hW⟩
  refine ⟨-W, ?_⟩
  intro θ
  linarith [hW θ]

lemma circleFrameFunction_sub {f g : ℝ → ℝ}
    (hf : circleFrameFunction f) (hg : circleFrameFunction g) :
    circleFrameFunction (fun θ => f θ - g θ) := by
  simpa [sub_eq_add_neg] using circleFrameFunction_add hf (circleFrameFunction_neg hg)

lemma circleFrameFunction_smul (c : ℝ) {f : ℝ → ℝ}
    (hf : circleFrameFunction f) :
    circleFrameFunction (fun θ => c * f θ) := by
  rcases hf with ⟨W, hW⟩
  refine ⟨c * W, ?_⟩
  intro θ
  calc
    c * f θ + c * f (θ + π / 2) = c * (f θ + f (θ + π / 2)) := by ring
    _ = c * W := by rw [hW θ]

lemma circleFrameFunction_comp_add_const {f : ℝ → ℝ}
    (hf : circleFrameFunction f) (a : ℝ) :
    circleFrameFunction (fun θ => f (θ + a)) := by
  rcases hf with ⟨W, hW⟩
  refine ⟨W, ?_⟩
  intro θ
  simpa [add_assoc, add_left_comm, add_comm] using hW (θ + a)

lemma circleCosMode_frame_zero : circleFrameFunction (circleCosMode 0) := by
  refine ⟨2, ?_⟩
  intro θ
  simp [circleCosMode]
  norm_num

lemma circleCosMode_frame_of_mod_four_eq_two {n : ℕ} (hn : n % 4 = 2) :
    circleFrameFunction (circleCosMode n) := by
  have hk : n = 4 * (n / 4) + 2 := by
    have hdiv := Nat.mod_add_div n 4
    omega
  refine ⟨0, ?_⟩
  intro θ
  rw [hk]
  have hcos :
      Real.cos (((4 * (n / 4) + 2 : ℕ) : ℝ) * (θ + π / 2)) =
        -Real.cos (((4 * (n / 4) + 2 : ℕ) : ℝ) * θ) := by
    have hhalf :
        (((4 * (n / 4) + 2 : ℕ) : ℝ) * (π / 2)) =
          (((2 * (n / 4) + 1 : ℕ) : ℝ) * π) := by
      have hnat : (4 * (n / 4) + 2 : ℕ) = 2 * (2 * (n / 4) + 1) := by omega
      rw [hnat, Nat.cast_mul]
      ring
    have harg :
        (((4 * (n / 4) + 2 : ℕ) : ℝ) * (θ + π / 2)) =
          (((4 * (n / 4) + 2 : ℕ) : ℝ) * θ) + ((2 * (n / 4) + 1 : ℕ) : ℝ) * π := by
      rw [mul_add, hhalf]
    rw [harg, Real.cos_add_nat_mul_pi]
    have hpow : (-1 : ℝ) ^ (2 * (n / 4) + 1) = -1 := by
      rw [neg_one_pow_eq_pow_mod_two]
      norm_num
    simp [hpow]
  unfold circleCosMode
  rw [hcos]
  ring

lemma circleCosMode_eq_zero_weight_of_pos {n : ℕ} (hn : 0 < n)
    (hframe : circleFrameFunction (circleCosMode n)) :
    Real.cos ((n : ℝ) * (π / 2)) = -1 ∧ Real.sin ((n : ℝ) * (π / 2)) = 0 := by
  rcases hframe with ⟨W, hW⟩
  have h0 := hW 0
  have hπ := hW ((π : ℝ) / n)
  have hπ2 := hW ((π : ℝ) / (2 * n))
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hW0 : W = 1 + Real.cos ((n : ℝ) * (π / 2)) := by
    simpa [circleCosMode, hn0] using h0.symm
  have hWπ :
      W = -1 - Real.cos ((n : ℝ) * (π / 2)) := by
    have hcalc :
        Real.cos ((n : ℝ) * (π / n)) + Real.cos ((n : ℝ) * (π / n + π / 2))
          = -1 - Real.cos ((n : ℝ) * (π / 2)) := by
      have h1 : (n : ℝ) * (π / n) = π := by field_simp [hn0]
      have h2 : (n : ℝ) * (π / n + π / 2) = π + (n : ℝ) * (π / 2) := by
        field_simp [hn0]
      rw [h1, h2, Real.cos_pi, add_comm π _, Real.cos_add_pi]
      ring
    calc
      W = Real.cos ((n : ℝ) * (π / n)) + Real.cos ((n : ℝ) * (π / n + π / 2)) := by
            simpa [circleCosMode] using hπ.symm
      _ = -1 - Real.cos ((n : ℝ) * (π / 2)) := hcalc
  have hcos : Real.cos ((n : ℝ) * (π / 2)) = -1 := by
    linarith [hW0, hWπ]
  have hWzero : W = 0 := by linarith [hW0, hcos]
  have hsin : Real.sin ((n : ℝ) * (π / 2)) = 0 := by
    have hcalc :
        Real.cos ((n : ℝ) * (π / (2 * n))) +
            Real.cos ((n : ℝ) * (π / (2 * n) + π / 2))
          = -Real.sin ((n : ℝ) * (π / 2)) := by
      have h1 : (n : ℝ) * (π / (2 * n)) = π / 2 := by
        field_simp [hn0]
      have h2 : (n : ℝ) * (π / (2 * n) + π / 2) = π / 2 + (n : ℝ) * (π / 2) := by
        field_simp [hn0]
      rw [h1, h2, Real.cos_pi_div_two, add_comm (π / 2) _, Real.cos_add_pi_div_two]
      ring
    have : W = -Real.sin ((n : ℝ) * (π / 2)) := by
      calc
        W =
            Real.cos ((n : ℝ) * (π / (2 * n))) +
              Real.cos ((n : ℝ) * (π / (2 * n) + π / 2)) := by
                simpa [circleCosMode] using hπ2.symm
        _ = -Real.sin ((n : ℝ) * (π / 2)) := hcalc
    linarith
  exact ⟨hcos, hsin⟩

lemma mod_four_eq_two_of_cos_neg_one_and_sin_zero {n : ℕ}
    (hcos : Real.cos ((n : ℝ) * (π / 2)) = -1)
    (hsin : Real.sin ((n : ℝ) * (π / 2)) = 0) :
    n % 4 = 2 := by
  have hmod2 : n % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · exact h0
    · exfalso
      have hk : n = 2 * (n / 2) + 1 := by
        have hdiv := Nat.mod_add_div n 2
        omega
      rw [hk] at hsin
      have harg :
          (((2 * (n / 2) + 1 : ℕ) : ℝ) * (π / 2)) =
            π / 2 + ((n / 2 : ℕ) : ℝ) * π := by
        have hnat : (2 * (n / 2) + 1 : ℕ) = 1 + 2 * (n / 2) := by omega
        rw [hnat, Nat.cast_add, Nat.cast_mul]
        ring
      have : Real.sin (((2 * (n / 2) + 1 : ℕ) : ℝ) * (π / 2)) = (-1 : ℝ) ^ (n / 2) := by
        calc
          Real.sin (((2 * (n / 2) + 1 : ℕ) : ℝ) * (π / 2))
              = Real.sin (π / 2 + ((n / 2 : ℕ) : ℝ) * π) := by rw [harg]
          _ = (-1 : ℝ) ^ (n / 2) * Real.sin (π / 2) := by
                rw [Real.sin_add_nat_mul_pi]
          _ = (-1 : ℝ) ^ (n / 2) := by simp
      rw [this] at hsin
      have hpow : ((-1 : ℝ) ^ (n / 2)) ≠ 0 := by simp
      exact hpow hsin
  have hm : n = 2 * (n / 2) := by
    have hdiv := Nat.mod_add_div n 2
    omega
  have hmodd : (n / 2) % 2 = 1 := by
    rw [hm] at hcos
    have hcos' : Real.cos (((n / 2 : ℕ) : ℝ) * π) = -1 := by
      have harg :
          (((n / 2 : ℕ) : ℝ) * π) = (((2 * (n / 2) : ℕ) : ℝ) * (π / 2)) := by
        rw [Nat.cast_mul]
        ring
      calc
        Real.cos (((n / 2 : ℕ) : ℝ) * π)
            = Real.cos (((2 * (n / 2) : ℕ) : ℝ) * (π / 2)) := by rw [harg]
        _ = -1 := by simpa using hcos
    have hpow : (-1 : ℝ) ^ (n / 2) = -1 := by
      simpa [Real.cos_nat_mul_pi] using hcos'
    rcases Nat.mod_two_eq_zero_or_one (n / 2) with hm0 | hm1
    · exfalso
      have : (-1 : ℝ) ^ (n / 2) = 1 := by
        rw [neg_one_pow_eq_pow_mod_two, hm0]
        norm_num
      linarith [hpow]
    · exact hm1
  have hdiv := Nat.mod_add_div (n / 2) 2
  omega

theorem circleCosMode_frame_iff (n : ℕ) :
    circleFrameFunction (circleCosMode n) ↔ n = 0 ∨ n ≡ 2 [MOD 4] := by
  constructor
  · intro hframe
    by_cases hn : n = 0
    · exact Or.inl hn
    · right
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rcases circleCosMode_eq_zero_weight_of_pos hnpos hframe with ⟨hcos, hsin⟩
      have hmod : n % 4 = 2 := mod_four_eq_two_of_cos_neg_one_and_sin_zero hcos hsin
      simpa [Nat.ModEq] using hmod
  · rintro (rfl | hmod)
    · exact circleCosMode_frame_zero
    · have hmod' : n % 4 = 2 := by simpa [Nat.ModEq] using hmod
      exact circleCosMode_frame_of_mod_four_eq_two hmod'

theorem circleCosMode_phase_frame_iff (n : ℕ) (φ : ℝ) :
    circleFrameFunction (fun θ => Real.cos ((n : ℝ) * θ + φ)) ↔
      n = 0 ∨ n ≡ 2 [MOD 4] := by
  by_cases hn : n = 0
  · subst hn
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      simpa using circleFrameFunction_const (Real.cos φ)
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hphase :
        (fun θ => Real.cos ((n : ℝ) * θ + φ)) =
          fun θ => circleCosMode n (θ + φ / n) := by
      funext θ
      unfold circleCosMode
      congr 1
      field_simp [hn0]
    have hunphase :
        circleCosMode n = fun θ => Real.cos ((n : ℝ) * (θ - φ / n) + φ) := by
      funext θ
      unfold circleCosMode
      congr 1
      field_simp [hn0]
      ring
    constructor
    · intro hframe
      have hbase : circleFrameFunction (circleCosMode n) := by
        simpa [hunphase, sub_eq_add_neg, neg_div] using
          circleFrameFunction_comp_add_const hframe (-φ / n)
      exact (circleCosMode_frame_iff n).1 hbase
    · intro hmod
      have hbase : circleFrameFunction (circleCosMode n) := (circleCosMode_frame_iff n).2 hmod
      have hshift :
          circleFrameFunction (fun θ => circleCosMode n (θ + φ / n)) :=
        circleFrameFunction_comp_add_const hbase (φ / n)
      simpa [hphase] using hshift
