import SphericalHarmonics.NorthFixedAmbient
import SphericalHarmonics.FiniteDimensional
import SphericalHarmonics.Fischer
import SphericalHarmonics.Zonal
import SphericalHarmonics.RotationInvariant
import SphericalHarmonics.SectorOrthogonality
import Mathlib.LinearAlgebra.Dimension.Constructions

open scoped BigOperators

noncomputable section

namespace SphericalHarmonics

/-- The ambient harmonic degree-`n` slice fixed by all north-axis rotations. -/
def northFixedAmbientHarmonicSubmodule (n : ℕ) : Submodule ℝ Poly3 where
  carrier := {p | p ∈ harmonicHomogeneousSubmodule n ∧
    ∀ t : ℝ, (rotation01 t).compPolynomial p = p}
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, ?_⟩
    intro t
    simp
  add_mem' hp hq := by
    refine ⟨Submodule.add_mem _ hp.1 hq.1, ?_⟩
    intro t
    simp [hp.2 t, hq.2 t]
  smul_mem' c p hp := by
    refine ⟨Submodule.smul_mem _ c hp.1, ?_⟩
    intro t
    simp [hp.2 t]

@[simp] theorem mem_northFixedAmbientHarmonicSubmodule_iff {n : ℕ} {p : Poly3} :
    p ∈ northFixedAmbientHarmonicSubmodule n ↔
      p ∈ harmonicHomogeneousSubmodule n ∧
      ∀ t : ℝ, (rotation01 t).compPolynomial p = p := by
  rfl

noncomputable instance finiteDimensional_northFixedAmbientHarmonicSubmodule (n : ℕ) :
    FiniteDimensional ℝ (northFixedAmbientHarmonicSubmodule n) :=
  Submodule.finiteDimensional_of_le
    (show northFixedAmbientHarmonicSubmodule n ≤ harmonicHomogeneousSubmodule n from
      fun _ hp => hp.1)

/-- The monomial exponent `x^a y^b z^c`. -/
def tripleExp (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

@[simp] theorem tripleExp_apply_zero (a b c : ℕ) : tripleExp a b c 0 = a := by
  simp [tripleExp]

@[simp] theorem tripleExp_apply_one (a b c : ℕ) : tripleExp a b c 1 = b := by
  simp [tripleExp]

@[simp] theorem tripleExp_apply_two (a b c : ℕ) : tripleExp a b c 2 = c := by
  simp [tripleExp]

theorem tripleExp_degree (a b c : ℕ) : (tripleExp a b c).degree = a + b + c := by
  rw [Finsupp.degree_apply]
  calc
    (tripleExp a b c).sum (fun _ e ↦ e) = ∑ i : Fin 3, tripleExp a b c i := by
      rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
    _ = a + b + c := by
      simp [tripleExp, Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]

theorem coeff_eq_zero_of_isHomogeneous_of_ne_degree {n a b c : ℕ} {p : Poly3}
    (hp : p.IsHomogeneous n) (hdeg : a + b + c ≠ n) :
    MvPolynomial.coeff (tripleExp a b c) p = 0 := by
  apply hp.coeff_eq_zero
  simpa [tripleExp_degree] using hdeg

lemma angularDeriv01_eq_zero_of_isHomogeneous_of_rotation01_compPolynomial_eq_self
    {n : ℕ} {p : Poly3} (hp : p.IsHomogeneous n)
    (hfix : ∀ t : ℝ, (rotation01 t).compPolynomial p = p) :
    angularDeriv 0 1 p = 0 := by
  apply MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero (angularDeriv_isHomogeneous hp)
  intro x
  let xE : E3 := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm x
  have hconst : ∀ t : ℝ, MvPolynomial.eval (rot01Point t xE).ofLp p = MvPolynomial.eval x p := by
    intro t
    have h := congrArg (fun q : Poly3 => MvPolynomial.eval xE.ofLp q) (hfix t)
    calc
      MvPolynomial.eval (rot01Point t xE).ofLp p
          = MvPolynomial.eval xE.ofLp ((rotation01 t).compPolynomial p) := by
              symm
              simpa [rotation01_apply] using (Rotation.eval_compPolynomial (rotation01 t) p xE)
      _ = MvPolynomial.eval xE.ofLp p := h
      _ = MvPolynomial.eval x p := by simp [xE]
  have hderiv := hasDerivAt_eval_rot01Point p xE 0
  have hfun :
      (fun t : ℝ => MvPolynomial.eval (rot01Point t xE).ofLp p) =
        fun _ : ℝ => MvPolynomial.eval x p := by
    funext t
    exact hconst t
  have hconstDeriv :
      HasDerivAt (fun t : ℝ => MvPolynomial.eval (rot01Point t xE).ofLp p) 0 0 := by
    simpa [hfun] using (hasDerivAt_const 0 (MvPolynomial.eval x p))
  have := hderiv.unique hconstDeriv
  simpa [xE, rot01Point_zero] using this

theorem angularDeriv01_eq_zero_of_mem_northFixedAmbientHarmonicSubmodule
    {n : ℕ} {p : Poly3} (hp : p ∈ northFixedAmbientHarmonicSubmodule n) :
    angularDeriv 0 1 p = 0 := by
  refine angularDeriv01_eq_zero_of_isHomogeneous_of_rotation01_compPolynomial_eq_self
    (n := n) ?_ hp.2
  exact (MvPolynomial.mem_homogeneousSubmodule n p).mp hp.1.1

lemma tripleExp_sub_zero_add_one (a b c : ℕ) :
    (tripleExp (a + 1) (b + 1) c - Finsupp.single 0 1) + Finsupp.single 1 1 =
      tripleExp a (b + 2) c := by
  ext i
  fin_cases i <;> simp [tripleExp]

lemma tripleExp_sub_one_add_zero (a b c : ℕ) :
    (tripleExp (a + 1) (b + 1) c - Finsupp.single 1 1) + Finsupp.single 0 1 =
      tripleExp (a + 2) b c := by
  ext i
  fin_cases i <;> simp [tripleExp]

lemma tripleExp_add_zero_twice (a c : ℕ) :
    tripleExp a 0 c + Finsupp.single 0 1 + Finsupp.single 0 1 = tripleExp (a + 2) 0 c := by
  ext i
  fin_cases i <;> simp [tripleExp, add_assoc, add_left_comm, add_comm]

lemma tripleExp_add_one_twice (a c : ℕ) :
    tripleExp a 0 c + Finsupp.single 1 1 + Finsupp.single 1 1 = tripleExp a 2 c := by
  ext i
  fin_cases i <;> simp [tripleExp, add_assoc, add_left_comm, add_comm]

lemma tripleExp_add_two_twice (a c : ℕ) :
    tripleExp a 0 c + Finsupp.single 2 1 + Finsupp.single 2 1 = tripleExp a 0 (c + 2) := by
  ext i
  fin_cases i <;> simp [tripleExp, add_assoc, add_left_comm, add_comm]

lemma coeff_angularDeriv01_edge_x (p : Poly3) (a c : ℕ) :
    MvPolynomial.coeff (tripleExp (a + 1) 0 c) (angularDeriv 0 1 p) =
      MvPolynomial.coeff (tripleExp a 1 c) p := by
  have h1 : ¬ (1 : Fin 3) ∈ (tripleExp (a + 1) 0 c).support := by
    simp [tripleExp]
  simp [angularDeriv, MvPolynomial.coeff_X_mul', tripleExp, h1, coeff_pderiv]
  congr 1
  ext i
  fin_cases i <;> simp [tripleExp]

lemma coeff_angularDeriv01_edge_y (p : Poly3) (b c : ℕ) :
    MvPolynomial.coeff (tripleExp 0 (b + 1) c) (angularDeriv 0 1 p) =
      -MvPolynomial.coeff (tripleExp 1 b c) p := by
  have h0 : ¬ (0 : Fin 3) ∈ (tripleExp 0 (b + 1) c).support := by
    simp [tripleExp]
  simp [angularDeriv, MvPolynomial.coeff_X_mul', tripleExp, h0, coeff_pderiv]
  congr 1
  ext i
  fin_cases i <;> simp [tripleExp]

lemma coeff_angularDeriv01_interior (p : Poly3) (a b c : ℕ) :
    MvPolynomial.coeff (tripleExp (a + 1) (b + 1) c) (angularDeriv 0 1 p) =
      (b + 2 : ℝ) * MvPolynomial.coeff (tripleExp a (b + 2) c) p -
      (a + 2 : ℝ) * MvPolynomial.coeff (tripleExp (a + 2) b c) p := by
  have h0 : (0 : Fin 3) ∈ (tripleExp (a + 1) (b + 1) c).support := by
    simp [tripleExp]
  have h1 : (1 : Fin 3) ∈ (tripleExp (a + 1) (b + 1) c).support := by
    simp [tripleExp]
  have hx :
      MvPolynomial.coeff (tripleExp (a + 1) (b + 1) c) (MvPolynomial.X 0 * MvPolynomial.pderiv 1 p) =
        (b + 2 : ℝ) * MvPolynomial.coeff (tripleExp a (b + 2) c) p := by
    rw [MvPolynomial.coeff_X_mul']
    simp [h0, coeff_pderiv, tripleExp_sub_zero_add_one]
    left
    ring
  have hy :
      MvPolynomial.coeff (tripleExp (a + 1) (b + 1) c) (MvPolynomial.X 1 * MvPolynomial.pderiv 0 p) =
        (a + 2 : ℝ) * MvPolynomial.coeff (tripleExp (a + 2) b c) p := by
    rw [MvPolynomial.coeff_X_mul']
    simp [h1, coeff_pderiv, tripleExp_sub_one_add_zero]
    left
    ring
  simp [angularDeriv, hx, hy]

lemma coeff_laplacian_axis_xz (p : Poly3) (a c : ℕ) :
    MvPolynomial.coeff (tripleExp a 0 c) (laplacian p) =
      ((a + 2 : ℝ) * (a + 1 : ℝ)) * MvPolynomial.coeff (tripleExp (a + 2) 0 c) p +
      (2 : ℝ) * MvPolynomial.coeff (tripleExp a 2 c) p +
      ((c + 2 : ℝ) * (c + 1 : ℝ)) * MvPolynomial.coeff (tripleExp a 0 (c + 2)) p := by
  unfold laplacian
  simp [Fin.sum_univ_three, coeff_pderiv, tripleExp_add_zero_twice, tripleExp_add_one_twice,
    tripleExp_add_two_twice]
  ring

lemma coeff_step_of_mem_northFixedAmbientHarmonicSubmodule
    {n m i c : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n)
    (hi : i + 2 ≤ m) :
    ((i + 2 : ℝ)) * MvPolynomial.coeff (tripleExp (m - i - 2) (i + 2) c) p =
      (↑m - ↑i) * MvPolynomial.coeff (tripleExp (m - i) i c) p := by
  have hderiv : angularDeriv 0 1 p = 0 :=
    angularDeriv01_eq_zero_of_mem_northFixedAmbientHarmonicSubmodule hp
  have hcoeff := coeff_angularDeriv01_interior p (m - i - 2) i c
  have hm : (m - i - 2) + 2 = m - i := by
    omega
  have hm1 : 1 + (m - i - 2) = m - i - 1 := by
    omega
  have hmi : i ≤ m := by
    omega
  have hsub : (((m - i : ℕ) : ℝ)) = (↑m - ↑i) := by
    simp [Nat.cast_sub hmi]
  have hcast : (((m - i - 2 : ℕ) : ℝ) + 2) = (↑m - ↑i) := by
    calc
      (((m - i - 2 : ℕ) : ℝ) + 2) = ((m - i : ℕ) : ℝ) := by
        exact_mod_cast hm
      _ = (↑m - ↑i) := hsub
  have hcoeff' :
      MvPolynomial.coeff (tripleExp (m - i - 1) (i + 1) c) (angularDeriv 0 1 p) =
        ((i + 2 : ℝ)) * MvPolynomial.coeff (tripleExp (m - i - 2) (i + 2) c) p -
          (↑m - ↑i) * MvPolynomial.coeff (tripleExp (m - i) i c) p := by
    simpa [hm, hm1, hcast, Nat.cast_add, Nat.cast_ofNat, add_assoc, add_left_comm, add_comm] using hcoeff
  rw [hderiv] at hcoeff'
  have hzero :
      0 =
        ((i + 2 : ℝ)) * MvPolynomial.coeff (tripleExp (m - i - 2) (i + 2) c) p -
          (↑m - ↑i) * MvPolynomial.coeff (tripleExp (m - i) i c) p := by
    simpa using hcoeff'
  exact sub_eq_zero.mp hzero.symm

lemma coeff_eq_zero_of_second_one_of_mem_northFixedAmbientHarmonicSubmodule
    {n a c : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n) :
    MvPolynomial.coeff (tripleExp a 1 c) p = 0 := by
  have hderiv : angularDeriv 0 1 p = 0 :=
    angularDeriv01_eq_zero_of_mem_northFixedAmbientHarmonicSubmodule hp
  have hcoeff := coeff_angularDeriv01_edge_x p a c
  rw [hderiv] at hcoeff
  simpa using hcoeff.symm

lemma coeff_eq_zero_of_first_one_of_mem_northFixedAmbientHarmonicSubmodule
    {n b c : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n) :
    MvPolynomial.coeff (tripleExp 1 b c) p = 0 := by
  have hderiv : angularDeriv 0 1 p = 0 :=
    angularDeriv01_eq_zero_of_mem_northFixedAmbientHarmonicSubmodule hp
  have hcoeff := coeff_angularDeriv01_edge_y p b c
  rw [hderiv] at hcoeff
  have : -MvPolynomial.coeff (tripleExp 1 b c) p = 0 := by simpa using hcoeff
  linarith

lemma coeff_eq_zero_of_odd_second_of_mem_northFixedAmbientHarmonicSubmodule
    {n m k c : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n)
    (hk : 2 * k + 1 ≤ m) :
    MvPolynomial.coeff (tripleExp (m - (2 * k + 1)) (2 * k + 1) c) p = 0 := by
  induction k with
  | zero =>
      simpa using
        coeff_eq_zero_of_second_one_of_mem_northFixedAmbientHarmonicSubmodule
          (hp := hp) (a := m - 1) (c := c)
  | succ k ih =>
      have hk' : 2 * k + 1 ≤ m := by omega
      have hi : (2 * k + 1) + 2 ≤ m := by omega
      have hstep :=
        coeff_step_of_mem_northFixedAmbientHarmonicSubmodule
          (hp := hp) (m := m) (i := 2 * k + 1) (c := c) hi
      have hprev :
          MvPolynomial.coeff (tripleExp (m - (2 * k + 1)) (2 * k + 1) c) p = 0 :=
        ih hk'
      have hzero :
          (((2 * k + 1 : ℕ) : ℝ) + 2) *
              MvPolynomial.coeff (tripleExp (m - (2 * k + 1) - 2) ((2 * k + 1) + 2) c) p = 0 := by
        rw [hstep, hprev, mul_zero]
      have hfac : ((((2 * k + 1 : ℕ) : ℝ) + 2)) ≠ 0 := by positivity
      have hnew :
          MvPolynomial.coeff (tripleExp (m - (2 * k + 1) - 2) ((2 * k + 1) + 2) c) p = 0 :=
        (mul_eq_zero.mp hzero).resolve_left hfac
      simpa [two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using hnew

lemma coeff_eq_zero_of_odd_first_of_mem_northFixedAmbientHarmonicSubmodule
    {n m k c : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n)
    (hk : 2 * k + 1 ≤ m) :
    MvPolynomial.coeff (tripleExp (2 * k + 1) (m - (2 * k + 1)) c) p = 0 := by
  induction k with
  | zero =>
      simpa [Nat.zero_mul, Nat.zero_add] using
        coeff_eq_zero_of_first_one_of_mem_northFixedAmbientHarmonicSubmodule
          (hp := hp) (b := m - 1) (c := c)
  | succ k ih =>
      have hk' : 2 * k + 1 ≤ m := by omega
      have hi : (m - (2 * k + 3)) + 2 ≤ m := by omega
      have hstep :=
        coeff_step_of_mem_northFixedAmbientHarmonicSubmodule
          (hp := hp) (m := m) (i := m - (2 * k + 3)) (c := c) hi
      have hprev :
          MvPolynomial.coeff (tripleExp (2 * k + 1) (m - (2 * k + 1)) c) p = 0 :=
        ih hk'
      have hmle : m - (2 * k + 3) ≤ m := by omega
      have hm : m - (m - (2 * k + 3)) = 2 * k + 3 := by omega
      have hm' : m - (m - (2 * k + 3)) - 2 = 2 * k + 1 := by omega
      have hm'' : (m - (2 * k + 3)) + 2 = m - (2 * k + 1) := by omega
      have hstep' :
          (↑(m - (2 * k + 3)) + 2) *
              MvPolynomial.coeff (tripleExp (2 * k + 1) (m - (2 * k + 1)) c) p =
            (↑m - ↑(m - (2 * k + 3))) *
              MvPolynomial.coeff (tripleExp (2 * k + 3) (m - (2 * k + 3)) c) p := by
        simpa [hm, hm', hm''] using hstep
      have hzero :
          (↑m - ↑(m - (2 * k + 3))) *
              MvPolynomial.coeff
                (tripleExp (2 * k + 3) (m - (2 * k + 3)) c) p = 0 := by
        rw [← hstep', hprev]
        simp
      have hscalar :
          (↑m - ↑(m - (2 * k + 3)) : ℝ) = (2 * k + 3 : ℝ) := by
        calc
          (↑m - ↑(m - (2 * k + 3)) : ℝ)
              = (((m - (m - (2 * k + 3)) : ℕ) : ℝ)) := by
                  rw [Nat.cast_sub hmle]
          _ = (2 * k + 3 : ℝ) := by
                exact_mod_cast hm
      have hfac : (↑m - ↑(m - (2 * k + 3)) : ℝ) ≠ 0 := by
        rw [hscalar]
        positivity
      have hnew :
          MvPolynomial.coeff
            (tripleExp (2 * k + 3) (m - (2 * k + 3)) c) p = 0 :=
        (mul_eq_zero.mp hzero).resolve_left hfac
      exact hnew

lemma coeff_head_recurrence_of_mem_northFixedAmbientHarmonicSubmodule
    {n a c : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n) :
    ((a + 2 : ℝ) ^ 2) * MvPolynomial.coeff (tripleExp (a + 2) 0 c) p +
      ((c + 2 : ℝ) * (c + 1 : ℝ)) * MvPolynomial.coeff (tripleExp a 0 (c + 2)) p = 0 := by
  have hharm : laplacian p = 0 := hp.1.2
  have haxis := coeff_laplacian_axis_xz p a c
  rw [hharm] at haxis
  have hstep :=
    coeff_step_of_mem_northFixedAmbientHarmonicSubmodule
      (hp := hp) (m := a + 2) (i := 0) (c := c) (by omega)
  have hstep' :
      (2 : ℝ) * MvPolynomial.coeff (tripleExp a 2 c) p =
        (a + 2 : ℝ) * MvPolynomial.coeff (tripleExp (a + 2) 0 c) p := by
    simpa using hstep
  rw [hstep'] at haxis
  have hcombine :
      (a + 2 : ℝ) * (a + 1 : ℝ) * MvPolynomial.coeff (tripleExp (a + 2) 0 c) p +
          (a + 2 : ℝ) * MvPolynomial.coeff (tripleExp (a + 2) 0 c) p =
        ((a + 2 : ℝ) ^ 2) * MvPolynomial.coeff (tripleExp (a + 2) 0 c) p := by
    ring
  rw [hcombine] at haxis
  simpa using haxis.symm

lemma coeff_eq_zero_of_even_second_of_head_zero_of_mem_northFixedAmbientHarmonicSubmodule
    {n m k c : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n)
    (hk : 2 * k ≤ m)
    (hhead : MvPolynomial.coeff (tripleExp m 0 c) p = 0) :
    MvPolynomial.coeff (tripleExp (m - 2 * k) (2 * k) c) p = 0 := by
  induction k with
  | zero =>
      simpa [Nat.zero_mul, Nat.sub_zero] using hhead
  | succ k ih =>
      have hk' : 2 * k ≤ m := by omega
      have hprev :
          MvPolynomial.coeff (tripleExp (m - 2 * k) (2 * k) c) p = 0 :=
        ih hk'
      have hi : 2 * k + 2 ≤ m := by omega
      have hstep :=
        coeff_step_of_mem_northFixedAmbientHarmonicSubmodule
          (hp := hp) (m := m) (i := 2 * k) (c := c) hi
      have hzero :
          (↑(2 * k) + 2) *
              MvPolynomial.coeff (tripleExp (m - 2 * k - 2) (2 * k + 2) c) p = 0 := by
        rw [hstep, hprev, mul_zero]
      have hfac : (↑(2 * k) + 2 : ℝ) ≠ 0 := by positivity
      have hnew :
          MvPolynomial.coeff (tripleExp (m - 2 * k - 2) (2 * k + 2) c) p = 0 :=
        (mul_eq_zero.mp hzero).resolve_left hfac
      simpa [two_mul, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using hnew

lemma head_coeff_eq_zero_of_top_zero_of_mem_northFixedAmbientHarmonicSubmodule
    {n k : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n)
    (hk : 2 * k ≤ n)
    (htop : MvPolynomial.coeff (tripleExp 0 0 n) p = 0) :
    MvPolynomial.coeff (tripleExp (2 * k) 0 (n - 2 * k)) p = 0 := by
  induction k with
  | zero =>
      simpa [Nat.zero_mul, Nat.sub_zero] using htop
  | succ k ih =>
      have hk' : 2 * k ≤ n := by omega
      have hprev :
          MvPolynomial.coeff (tripleExp (2 * k) 0 (n - 2 * k)) p = 0 :=
        ih hk'
      have hrec :=
        coeff_head_recurrence_of_mem_northFixedAmbientHarmonicSubmodule
          (hp := hp) (a := 2 * k) (c := n - (2 * k + 2))
      have hc : (n - (2 * k + 2)) + 2 = n - 2 * k := by
        omega
      have hzero :
          ((2 * k + 2 : ℝ) ^ 2) *
              MvPolynomial.coeff (tripleExp (2 * k + 2) 0 (n - (2 * k + 2))) p = 0 := by
        rw [hc, hprev, mul_zero, add_zero] at hrec
        simpa [Nat.cast_mul, Nat.cast_ofNat, two_mul, add_assoc, add_left_comm, add_comm] using hrec
      have hfac : ((2 * k + 2 : ℝ) ^ 2) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hzero).resolve_left hfac

lemma tripleExp_eq_self_of_finsupp (d : Fin 3 →₀ ℕ) :
    tripleExp (d 0) (d 1) (d 2) = d := by
  ext i
  fin_cases i <;> simp [tripleExp]

lemma coeff_eq_zero_of_top_zero_of_mem_northFixedAmbientHarmonicSubmodule
    {n a b c : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n)
    (hdeg : a + b + c = n)
    (htop : MvPolynomial.coeff (tripleExp 0 0 n) p = 0) :
    MvPolynomial.coeff (tripleExp a b c) p = 0 := by
  rcases Nat.even_or_odd b with hb | hb
  · rcases Nat.even_or_odd a with ha | ha
    · rcases hb with ⟨kb, rfl⟩
      rcases ha with ⟨ka, rfl⟩
      have hkhead : 2 * (ka + kb) ≤ n := by
        omega
      have hhead :=
        head_coeff_eq_zero_of_top_zero_of_mem_northFixedAmbientHarmonicSubmodule
          (hp := hp) (k := ka + kb) hkhead htop
      have hc : c = n - 2 * (ka + kb) := by
        omega
      have hhead' :
          MvPolynomial.coeff (tripleExp (2 * (ka + kb)) 0 c) p = 0 := by
        simpa [hc, two_mul, add_assoc, add_left_comm, add_comm] using hhead
      have hk : 2 * kb ≤ 2 * (ka + kb) := by
        omega
      have hslice :=
        coeff_eq_zero_of_even_second_of_head_zero_of_mem_northFixedAmbientHarmonicSubmodule
          (hp := hp) (m := 2 * (ka + kb)) (k := kb) (c := c) hk hhead'
      have hm1 : 2 * (ka + kb) - (kb + kb) = ka + ka := by
        omega
      have hm2 : 2 * kb = kb + kb := by
        ring
      simpa [hm1, hm2] using hslice
    · rcases ha with ⟨ka, rfl⟩
      have hk : 2 * ka + 1 ≤ 2 * ka + 1 + b := by omega
      have hzero :=
        coeff_eq_zero_of_odd_first_of_mem_northFixedAmbientHarmonicSubmodule
          (hp := hp) (m := 2 * ka + 1 + b) (k := ka) (c := c) hk
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using hzero
  · rcases hb with ⟨kb, rfl⟩
    have hk : 2 * kb + 1 ≤ a + (2 * kb + 1) := by omega
    have hzero :=
      coeff_eq_zero_of_odd_second_of_mem_northFixedAmbientHarmonicSubmodule
        (hp := hp) (m := a + (2 * kb + 1)) (k := kb) (c := c) hk
    simpa [two_mul, add_assoc, add_left_comm, add_comm] using hzero

theorem eq_zero_of_top_coeff_zero_of_mem_northFixedAmbientHarmonicSubmodule
    {n : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n)
    (htop : MvPolynomial.coeff (tripleExp 0 0 n) p = 0) :
    p = 0 := by
  have hhom : p.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n p).mp hp.1.1
  ext d
  rw [← tripleExp_eq_self_of_finsupp d]
  by_cases hdeg : d 0 + d 1 + d 2 = n
  · exact coeff_eq_zero_of_top_zero_of_mem_northFixedAmbientHarmonicSubmodule
      (hp := hp) (a := d 0) (b := d 1) (c := d 2) hdeg htop
  · exact coeff_eq_zero_of_isHomogeneous_of_ne_degree hhom hdeg

lemma northLinearPow_ne_radiusSq_mul (n : ℕ) (q : Poly3) :
    ((northLinearAmbient : Poly3) ^ (n + 2)) ≠ radiusSq * q := by
  intro hEq
  let v : Fin 3 → ℂ := fun i =>
    if i = 0 then 1 else if i = 1 then 0 else Complex.I
  have hEval :=
    congrArg (fun r : Poly3 => MvPolynomial.eval₂ (algebraMap ℝ ℂ) v r) hEq
  have hleft :
      MvPolynomial.eval₂ (algebraMap ℝ ℂ) v ((northLinearAmbient : Poly3) ^ (n + 2)) =
        Complex.I ^ (n + 2) := by
    simp [northLinearAmbient, v]
  have hright :
      MvPolynomial.eval₂ (algebraMap ℝ ℂ) v (radiusSq * q) = 0 := by
    rw [MvPolynomial.eval₂_mul]
    simp [radiusSq, Fin.sum_univ_three, pow_two, v]
  have hzero : Complex.I ^ (n + 2) = 0 := by
    simpa [hleft, hright] using hEval
  exact (pow_ne_zero (n + 2) Complex.I_ne_zero) hzero

lemma exists_nonzero_mem_northFixedAmbientHarmonicSubmodule_of_nonzero_sector
    {n : ℕ} {f : sector n} (hfne : f ≠ 0) :
    ∃ p : Poly3, p ∈ northFixedAmbientHarmonicSubmodule n ∧ p ≠ 0 := by
  let u : sectorL2 n := sectorToSectorL2 n f
  have hu0 : u ≠ 0 := by
    intro hu0
    exact hfne (sectorToSectorL2_injective n hu0)
  have hWrot : SectorSubmodule.IsRotationInvariant n (⊤ : Submodule ℝ (sectorL2 n)) := by
    intro ρ x hx
    simp
  have hWne : (⊤ : Submodule ℝ (sectorL2 n)) ≠ ⊥ := by
    intro hbot
    have hu_mem : u ∈ (⊤ : Submodule ℝ (sectorL2 n)) := by
      simp
    have hu_bot : u ∈ (⊥ : Submodule ℝ (sectorL2 n)) := by
      simpa [hbot] using hu_mem
    exact hu0 (by simpa [Submodule.mem_bot] using hu_bot)
  rcases exists_nonzero_fixed_ambientRepresentative_of_isRotationInvariant_of_ne_bot hWrot hWne with
    ⟨p, -, hp0, hprot⟩
  refine ⟨p.1, ⟨p.2, hprot⟩, ?_⟩
  intro hp1
  apply hp0
  apply Subtype.ext
  simp [sectorToSectorL2, hp1]

theorem exists_nonzero_mem_northFixedAmbientHarmonicSubmodule (n : ℕ) :
    ∃ p : Poly3, p ∈ northFixedAmbientHarmonicSubmodule n ∧ p ≠ 0 := by
  cases n with
  | zero =>
      let f : sector 0 := ⟨zonal0, zonal0_mem_sector⟩
      have hfne : f ≠ 0 := by
        intro hf0
        have hval : ((f : C(S2, ℝ)) northPole) ≠ 0 := by
          simp [f]
        have hEval := congrArg (fun g : sector 0 => ((g : C(S2, ℝ)) northPole)) hf0
        exact hval (by simpa [f] using hEval)
      exact exists_nonzero_mem_northFixedAmbientHarmonicSubmodule_of_nonzero_sector
        (f := f) hfne
  | succ n =>
      cases n with
      | zero =>
          let f : sector 1 := ⟨zonal1, zonal1_mem_sector⟩
          have hfne : f ≠ 0 := by
            intro hf0
            have hval : ((f : C(S2, ℝ)) northPole) ≠ 0 := by
              simp [f, northPole]
            have hEval := congrArg (fun g : sector 1 => ((g : C(S2, ℝ)) northPole)) hf0
            exact hval (by simpa [f, northPole] using hEval)
          exact exists_nonzero_mem_northFixedAmbientHarmonicSubmodule_of_nonzero_sector
            (f := f) hfne
      | succ n =>
          let zpow : Poly3 := (northLinearAmbient : Poly3) ^ (n + 2)
          have hzpow_mem : zpow ∈ homogeneousSubmodule (n + 2) := by
            refine (MvPolynomial.mem_homogeneousSubmodule (n + 2) zpow).mpr ?_
            simpa [zpow, northLinearAmbient] using
              (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (2 : Fin 3) (n + 2))
          obtain ⟨h, q, hh, hq, hdecomp⟩ :=
            exists_harmonic_add_radiusSq_mul_of_mem_homogeneousSubmodule hzpow_mem
          have hhne : h ≠ 0 := by
            intro hh0
            have hdecomp' : zpow = radiusSq * q := by simpa [zpow, hh0] using hdecomp
            exact northLinearPow_ne_radiusSq_mul n q hdecomp'
          let hs : sector (n + 2) := ⟨restrictToSphere h, restrict_mem_sector hh⟩
          have hsne : hs ≠ 0 := by
            intro hs0
            let hhsub : harmonicHomogeneousSubmodule (n + 2) := ⟨h, hh⟩
            have hres : restrictToSphere hhsub.1 = 0 := by
              simpa [hs] using congrArg Subtype.val hs0
            have hres' : restrictToSphere hhsub.1 = restrictToSphere (0 : harmonicHomogeneousSubmodule (n + 2)).1 := by
              simpa using hres
            have hzero :=
              restrictToSphere_injective_on_harmonicHomogeneousSubmodule (n + 2) hres'
            exact hhne (congrArg Subtype.val hzero)
          exact exists_nonzero_mem_northFixedAmbientHarmonicSubmodule_of_nonzero_sector
            (f := hs) hsne

theorem exists_mem_northFixedAmbientHarmonicSubmodule_topCoeff_ne_zero (n : ℕ) :
    ∃ p : Poly3, p ∈ northFixedAmbientHarmonicSubmodule n ∧
      MvPolynomial.coeff (tripleExp 0 0 n) p ≠ 0 := by
  rcases exists_nonzero_mem_northFixedAmbientHarmonicSubmodule n with ⟨p, hp, hp0⟩
  refine ⟨p, hp, ?_⟩
  intro htop
  exact hp0 (eq_zero_of_top_coeff_zero_of_mem_northFixedAmbientHarmonicSubmodule hp htop)

theorem finrank_northFixedAmbientHarmonicSubmodule_eq_one (n : ℕ) :
    Module.finrank ℝ (northFixedAmbientHarmonicSubmodule n) = 1 := by
  obtain ⟨p, hp, htop⟩ := exists_mem_northFixedAmbientHarmonicSubmodule_topCoeff_ne_zero n
  let v : northFixedAmbientHarmonicSubmodule n := ⟨p, hp⟩
  have hv : v ≠ 0 := by
    intro hv0
    apply htop
    simpa [v] using congrArg (fun q : Poly3 => MvPolynomial.coeff (tripleExp 0 0 n) q) (congrArg Subtype.val hv0)
  have hle :
      Module.finrank ℝ (northFixedAmbientHarmonicSubmodule n) ≤ 1 := by
    apply finrank_le_one v
    intro w
    let c : ℝ := MvPolynomial.coeff (tripleExp 0 0 n) w.1 /
      MvPolynomial.coeff (tripleExp 0 0 n) p
    refine ⟨c, ?_⟩
    apply Subtype.ext
    have hmem :
        w.1 - c • p ∈ northFixedAmbientHarmonicSubmodule n := by
      exact Submodule.sub_mem _ w.2 (Submodule.smul_mem _ c hp)
    have hcoeff0 :
        MvPolynomial.coeff (tripleExp 0 0 n) (w.1 - c • p) = 0 := by
      rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, smul_eq_mul]
      simp [c]
      field_simp [htop]
      ring
    have hzero :=
      eq_zero_of_top_coeff_zero_of_mem_northFixedAmbientHarmonicSubmodule hmem hcoeff0
    exact (sub_eq_zero.mp hzero).symm
  have hpos :
      0 < Module.finrank ℝ (northFixedAmbientHarmonicSubmodule n) := by
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩
  omega

end SphericalHarmonics
