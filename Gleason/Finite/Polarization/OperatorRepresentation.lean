import Mathlib
import Gleason.Finite.Polarization.BoundedQuadraticForm
import Gleason.Finite.Polarization.Definition
import Gleason.Finite.Polarization.Additivity
import Gleason.Finite.Polarization.LeftScalar
import Gleason.Finite.Polarization.RightScalar
import Gleason.Finite.Polarization.Bound

section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
Riesz representation applied to polarization (Lean 4.26).

From earlier files, `polarization q x y` is linear in `x` and conjugate-linear in `y`.
Define `B x y := star (polarization q x y)`. Then `B` is conjugate-linear in `x`
and linear in `y`, so Mathlib’s packaged Riesz representation for bounded
sesquilinear forms applies (`InnerProductSpace.continuousLinearMapOfBilin`).

We obtain `T : H →L[ℂ] H` with
`polarization q x y = ⟪y, T x⟫` and hence `q x = re ⟪x, T x⟫`.
-/
theorem polarization_eq_inner_product (q : H → ℝ) (hq : IsBoundedQuadraticForm q) :
    ∃ T : H →L[ℂ] H,
      (∀ x y : H, polarization q x y = inner (𝕜 := ℂ) y (T x)) ∧
      (∀ x : H, q x = (inner (𝕜 := ℂ) x (T x)).re) := by
  classical

  -- global bound on polarization from B7
  rcases polarization_le_norm_mul_norm (H := H) q hq with ⟨C, hpol⟩

  -- ensure a nonnegative constant for `mkContinuous` (needed in Lean 4.26)
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := by
    simpa [C0] using (le_max_right C 0)

  have hpol0 : ∀ x y : H, ‖polarization q x y‖ ≤ C0 * ‖x‖ * ‖y‖ := by
    intro x y
    have h := hpol x y
    have hC : C ≤ C0 := by
      simpa [C0] using (le_max_left C 0)
    have hxy : 0 ≤ ‖x‖ * ‖y‖ := by
      exact mul_nonneg (norm_nonneg x) (norm_nonneg y)
    have hCmul : C * ‖x‖ * ‖y‖ ≤ C0 * ‖x‖ * ‖y‖ := by
      -- rewrite as multiplication by the nonnegative factor `‖x‖*‖y‖`
      simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hC hxy)
    exact le_trans h hCmul

  -- underlying linear map in `y`
  let ψ (x : H) : H →ₗ[ℂ] ℂ :=
  { toFun := fun y => star (polarization q x y)
    map_add' := by
      intro y₁ y₂
      simpa using congrArg star (polarization_add_right q hq x y₁ y₂)
    map_smul' := by
      intro c y
      -- `polarization_smul_right` is conjugate-linear in `y`;
      -- starring converts it to linearity.
      have h := congrArg star (polarization_smul_right q hq c x y)
      -- reorder with commutativity
      simpa [mul_assoc, mul_comm, mul_left_comm] using h }

  have hCφ : ∀ x : H, 0 ≤ C0 * ‖x‖ := by
    intro x
    exact mul_nonneg hC0 (norm_nonneg x)

  have hψ : ∀ x y : H, ‖ψ x y‖ ≤ (C0 * ‖x‖) * ‖y‖ := by
    intro x y
    have h := hpol0 x y
    -- `‖star z‖ = ‖z‖`, and reassociate products
    simpa [ψ, mul_assoc, mul_left_comm, mul_comm] using h

  -- for each `x`, a continuous linear map in `y`
  let φ : H → (H →L[ℂ] ℂ) := fun x =>
    LinearMap.mkContinuous (ψ x) (C0 * ‖x‖) (by
      intro y
      simpa using (hψ x y))

  have hφ : ∀ x : H, ‖φ x‖ ≤ C0 * ‖x‖ := by
    intro x
    -- operator norm bound from the `mkContinuous` construction
    simpa [φ] using
      (LinearMap.mkContinuous_norm_le (ψ x) (C := C0 * ‖x‖)
        (hCφ x)
        (by
          intro y
          simpa using (hψ x y)))

  -- conjugate-linear map in `x` into the operator space
  let Blin : H →ₗ⋆[ℂ] (H →L[ℂ] ℂ) :=
  { toFun := φ
    map_add' := by
      intro x₁ x₂
      ext y
      simpa [φ, ψ] using congrArg star (polarization_add_left q hq x₁ x₂ y)
    map_smul' := by
      intro c x
      ext y
      -- polarization is linear in `x`; after `star` we get conjugate-linearity
      have h := congrArg star (polarization_smul_left q hq c x y)
      -- scalar on the codomain is `star c`; commute if needed
      simpa [φ, ψ, mul_assoc, mul_comm, mul_left_comm] using h }

  -- make it continuous
  let B : H →L⋆[ℂ] (H →L[ℂ] ℂ) :=
    Blin.mkContinuous C0 (by
      intro x
      -- `‖Blin x‖ = ‖φ x‖`
      simpa [Blin] using hφ x)

  -- Riesz representation for bounded sesquilinear forms
  let T : H →L[ℂ] H := InnerProductSpace.continuousLinearMapOfBilin (E := H) B

  have hrepr : ∀ x y : H, polarization q x y = inner (𝕜 := ℂ) y (T x) := by
    intro x y
    -- standard lemma: inner (T x) y = (B x) y = star (polarization q x y)
    have h := InnerProductSpace.continuousLinearMapOfBilin_apply (B := B) x y
    have hs : star (inner (𝕜 := ℂ) (T x) y) = polarization q x y := by
      -- take `star` of both sides and unfold `(B x) y`
      simpa [T, B, Blin, φ, ψ] using congrArg star h
    -- `star(inner (T x) y) = inner y (T x)`
    simpa [inner_conj_symm] using hs.symm

  refine ⟨T, hrepr, ?_⟩

  intro x

  -- q 0 = 0
  have q0 : q 0 = 0 := by
    -- `0 • x = 0`
    simpa using (hq.sq_hom (0 : ℂ) x)

  -- q (2•x) = 4 * q x
  have h2 : q ((2 : ℂ) • x) = 4 * q x := by
    have h := hq.sq_hom (2 : ℂ) x
    -- normalize the scalar square to `4`
    have hn : ‖(2 : ℂ)‖ ^ 2 = (4 : ℝ) := by norm_num
    have hpow : (2 : ℝ) ^ 2 = (4 : ℝ) := by norm_num
    -- depending on the exact form of `sq_hom`, either lemma may fire after simp
    simpa [hn, hpow, mul_assoc, mul_comm, mul_left_comm] using h

  -- rewrite to `q (x + x)` for the polarization identity simp output
  have h2' : q (x + x) = 4 * q x := by
    simpa [two_smul] using h2

  have hre : (polarization q x x).re = q x := by
    -- Real part of polarization at (x,x)
    have hdef : (polarization q x x).re = (q (x + x) - q 0) / 4 := by
      -- `simp` may produce `q (2 • x)`; `two_smul` converts to `x+x`.
      simp [polarization, two_smul]
    have h4 : (4 : ℝ) ≠ 0 := by norm_num
    calc
      (polarization q x x).re = (q (x + x) - q 0) / 4 := hdef
      _ = (4 * q x - 0) / 4 := by simp [h2', q0]
      _ = q x := by
        field_simp [h4]
        simp

  -- apply the representation at y=x
  have hxT : polarization q x x = inner (𝕜 := ℂ) x (T x) := by
    simpa using (hrepr x x)

  calc
    q x = (polarization q x x).re := by simpa using hre.symm
    _ = (inner (𝕜 := ℂ) x (T x)).re := by simpa [hxT]

end
