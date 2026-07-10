import Mathlib
import Gleason.Finite.Polarization.OperatorRepresentation
import Gleason.Finite.Quadratic.Bound
import Gleason.Finite.Quadratic.Basic

noncomputable section

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

/--
The frame operator associated to the bounded quadratic form `frame_quadratic μ` is positive:
for the operator `T` obtained from `polarization_eq_inner_product`, we have
`0 ≤ re ⟪T x, x⟫` for all `x`.

This is immediate from:
- `frame_quadratic_nonneg μ x`
- `frame_quadratic μ x = re ⟪x, T x⟫` from `polarization_eq_inner_product`
- `re ⟪T x, x⟫ = re ⟪x, T x⟫` by conjugate symmetry of `inner`.
-/
theorem frame_operator_positive (μ : FrameFunction H)
    (h_para :
      ∀ x y : H,
        frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
          = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y) :
    let T :=
      (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ)
        (frame_quadratic_is_bounded_quadratic (H := H) μ h_para)).choose
    ∀ x : H, 0 ≤ (inner (𝕜 := ℂ) (T x) x).re := by
  classical
  dsimp
  intro x

  -- Name the chosen operator.
  let T : H →L[ℂ] H :=
    (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ)
      (frame_quadratic_is_bounded_quadratic (H := H) μ h_para)).choose
  change 0 ≤ (inner (𝕜 := ℂ) (T x) x).re

  -- `frame_quadratic μ x = re ⟪x, T x⟫`
  have hqTx : frame_quadratic (H := H) μ x = (inner (𝕜 := ℂ) x (T x)).re := by
    have h :=
      (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ)
        (frame_quadratic_is_bounded_quadratic (H := H) μ h_para)).choose_spec.2 x
    simpa [T] using h

  -- Nonnegativity of the quadratic form
  have hnonneg : 0 ≤ frame_quadratic (H := H) μ x :=
    frame_quadratic_nonneg (H := H) μ x

  have hinner : 0 ≤ (inner (𝕜 := ℂ) x (T x)).re := by
    simpa [hqTx] using hnonneg

  -- Real parts agree: `re ⟪T x, x⟫ = re ⟪x, T x⟫`
  have hre : (inner (𝕜 := ℂ) (T x) x).re = (inner (𝕜 := ℂ) x (T x)).re := by
    -- `⟪T x, x⟫ = star ⟪x, T x⟫` and `re (star z) = re z`
    calc
      (inner (𝕜 := ℂ) (T x) x).re
          = ((star (inner (𝕜 := ℂ) x (T x)))).re := by
              simpa [inner_conj_symm]
      _ = (inner (𝕜 := ℂ) x (T x)).re := by
        simpa [Complex.star_def] using (Complex.conj_re (inner (𝕜 := ℂ) x (T x)))

  simpa [hre] using hinner
