import Mathlib

import Gleason.Finite.FrameFunction
import Gleason.Finite.Quadratic.Parallelogram
import Gleason.Finite.Polarization.OperatorRepresentation
import Gleason.Finite.Quadratic.Bound

noncomputable section

open scoped BigOperators

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

namespace GleasonC3h

/-- A Lipschitz bound for `frame_quadratic μ` on the unit sphere, derived from the
parallelogram identity (hence from `HasQuad2D` in dimension ≥ 3). -/
theorem frame_quadratic_lipschitz_common_orthogonal
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H) (hquad : μ.HasQuad2D) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x y w : H,
        ‖x‖ = 1 → ‖y‖ = 1 → ‖w‖ = 1 →
        inner (𝕜 := ℂ) x w = 0 → inner (𝕜 := ℂ) y w = 0 →
        |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ y| ≤ K * ‖x - y‖ := by
  classical
  -- Obtain the full parallelogram law from `HasQuad2D`.
  have h_para :
      ∀ x y : H,
        frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
          = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by
    intro x y
    simpa using (frame_quadratic_parallelogram (H := H) hdim μ hquad x y)

  -- Build a bounded quadratic form and apply the polarization representation.
  let hq : IsBoundedQuadraticForm (H := H) (frame_quadratic (H := H) μ) :=
    frame_quadratic_is_bounded_quadratic (H := H) μ h_para

  rcases polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ) hq with
    ⟨T, _hpol, hqT⟩

  refine ⟨2 * ‖T‖, by positivity, ?_⟩
  intro x y w hx hy _hw _hxw _hyw

  -- We prove a stronger inequality which does not use `w`.
  have hx' : ‖x‖ ≤ 1 := by simpa [hx]
  have hy' : ‖y‖ ≤ 1 := by simpa [hy]

  -- Rewrite in terms of the representing operator `T`.
  have hqx : frame_quadratic (H := H) μ x = (inner (𝕜 := ℂ) x (T x)).re := hqT x
  have hqy : frame_quadratic (H := H) μ y = (inner (𝕜 := ℂ) y (T y)).re := hqT y

  -- Bound the real-part difference by the norm of a complex difference.
  have hre :
      |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ y|
        ≤ ‖inner (𝕜 := ℂ) x (T x) - inner (𝕜 := ℂ) y (T y)‖ := by
    -- Use `|re z| ≤ ‖z‖` with `z = ⟪x,Tx⟫ - ⟪y,Ty⟫`.
    simpa [hqx, hqy, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (RCLike.abs_re_le_norm (inner (𝕜 := ℂ) x (T x) - inner (𝕜 := ℂ) y (T y)))

  -- Now bound the complex difference using Cauchy–Schwarz and the operator norm.
  have hdiff :
      ‖inner (𝕜 := ℂ) x (T x) - inner (𝕜 := ℂ) y (T y)‖
        ≤ (2 * ‖T‖) * ‖x - y‖ := by
    -- Split into two differences and use the triangle inequality.
    have hsplit :
        inner (𝕜 := ℂ) x (T x) - inner (𝕜 := ℂ) y (T y)
          =
        (inner (𝕜 := ℂ) x (T x) - inner (𝕜 := ℂ) y (T x)) +
          (inner (𝕜 := ℂ) y (T x) - inner (𝕜 := ℂ) y (T y)) := by
      ring

    have hA :
        ‖inner (𝕜 := ℂ) x (T x) - inner (𝕜 := ℂ) y (T x)‖ ≤ ‖x - y‖ * ‖T x‖ := by
      -- rewrite as `⟪x-y, Tx⟫`
      have : inner (𝕜 := ℂ) (x - y) (T x) = inner (𝕜 := ℂ) x (T x) - inner (𝕜 := ℂ) y (T x) := by
        simpa [inner_sub_left]
      -- apply Cauchy–Schwarz
      have hcs : ‖inner (𝕜 := ℂ) (x - y) (T x)‖ ≤ ‖x - y‖ * ‖T x‖ :=
        (norm_inner_le_norm (x - y) (T x))
      simpa [this] using hcs

    have hB :
        ‖inner (𝕜 := ℂ) y (T x) - inner (𝕜 := ℂ) y (T y)‖ ≤ ‖y‖ * ‖T (x - y)‖ := by
      have : inner (𝕜 := ℂ) y (T (x - y)) = inner (𝕜 := ℂ) y (T x) - inner (𝕜 := ℂ) y (T y) := by
        simpa [map_sub, inner_sub_right]
      have hcs : ‖inner (𝕜 := ℂ) y (T (x - y))‖ ≤ ‖y‖ * ‖T (x - y)‖ :=
        (norm_inner_le_norm y (T (x - y)))
      simpa [this] using hcs

    calc
      ‖inner (𝕜 := ℂ) x (T x) - inner (𝕜 := ℂ) y (T y)‖
          = ‖(inner (𝕜 := ℂ) x (T x) - inner (𝕜 := ℂ) y (T x)) +
                (inner (𝕜 := ℂ) y (T x) - inner (𝕜 := ℂ) y (T y))‖ := by
              -- rewrite the difference using the algebraic split
              rw [hsplit]
      _ ≤ ‖inner (𝕜 := ℂ) x (T x) - inner (𝕜 := ℂ) y (T x)‖ +
            ‖inner (𝕜 := ℂ) y (T x) - inner (𝕜 := ℂ) y (T y)‖ := by
            exact norm_add_le _ _
      _ ≤ (‖x - y‖ * ‖T x‖) + (‖y‖ * ‖T (x - y)‖) := by
            exact add_le_add hA hB
      _ ≤ (‖x - y‖ * (‖T‖ * ‖x‖)) + (‖y‖ * (‖T‖ * ‖x - y‖)) := by
            gcongr
            · exact (T.le_opNorm x)
            · exact (T.le_opNorm (x - y))
      _ = (2 * ‖T‖) * ‖x - y‖ := by
            calc
              ‖x - y‖ * (‖T‖ * ‖x‖) + ‖y‖ * (‖T‖ * ‖x - y‖)
                  = ‖x - y‖ * ‖T‖ + ‖T‖ * ‖x - y‖ := by
                      simp [hx, hy, mul_assoc, mul_left_comm, mul_comm]
              _ = (2 * ‖T‖) * ‖x - y‖ := by ring

  -- Combine and rewrite.
  have := le_trans hre hdiff
  -- `‖x - y‖ = ‖x - y‖` and `‖x - y‖ = ‖x - y‖`; also `x - y = x - y`.
  simpa [mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

end GleasonC3h
