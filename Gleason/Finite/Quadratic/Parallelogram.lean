import Mathlib
import Gleason.Finite.FrameFunction
import Gleason.Finite.Quadratic.Basic
import Gleason.Finite.Quadratic.Homogeneity
import Gleason.Finite.Quadratic.OrthogonalParallelogram
import Gleason.Finite.OrthogonalComplement

noncomputable section

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

theorem frame_quadratic_parallelogram
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H) (hquad : μ.HasQuad2D) (x y : H) :
    frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
      2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by
  classical
  by_cases hy0 : y = 0
  · subst hy0
    simp [sub_eq_add_neg, frame_quadratic_zero (H := H)]
    ring

  -- Pick w ⟂ x and w ⟂ y (nonzero) using dim ≥ 3 (A5)
  rcases exists_ortho_vector_of_dim_ge_3 (H := H) hdim x y with ⟨w, hw0, hwx, hwy⟩
  have hxw : inner (𝕜 := ℂ) x w = 0 := (inner_eq_zero_symm).2 hwx
  have hyw : inner (𝕜 := ℂ) y w = 0 := (inner_eq_zero_symm).2 hwy

  -- Let d = ⟪w,w⟫ ≠ 0 and pick s so that ⟪x+w, y+s•w⟫ = 0.
  let d : ℂ := inner (𝕜 := ℂ) w w
  have hd : d ≠ 0 := by
    intro h
    exact hw0 (inner_self_eq_zero.mp h)

  let s : ℂ := - inner (𝕜 := ℂ) x y / d

  have hs : s * d = - inner (𝕜 := ℂ) x y := by
    -- Isolate the inverse cancellation explicitly.
    have invmul : (d⁻¹ * d : ℂ) = 1 := inv_mul_cancel₀ hd
    calc
      s * d = (- inner (𝕜 := ℂ) x y / d) * d := by simp [s]
      _ = (- inner (𝕜 := ℂ) x y) * (d⁻¹ * d) := by
            simp [div_eq_mul_inv, mul_assoc]
      _ = (- inner (𝕜 := ℂ) x y) * 1 := by simp [invmul]
      _ = - inner (𝕜 := ℂ) x y := by simp

  have hs0 : inner (𝕜 := ℂ) x y + s * d = 0 := by
    simpa [hs]  -- ⟪x,y⟫ + (−⟪x,y⟫) = 0

  have horth1 : inner (𝕜 := ℂ) (x + w) (y + s • w) = 0 := by
    calc
      inner (𝕜 := ℂ) (x + w) (y + s • w)
          = inner (𝕜 := ℂ) x y + s * inner (𝕜 := ℂ) w w := by
              simp [inner_add_left, inner_add_right, inner_smul_right, hxw, hwy, hyw, add_assoc]
      _ = inner (𝕜 := ℂ) x y + s * d := by simp [d]
      _ = 0 := hs0

  have horth2 : inner (𝕜 := ℂ) (x - w) (y - s • w) = 0 := by
    calc
      inner (𝕜 := ℂ) (x - w) (y - s • w)
          = inner (𝕜 := ℂ) x y + s * inner (𝕜 := ℂ) w w := by
              simp [sub_eq_add_neg, inner_add_left, inner_add_right, inner_smul_right,
                hxw, hwy, hyw, add_assoc]
      _ = inner (𝕜 := ℂ) x y + s * d := by simp [d]
      _ = 0 := hs0

  -- Shorthands
  let Q : H → ℝ := fun z => frame_quadratic (H := H) μ z
  let zw : H := w + s • w
  let tw : H := w - s • w

  -- Apply orthogonal parallelogram twice (A4)
  have E1 := parallelogram_orthogonal (H := H) μ hquad (x + w) (y + s • w) horth1
  have E2 := parallelogram_orthogonal (H := H) μ hquad (x - w) (y - s • w) horth2

  -- Rewrite E1 and E2 into (x±y) ± (w ± s•w) forms and add
  have E1rw :
      Q ((x + y) + zw) + Q ((x - y) + tw) =
        2 * Q (x + w) + 2 * Q (y + s • w) := by
    simpa [Q, zw, tw, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using E1

  have E2rw :
      Q ((x + y) - zw) + Q ((x - y) - tw) =
        2 * Q (x - w) + 2 * Q (y - s • w) := by
    simpa [Q, zw, tw, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using E2

  have SumE :
      (Q ((x + y) + zw) + Q ((x + y) - zw)) + (Q ((x - y) + tw) + Q ((x - y) - tw)) =
        2 * (Q (x + w) + Q (x - w)) + 2 * (Q (y + s • w) + Q (y - s • w)) := by
    linarith [E1rw, E2rw]

  -- Now apply orthogonal parallelogram to (x±y) ⟂ (w ± s•w)
  have hxy_zw : inner (𝕜 := ℂ) (x + y) zw = 0 := by
    simp [zw, inner_add_left, inner_add_right, inner_smul_right, hxw, hyw]
  have hxm_tw : inner (𝕜 := ℂ) (x - y) tw = 0 := by
    simp [tw, sub_eq_add_neg, inner_add_left, inner_add_right, inner_smul_right, hxw, hyw]

  have Pxy :
      Q ((x + y) + zw) + Q ((x + y) - zw) = 2 * Q (x + y) + 2 * Q zw := by
    simpa [Q] using parallelogram_orthogonal (H := H) μ hquad (x + y) zw hxy_zw

  have Pxm :
      Q ((x - y) + tw) + Q ((x - y) - tw) = 2 * Q (x - y) + 2 * Q tw := by
    simpa [Q] using parallelogram_orthogonal (H := H) μ hquad (x - y) tw hxm_tw

  have HS0 :
      2 * (Q (x + y) + Q (x - y)) + 2 * (Q zw + Q tw) =
        2 * (Q (x + w) + Q (x - w)) + 2 * (Q (y + s • w) + Q (y - s • w)) := by
    linarith [SumE, Pxy, Pxm]

  -- Replace RHS sums using orthogonal parallelogram on (x,w) and (y, s•w)
  have Pxw :
      Q (x + w) + Q (x - w) = 2 * Q x + 2 * Q w := by
    simpa [Q] using parallelogram_orthogonal (H := H) μ hquad x w hxw

  have Pyw :
      Q (y + s • w) + Q (y - s • w) = 2 * Q y + 2 * Q (s • w) := by
    have : inner (𝕜 := ℂ) y (s • w) = 0 := by simp [inner_smul_right, hyw]
    simpa [Q] using parallelogram_orthogonal (H := H) μ hquad y (s • w) this

  have HS1 :
      2 * (Q (x + y) + Q (x - y)) + 2 * (Q zw + Q tw) =
        4 * Q x + 4 * Q y + 4 * Q w + 4 * Q (s • w) := by
    linarith [HS0, Pxw, Pyw]

  -- Homogeneity to express the w-terms as coefficients times Q(w)
  have Qs : Q (s • w) = ‖s‖ ^ 2 * Q w := by
    simpa [Q] using frame_quadratic_sq_hom (H := H) μ s w

  have Qzw : Q zw = ‖(1 + s : ℂ)‖ ^ 2 * Q w := by
    have : zw = (1 + s) • w := by simp [zw, add_smul, one_smul]
    simpa [Q, this] using frame_quadratic_sq_hom (H := H) μ (1 + s) w

  have Qtw : Q tw = ‖(1 - s : ℂ)‖ ^ 2 * Q w := by
    have : tw = (1 - s) • w := by simp [tw, sub_eq_add_neg, add_smul, one_smul]
    simpa [Q, this] using frame_quadratic_sq_hom (H := H) μ (1 - s) w

  -- Norm identity: ‖1+s‖^2 + ‖1-s‖^2 = 2 + 2‖s‖^2
  have hnorm : ‖(1 + s : ℂ)‖ ^ 2 + ‖(1 - s : ℂ)‖ ^ 2 = 2 + 2 * ‖s‖ ^ 2 := by
    -- use normSq add/sub cancels cross term; then convert via sq_norm
    have hns :
        Complex.normSq (1 + s) + Complex.normSq (1 - s) = 2 + 2 * Complex.normSq s := by
      simp [Complex.normSq_add, Complex.normSq_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      ring
    simpa [Complex.sq_norm] using hns

  -- Cancel w-terms from HS1 using hnorm (no linarith with symbolic coefficients)
  have wcancel :
      2 * (Q zw + Q tw) = 4 * Q w + 4 * Q (s • w) := by
    calc
      2 * (Q zw + Q tw)
          = 2 * (‖(1 + s : ℂ)‖ ^ 2 * Q w + ‖(1 - s : ℂ)‖ ^ 2 * Q w) := by
              simp [Qzw, Qtw]
      _ = (2 * (‖(1 + s : ℂ)‖ ^ 2 + ‖(1 - s : ℂ)‖ ^ 2)) * Q w := by ring
      _ = (2 * (2 + 2 * ‖s‖ ^ 2)) * Q w := by simpa [hnorm]
      _ = (4 * (1 + ‖s‖ ^ 2)) * Q w := by ring
      _ = 4 * Q w + 4 * (‖s‖ ^ 2 * Q w) := by ring
      _ = 4 * Q w + 4 * Q (s • w) := by simp [Qs, mul_assoc, mul_left_comm, mul_comm]

  have HS2 :
      2 * (Q (x + y) + Q (x - y)) = 4 * Q x + 4 * Q y := by
    -- subtract the equal w-terms from HS1
    have := HS1
    -- rewrite the LHS w part using wcancel, then simplify
    -- Now both sides have the same w-part, so it cancels.
    linarith [this, wcancel]

  -- Divide by 2 to finish
  have : Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y := by
    linarith [HS2]
  simpa [Q] using this
