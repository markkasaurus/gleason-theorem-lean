import Mathlib
import Gleason.Finite.OrthogonalComplement

noncomputable section

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

theorem exists_common_orthogonal_unit
  (hdim : 3 ≤ Module.finrank ℂ H)
  (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
  ∃ w : H, ‖w‖ = 1 ∧ inner (𝕜 := ℂ) x w = 0 ∧ inner (𝕜 := ℂ) y w = 0 := by
  classical

  -- get a nonzero vector orthogonal to both (A5)
  rcases exists_ortho_vector_of_dim_ge_3 (H := H) hdim x y with ⟨w0, hw0, hw0x, hw0y⟩

  have hw0_norm_ne : ‖w0‖ ≠ 0 := by
    simpa [norm_eq_zero] using hw0

  -- normalize
  let w : H := ((‖w0‖)⁻¹ : ℂ) • w0

  have hw_norm : ‖w‖ = 1 := by
    calc
      ‖w‖ = ‖((‖w0‖)⁻¹ : ℂ)‖ * ‖w0‖ := by simp [w, norm_smul]
      _ = (‖w0‖ : ℝ)⁻¹ * ‖w0‖ := by
            -- `‖(r : ℂ)‖ = ‖r‖` for real `r`
            simp
      _ = 1 := by simpa using (inv_mul_cancel₀ hw0_norm_ne)

  have hxw : inner (𝕜 := ℂ) x w = 0 := by
    have hxw0 : inner (𝕜 := ℂ) x w0 = 0 := (inner_eq_zero_symm).2 hw0x
    -- linearity in the right argument
    simpa [w, inner_smul_right, hxw0]

  have hyw : inner (𝕜 := ℂ) y w = 0 := by
    have hyw0 : inner (𝕜 := ℂ) y w0 = 0 := (inner_eq_zero_symm).2 hw0y
    simpa [w, inner_smul_right, hyw0]

  -- `hx`, `hy` are unused but kept to match the prompt signature
  exact ⟨w, hw_norm, hxw, hyw⟩

