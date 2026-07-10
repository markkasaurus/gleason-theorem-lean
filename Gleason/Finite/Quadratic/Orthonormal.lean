import Mathlib
import Gleason.Finite.FrameFunction
import Gleason.Finite.Quadratic.Homogeneity

noncomputable section

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

theorem frame_quadratic_linear_combination
    (μ : FrameFunction H) (hquad : μ.HasQuad2D)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) (a b : ℝ) :
    frame_quadratic (H := H) μ (a • u + b • v) + frame_quadratic (H := H) μ (a • u - b • v) =
      2 * a ^ 2 * frame_quadratic (H := H) μ u + 2 * b ^ 2 * frame_quadratic (H := H) μ v := by
  classical
  rcases hquad u v hu hv huv with ⟨α, β, γ, hpoly⟩

  have hα : α = 2 * frame_quadratic (H := H) μ u := by
    have : frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ u = α := by
      simpa using (hpoly 1 0)
    linarith

  have hγ : γ = 2 * frame_quadratic (H := H) μ v := by
    have : frame_quadratic (H := H) μ v + frame_quadratic (H := H) μ (-v) = γ := by
      simpa using (hpoly 0 1)
    have : frame_quadratic (H := H) μ v + frame_quadratic (H := H) μ v = γ := by
      simpa [frame_quadratic_neg (H := H)] using this
    linarith

  have hβ : β = 0 := by
    have h11 :
        frame_quadratic (H := H) μ (u + v) + frame_quadratic (H := H) μ (u - v) =
          α + β + γ := by
      simpa using (hpoly 1 1)
    have h1m1 :
        frame_quadratic (H := H) μ (u + (-v)) + frame_quadratic (H := H) μ (u + v) =
          α + (-β) + γ := by
      simpa using (hpoly 1 (-1))
    have hrhs : α + β + γ = α + (-β) + γ := by
      calc
        α + β + γ
            = frame_quadratic (H := H) μ (u + v) + frame_quadratic (H := H) μ (u - v) := by
                simpa using h11.symm
        _   = frame_quadratic (H := H) μ (u - v) + frame_quadratic (H := H) μ (u + v) := by
                simp [add_comm]
        _   = frame_quadratic (H := H) μ (u + (-v)) + frame_quadratic (H := H) μ (u + v) := by
                simp [sub_eq_add_neg]
        _   = α + (-β) + γ := h1m1
    linarith

  have habC := hpoly a b
  have hab :
      frame_quadratic (H := H) μ (a • u + b • v) + frame_quadratic (H := H) μ (a • u - b • v) =
        α * a ^ 2 + β * a * b + γ * b ^ 2 := by
    -- convert ℝ-smul to ℂ-smul as used in `HasQuad2D`
    simpa [Algebra.smul_def] using habC

  calc
    frame_quadratic (H := H) μ (a • u + b • v) + frame_quadratic (H := H) μ (a • u - b • v)
        = α * a ^ 2 + β * a * b + γ * b ^ 2 := hab
    _   = (2 * frame_quadratic (H := H) μ u) * a ^ 2 + (2 * frame_quadratic (H := H) μ v) * b ^ 2 := by
            simp [hα, hβ, hγ, add_assoc, add_left_comm, add_comm]
    _   = 2 * a ^ 2 * frame_quadratic (H := H) μ u + 2 * b ^ 2 * frame_quadratic (H := H) μ v := by
            ring
