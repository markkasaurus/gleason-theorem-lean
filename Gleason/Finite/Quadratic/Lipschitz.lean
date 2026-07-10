import Mathlib

import Gleason.Finite.FrameFunction
import Gleason.Finite.CommonOrthogonal
import Gleason.Finite.Quadratic.LocalLipschitz

noncomputable section

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

open GleasonC3h

/-- Global Lipschitz bound on the unit sphere (currently routed through `HasQuad2D`). -/
theorem frame_quadratic_lipschitz
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H) (hquad : μ.HasQuad2D) :
    ∃ C : ℝ, ∀ x y : H, ‖x‖ = 1 → ‖y‖ = 1 →
      |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ y| ≤ C * ‖x - y‖ := by
  classical
  rcases
      (GleasonC3h.frame_quadratic_lipschitz_common_orthogonal (H := H) hdim μ hquad) with
    ⟨K, hK0, hK⟩
  refine ⟨K, ?_⟩
  intro x y hx hy
  rcases exists_common_orthogonal_unit (H := H) hdim x y hx hy with ⟨w, hw, hxw, hyw⟩
  simpa using (hK x y w hx hy hw hxw hyw)

