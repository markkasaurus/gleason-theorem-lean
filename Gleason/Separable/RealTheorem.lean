import Gleason.Separable.RealUniqueness

/-!
# Gleason's Theorem for Separable Real Hilbert Spaces
-/

noncomputable section

namespace ClassicalGleason.Separable

universe v

/-- Gleason's theorem for separable real Hilbert spaces of dimension at least
three, including uniqueness of the positive trace-class representative. -/
theorem gleason_theorem_separable_real : GleasonStatement.{0, v} ℝ := by
  intro H _ _ _ _ hdim m
  refine ⟨m.realRepresentingOperator hdim,
    m.realRepresentingOperator_represents hdim, ?_⟩
  intro T hT
  exact represents_unique_real m hT
    (m.realRepresentingOperator_represents hdim)

end ClassicalGleason.Separable
