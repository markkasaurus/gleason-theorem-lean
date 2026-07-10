import Gleason.Separable.ComplexUniqueness

/-!
# Gleason's Theorem for Separable Complex Hilbert Spaces
-/

noncomputable section

namespace ClassicalGleason.Separable

universe v

/-- Gleason's theorem for separable complex Hilbert spaces of dimension at
least three, including uniqueness of the positive trace-class representative. -/
theorem gleason_theorem_separable_complex : GleasonStatement.{0, v} ℂ := by
  intro H _ _ _ _ hdim m
  refine ⟨m.representingOperator hdim, m.representingOperator_represents hdim, ?_⟩
  intro T hT
  exact represents_unique_complex m hT (m.representingOperator_represents hdim)

end ClassicalGleason.Separable
