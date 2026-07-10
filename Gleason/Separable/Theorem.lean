import Gleason.Separable.RealTheorem
import Gleason.Separable.ComplexTheorem

/-!
# Gleason's Theorem

The theorem holds for separable real and complex Hilbert spaces of dimension
at least three. In each case the representing positive trace-class operator
exists and is unique.
-/

noncomputable section

namespace ClassicalGleason.Separable

universe v

/-- Gleason's theorem for separable real and complex Hilbert spaces. -/
theorem gleason_theorem_separable :
    GleasonStatement.{0, v} ℝ ∧ GleasonStatement.{0, v} ℂ :=
  ⟨gleason_theorem_separable_real, gleason_theorem_separable_complex⟩

end ClassicalGleason.Separable
