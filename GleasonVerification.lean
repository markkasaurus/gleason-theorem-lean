import GleasonStatement
import Gleason.Separable.Theorem

/-!
# Verification Entry Point

This module connects the Mathlib-only public statement to the completed proof.
-/

noncomputable section

namespace ClassicalGleason.Separable

universe v

/-- Proof of the statement declared in `GleasonStatement.lean`. -/
theorem gleason_theorem_verified :
    GleasonStatement.{0, v} ℝ ∧ GleasonStatement.{0, v} ℂ :=
  gleason_theorem_separable

end ClassicalGleason.Separable
