import Gleason.Finite.ProjectionFrame
import Gleason.Continuity.Theorem

/-!
End-to-end finite-dimensional projection-frame theorem using the classical
oscillation route.
-/

noncomputable section

namespace ClassicalGleason

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

theorem gleason_theorem_finite_from_oscillation
    (hdim : 3 ≤ Module.finrank ℂ H)
    (f : ProjectionFrameFunction H) :
    ∃ ρ : H →L[ℂ] H,
      ρ.IsPositive ∧
      reTr ρ = 1 ∧
      ∀ P : H →L[ℂ] H, IsOrthProj P → f.μ P = reTr (ρ * P) := by
  exact
    gleason_theorem_finite_of_parallelogram (H := H)
      (fun μ x y => frame_quadratic_full_parallelogram_from_oscillation hdim μ x y)
      hdim f

theorem finite_gleason_statement_from_oscillation : FiniteGleasonStatement := by
  intro H _ _ _ _ hdim f
  exact gleason_theorem_finite_from_oscillation (H := H) hdim f

end ClassicalGleason
