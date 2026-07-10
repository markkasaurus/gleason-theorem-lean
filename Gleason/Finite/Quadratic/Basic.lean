import Mathlib
import Gleason.Finite.FrameFunction

noncomputable section

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

theorem frame_quadratic_zero (μ : FrameFunction H) :
    frame_quadratic (H := H) μ 0 = 0 := by
  classical
  simp [frame_quadratic]

theorem frame_quadratic_nonneg (μ : FrameFunction H) (x : H) :
    0 ≤ frame_quadratic (H := H) μ x := by
  classical
  by_cases hx : x = 0
  · simp [frame_quadratic, hx]
  ·
    have hμ : 0 ≤ μ.μ (RankOne.rankOneProjection (H := H) x hx) := μ.nonneg _
    have hnorm : 0 ≤ ‖x‖ ^ 2 := by
      simpa [pow_two] using (mul_self_nonneg ‖x‖)
    simpa [frame_quadratic, hx] using mul_nonneg hμ hnorm
