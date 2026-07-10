import Mathlib

noncomputable section

namespace GleasonGeometricOscillation

open Filter

universe u v

variable {α : Type u} {β : Type v}
variable [PseudoMetricSpace α] [PseudoMetricSpace β]

/-- If a function admits a sequence of distance scales `δ n`
and corresponding oscillation bounds `b n → 0`, then it is uniformly continuous. -/
theorem uniformContinuous_of_scaleControl
    {f : α → β}
    {δ b : ℕ → ℝ}
    (hδpos : ∀ n, 0 < δ n)
    (hb0 : Filter.Tendsto b Filter.atTop (nhds 0))
    (hcontrol : ∀ n {x y : α}, dist x y < δ n → dist (f x) (f y) ≤ b n) :
    UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hEventually : ∀ᶠ n : ℕ in atTop, b n < ε := by
    exact hb0.eventually (Iio_mem_nhds hε)
  rcases Filter.eventually_atTop.1 hEventually with ⟨N, hN⟩
  refine ⟨δ N, hδpos N, ?_⟩
  intro x y hxy
  exact lt_of_le_of_lt (hcontrol N hxy) (hN N le_rfl)

/-- Geometric decay of oscillation bounds implies uniform continuity. -/
theorem uniformContinuous_of_geometricControl
    {f : α → β}
    {C ρ θ : ℝ}
    (hρ0 : 0 < ρ)
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcontrol : ∀ n {x y : α}, dist x y < ρ ^ n → dist (f x) (f y) ≤ C * θ ^ n) :
    UniformContinuous f := by
  refine uniformContinuous_of_scaleControl
    (δ := fun n => ρ ^ n) (b := fun n => C * θ ^ n) ?_ ?_ ?_
  · intro n
    exact pow_pos hρ0 n
  · simpa [mul_comm] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).const_mul C
  · intro n x y hxy
    exact hcontrol n hxy

theorem continuous_of_scaleControl
    {f : α → β}
    {δ b : ℕ → ℝ}
    (hδpos : ∀ n, 0 < δ n)
    (hb0 : Filter.Tendsto b Filter.atTop (nhds 0))
    (hcontrol : ∀ n {x y : α}, dist x y < δ n → dist (f x) (f y) ≤ b n) :
    Continuous f :=
  (uniformContinuous_of_scaleControl hδpos hb0 hcontrol).continuous

theorem continuous_of_geometricControl
    {f : α → β}
    {C ρ θ : ℝ}
    (hρ0 : 0 < ρ)
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcontrol : ∀ n {x y : α}, dist x y < ρ ^ n → dist (f x) (f y) ≤ C * θ ^ n) :
    Continuous f :=
  (uniformContinuous_of_geometricControl hρ0 hθ0 hθ1 hcontrol).continuous

end GleasonGeometricOscillation
