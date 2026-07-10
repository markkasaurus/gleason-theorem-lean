import Mathlib
import Gleason.Finite.Polarization.BoundedQuadraticForm
import Gleason.Finite.Polarization.Definition
import Gleason.Finite.Polarization.Additivity
import Gleason.Finite.Polarization.LeftScalar
import Gleason.Finite.Polarization.RightScalar
import Gleason.Finite.Polarization.Bound

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

open scoped ComplexConjugate

/-- Continuity in the left argument: `x ↦ polarization q x y` is continuous. -/
theorem polarization_continuous_left (q : H → ℝ) (hq : IsBoundedQuadraticForm q) (y : H) :
    Continuous (fun x : H => polarization q x y) := by
  classical
  rcases polarization_le_norm_mul_norm (H := H) q hq with ⟨C, hC⟩
  -- ℂ-linear in the left argument (B4 + B5)
  let f : H →ₗ[ℂ] ℂ :=
  { toFun := fun x => polarization q x y
    map_add' := by
      intro x₁ x₂
      simpa using (polarization_add_left q hq x₁ x₂ y)
    map_smul' := by
      intro c x
      simpa [smul_eq_mul] using (polarization_smul_left q hq c x y) }
  let K : ℝ := C * ‖y‖
  have hK : ∀ x : H, ‖f x‖ ≤ K * ‖x‖ := by
    intro x
    have hx := hC x y
    -- C * ‖x‖ * ‖y‖ = (C * ‖y‖) * ‖x‖
    simpa [f, K, mul_assoc, mul_left_comm, mul_comm] using hx
  simpa using (LinearMap.mkContinuous f K hK).continuous

/-- Continuity in the right argument: `y ↦ polarization q x y` is continuous. -/
theorem polarization_continuous_right (q : H → ℝ) (hq : IsBoundedQuadraticForm q) (x : H) :
    Continuous (fun y : H => polarization q x y) := by
  classical
  rcases polarization_le_norm_mul_norm (H := H) q hq with ⟨C, hC⟩
  -- ℝ-linear in the right argument (B4 + B6 gives right scalar rule, restricted to ℝ)
  let f : H →ₗ[ℝ] ℂ :=
  { toFun := fun y => polarization q x y
    map_add' := by
      intro y₁ y₂
      simpa using (polarization_add_right q hq x y₁ y₂)
    map_smul' := by
      intro r y
      -- use the complex scalar rule with c = r
      have hs : polarization q x ((r : ℂ) • y) = conj (r : ℂ) * polarization q x y :=
        polarization_smul_right q hq (r : ℂ) x y
      have hconj : conj (r : ℂ) = (r : ℂ) := by simp
      -- interpret ℝ-smul on H and ℂ via algebraMap ℝ ℂ
      -- and ℝ-smul on ℂ as multiplication by (r:ℂ)
      simpa [Algebra.smul_def, hconj, mul_assoc] using hs }
  let K : ℝ := C * ‖x‖
  have hK : ∀ y : H, ‖f y‖ ≤ K * ‖y‖ := by
    intro y
    have hy := hC x y
    simpa [f, K, mul_assoc, mul_left_comm, mul_comm] using hy
  simpa using (LinearMap.mkContinuous f K hK).continuous
