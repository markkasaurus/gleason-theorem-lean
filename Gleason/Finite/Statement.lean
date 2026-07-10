import Mathlib

/-!
# Finite-Dimensional Projection-Frame Gleason Statement

This file contains only the public mathematical statement and its supporting
definitions.  It intentionally has no dependency on the implementation files.
-/

noncomputable section

namespace ClassicalGleason

/-- Orthogonal projections as self-adjoint idempotent continuous linear maps. -/
def IsOrthProj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : H →L[ℂ] H) : Prop :=
  IsIdempotentElem P ∧ IsSelfAdjoint P

/-- A normalized finitely additive probability measure on orthogonal projections. -/
structure ProjectionFrameFunction (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  μ : (H →L[ℂ] H) → ℝ
  nonneg : ∀ P : H →L[ℂ] H, IsOrthProj P → 0 ≤ μ P
  additive : ∀ P Q : H →L[ℂ] H, IsOrthProj P → IsOrthProj Q → P * Q = 0 →
    μ (P + Q) = μ P + μ Q
  normalized : μ (1 : H →L[ℂ] H) = 1

/-- Real part of the finite-dimensional complex trace. -/
def reTr {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] (A : H →L[ℂ] H) : ℝ :=
  (LinearMap.trace ℂ H A.toLinearMap).re

/-- The finite-dimensional projection-frame form of Gleason's theorem. -/
def FiniteGleasonStatement : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [FiniteDimensional ℂ H],
    3 ≤ Module.finrank ℂ H →
    ∀ f : ProjectionFrameFunction H,
      ∃ ρ : H →L[ℂ] H,
        ρ.IsPositive ∧
        reTr ρ = 1 ∧
        ∀ P : H →L[ℂ] H, IsOrthProj P → f.μ P = reTr (ρ * P)

end ClassicalGleason
