import Gleason.Harmonic.Auxiliary.PoleAverage
import Gleason.Harmonic.Sphere.S2GreatCircleConstraint
import Gleason.Harmonic.Sphere.SphericalSectorProjection
import SphericalHarmonics.LowDegree

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

/-- Precompose a function on `spherePoint3` with the bridge `S² → spherePoint3`. -/
def pullSpherePoint3FnLinear : (spherePoint3 → ℝ) →ₗ[ℝ] (S2 → ℝ) where
  toFun g := fun z => g (s2ToSpherePoint3 z)
  map_add' := by
    intro f g
    rfl
  map_smul' := by
    intro c f
    rfl

/-- The transported pole-average operator on `S²`, valued in functions on `S²`. -/
def s2PoleAverageLinear : C(S2, ℝ) →ₗ[ℝ] (S2 → ℝ) :=
  pullSpherePoint3FnLinear.comp <| poleAverageLinear.comp s2Pullback.toLinearMap

@[simp] theorem s2PoleAverageLinear_apply
    (f : C(S2, ℝ)) (z : S2) :
    s2PoleAverageLinear f z =
      poleAverageLinear (s2Pullback f) (s2ToSpherePoint3 z) := by
  rfl

@[simp] theorem poleAverageLinear_const (c : ℝ) :
    poleAverageLinear (ContinuousMap.const _ c) = fun _ : spherePoint3 => c := by
  ext z
  rw [poleAverageLinear_apply, greatCircleAverageLinear_apply, northEquatorAverageLinear_apply]
  have hfun :
      (fun θ : ℝ =>
        (spherePrecomp
          (sphereTripleIsometryEquiv (poleChoiceX z) (poleChoiceY z) z
            (poleChoice_spec z).1 (poleChoice_spec z).2.1 (poleChoice_spec z).2.2)
          (ContinuousMap.const _ c)) (equatorSpherePoint θ)) = fun _ : ℝ => c := by
    funext θ
    simp [spherePrecomp_apply]
  rw [hfun, intervalIntegral.integral_const]
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [hpi]
  simpa [two_mul, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

@[simp] theorem s2PoleAverageLinear_const (c : ℝ) :
    s2PoleAverageLinear (ContinuousMap.const _ c) = fun _ : S2 => c := by
  have hpull : s2Pullback (ContinuousMap.const _ c) = ContinuousMap.const _ c := by
    ext x
    rfl
  ext z
  rw [s2PoleAverageLinear_apply, hpull, poleAverageLinear_const]

/-- The transported pole-average centered-constraint operator on `S²`, valued in functions on
`S²`. -/
def s2PoleAverageCenteredConstraintLinear : C(S2, ℝ) →ₗ[ℝ] (S2 → ℝ) :=
  pullSpherePoint3FnLinear.comp <|
    poleAverageCenteredConstraintLinear.comp s2Pullback.toLinearMap

@[simp] theorem s2PoleAverageCenteredConstraintLinear_apply
    (f : C(S2, ℝ)) (z : S2) :
    s2PoleAverageCenteredConstraintLinear f z =
      poleAverageCenteredConstraintLinear (s2Pullback f) (s2ToSpherePoint3 z) := by
  rfl

theorem s2PoleAverageCenteredConstraintLinear_apply_eq
    (f : C(S2, ℝ)) (z : S2) :
    s2PoleAverageCenteredConstraintLinear f z =
      s2PoleAverageLinear f z + f z / 2 - (3 / 2 : ℝ) * sphereFrameCenter (s2Pullback f) := by
  rw [s2PoleAverageCenteredConstraintLinear_apply, poleAverageCenteredConstraintLinear_apply,
    s2PoleAverageLinear_apply, sphereFrameCentered_apply]
  have hconst :
      poleAverageLinear (ContinuousMap.const _ (sphereFrameCenter (s2Pullback f)))
        (s2ToSpherePoint3 z) =
      sphereFrameCenter (s2Pullback f) := by
    simpa using congrArg (fun g : spherePoint3 → ℝ => g (s2ToSpherePoint3 z))
      (poleAverageLinear_const (sphereFrameCenter (s2Pullback f)))
  have hpole :
      poleAverageLinear (sphereFrameCentered (s2Pullback f)) (s2ToSpherePoint3 z) =
        poleAverageLinear (s2Pullback f) (s2ToSpherePoint3 z) -
          sphereFrameCenter (s2Pullback f) := by
    rw [show sphereFrameCentered (s2Pullback f) =
        s2Pullback f - ContinuousMap.const _ (sphereFrameCenter (s2Pullback f)) by rfl]
    rw [map_sub]
    simpa [Pi.sub_apply] using hconst
  rw [hpole, s2Pullback_apply]
  have hs2 : spherePoint3ToS2 (s2ToSpherePoint3 z) = z := by simp
  rw [hs2]
  ring_nf

private theorem one_mem_sector_zero : (1 : C(S2, ℝ)) ∈ sector 0 := by
  have hz0 : zonal0 = (1 : C(S2, ℝ)) := by
    ext x
    simp [zonal0, zonalFromPolynomial]
  rw [← hz0]
  exact zonal0_mem_sector

@[simp] theorem ambientSectorProjectionContinuous_const_eq_zero_of_ne_zero
    {n : ℕ} (hn0 : n ≠ 0) (c : ℝ) :
    ambientSectorProjectionContinuous n (ContinuousMap.const _ c) = 0 := by
  have hconstEq : (ContinuousMap.const _ c : C(S2, ℝ)) = c • (1 : C(S2, ℝ)) := by
    ext x
    simp
  have hconst : (ContinuousMap.const _ c : C(S2, ℝ)) ∈ sector 0 := by
    rw [hconstEq]
    exact (sector 0).smul_mem c one_mem_sector_zero
  exact ambientSectorProjectionContinuous_eq_zero_of_orthogonal
    (m := 0) (n := n) (by simpa using hn0.symm) hconst

theorem mem_continuousSphereGreatCircleConstraintSubmoduleS2_iff_s2PoleAverageCenteredConstraint
    (f : C(S2, ℝ)) :
    f ∈ continuousSphereGreatCircleConstraintSubmoduleS2 ↔
      s2PoleAverageCenteredConstraintLinear f = 0 := by
  constructor
  · intro hf
    ext z
    have h0 :
        poleAverageCenteredConstraintLinear (s2Pullback f) = 0 :=
      (mem_continuousSphereGreatCircleConstraintSubmodule_iff_poleAverageCenteredConstraint
        (s2Pullback f)).1 hf
    simpa [s2PoleAverageCenteredConstraintLinear_apply] using
      congrArg (fun g : spherePoint3 → ℝ => g (s2ToSpherePoint3 z)) h0
  · intro h0
    rw [mem_continuousSphereGreatCircleConstraintSubmoduleS2_iff]
    rw [mem_continuousSphereGreatCircleConstraintSubmodule_iff_poleAverageCenteredConstraint]
    ext x
    have hx := congrArg (fun g : S2 → ℝ => g (spherePoint3ToS2 x)) h0
    simpa [s2PoleAverageCenteredConstraintLinear_apply] using hx

theorem s2PoleAverageCenteredConstraintLinear_ne_zero_of_not_mem_continuousSphereGreatCircleConstraintSubmoduleS2
    {f : C(S2, ℝ)}
    (hf : f ∉ continuousSphereGreatCircleConstraintSubmoduleS2) :
    s2PoleAverageCenteredConstraintLinear f ≠ 0 := by
  intro h0
  exact hf <|
    (mem_continuousSphereGreatCircleConstraintSubmoduleS2_iff_s2PoleAverageCenteredConstraint f).2
      h0

end GleasonS2Bridge
