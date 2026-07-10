import Gleason.Harmonic.Sphere.S2PoleAverageOperator
import Gleason.Harmonic.Sphere.S2PointConstraintBridge

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

def s2PoleAverageContinuousOfGreatCircleConstraint
    (f : C(S2, ℝ))
    (_hf : f ∈ continuousSphereGreatCircleConstraintSubmoduleS2) :
    C(S2, ℝ) :=
  ContinuousMap.const _ ((3 / 2 : ℝ) * sphereFrameCenter (s2Pullback f)) - ((1 / 2 : ℝ) • f)

@[simp] theorem s2PoleAverageContinuousOfGreatCircleConstraint_apply
    (f : C(S2, ℝ))
    (hf : f ∈ continuousSphereGreatCircleConstraintSubmoduleS2)
    (z : S2) :
    s2PoleAverageContinuousOfGreatCircleConstraint f hf z =
      (3 / 2 : ℝ) * sphereFrameCenter (s2Pullback f) - f z / 2 := by
  simp [s2PoleAverageContinuousOfGreatCircleConstraint]
  ring

theorem s2PoleAverageLinear_eq_s2PoleAverageContinuousOfGreatCircleConstraint
    {f : C(S2, ℝ)}
    (hf : f ∈ continuousSphereGreatCircleConstraintSubmoduleS2) :
    s2PoleAverageLinear f = s2PoleAverageContinuousOfGreatCircleConstraint f hf := by
  ext z
  have hzero :
      s2PoleAverageCenteredConstraintLinear f z = 0 := by
    have hfun :
        s2PoleAverageCenteredConstraintLinear f = 0 :=
      (mem_continuousSphereGreatCircleConstraintSubmoduleS2_iff_s2PoleAverageCenteredConstraint f).1 hf
    simpa using congrArg (fun g : S2 → ℝ => g z) hfun
  rw [s2PoleAverageCenteredConstraintLinear_apply_eq] at hzero
  have :
      s2PoleAverageLinear f z =
        (3 / 2 : ℝ) * sphereFrameCenter (s2Pullback f) - f z / 2 := by
    linarith
  simpa [s2PoleAverageContinuousOfGreatCircleConstraint_apply] using this

theorem ambientSectorProjectionContinuous_s2PoleAverageContinuousOfGreatCircleConstraint
    {n : ℕ} (hn0 : n ≠ 0)
    {f : C(S2, ℝ)}
    (hf : f ∈ continuousSphereGreatCircleConstraintSubmoduleS2) :
    ambientSectorProjectionContinuous n
      (s2PoleAverageContinuousOfGreatCircleConstraint f hf) =
      -((1 / 2 : ℝ)) • ambientSectorProjectionContinuous n f := by
  have hconst :
      ambientSectorProjectionContinuous n
        (ContinuousMap.const _ ((3 / 2 : ℝ) * sphereFrameCenter (s2Pullback f))) = 0 :=
    ambientSectorProjectionContinuous_const_eq_zero_of_ne_zero hn0 _
  rw [s2PoleAverageContinuousOfGreatCircleConstraint, map_sub, hconst, zero_sub]
  rw [map_smul]
  simp

theorem ambientSectorProjectionContinuous_s2PoleAverageLinear_eq_neg_half_of_mem_greatCircleConstraint
    {n : ℕ} (hn0 : n ≠ 0)
    {f : C(S2, ℝ)}
    (hf : f ∈ continuousSphereGreatCircleConstraintSubmoduleS2) :
    ambientSectorProjectionContinuous n
      (s2PoleAverageContinuousOfGreatCircleConstraint f hf) =
      -((1 / 2 : ℝ)) • ambientSectorProjectionContinuous n f := by
  exact
    ambientSectorProjectionContinuous_s2PoleAverageContinuousOfGreatCircleConstraint
      hn0 hf

theorem s2PoleAverageLinear_eq_s2PoleAverageContinuousOfPointConstraint
    {f : C(S2, ℝ)}
    (hf : f ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2) :
    s2PoleAverageLinear f =
      s2PoleAverageContinuousOfGreatCircleConstraint f
        (by
          have hframe : f ∈ continuousSphereFrameSubmoduleS2 := by
            simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
              using hf
          exact
            continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
              hframe) := by
  have hconstraint : f ∈ continuousSphereGreatCircleConstraintSubmoduleS2 := by
    have hframe : f ∈ continuousSphereFrameSubmoduleS2 := by
      simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
        using hf
    exact
      continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
        hframe
  exact s2PoleAverageLinear_eq_s2PoleAverageContinuousOfGreatCircleConstraint hconstraint

theorem ambientSectorProjectionContinuous_s2PoleAverageLinear_eq_neg_half_of_mem_pointConstraint
    {n : ℕ} (hn0 : n ≠ 0)
    {f : C(S2, ℝ)}
    (hf : f ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2) :
    ambientSectorProjectionContinuous n
      (s2PoleAverageContinuousOfGreatCircleConstraint f
        (by
          have hframe : f ∈ continuousSphereFrameSubmoduleS2 := by
            simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
              using hf
          exact
            continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
              hframe)) =
      -((1 / 2 : ℝ)) • ambientSectorProjectionContinuous n f := by
  have hconstraint : f ∈ continuousSphereGreatCircleConstraintSubmoduleS2 := by
    have hframe : f ∈ continuousSphereFrameSubmoduleS2 := by
      simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
        using hf
    exact
      continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
        hframe
  exact
    ambientSectorProjectionContinuous_s2PoleAverageContinuousOfGreatCircleConstraint hn0 hconstraint

theorem s2Pullback_s2PoleAverageContinuousOfGreatCircleConstraint_eq_poleAverageLinear
    {f : C(S2, ℝ)}
    (hf : f ∈ continuousSphereGreatCircleConstraintSubmoduleS2) :
    s2Pullback (s2PoleAverageContinuousOfGreatCircleConstraint f hf) =
      poleAverageLinear (s2Pullback f) := by
  ext x
  rw [s2Pullback_apply]
  have hEq :=
    congrArg (fun g : S2 → ℝ => g (spherePoint3ToS2 x))
      (s2PoleAverageLinear_eq_s2PoleAverageContinuousOfGreatCircleConstraint hf)
  simpa [s2PoleAverageLinear_apply, s2ToSpherePoint3_symm_apply] using hEq.symm

theorem s2Pullback_s2PoleAverageContinuousOfPointConstraint_eq_poleAverageLinear
    {f : C(S2, ℝ)}
    (hf : f ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2) :
  s2Pullback
      (s2PoleAverageContinuousOfGreatCircleConstraint f
        (by
          have hframe : f ∈ continuousSphereFrameSubmoduleS2 := by
            simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
              using hf
          exact
            continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
              hframe)) =
      poleAverageLinear (s2Pullback f) := by
  have hconstraint : f ∈ continuousSphereGreatCircleConstraintSubmoduleS2 := by
    have hframe : f ∈ continuousSphereFrameSubmoduleS2 := by
      simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
        using hf
    exact
      continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
        hframe
  exact s2Pullback_s2PoleAverageContinuousOfGreatCircleConstraint_eq_poleAverageLinear hconstraint

theorem s2PoleAverageContinuousOfGreatCircleConstraint_mem_continuousSphereGreatCircleConstraintSubmoduleS2
    {f : C(S2, ℝ)}
    (hf : f ∈ continuousSphereGreatCircleConstraintSubmoduleS2) :
    s2PoleAverageContinuousOfGreatCircleConstraint f hf ∈
      continuousSphereGreatCircleConstraintSubmoduleS2 := by
  let g :=
    s2PoleAverageContinuousOfGreatCircleConstraint f hf
  rw [mem_continuousSphereGreatCircleConstraintSubmoduleS2_iff_s2PoleAverageCenteredConstraint]
  ext z
  have hf0 :
      s2PoleAverageCenteredConstraintLinear f = 0 :=
    (mem_continuousSphereGreatCircleConstraintSubmoduleS2_iff_s2PoleAverageCenteredConstraint f).1 hf
  have hfz : s2PoleAverageCenteredConstraintLinear f z = 0 := by
    simpa using congrArg (fun g : S2 → ℝ => g z) hf0
  have hcenter :
      sphereFrameCenter (s2Pullback g) =
        sphereFrameCenter (s2Pullback f) := by
    dsimp [g, s2PoleAverageContinuousOfGreatCircleConstraint]
    simp [s2Pullback_apply, sphereFrameCenter, sub_eq_add_neg]
    ring
  have hpole :
      s2PoleAverageLinear g z =
        (3 / 2 : ℝ) * sphereFrameCenter (s2Pullback f) -
          s2PoleAverageLinear f z / 2 := by
    have hfun :
        s2PoleAverageLinear g =
          s2PoleAverageLinear
            (ContinuousMap.const _ ((3 / 2 : ℝ) * sphereFrameCenter (s2Pullback f))) -
            ((1 / 2 : ℝ) • s2PoleAverageLinear f) := by
      dsimp [g, s2PoleAverageContinuousOfGreatCircleConstraint]
      simp
    have hz' := congrArg (fun h : S2 → ℝ => h z) hfun
    rw [s2PoleAverageLinear_const] at hz'
    simp only [Pi.sub_apply, Pi.smul_apply] at hz'
    simpa [sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hz'
  have hgval :
      g z = (3 / 2 : ℝ) * sphereFrameCenter (s2Pullback f) - f z / 2 := by
    simp [g, s2PoleAverageContinuousOfGreatCircleConstraint_apply]
  rw [s2PoleAverageCenteredConstraintLinear_apply_eq]
  rw [hpole, hgval, hcenter]
  rw [s2PoleAverageCenteredConstraintLinear_apply_eq] at hfz
  have hfz' := hfz
  ring_nf at hfz' ⊢
  have hscaled := congrArg (fun t : ℝ => (-((1 / 2 : ℝ))) * t) hfz'
  ring_nf at hscaled
  simpa using hscaled

theorem s2PoleAverageContinuousOfPointConstraint_mem_continuousSphereGreatCircleConstraintSubmoduleS2
    {f : C(S2, ℝ)}
    (hf : f ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2) :
    s2PoleAverageContinuousOfGreatCircleConstraint f
        (by
          have hframe : f ∈ continuousSphereFrameSubmoduleS2 := by
            simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
              using hf
          exact
            continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
              hframe) ∈
      continuousSphereGreatCircleConstraintSubmoduleS2 := by
  have hconstraint : f ∈ continuousSphereGreatCircleConstraintSubmoduleS2 := by
    have hframe : f ∈ continuousSphereFrameSubmoduleS2 := by
      simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
        using hf
    exact
      continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
        hframe
  exact
    s2PoleAverageContinuousOfGreatCircleConstraint_mem_continuousSphereGreatCircleConstraintSubmoduleS2
      hconstraint

theorem continuousSphereFrameSubmoduleS2_const
    (c : ℝ) :
    ContinuousMap.const _ c ∈ continuousSphereFrameSubmoduleS2 := by
  show s2Pullback (ContinuousMap.const _ c) ∈ continuousSphereFrameSubmodule
  intro x y z hxy hxz hyz
  simp

theorem s2PoleAverageContinuousOfPointConstraint_mem_continuousSphereGreatCirclePointConstraintSubmoduleS2
    {f : C(S2, ℝ)}
    (hf : f ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2) :
    s2PoleAverageContinuousOfGreatCircleConstraint f
        (by
          have hframe : f ∈ continuousSphereFrameSubmoduleS2 := by
            simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
              using hf
          exact
            continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
              hframe) ∈
      continuousSphereGreatCirclePointConstraintSubmoduleS2 := by
  have hframe : f ∈ continuousSphereFrameSubmoduleS2 := by
    simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
      using hf
  have hconst :
      ContinuousMap.const _ ((3 / 2 : ℝ) * sphereFrameCenter (s2Pullback f)) ∈
        continuousSphereFrameSubmoduleS2 :=
    continuousSphereFrameSubmoduleS2_const _
  have hgframe :
      s2PoleAverageContinuousOfGreatCircleConstraint f
          (by
            have hframe' : f ∈ continuousSphereFrameSubmoduleS2 := by
              simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                using hf
            exact
              continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                hframe') ∈
        continuousSphereFrameSubmoduleS2 := by
    exact continuousSphereFrameSubmoduleS2.sub_mem hconst
      (continuousSphereFrameSubmoduleS2.smul_mem ((1 / 2 : ℝ)) hframe)
  simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
    using hgframe

end GleasonS2Bridge
