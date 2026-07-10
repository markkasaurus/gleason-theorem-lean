import Gleason.Harmonic.Auxiliary.FunkSpectralBridge
import Mathlib.Analysis.Normed.Operator.Extend

noncomputable section

open scoped ENNReal MeasureTheory

namespace GleasonS2Bridge

open SphericalHarmonics

def s2PoleAverageToL2Linear : C(S2, ℝ) →ₗ[ℝ] L2S2Geom :=
  continuousToLp.toLinearMap.comp s2PoleAverageContinuousLinear

@[simp] theorem s2PoleAverageToL2Linear_apply (f : C(S2, ℝ)) :
    s2PoleAverageToL2Linear f =
      continuousToLp (s2PoleAverageContinuousLinear f) := rfl

def s2PoleAverageL2OperatorOfBound
    (C : ℝ)
    (_hbound :
      ∀ f : C(S2, ℝ),
        ‖continuousToLp (s2PoleAverageContinuousLinear f)‖ ≤
          C * ‖continuousToLp f‖) :
    L2S2Geom →L[ℝ] L2S2Geom :=
  s2PoleAverageToL2Linear.extendOfNorm continuousToLp.toLinearMap

theorem s2PoleAverageL2OperatorOfBound_apply
    (C : ℝ)
    (hbound :
      ∀ f : C(S2, ℝ),
        ‖continuousToLp (s2PoleAverageContinuousLinear f)‖ ≤
          C * ‖continuousToLp f‖)
    (f : C(S2, ℝ)) :
    s2PoleAverageL2OperatorOfBound C hbound (continuousToLp f) =
      continuousToLp (s2PoleAverageContinuousLinear f) := by
  simpa [s2PoleAverageL2OperatorOfBound, s2PoleAverageToL2Linear] using
    LinearMap.extendOfNorm_eq
      (f := s2PoleAverageToL2Linear)
      (e := continuousToLp.toLinearMap)
      continuousToLp_denseRange
      ⟨C, hbound⟩
      f

theorem s2PoleAverageL2OperatorOfBound_isRotationEquivariant
    (C : ℝ)
    (hbound :
      ∀ f : C(S2, ℝ),
        ‖continuousToLp (s2PoleAverageContinuousLinear f)‖ ≤
          C * ‖continuousToLp f‖) :
    ContinuousLinearMap.IsRotationEquivariant
      (s2PoleAverageL2OperatorOfBound C hbound) := by
  intro ρ x
  let T : L2S2Geom →L[ℝ] L2S2Geom :=
    s2PoleAverageL2OperatorOfBound C hbound
  have hclosed :
      IsClosed
        {x : L2S2Geom |
          T (Rotation.compL2Rotation ρ x) =
            Rotation.compL2Rotation ρ (T x)} := by
    exact isClosed_eq
      (T.continuous.comp (Rotation.compL2Rotation ρ).continuous)
      ((Rotation.compL2Rotation ρ).continuous.comp T.continuous)
  refine continuousToLp_denseRange.induction_on x hclosed ?_
  intro f
  calc
    T (Rotation.compL2Rotation ρ (continuousToLp f))
        = T (continuousToLp (Rotation.compContinuous ρ.symm f)) := by
            rw [continuousToLp_compContinuous_symm]
    _ = continuousToLp
          (s2PoleAverageContinuousLinear (Rotation.compContinuous ρ.symm f)) := by
            rw [s2PoleAverageL2OperatorOfBound_apply]
    _ = continuousToLp
          (Rotation.compContinuous ρ.symm (s2PoleAverageContinuousLinear f)) := by
            rw [s2PoleAverageContinuousLinear_compContinuous]
    _ = Rotation.compL2Rotation ρ
          (continuousToLp (s2PoleAverageContinuousLinear f)) := by
            rw [continuousToLp_compContinuous_symm]
    _ = Rotation.compL2Rotation ρ (T (continuousToLp f)) := by
            rw [s2PoleAverageL2OperatorOfBound_apply]

theorem projected_poleAverage_commutation_of_l2_bound
    (C : ℝ)
    (hbound :
      ∀ f : C(S2, ℝ),
        ‖continuousToLp (s2PoleAverageContinuousLinear f)‖ ≤
          C * ‖continuousToLp f‖)
    (n : ℕ) (g : C(S2, ℝ)) :
    poleAverageLinear
        (harmonicDegreeProjectionContinuous n (s2Pullback g)) sphereE3 =
      harmonicDegreeProjectionContinuous n
        (s2Pullback (s2PoleAverageContinuousLinear g)) sphereE3 := by
  exact
    projected_poleAverage_commutation_of_l2_poleAverage_operator
      (s2PoleAverageL2OperatorOfBound C hbound)
      (s2PoleAverageL2OperatorOfBound_isRotationEquivariant C hbound)
      (fun f => (s2PoleAverageL2OperatorOfBound_apply C hbound f).symm)
      n g

theorem projected_poleAverage_commutation_of_l2_bound_pointConstraint
    (C : ℝ)
    (hbound :
      ∀ f : C(S2, ℝ),
        ‖continuousToLp (s2PoleAverageContinuousLinear f)‖ ≤
          C * ‖continuousToLp f‖)
    {n : ℕ} {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2) :
    poleAverageLinear
        (harmonicDegreeProjectionContinuous n (s2Pullback g)) sphereE3 =
      harmonicDegreeProjectionContinuous n
        (s2Pullback
          (s2PoleAverageContinuousOfGreatCircleConstraint g
            (by
              have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
                simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                  using hgpc
              exact continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                hframe)))
        sphereE3 := by
  exact
    projected_poleAverage_commutation_of_l2_poleAverage_operator_pointConstraint
      (s2PoleAverageL2OperatorOfBound C hbound)
      (s2PoleAverageL2OperatorOfBound_isRotationEquivariant C hbound)
      (fun f => (s2PoleAverageL2OperatorOfBound_apply C hbound f).symm)
      hgpc

end GleasonS2Bridge
