import SphericalHarmonics.SectorOperator
import Gleason.Harmonic.Sphere.S2ExceptionalSectorReduction
import Gleason.Harmonic.Sphere.S2PoleAverageExceptionalDegree
import Gleason.Harmonic.Sphere.SphereDegreeProjection
import Gleason.Harmonic.PoleAverage.PoleAverageLift

noncomputable section

open scoped ENNReal MeasureTheory

namespace GleasonS2Bridge

open SphericalHarmonics

/-- Continuous-level projection commutation follows from an equivariant `L²` lift.

This is the form needed for the Funk transform: once a continuous operator on functions is shown
to be represented on `L²(S²)` by a continuous rotation-equivariant endomorphism, it commutes with
all harmonic degree projections. -/
theorem ambientSectorProjectionContinuous_commute_of_l2_equivariant_lift
    (A : C(S2, ℝ) →ₗ[ℝ] C(S2, ℝ))
    (T : L2S2Geom →L[ℝ] L2S2Geom)
    (hTrot : ContinuousLinearMap.IsRotationEquivariant T)
    (hlift : ∀ f : C(S2, ℝ), continuousToLp (A f) = T (continuousToLp f))
    (n : ℕ) (f : C(S2, ℝ)) :
    ambientSectorProjectionContinuous n (A f) =
      A (ambientSectorProjectionContinuous n f) := by
  apply
    (ContinuousMap.toLp_injective
      (p := (2 : ℝ≥0∞)) (μ := rotationMeasure) (𝕜 := ℝ) (E := ℝ))
  calc
    continuousToLp (ambientSectorProjectionContinuous n (A f))
        = (sectorL2 n).starProjection (continuousToLp (A f)) := by
            exact continuousToLp_ambientSectorProjectionContinuous n (A f)
    _ = (sectorL2 n).starProjection (T (continuousToLp f)) := by
            rw [hlift f]
    _ = T ((sectorL2 n).starProjection (continuousToLp f)) := by
            exact
              SphericalHarmonics.ContinuousLinearMap.sectorL2_starProjection_commute_of_isRotationEquivariant
                hTrot n (continuousToLp f)
    _ = T (continuousToLp (ambientSectorProjectionContinuous n f)) := by
            rw [continuousToLp_ambientSectorProjectionContinuous]
    _ = continuousToLp (A (ambientSectorProjectionContinuous n f)) := by
            rw [hlift (ambientSectorProjectionContinuous n f)]

/-- A continuous rotation-equivariant `L²` lift of pole averaging gives the
degree-projection commutation needed in the endpoint argument.

The continuous pole-average operator supplies `A`; the remaining analytic obligation for this
interface is the corresponding equivariant `L²` operator `T` satisfying `hlift`. -/
theorem projected_poleAverage_commutation_of_l2_equivariant_poleAverage_lift
    (A : C(S2, ℝ) →ₗ[ℝ] C(S2, ℝ))
    (T : L2S2Geom →L[ℝ] L2S2Geom)
    (hTrot : ContinuousLinearMap.IsRotationEquivariant T)
    (hlift : ∀ f : C(S2, ℝ), continuousToLp (A f) = T (continuousToLp f))
    (hA_pole : ∀ f : C(S2, ℝ), s2Pullback (A f) = poleAverageLinear (s2Pullback f))
    (n : ℕ) (g : C(S2, ℝ)) :
    poleAverageLinear
        (harmonicDegreeProjectionContinuous n (s2Pullback g)) sphereE3 =
      harmonicDegreeProjectionContinuous n (s2Pullback (A g)) sphereE3 := by
  have hcomm :
      ambientSectorProjectionContinuous n (A g) =
        A (ambientSectorProjectionContinuous n g) :=
    ambientSectorProjectionContinuous_commute_of_l2_equivariant_lift
      A T hTrot hlift n g
  have hpull :=
    congrArg (fun f : C(S2, ℝ) => s2Pullback f) hcomm
  have hval :=
    congrArg (fun f : C(spherePoint3, ℝ) => f sphereE3) hpull
  calc
    poleAverageLinear
        (harmonicDegreeProjectionContinuous n (s2Pullback g)) sphereE3
        =
      poleAverageLinear
        (s2Pullback (ambientSectorProjectionContinuous n g)) sphereE3 := by
        simp [harmonicDegreeProjectionContinuous]
    _ = s2Pullback (A (ambientSectorProjectionContinuous n g)) sphereE3 := by
        rw [hA_pole (ambientSectorProjectionContinuous n g)]
    _ = s2Pullback (ambientSectorProjectionContinuous n (A g)) sphereE3 := hval.symm
    _ = harmonicDegreeProjectionContinuous n (s2Pullback (A g)) sphereE3 := by
        simp [harmonicDegreeProjectionContinuous]

/-- The same interface specialized to a point-constraint input, where the
already-formalized continuous representative of pole averaging is available. -/
theorem projected_poleAverage_commutation_of_l2_equivariant_poleAverage_lift_pointConstraint
    (A : C(S2, ℝ) →ₗ[ℝ] C(S2, ℝ))
    (T : L2S2Geom →L[ℝ] L2S2Geom)
    (hTrot : ContinuousLinearMap.IsRotationEquivariant T)
    (hlift : ∀ f : C(S2, ℝ), continuousToLp (A f) = T (continuousToLp f))
    (hA_pole : ∀ f : C(S2, ℝ), s2Pullback (A f) = poleAverageLinear (s2Pullback f))
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
  have hcomm :=
    projected_poleAverage_commutation_of_l2_equivariant_poleAverage_lift
      A T hTrot hlift hA_pole n g
  have hAg :
      A g =
        s2PoleAverageContinuousOfGreatCircleConstraint g
          (by
            have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
              simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                using hgpc
            exact continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
              hframe) := by
    apply s2Pullback.injective
    ext x
    change s2Pullback (A g) x =
      s2Pullback
        (s2PoleAverageContinuousOfGreatCircleConstraint g
          (by
            have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
              simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                using hgpc
            exact continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
              hframe)) x
    rw [hA_pole g]
    exact
      congrFun
        (s2Pullback_s2PoleAverageContinuousOfPointConstraint_eq_poleAverageLinear hgpc).symm x
  simpa [hAg] using hcomm

theorem projected_poleAverage_commutation_of_l2_poleAverage_operator
    (T : L2S2Geom →L[ℝ] L2S2Geom)
    (hTrot : ContinuousLinearMap.IsRotationEquivariant T)
    (hlift :
      ∀ f : C(S2, ℝ),
        continuousToLp (s2PoleAverageContinuousLinear f) = T (continuousToLp f))
    (n : ℕ) (g : C(S2, ℝ)) :
    poleAverageLinear
        (harmonicDegreeProjectionContinuous n (s2Pullback g)) sphereE3 =
      harmonicDegreeProjectionContinuous n
        (s2Pullback (s2PoleAverageContinuousLinear g)) sphereE3 := by
  exact
    projected_poleAverage_commutation_of_l2_equivariant_poleAverage_lift
      s2PoleAverageContinuousLinear T hTrot hlift
      s2Pullback_s2PoleAverageContinuousLinear_eq_poleAverageLinear n g

theorem projected_poleAverage_commutation_of_l2_poleAverage_operator_pointConstraint
    (T : L2S2Geom →L[ℝ] L2S2Geom)
    (hTrot : ContinuousLinearMap.IsRotationEquivariant T)
    (hlift :
      ∀ f : C(S2, ℝ),
        continuousToLp (s2PoleAverageContinuousLinear f) = T (continuousToLp f))
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
    projected_poleAverage_commutation_of_l2_equivariant_poleAverage_lift_pointConstraint
      s2PoleAverageContinuousLinear T hTrot hlift
      s2Pullback_s2PoleAverageContinuousLinear_eq_poleAverageLinear hgpc

end GleasonS2Bridge
