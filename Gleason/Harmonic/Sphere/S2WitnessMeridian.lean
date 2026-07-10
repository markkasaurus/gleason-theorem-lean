import Gleason.Harmonic.Sphere.SphereDegreeProjection
import Gleason.Harmonic.Sphere.S2DistinguishedNorthZonal
import Gleason.Harmonic.HighDegree.EvenBoundedLowDegree
import Gleason.Harmonic.Zonal.NorthFixedMeridian
import Gleason.Harmonic.PoleAverage.PoleAverageProfilePoly
import Gleason.Harmonic.Profile.SquaredQuotientSpecialZBridge
import Gleason.Harmonic.Sphere.S2DistinguishedSquaredProfilePoly

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

theorem sphereCoordMvEval_specialZPoint_eq_northMeridianPolynomial_eval
    {g : C(spherePoint3, ℝ)} {p : MvPolynomial (Fin 3) ℝ}
    (hgz : IsNorthZonal g)
    (hpEval : sphereCoordMvEval p = g)
    (r : Set.Icc (0 : ℝ) 1) :
    g (specialZPoint r) =
      (northMeridianPolynomial p).eval (Real.sqrt (1 - r.1 ^ 2)) := by
  calc
    g (specialZPoint r)
        = northZonalProfile g
            ⟨sphereCoordZ (specialZPoint r), snd_mem_Icc (specialZPoint r)⟩ := by
              simpa using
                (northZonalProfile_eq_of_isNorthZonal hgz (specialZPoint r)).symm
    _ = (northMeridianPolynomial p).eval
          (sphereCoordZ (specialZPoint r)) := by
            simpa using
              northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal
                hgz hpEval ⟨sphereCoordZ (specialZPoint r), snd_mem_Icc (specialZPoint r)⟩
    _ = (northMeridianPolynomial p).eval (Real.sqrt (1 - r.1 ^ 2)) := by
          simp

theorem sphereCoordMvEval_specialXPoint_eq_northMeridianPolynomial_eval
    {g : C(spherePoint3, ℝ)} {p : MvPolynomial (Fin 3) ℝ}
    (hgz : IsNorthZonal g)
    (hpEval : sphereCoordMvEval p = g)
    (r : Set.Icc (0 : ℝ) 1) :
    g (specialXPoint r) =
      (northMeridianPolynomial p).eval r.1 := by
  calc
    g (specialXPoint r)
        = northZonalProfile g (nonnegIccToIcc r) := by
            simpa using (northZonalProfile_nonneg_of_isNorthZonal hgz r).symm
    _ = (northMeridianPolynomial p).eval r.1 := by
          simpa [nonnegIccToIcc] using
            northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal
              hgz hpEval (nonnegIccToIcc r)

theorem exists_nonzero_northMeridianPolynomial_of_northFixed_pointConstraint_witness
    {n : ℕ} {g : C(S2, ℝ)}
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ p : harmonicHomogeneousSubmodule n,
      harmonicDegreeProjectionContinuous n (s2Pullback g) = sphereCoordMvEval p.1 ∧
      northMeridianPolynomial p.1 ≠ 0 := by
  rcases exists_nonzero_northMeridianPolynomial_of_distinguishedZonalSector n with
    ⟨p, hpRes, hpMer⟩
  refine ⟨p, ?_, hpMer⟩
  calc
    harmonicDegreeProjectionContinuous n (s2Pullback g)
        = s2Pullback (ambientSectorProjectionContinuous n g) := by
            simp
    _ = s2Pullback
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
            rw [hgproj]
    _ = sphereCoordMvEval p.1 := by
          rw [← s2Pullback_restrictToSphere p.1, hpRes]

theorem exists_nonzero_northMeridianPolynomial_with_bad_degree_poleAverage_identity
    {n : ℕ} (hn0 : n ≠ 0) {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ p : harmonicHomogeneousSubmodule n,
      harmonicDegreeProjectionContinuous n (s2Pullback g) = sphereCoordMvEval p.1 ∧
      northMeridianPolynomial p.1 ≠ 0 ∧
      let gavg : C(S2, ℝ) :=
        s2PoleAverageContinuousOfGreatCircleConstraint g
          (by
            have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
              simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                using hgpc
            exact
              continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                hframe)
      harmonicDegreeProjectionContinuous n (s2Pullback gavg) =
        -((1 / 2 : ℝ)) • sphereCoordMvEval p.1 := by
  rcases
      exists_nonzero_northMeridianPolynomial_of_northFixed_pointConstraint_witness
        hgproj with
    ⟨p, hpProj, hpMer⟩
  refine ⟨p, hpProj, hpMer, ?_⟩
  calc
    harmonicDegreeProjectionContinuous n
        (s2Pullback
          (s2PoleAverageContinuousOfGreatCircleConstraint g
            (by
              have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
                simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                  using hgpc
              exact
                continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                  hframe)))
        = -((1 / 2 : ℝ)) • harmonicDegreeProjectionContinuous n (s2Pullback g) := by
            simpa using
              harmonicDegreeProjectionContinuous_s2PoleAverageContinuousOfPointConstraint_eq_neg_half
                (n := n) hn0 hgpc
    _ = -((1 / 2 : ℝ)) • sphereCoordMvEval p.1 := by rw [hpProj]

theorem exists_nonzero_northMeridianPolynomial_with_bad_degree_special_average_identity
    {n : ℕ} {g : C(S2, ℝ)}
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ p : harmonicHomogeneousSubmodule n,
      harmonicDegreeProjectionContinuous n (s2Pullback g) = sphereCoordMvEval p.1 ∧
      northMeridianPolynomial p.1 ≠ 0 ∧
      ∀ r : Set.Icc (0 : ℝ) 1,
        2 *
            poleAverageLinear
              (harmonicDegreeProjectionContinuous n (s2Pullback g))
              (specialZPoint r) =
          (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1 := by
  rcases
      exists_nonzero_northMeridianPolynomial_of_northFixed_pointConstraint_witness
        hgproj with
    ⟨p, hpProj, hpMer⟩
  refine ⟨p, hpProj, hpMer, ?_⟩
  intro r
  have hpDist :
      sphereCoordMvEval p.1 =
        s2Pullback
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
    calc
      sphereCoordMvEval p.1
          = harmonicDegreeProjectionContinuous n (s2Pullback g) := hpProj.symm
      _ = s2Pullback (ambientSectorProjectionContinuous n g) := by simp
      _ = s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
              rw [hgproj]
  rw [hpProj]
  exact
    two_mul_poleAverageLinear_specialZPoint_eq_northZonalScalarPolynomial
      (hgz := by
        rw [hpDist]
        exact isNorthZonal_s2Pullback_distinguishedZonalSector n)
      (hpEval := rfl)
      r

theorem exists_nonzero_northMeridianPolynomial_with_bad_degree_special_value_identity
    {n : ℕ} (hn0 : n ≠ 0) {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ p : harmonicHomogeneousSubmodule n,
      harmonicDegreeProjectionContinuous n (s2Pullback g) = sphereCoordMvEval p.1 ∧
      northMeridianPolynomial p.1 ≠ 0 ∧
      ∀ r : Set.Icc (0 : ℝ) 1,
        harmonicDegreeProjectionContinuous n
            (s2Pullback
              (s2PoleAverageContinuousOfGreatCircleConstraint g
                (by
                  have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
                    simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                      using hgpc
                  exact
                    continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                      hframe)))
            (specialZPoint r) =
          -((1 / 2 : ℝ)) *
            (northMeridianPolynomial p.1).eval (Real.sqrt (1 - r.1 ^ 2)) := by
  rcases
      exists_nonzero_northMeridianPolynomial_with_bad_degree_poleAverage_identity
        hn0 hgpc hgproj with
    ⟨p, hpProj, hpMer, hpAvg⟩
  refine ⟨p, hpProj, hpMer, ?_⟩
  intro r
  have hpDist :
      sphereCoordMvEval p.1 =
        s2Pullback
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
    calc
      sphereCoordMvEval p.1
          = harmonicDegreeProjectionContinuous n (s2Pullback g) := hpProj.symm
      _ = s2Pullback (ambientSectorProjectionContinuous n g) := by simp
      _ = s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
              rw [hgproj]
  have hmerEval :
      sphereCoordMvEval p.1 (specialZPoint r) =
        (northMeridianPolynomial p.1).eval (Real.sqrt (1 - r.1 ^ 2)) := by
    exact
      sphereCoordMvEval_specialZPoint_eq_northMeridianPolynomial_eval
        (hgz := by
          rw [hpDist]
          exact isNorthZonal_s2Pullback_distinguishedZonalSector n)
        (hpEval := rfl)
        r
  have hpoint :=
    congrArg
      (fun f : C(spherePoint3, ℝ) => f (specialZPoint r))
      hpAvg
  simpa [hmerEval]
    using hpoint

theorem exists_nonzero_northMeridianPolynomial_with_bad_degree_special_system
    {n : ℕ} (hn0 : n ≠ 0) {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ p : harmonicHomogeneousSubmodule n,
      harmonicDegreeProjectionContinuous n (s2Pullback g) = sphereCoordMvEval p.1 ∧
      northMeridianPolynomial p.1 ≠ 0 ∧
      (∀ r : Set.Icc (0 : ℝ) 1,
        2 *
            poleAverageLinear
              (harmonicDegreeProjectionContinuous n (s2Pullback g))
              (specialZPoint r) =
          (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1) ∧
      (∀ r : Set.Icc (0 : ℝ) 1,
        harmonicDegreeProjectionContinuous n
            (s2Pullback
              (s2PoleAverageContinuousOfGreatCircleConstraint g
                (by
                  have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
                    simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                      using hgpc
                  exact
                    continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                      hframe)))
            (specialZPoint r) =
          -((1 / 2 : ℝ)) *
            (northMeridianPolynomial p.1).eval (Real.sqrt (1 - r.1 ^ 2))) := by
  rcases
      exists_nonzero_northMeridianPolynomial_of_northFixed_pointConstraint_witness
        hgproj with
    ⟨p, hpProj, hpMer⟩
  refine ⟨p, hpProj, hpMer, ?_, ?_⟩
  · intro r
    have hpDist :
        sphereCoordMvEval p.1 =
          s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
      calc
        sphereCoordMvEval p.1
            = harmonicDegreeProjectionContinuous n (s2Pullback g) := hpProj.symm
        _ = s2Pullback (ambientSectorProjectionContinuous n g) := by simp
        _ = s2Pullback
              (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
                rw [hgproj]
    rw [hpProj]
    exact
      two_mul_poleAverageLinear_specialZPoint_eq_northZonalScalarPolynomial
        (hgz := by
          rw [hpDist]
          exact isNorthZonal_s2Pullback_distinguishedZonalSector n)
        (hpEval := rfl)
        r
  · intro r
    have hpAvg :
        harmonicDegreeProjectionContinuous n
            (s2Pullback
              (s2PoleAverageContinuousOfGreatCircleConstraint g
                (by
                  have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
                    simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                      using hgpc
                  exact
                    continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                      hframe))) =
          -((1 / 2 : ℝ)) • sphereCoordMvEval p.1 := by
      calc
        harmonicDegreeProjectionContinuous n
            (s2Pullback
              (s2PoleAverageContinuousOfGreatCircleConstraint g
                (by
                  have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
                    simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                      using hgpc
                  exact
                    continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                      hframe)))
            = -((1 / 2 : ℝ)) • harmonicDegreeProjectionContinuous n (s2Pullback g) := by
                simpa using
                  harmonicDegreeProjectionContinuous_s2PoleAverageContinuousOfPointConstraint_eq_neg_half
                    (n := n) hn0 hgpc
        _ = -((1 / 2 : ℝ)) • sphereCoordMvEval p.1 := by rw [hpProj]
    have hpDist :
        sphereCoordMvEval p.1 =
          s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
      calc
        sphereCoordMvEval p.1
            = harmonicDegreeProjectionContinuous n (s2Pullback g) := hpProj.symm
        _ = s2Pullback (ambientSectorProjectionContinuous n g) := by simp
        _ = s2Pullback
              (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
                rw [hgproj]
    have hmerEval :
        sphereCoordMvEval p.1 (specialZPoint r) =
          (northMeridianPolynomial p.1).eval (Real.sqrt (1 - r.1 ^ 2)) := by
      exact
        sphereCoordMvEval_specialZPoint_eq_northMeridianPolynomial_eval
          (hgz := by
            rw [hpDist]
            exact isNorthZonal_s2Pullback_distinguishedZonalSector n)
          (hpEval := rfl)
          r
    have hpoint :=
      congrArg
        (fun f : C(spherePoint3, ℝ) => f (specialZPoint r))
        hpAvg
    simpa [hmerEval]
      using hpoint

theorem exists_nonzero_northMeridianPolynomial_with_bad_degree_specialX_value_identity
    {n : ℕ} (hn0 : n ≠ 0) {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ p : harmonicHomogeneousSubmodule n,
      harmonicDegreeProjectionContinuous n (s2Pullback g) = sphereCoordMvEval p.1 ∧
      northMeridianPolynomial p.1 ≠ 0 ∧
      ∀ r : Set.Icc (0 : ℝ) 1,
        harmonicDegreeProjectionContinuous n
            (s2Pullback
              (s2PoleAverageContinuousOfGreatCircleConstraint g
                (by
                  have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
                    simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                      using hgpc
                  exact
                    continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                      hframe)))
            (specialXPoint r) =
          -((1 / 2 : ℝ)) * (northMeridianPolynomial p.1).eval r.1 := by
  rcases
      exists_nonzero_northMeridianPolynomial_with_bad_degree_poleAverage_identity
        hn0 hgpc hgproj with
    ⟨p, hpProj, hpMer, hpAvg⟩
  refine ⟨p, hpProj, hpMer, ?_⟩
  intro r
  have hpDist :
      sphereCoordMvEval p.1 =
        s2Pullback
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
    calc
      sphereCoordMvEval p.1
          = harmonicDegreeProjectionContinuous n (s2Pullback g) := hpProj.symm
      _ = s2Pullback (ambientSectorProjectionContinuous n g) := by simp
      _ = s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
              rw [hgproj]
  have hmerEval :
      sphereCoordMvEval p.1 (specialXPoint r) =
        (northMeridianPolynomial p.1).eval r.1 := by
    exact
      sphereCoordMvEval_specialXPoint_eq_northMeridianPolynomial_eval
        (hgz := by
          rw [hpDist]
          exact isNorthZonal_s2Pullback_distinguishedZonalSector n)
        (hpEval := rfl)
        r
  have hpoint :=
    congrArg
      (fun f : C(spherePoint3, ℝ) => f (specialXPoint r))
      hpAvg
  simpa [hmerEval]
    using hpoint

theorem exists_nonzero_northMeridianPolynomial_with_bad_degree_specialXZ_system
    {n : ℕ} (hn0 : n ≠ 0) {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ p : harmonicHomogeneousSubmodule n,
      harmonicDegreeProjectionContinuous n (s2Pullback g) = sphereCoordMvEval p.1 ∧
      northMeridianPolynomial p.1 ≠ 0 ∧
      (∀ r : Set.Icc (0 : ℝ) 1,
        2 *
            poleAverageLinear
              (harmonicDegreeProjectionContinuous n (s2Pullback g))
              (specialZPoint r) =
          (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1) ∧
      (∀ r : Set.Icc (0 : ℝ) 1,
        harmonicDegreeProjectionContinuous n
            (s2Pullback
              (s2PoleAverageContinuousOfGreatCircleConstraint g
                (by
                  have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
                    simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                      using hgpc
                  exact
                    continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                      hframe)))
            (specialZPoint r) =
          -((1 / 2 : ℝ)) *
            (northMeridianPolynomial p.1).eval (Real.sqrt (1 - r.1 ^ 2))) ∧
      (∀ r : Set.Icc (0 : ℝ) 1,
        harmonicDegreeProjectionContinuous n
            (s2Pullback
              (s2PoleAverageContinuousOfGreatCircleConstraint g
                (by
                  have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
                    simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                      using hgpc
                  exact
                    continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                      hframe)))
            (specialXPoint r) =
          -((1 / 2 : ℝ)) * (northMeridianPolynomial p.1).eval r.1) := by
  rcases
      exists_nonzero_northMeridianPolynomial_with_bad_degree_special_system
        hn0 hgpc hgproj with
    ⟨p, hpProj, hpMer, hspecialZavg, hspecialZval⟩
  rcases
      exists_nonzero_northMeridianPolynomial_with_bad_degree_specialX_value_identity
        hn0 hgpc hgproj with
    ⟨p', hpProj', hpMer', hspecialXval⟩
  have hpEq : p = p' := by
    have hres : restrictToSphere p.1 = restrictToSphere p'.1 := by
      apply s2Pullback.injective
      simpa [s2Pullback_restrictToSphere] using hpProj.symm.trans hpProj'
    exact restrictToSphere_injective_on_harmonicHomogeneousSubmodule n (by simpa using hres)
  subst hpEq
  exact ⟨p, hpProj, hpMer, hspecialZavg, hspecialZval, hspecialXval⟩

theorem exists_nonzero_northMeridianPolynomial_with_bad_degree_sqquotient_specialZ_system
    {n : ℕ} (hn0 : n ≠ 0) (hnEven : Even n) {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ p : harmonicHomogeneousSubmodule n, ∃ q : C(unitIcc, ℝ),
      harmonicDegreeProjectionContinuous n (s2Pullback g) = sphereCoordMvEval p.1 ∧
      northMeridianPolynomial p.1 ≠ 0 ∧
      (∀ u : unitIcc,
        sqCenteredNorthZonalProfile (sphereCoordMvEval p.1) u = u.1 * q u) ∧
      (∀ r : Set.Icc (0 : ℝ) 1,
        (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1 -
            2 * (northMeridianPolynomial p.1).eval 0 =
          (r.1 ^ 2) * northZonalSqQuotientAverage q
            ⟨r.1 ^ 2, sq_mem_Icc (nonnegIccToIcc r)⟩) ∧
      (∀ r : Set.Icc (0 : ℝ) 1,
        harmonicDegreeProjectionContinuous n
            (s2Pullback
              (s2PoleAverageContinuousOfGreatCircleConstraint g
                (by
                  have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
                    simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                      using hgpc
                  exact
                    continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                      hframe)))
            (specialZPoint r) =
          -((1 / 2 : ℝ)) *
            (northMeridianPolynomial p.1).eval (Real.sqrt (1 - r.1 ^ 2))) := by
  rcases
      exists_nonzero_northMeridianPolynomial_with_bad_degree_special_system
        hn0 hgpc hgproj with
    ⟨p, hpProj, hpMer, hspecialZavg, hspecialZval⟩
  rcases
      exists_sqCenteredNorthZonalProfile_quotient_of_even_distinguishedZonalSector
        (n := n) hnEven with
    ⟨q, hqDist⟩
  refine ⟨p, q, hpProj, hpMer, ?_, ?_, hspecialZval⟩
  · intro u
    have hpDist :
        sphereCoordMvEval p.1 =
          s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
      calc
        sphereCoordMvEval p.1
            = harmonicDegreeProjectionContinuous n (s2Pullback g) := hpProj.symm
        _ = s2Pullback (ambientSectorProjectionContinuous n g) := by simp
        _ = s2Pullback
              (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
                rw [hgproj]
    simpa [hpDist] using hqDist u
  · intro r
    have hpDist :
        sphereCoordMvEval p.1 =
          s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
      calc
        sphereCoordMvEval p.1
            = harmonicDegreeProjectionContinuous n (s2Pullback g) := hpProj.symm
        _ = s2Pullback (ambientSectorProjectionContinuous n g) := by simp
        _ = s2Pullback
              (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
                rw [hgproj]
    have hgz : IsNorthZonal (sphereCoordMvEval p.1) := by
      rw [hpDist]
      exact isNorthZonal_s2Pullback_distinguishedZonalSector n
    have hzero :
        northZonalProfile (sphereCoordMvEval p.1) zeroIcc =
          (northMeridianPolynomial p.1).eval 0 := by
      simpa using
        northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal
          (g := sphereCoordMvEval p.1) (p := p.1) hgz rfl zeroIcc
    have hg :
        s2Pullback
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) ∈
            continuousHarmonicSphereDegreeSubmodule n :=
      s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule_distinguishedZonalSector n
    have hpow : (-1 : ℝ) ^ n = 1 := by
      rcases hnEven with ⟨k, hk⟩
      subst hk
      simp
    have hanti :
        ∀ x : spherePoint3,
          s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
              (sphereAntipode x) =
            s2Pullback
              (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
              x := by
      intro x
      calc
        s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
            (sphereAntipode x)
          =
            (-1 : ℝ) ^ n *
              s2Pullback
                (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
                x := by
                  exact
                    sphereRestriction_sphereNeg_of_mem_continuousHarmonicSphereDegreeSubmodule
                      hg x
        _ =
            s2Pullback
              (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
              x := by simp [hpow]
    have hbridge :=
      two_mul_poleAverageLinear_specialZPoint_sub_two_zero_eq_sqMul_northZonalSqQuotientAverage
        (f :=
          s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))))
        (hfz := isNorthZonal_s2Pullback_distinguishedZonalSector n)
        hanti q hqDist r
    calc
      (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1 -
          2 * (northMeridianPolynomial p.1).eval 0
        =
          2 * poleAverageLinear (sphereCoordMvEval p.1) (specialZPoint r) -
            2 * northZonalProfile (sphereCoordMvEval p.1) zeroIcc := by
              rw [← hspecialZavg r, hpProj, hzero]
      _ =
          (r.1 ^ 2) * northZonalSqQuotientAverage q
            ⟨r.1 ^ 2, sq_mem_Icc (nonnegIccToIcc r)⟩ := by
              simpa [hpDist] using hbridge

theorem exists_nonzero_northMeridianPolynomial_with_bad_degree_sqquotient_poly_specialZ_system
    {n : ℕ} (_hn0 : n ≠ 0) (hnEven : Even n) {g : C(S2, ℝ)}
    (_hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ p : harmonicHomogeneousSubmodule n, ∃ q : Polynomial ℝ,
      harmonicDegreeProjectionContinuous n (s2Pullback g) = sphereCoordMvEval p.1 ∧
      northMeridianPolynomial p.1 ≠ 0 ∧
      (∀ u : unitIcc,
        sqCenteredNorthZonalProfile (sphereCoordMvEval p.1) u = u.1 * q.eval u.1) ∧
      (∀ r : Set.Icc (0 : ℝ) 1,
        (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1 -
            2 * (northMeridianPolynomial p.1).eval 0 =
          (r.1 ^ 2) * (northZonalSqQuotientPolynomial q).eval (r.1 ^ 2)) := by
  rcases
      exists_nonzero_northMeridianPolynomial_of_northFixed_pointConstraint_witness
        hgproj with
    ⟨p, hpProj, hpMer⟩
  have hpDist :
      sphereCoordMvEval p.1 =
        s2Pullback
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
    calc
      sphereCoordMvEval p.1
          = harmonicDegreeProjectionContinuous n (s2Pullback g) := hpProj.symm
      _ = s2Pullback (ambientSectorProjectionContinuous n g) := by simp
      _ = s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
              rw [hgproj]
  have hgz : IsNorthZonal (sphereCoordMvEval p.1) := by
    rw [hpDist]
    exact isNorthZonal_s2Pullback_distinguishedZonalSector n
  have hpEven : sphereCoordPolyAntipode p.1 = p.1 := by
    exact sphereCoordPolyAntipode_eq_self_of_mem_homogeneousSubmodule_even p.2.1 hnEven
  rcases exists_sqCenteredNorthZonalPolynomial_of_isNorthZonal_of_even_mvPolynomial
      hgz (rfl : sphereCoordMvEval p.1 = sphereCoordMvEval p.1) hpEven with
    ⟨p0, hp0⟩
  have hp00eval : p0.eval 0 = 0 := by
    calc
      p0.eval 0 = p0.eval zeroUnitIcc.1 := by simp [zeroUnitIcc]
      _ = sqCenteredNorthZonalProfile (sphereCoordMvEval p.1) zeroUnitIcc := by
            symm
            simpa using hp0 zeroUnitIcc
      _ = 0 := by
            rw [sqCenteredNorthZonalProfile_apply]
            have hzero :
                (⟨Real.sqrt (↑zeroUnitIcc), by
                  constructor
                  · nlinarith [Real.sqrt_nonneg (↑zeroUnitIcc)]
                  · have hsq : (Real.sqrt (↑zeroUnitIcc)) ^ 2 = (↑zeroUnitIcc : ℝ) := by
                      exact Real.sq_sqrt zeroUnitIcc.2.1
                    nlinarith [zeroUnitIcc.2.2, Real.sqrt_nonneg (↑zeroUnitIcc), hsq]⟩
                  : Set.Icc (-1 : ℝ) 1) = zeroIcc := by
              apply Subtype.ext
              simp [zeroUnitIcc, zeroIcc]
            rw [hzero]
            exact centeredNorthZonalProfile_zero _
  have hp00 : p0.coeff 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hp00eval
  have hqDiv : ∀ u : unitIcc,
      sqCenteredNorthZonalProfile (sphereCoordMvEval p.1) u = u.1 * (p0.divX).eval u.1 := by
    intro u
    have hdivxEval :
        (Polynomial.X * p0.divX + Polynomial.C (p0.coeff 0)).eval u.1 = p0.eval u.1 := by
      exact congrArg (fun r : Polynomial ℝ => r.eval u.1) (Polynomial.X_mul_divX_add p0)
    have hdivxEval' :
        p0.eval u.1 = u.1 * (p0.divX).eval u.1 + p0.coeff 0 := by
      have htmp :
          p0.eval u.1 = (Polynomial.X * p0.divX + Polynomial.C (p0.coeff 0)).eval u.1 :=
        hdivxEval.symm
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] at htmp
      simpa using htmp
    calc
      sqCenteredNorthZonalProfile (sphereCoordMvEval p.1) u = p0.eval u.1 := hp0 u
      _ = u.1 * (p0.divX).eval u.1 + p0.coeff 0 := hdivxEval'
      _ = u.1 * (p0.divX).eval u.1 := by simp [hp00]
  refine ⟨p, p0.divX, hpProj, hpMer, hqDiv, ?_⟩
  · intro r
    have hzero :
        northZonalProfile (sphereCoordMvEval p.1) zeroIcc =
          (northMeridianPolynomial p.1).eval 0 := by
      simpa using
        northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal
          (g := sphereCoordMvEval p.1) (p := p.1) hgz rfl zeroIcc
    have hbridge :=
      two_mul_poleAverageLinear_specialZPoint_sub_two_zero_eq_sqMul_northZonalSqQuotientAverage
        (f := sphereCoordMvEval p.1) hgz
        (by
          intro x
          calc
            sphereCoordMvEval p.1 (sphereAntipode x)
              = sphereCoordMvEval (sphereCoordPolyAntipode p.1) x := by
                  simp [sphereCoordMvEval_polyAntipode]
            _ = sphereCoordMvEval p.1 x := by simp [hpEven])
        ((p0.divX).toContinuousMapOn (Set.Icc (0 : ℝ) 1))
        (by
          intro u
          simpa using hqDiv u)
        r
    calc
      (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1 -
          2 * (northMeridianPolynomial p.1).eval 0
        =
          2 * poleAverageLinear (sphereCoordMvEval p.1) (specialZPoint r) -
            2 * northZonalProfile (sphereCoordMvEval p.1) zeroIcc := by
              rw [two_mul_poleAverageLinear_specialZPoint_eq_northZonalScalarPolynomial
                    (hgz := hgz) (hpEval := rfl) r, hzero]
      _ =
          (r.1 ^ 2) *
            northZonalSqQuotientAverage ((p0.divX).toContinuousMapOn unitIcc)
              ⟨r.1 ^ 2, sq_mem_Icc (nonnegIccToIcc r)⟩ := by
                simpa using hbridge
      _ = (r.1 ^ 2) * (northZonalSqQuotientPolynomial (p0.divX)).eval (r.1 ^ 2) := by
            rw [northZonalSqQuotientAverage_toContinuousMapOn]
            rfl

end GleasonS2Bridge
