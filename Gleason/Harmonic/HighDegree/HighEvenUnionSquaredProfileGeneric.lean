import Gleason.Harmonic.HighDegree.HighEvenUnionCenteredProfileGeneric
import Gleason.Harmonic.HighDegree.HighEvenUnionProfilePolyApprox
import Gleason.Harmonic.Profile.SquaredProfileOperator
import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileDynamics

noncomputable section

open Complex InnerProductSpace Polynomial

theorem exists_sqquotient_poly_almost_fixed_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
        h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
        IsNorthZonal h ∧
        (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
        ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < ε ∧
        ‖northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h) -
            sqCenteredNorthZonalContinuousMap h‖ < 3 * ε := by
  intro ε hε
  rcases exists_northZonal_mem_highEvenUnion_close_of_mem_topologicalClosure_highEvenUnion_of_isNorthZonal
      hg.1 hgz (show 0 < ε / 6 by positivity) with
    ⟨h, hhHigh, hhz, hhdist⟩
  have hmono : Directed (· ≤ ·) highEvenBoundedHarmonicPolyHomogeneousImageSubmodule := by
    intro N M
    exact ⟨max N M,
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_left _ _),
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _)⟩
  rw [highEvenUnionHarmonicPolyHomogeneousImageSubmodule] at hhHigh
  rcases (Submodule.mem_iSup_of_directed highEvenBoundedHarmonicPolyHomogeneousImageSubmodule hmono).mp hhHigh with
    ⟨N, hhN⟩
  have hhEven :
      h ∈ evenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule N hhN
  rcases exists_even_mvPolynomial_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule hhEven with
    ⟨p, hpEval, hpEven⟩
  rcases exists_sqCenteredNorthZonalPolynomial_of_isNorthZonal_of_even_mvPolynomial hhz hpEval hpEven with
    ⟨p0, hp0⟩
  have hp00eval : p0.eval 0 = 0 := by
    calc
      p0.eval 0 = p0.eval zeroUnitIcc.1 := by simp [zeroUnitIcc]
      _ = sqCenteredNorthZonalProfile h zeroUnitIcc := by
            symm
            simpa using hp0 zeroUnitIcc
      _ = 0 := by
            rw [sqCenteredNorthZonalProfile_apply]
            have hzero :
                (⟨Real.sqrt (↑zeroUnitIcc), by
                  constructor
                  · nlinarith [Real.sqrt_nonneg (↑zeroUnitIcc)]
                  · have hsq : (Real.sqrt (↑zeroUnitIcc)) ^ 2 = (↑zeroUnitIcc : ℝ) :=
                      Real.sq_sqrt zeroUnitIcc.2.1
                    nlinarith [zeroUnitIcc.2.2, Real.sqrt_nonneg (↑zeroUnitIcc), hsq]⟩
                  : Set.Icc (-1 : ℝ) 1) = zeroIcc := by
              apply Subtype.ext
              simp [zeroUnitIcc, zeroIcc]
            rw [hzero]
            exact centeredNorthZonalProfile_zero h
  have hp00 : p0.coeff 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hp00eval
  refine ⟨h, p0.divX, hhHigh, hhz, ?_, ?_, ?_⟩
  · intro u
    have hdivxEval :
        (Polynomial.X * p0.divX + Polynomial.C (p0.coeff 0)).eval u.1 = p0.eval u.1 := by
      exact congrArg (fun r : ℝ[X] => r.eval u.1) (Polynomial.X_mul_divX_add p0)
    have hdivxEval' :
        p0.eval u.1 = u.1 * (p0.divX).eval u.1 + p0.coeff 0 := by
      have htmp :
          p0.eval u.1 = (Polynomial.X * p0.divX + Polynomial.C (p0.coeff 0)).eval u.1 := hdivxEval.symm
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] at htmp
      simpa using htmp
    calc
      sqCenteredNorthZonalProfile h u = p0.eval u.1 := hp0 u
      _ = u.1 * (p0.divX).eval u.1 + p0.coeff 0 := hdivxEval'
      _ = u.1 * (p0.divX).eval u.1 := by simp [hp00]
  · calc
      ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖
        ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
      _ < 2 * (ε / 6) := by gcongr
      _ < ε := by nlinarith [hε]
  · have hframe : g ∈ continuousSphereFrameSubmodule := hg.2
    have hfixProfile :
        northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap g) =
          sqCenteredNorthZonalContinuousMap g :=
      northZonalSqProfileAverage_sqCenteredNorthZonalContinuousMap_of_mem_frame hframe hgz
    have hdistProf :
        dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g) <
          2 * (ε / 6) := by
      calc
        dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g)
          = ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ := by
              simp [dist_eq_norm]
        _ ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
        _ < 2 * (ε / 6) := by gcongr
    calc
      ‖northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h) -
          sqCenteredNorthZonalContinuousMap h‖
        = dist (northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h))
            (sqCenteredNorthZonalContinuousMap h) := by
              simp [dist_eq_norm]
      _ ≤ dist (northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h))
            (northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap g)) +
          dist (sqCenteredNorthZonalContinuousMap g) (sqCenteredNorthZonalContinuousMap h) := by
            simpa [hfixProfile] using
              dist_triangle
                (northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h))
                (northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap g))
                (sqCenteredNorthZonalContinuousMap h)
      _ ≤ 2 * dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g) +
          dist (sqCenteredNorthZonalContinuousMap g) (sqCenteredNorthZonalContinuousMap h) := by
            gcongr
            exact dist_northZonalSqProfileAverage_le _ _
      _ < 2 * (2 * (ε / 6)) + 2 * (ε / 6) := by
            have hdistProf' :
                dist (sqCenteredNorthZonalContinuousMap g) (sqCenteredNorthZonalContinuousMap h) <
                  2 * (ε / 6) := by
              simpa [dist_comm] using hdistProf
            nlinarith
      _ = ε := by ring
      _ < 3 * ε := by nlinarith [hε]

theorem exists_sqprofile_near_linear_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε : ℝ}, 0 < ε → ∀ m : ℕ,
      ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
        h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
        IsNorthZonal h ∧
        (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
        ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < ε ∧
        ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖
          ≤ (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (3 * ε) +
              (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
  intro ε hε m
  rcases
      exists_sqquotient_poly_almost_fixed_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
        hg hgz hε with
    ⟨h, q, hhHigh, hhz, hq, hdist, hdefect⟩
  refine ⟨h, q, hhHigh, hhz, hq, hdist, ?_⟩
  have hp0 : (X * q : ℝ[X]).eval 0 = 0 := by
    simp
  have hpoly :
      sqCenteredNorthZonalContinuousMap h = sqProfilePolynomialMap (X * q) := by
    ext u
    change sqCenteredNorthZonalProfile h u = (X * q).eval u.1
    rw [hq u]
    simp
  have hdefect' :
      dist (northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)))
          (sqProfilePolynomialMap (X * q)) < 3 * ε := by
    simpa [hpoly, dist_eq_norm] using hdefect
  calc
    ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖
      = ‖sqProfilePolynomialMap (X * q) - sqProfileLinearPart (X * q)‖ := by
          rw [hpoly]
    _ ≤
        (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) *
            sqProfilePolynomialDefect (X * q) +
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
            exact norm_polynomial_sub_linear_le_of_sqprofile_almost_fixed (X * q) m hp0
    _ ≤
        (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (3 * ε) +
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
            gcongr
            exact le_of_lt hdefect'
