import Gleason.Harmonic.Profile.SquaredProfileOperator
import Gleason.Harmonic.HighDegree.HighEvenUnionSquaredQuotientPolyApprox
import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileDynamics

noncomputable section

open Complex InnerProductSpace Polynomial

theorem exists_fixed_northZonal_sqprofile_almost_fixed_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε : ℝ}, 0 < ε → ε < ‖g sphereE3‖ →
        ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ‖northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h) -
              sqCenteredNorthZonalContinuousMap h‖ < 6 * ε := by
  rcases exists_fixed_northZonal_sqquotient_poly_approx_of_nontrivial_tail_with_nonzero_pole_approx
      hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with ⟨h, q, hhHigh, hhz, hhpole, hq, hdist⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  have hframe : g ∈ continuousSphereFrameSubmodule := hg.2
  have hfixProfile :
      northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap g) =
        sqCenteredNorthZonalContinuousMap g :=
    northZonalSqProfileAverage_sqCenteredNorthZonalContinuousMap_of_mem_frame hframe hgz
  have hsqh :
      sqCenteredNorthZonalContinuousMap h =
        sqMulContinuousMap (q.toContinuousMapOn (Set.Icc (0 : ℝ) 1)) := by
    ext u
    change sqCenteredNorthZonalProfile h u = u.1 * (q.toContinuousMapOn (Set.Icc (0 : ℝ) 1)) u
    rw [hq u]
    rfl
  have hdistProf :
      dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g) <
        2 * ε := by
    calc
      dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g)
        = ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ := by
            simp [dist_eq_norm]
      _ ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
      _ < 2 * ε := by gcongr
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
    _ < 2 * (2 * ε) + 2 * ε := by
          have := hdistProf
          have hdistProf' :
              dist (sqCenteredNorthZonalContinuousMap g) (sqCenteredNorthZonalContinuousMap h) <
                2 * ε := by
            simpa [dist_comm] using hdistProf
          nlinarith
    _ = 6 * ε := by ring

theorem exists_fixed_northZonal_sqprofile_near_linear_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε : ℝ}, 0 < ε → ε < ‖g sphereE3‖ → ∀ m : ℕ,
        ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖
            ≤ (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
  rcases exists_fixed_northZonal_sqprofile_almost_fixed_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole m
  rcases happ hε hεpole with ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hdefect⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  have hp0 :
      (X * q : ℝ[X]).eval 0 = 0 := by
    simp
  have hpoly :
      sqCenteredNorthZonalContinuousMap h = sqProfilePolynomialMap (X * q) := by
    ext u
    change sqCenteredNorthZonalProfile h u = (X * q).eval u.1
    rw [hq u]
    simp
  have hdefect' :
      dist (northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)))
          (sqProfilePolynomialMap (X * q)) < 6 * ε := by
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
        (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
            gcongr
            exact le_of_lt hdefect'
