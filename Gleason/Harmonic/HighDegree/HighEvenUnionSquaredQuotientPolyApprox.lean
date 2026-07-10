import Gleason.Harmonic.HighDegree.HighEvenUnionProfilePolyApprox
import Gleason.Harmonic.HighDegree.HighEvenUnionClosedPole
import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientFixedContinuous

noncomputable section

open Complex InnerProductSpace Polynomial

theorem sqCenteredNorthZonalProfile_zero_eq_zero
    (f : C(spherePoint3, ℝ)) :
    sqCenteredNorthZonalProfile f zeroUnitIcc = 0 := by
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
  simp [centeredNorthZonalProfile, northZonalProfile]

theorem exists_fixed_northZonal_sqquotient_poly_approx_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      ∀ {ε : ℝ}, 0 < ε →
        ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < ε := by
  rcases exists_fixed_northZonal_profile_poly_approx_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, ?_⟩
  intro ε hε
  rcases happ hε with ⟨h, p, hhHigh, hhz, hp, hdist⟩
  have hp0eval : p.eval 0 = 0 := by
    calc
      p.eval 0 = p.eval zeroUnitIcc.1 := by simp [zeroUnitIcc]
      _ = sqCenteredNorthZonalProfile h zeroUnitIcc := by
            symm
            simpa using hp zeroUnitIcc
      _ = 0 := sqCenteredNorthZonalProfile_zero_eq_zero h
  have hp0 : p.coeff 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0eval
  refine ⟨h, p.divX, hhHigh, hhz, ?_, hdist⟩
  intro u
  have hdivxEval :
      (Polynomial.X * p.divX + Polynomial.C (p.coeff 0)).eval u.1 = p.eval u.1 := by
    exact congrArg (fun r : ℝ[X] => r.eval u.1) (Polynomial.X_mul_divX_add p)
  have hdivxEval' :
      p.eval u.1 = u.1 * (p.divX).eval u.1 + p.coeff 0 := by
    have htmp :
        p.eval u.1 = (Polynomial.X * p.divX + Polynomial.C (p.coeff 0)).eval u.1 := hdivxEval.symm
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] at htmp
    simpa using htmp
  calc
    sqCenteredNorthZonalProfile h u = p.eval u.1 := hp u
    _ = u.1 * (p.divX).eval u.1 + p.coeff 0 := hdivxEval'
    _ = u.1 * (p.divX).eval u.1 := by simp [hp0]

theorem exists_fixed_northZonal_sqquotient_poly_approx_of_nontrivial_tail_with_pole_ne_zero
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
      ∀ {ε : ℝ}, 0 < ε →
        ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < ε := by
  rcases exists_fixed_northZonal_with_highEvenUnion_approx_of_nontrivial_tail_with_pole_ne_zero hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε
  rcases happ (show 0 < ε / 2 by positivity) with ⟨h, hhHigh, hhz, hdist⟩
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
      _ = 0 := sqCenteredNorthZonalProfile_zero_eq_zero h
  have hp00 : p0.coeff 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hp00eval
  refine ⟨h, p0.divX, hhHigh, hhz, ?_, ?_⟩
  intro u
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
  calc
    ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖
      ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
    _ < 2 * (ε / 2) := by gcongr
    _ = ε := by ring

theorem exists_fixed_northZonal_sqquotient_poly_approx_of_nontrivial_tail_with_pole_ne_zero_and_norm
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
      ∀ {ε : ℝ}, 0 < ε →
        ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < 2 * ε := by
  rcases exists_fixed_northZonal_with_highEvenUnion_approx_of_nontrivial_tail_with_pole_ne_zero hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε
  rcases happ hε with ⟨h, hhHigh, hhz, hdist⟩
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
      _ = 0 := sqCenteredNorthZonalProfile_zero_eq_zero h
  have hp00 : p0.coeff 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hp00eval
  refine ⟨h, p0.divX, hhHigh, hhz, ?_, hdist, ?_⟩
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
      _ < 2 * ε := by gcongr

theorem exists_fixed_northZonal_sqquotient_poly_approx_of_nontrivial_tail_with_nonzero_pole_approx
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
          ‖h - g‖ < ε := by
  rcases exists_fixed_northZonal_sqquotient_poly_approx_of_nontrivial_tail_with_pole_ne_zero_and_norm hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε with ⟨h, q, hhHigh, hhz, hq, hdist, hsqdist⟩
  have hhPole : h sphereE3 ≠ 0 := by
    intro hh0
    have hdistPole : dist (h sphereE3) (g sphereE3) ≤ dist h g := by
      exact ContinuousMap.dist_apply_le_dist (f := h) (g := g) sphereE3
    have hdist' : dist h g < ε := by
      simpa [dist_eq_norm] using hdist
    have hge : ‖g sphereE3‖ < ε := by
      calc
        ‖g sphereE3‖ = dist (h sphereE3) (g sphereE3) := by simp [hh0, Real.dist_eq]
        _ ≤ dist h g := hdistPole
        _ < ε := hdist'
    exact (not_lt_of_ge (le_of_lt hεpole)) hge
  exact ⟨h, q, hhHigh, hhz, hhPole, hq, hdist⟩
