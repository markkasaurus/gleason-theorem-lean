import Gleason.Harmonic.Sphere.S2ExceptionalSectorReduction
import Gleason.Harmonic.Sphere.S2PointConstraintNorthAverage
import Gleason.Harmonic.Sphere.SphereDegreeProjection
import Gleason.Harmonic.Sphere.S2WitnessMeridian
import Gleason.Harmonic.Auxiliary.ExceptionalDegreeVanishing
import Gleason.Harmonic.Sphere.S2DistinguishedNorthZonal
import Gleason.Harmonic.Sphere.S2DistinguishedSquaredQuotientNonfixed

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

theorem continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_eq_bot_of_no_northFixed_pointConstraint_witness
    {n : ℕ}
    (hwitness :
      ¬ ∃ g : C(S2, ℝ),
        g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 ∧
        g ∈ northFixedSubmodule ∧
        ambientSectorProjectionContinuous n g =
          ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n = ⊥ := by
  by_contra hne
  rcases
      exists_northFixed_pointConstraint_witness_of_continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_ne_bot
        hne with
    ⟨g, hgpc, hgnorth, hgproj⟩
  exact hwitness ⟨g, hgpc, hgnorth, hgproj⟩

theorem False_of_northFixed_pointConstraint_witness_of_projected_component_mem_pointConstraint
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2)
    {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgnorth : g ∈ northFixedSubmodule)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
    (hprojpc :
      harmonicDegreeProjectionContinuous n (s2Pullback g) ∈
        continuousSphereGreatCirclePointConstraintSubmodule) :
    False := by
  let h :=
    harmonicDegreeProjectionContinuous n (s2Pullback g)
  have hhdeg : h ∈ continuousHarmonicSphereDegreeSubmodule n :=
    harmonicDegreeProjectionContinuous_mem_continuousHarmonicSphereDegreeSubmodule n (s2Pullback g)
  have hhz : IsNorthZonal h :=
    isNorthZonal_harmonicDegreeProjectionContinuous_of_mem_northFixedSubmodule
      (by simpa using hgnorth)
  have hzero :
      h = 0 :=
    eq_zero_of_mem_continuousHarmonicSphereDegreeSubmodule_ne_zero_two_of_northZonal_pointConstraint
      hn0 hn2 hhdeg hprojpc hhz
  have hdist :
      h =
        s2Pullback
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
    calc
      h = s2Pullback (ambientSectorProjectionContinuous n g) := by
            simp [h]
      _ =
        s2Pullback
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
            rw [hgproj]
  have hdist0 :
      s2Pullback
        (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) = 0 := by
    simpa [hdist] using hzero
  have hsector0 :
      (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) = 0 := by
    exact s2Pullback.injective hdist0
  exact distinguishedZonalSector_ne_zero n (Subtype.ext hsector0)

theorem stdGreatCirclePointConstraintLinear_harmonicDegreeProjectionContinuous_eq_zero_of_northFixed_pointConstraint_witness
    {n : ℕ} (hn0 : n ≠ 0)
    {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgnorth : g ∈ northFixedSubmodule)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    stdGreatCirclePointConstraintLinear
      (harmonicDegreeProjectionContinuous n (s2Pullback g)) = 0 := by
  let h := harmonicDegreeProjectionContinuous n (s2Pullback g)
  have hhz : IsNorthZonal h :=
    isNorthZonal_harmonicDegreeProjectionContinuous_of_mem_northFixedSubmodule
      (by simpa using hgnorth)
  rcases
      exists_nonzero_northMeridianPolynomial_with_bad_degree_special_system
        hn0 hgpc hgproj with
    ⟨p, hpProj, _hpMer, hspecialZavg, _hspecialZval⟩
  let r0 : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  have hsE3 : specialZPoint r0 = sphereE3 := by
    apply Subtype.ext
    simp [specialZPoint, northSection, sphereE3, r0]
  have hscalar0 :
      (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval 0 =
        2 * (northMeridianPolynomial p.1).eval 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      ← Polynomial.coeff_zero_eq_eval_zero]
    simpa [northZonalScalarCoeff_zero] using
      (coeff_northZonalScalarPolynomial (northMeridianPolynomial p.1) 0)
  have hhzp : IsNorthZonal (sphereCoordMvEval p.1) := by
    simpa [h, hpProj] using hhz
  have hvalE2 :
      h sphereE2 = (northMeridianPolynomial p.1).eval 0 := by
    have hmer :
        northZonalProfile (sphereCoordMvEval p.1) zeroIcc =
          (northMeridianPolynomial p.1).eval 0 := by
      simpa using
        northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal
          (g := sphereCoordMvEval p.1) (p := p.1) hhzp rfl zeroIcc
    calc
      h sphereE2 = northZonalProfile h zeroIcc := by
            symm
            exact northZonalProfile_zero_of_isNorthZonal hhz
      _ = northZonalProfile (sphereCoordMvEval p.1) zeroIcc := by
            simpa [h, hpProj]
      _ = (northMeridianPolynomial p.1).eval 0 := hmer
  have hvalE1 : h sphereE1 = (northMeridianPolynomial p.1).eval 0 := by
    have hs12 : sphereCoordZ sphereE1 = sphereCoordZ sphereE2 := by
      norm_num [sphereCoordZ, sphereE1, sphereE2]
    calc
      h sphereE1 = h sphereE2 := by
        apply eq_of_isNorthZonal_of_sphereCoordZ_eq hhz
        exact hs12
      _ = (northMeridianPolynomial p.1).eval 0 := hvalE2
  calc
    stdGreatCirclePointConstraintLinear h
        = 2 * northEquatorAverageLinear h - h sphereE1 - h sphereE2 := by
            simp [stdGreatCirclePointConstraintLinear_apply]
    _ = 2 * poleAverageLinear h sphereE3 - h sphereE1 - h sphereE2 := by
          rw [poleAverageLinear_sphereE3]
    _ = (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval 0 -
          h sphereE1 - h sphereE2 := by
            rw [← hsE3]
            linarith [hspecialZavg r0]
    _ = 2 * (northMeridianPolynomial p.1).eval 0 - h sphereE1 - h sphereE2 := by
          rw [hscalar0]
    _ = 0 := by
          rw [hvalE1, hvalE2]
          ring

theorem exists_special_pointConstraint_residual_of_northFixed_pointConstraint_witness
    {n : ℕ} (hn0 : n ≠ 0)
    {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgnorth : g ∈ northFixedSubmodule)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ p : harmonicHomogeneousSubmodule n,
      harmonicDegreeProjectionContinuous n (s2Pullback g) = sphereCoordMvEval p.1 ∧
      northMeridianPolynomial p.1 ≠ 0 ∧
      ∀ r : Set.Icc (0 : ℝ) 1,
        greatCirclePointConstraintLinear
          (specialXPoint r) sphereE2 (specialZPoint r)
          (specialXPoint_inner_sphereE2 r)
          (specialXPoint_inner_specialZPoint r)
          (sphereE2_inner_specialZPoint r)
          (harmonicDegreeProjectionContinuous n (s2Pullback g)) =
            (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1 -
              (northMeridianPolynomial p.1).eval r.1 -
              (northMeridianPolynomial p.1).eval 0 := by
  let h := harmonicDegreeProjectionContinuous n (s2Pullback g)
  have hhz : IsNorthZonal h :=
    isNorthZonal_harmonicDegreeProjectionContinuous_of_mem_northFixedSubmodule
      (by simpa using hgnorth)
  rcases
      exists_nonzero_northMeridianPolynomial_with_bad_degree_special_system
        hn0 hgpc hgproj with
    ⟨p, hpProj, hpMer, hspecialZavg, _hspecialZval⟩
  refine ⟨p, hpProj, hpMer, ?_⟩
  intro r
  have hhzp : IsNorthZonal (sphereCoordMvEval p.1) := by
    simpa [h, hpProj] using hhz
  have hvalX :
      h (specialXPoint r) = (northMeridianPolynomial p.1).eval r.1 := by
    calc
      h (specialXPoint r) = sphereCoordMvEval p.1 (specialXPoint r) := by
            simpa [h, hpProj]
      _ = (northMeridianPolynomial p.1).eval r.1 := by
            exact
              sphereCoordMvEval_specialXPoint_eq_northMeridianPolynomial_eval
                hhzp rfl r
  have hvalE2 :
      h sphereE2 = (northMeridianPolynomial p.1).eval 0 := by
    have hmer :
        northZonalProfile (sphereCoordMvEval p.1) zeroIcc =
          (northMeridianPolynomial p.1).eval 0 := by
      simpa using
        northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal
          (g := sphereCoordMvEval p.1) (p := p.1) hhzp rfl zeroIcc
    calc
      h sphereE2 = northZonalProfile h zeroIcc := by
            symm
            exact northZonalProfile_zero_of_isNorthZonal hhz
      _ = northZonalProfile (sphereCoordMvEval p.1) zeroIcc := by
            simpa [h, hpProj]
      _ = (northMeridianPolynomial p.1).eval 0 := hmer
  rw [greatCirclePointConstraintLinear_apply]
  calc
    2 *
        greatCircleAverageLinear
          (specialXPoint r) sphereE2 (specialZPoint r)
          (specialXPoint_inner_sphereE2 r)
          (specialXPoint_inner_specialZPoint r)
          (sphereE2_inner_specialZPoint r)
          h -
        h (specialXPoint r) - h sphereE2
      = 2 * poleAverageLinear h (specialZPoint r) -
          h (specialXPoint r) - h sphereE2 := by
            rw [← poleAverageLinear_eq_greatCircleAverageLinear
              h (specialXPoint r) sphereE2 (specialZPoint r)
              (specialXPoint_inner_sphereE2 r)
              (specialXPoint_inner_specialZPoint r)
              (sphereE2_inner_specialZPoint r)]
    _ =
        (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1 -
          h (specialXPoint r) - h sphereE2 := by
            linarith [hspecialZavg r]
    _ =
        (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1 -
          (northMeridianPolynomial p.1).eval r.1 -
          (northMeridianPolynomial p.1).eval 0 := by
            rw [hvalX, hvalE2]

theorem exists_special_sqquotient_residual_of_northFixed_pointConstraint_witness
    {n : ℕ} (hn0 : n ≠ 0) (hnEven : Even n)
    {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgnorth : g ∈ northFixedSubmodule)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ p : harmonicHomogeneousSubmodule n, ∃ q : Polynomial ℝ,
      harmonicDegreeProjectionContinuous n (s2Pullback g) = sphereCoordMvEval p.1 ∧
      northMeridianPolynomial p.1 ≠ 0 ∧
      (∀ u : unitIcc,
        sqCenteredNorthZonalProfile (sphereCoordMvEval p.1) u = u.1 * q.eval u.1) ∧
      (∀ r : Set.Icc (0 : ℝ) 1,
        greatCirclePointConstraintLinear
          (specialXPoint r) sphereE2 (specialZPoint r)
          (specialXPoint_inner_sphereE2 r)
          (specialXPoint_inner_specialZPoint r)
          (sphereE2_inner_specialZPoint r)
          (harmonicDegreeProjectionContinuous n (s2Pullback g)) =
            (r.1 ^ 2) *
              ((northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) - q.eval (r.1 ^ 2))) := by
  rcases
      exists_special_pointConstraint_residual_of_northFixed_pointConstraint_witness
        hn0 hgpc hgnorth hgproj with
    ⟨p, hpProj, hpMer, hresid⟩
  rcases
      exists_nonzero_northMeridianPolynomial_with_bad_degree_sqquotient_poly_specialZ_system
        hn0 hnEven hgpc hgproj with
    ⟨p', q, hpProj', hpMer', hq, hsqop⟩
  have hpEq : p = p' := by
    have hres : restrictToSphere p.1 = restrictToSphere p'.1 := by
      apply s2Pullback.injective
      simpa [s2Pullback_restrictToSphere] using hpProj.symm.trans hpProj'
    exact restrictToSphere_injective_on_harmonicHomogeneousSubmodule n (by simpa using hres)
  subst hpEq
  refine ⟨p, q, hpProj', hpMer', hq, ?_⟩
  intro r
  let u : unitIcc := ⟨r.1 ^ 2, sq_mem_Icc (nonnegIccToIcc r)⟩
  have hhz :
      IsNorthZonal (sphereCoordMvEval p.1) := by
    have hh :
        IsNorthZonal (harmonicDegreeProjectionContinuous n (s2Pullback g)) :=
      isNorthZonal_harmonicDegreeProjectionContinuous_of_mem_northFixedSubmodule
        (by simpa using hgnorth)
    simpa [hpProj'] using hh
  have hcenter :
      centeredNorthZonalProfile (sphereCoordMvEval p.1) (nonnegIccToIcc r) =
        (northMeridianPolynomial p.1).eval r.1 -
          (northMeridianPolynomial p.1).eval 0 := by
    simpa [nonnegIccToIcc] using
      centeredNorthZonalProfile_eq_northMeridianPolynomial_sub_const_of_isNorthZonal
        (g := sphereCoordMvEval p.1) (p := p.1) hhz rfl (nonnegIccToIcc r)
  have hsq :
      sqCenteredNorthZonalProfile (sphereCoordMvEval p.1) u =
        (northMeridianPolynomial p.1).eval r.1 -
          (northMeridianPolynomial p.1).eval 0 := by
    rw [sqCenteredNorthZonalProfile_apply]
    have hu :
        (⟨Real.sqrt u.1, by
          constructor
          · have hsqrt := Real.sqrt_nonneg u.1
            nlinarith
          · have hsq' : (Real.sqrt u.1) ^ 2 = u.1 := by
              exact Real.sq_sqrt u.2.1
            have hle : Real.sqrt u.1 ≤ 1 := by
              nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq']
            simpa using hle⟩ : Set.Icc (-1 : ℝ) 1) = nonnegIccToIcc r := by
      apply Subtype.ext
      simp [u, nonnegIccToIcc, Real.sqrt_sq, r.2.1]
    rw [hu, hcenter]
  have hfactor :
      (northMeridianPolynomial p.1).eval r.1 -
          (northMeridianPolynomial p.1).eval 0 =
        (r.1 ^ 2) * q.eval (r.1 ^ 2) := by
    calc
      (northMeridianPolynomial p.1).eval r.1 -
          (northMeridianPolynomial p.1).eval 0
        = sqCenteredNorthZonalProfile (sphereCoordMvEval p.1) u := by
            symm
            exact hsq
      _ = u.1 * q.eval u.1 := hq u
      _ = (r.1 ^ 2) * q.eval (r.1 ^ 2) := by rfl
  calc
    greatCirclePointConstraintLinear
        (specialXPoint r) sphereE2 (specialZPoint r)
        (specialXPoint_inner_sphereE2 r)
        (specialXPoint_inner_specialZPoint r)
        (sphereE2_inner_specialZPoint r)
        (harmonicDegreeProjectionContinuous n (s2Pullback g))
      =
        (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1 -
          (northMeridianPolynomial p.1).eval r.1 -
          (northMeridianPolynomial p.1).eval 0 := hresid r
    _ =
        ((northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1 -
          2 * (northMeridianPolynomial p.1).eval 0) -
          ((northMeridianPolynomial p.1).eval r.1 -
            (northMeridianPolynomial p.1).eval 0) := by ring
    _ =
        (r.1 ^ 2) * (northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) -
          ((northMeridianPolynomial p.1).eval r.1 -
            (northMeridianPolynomial p.1).eval 0) := by
          rw [hsqop r]
    _ =
        (r.1 ^ 2) * (northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) -
          (r.1 ^ 2) * q.eval (r.1 ^ 2) := by
          rw [hfactor]
    _ =
        (r.1 ^ 2) *
          ((northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) - q.eval (r.1 ^ 2)) := by
          ring

theorem False_of_northFixed_pointConstraint_witness_of_special_pointConstraint_zero
    {n : ℕ} (hn0 : n ≠ 0) (hnEven : Even n) (hn2 : 2 < n)
    {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgnorth : g ∈ northFixedSubmodule)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
    (hspecial :
      ∀ r : Set.Icc (0 : ℝ) 1,
        greatCirclePointConstraintLinear
          (specialXPoint r) sphereE2 (specialZPoint r)
          (specialXPoint_inner_sphereE2 r)
          (specialXPoint_inner_specialZPoint r)
          (sphereE2_inner_specialZPoint r)
          (harmonicDegreeProjectionContinuous n (s2Pullback g)) = 0) :
    False := by
  rcases
      exists_special_sqquotient_residual_of_northFixed_pointConstraint_witness
        hn0 hnEven hgpc hgnorth hgproj with
    ⟨p, q, hpProj, hpMer, hq, hresid⟩
  have hfix_eval :
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        (northZonalSqQuotientPolynomial q).eval x = q.eval x := by
    intro x hx
    let r : Set.Icc (0 : ℝ) 1 := ⟨Real.sqrt x, by
      constructor
      · exact Real.sqrt_nonneg x
      · have hsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.1.le
        nlinarith [hx.2, Real.sqrt_nonneg x, hsq]⟩
    have hzero : greatCirclePointConstraintLinear
        (specialXPoint r) sphereE2 (specialZPoint r)
        (specialXPoint_inner_sphereE2 r)
        (specialXPoint_inner_specialZPoint r)
        (sphereE2_inner_specialZPoint r)
        (harmonicDegreeProjectionContinuous n (s2Pullback g)) = 0 := hspecial r
    rw [hresid r] at hzero
    have hsq : r.1 ^ 2 = x := by
      simp [r, Real.sq_sqrt, hx.1.le]
    rw [hsq] at hzero
    have hx0 : x ≠ 0 := by
      linarith [hx.1]
    have hmul :
        x * ((northZonalSqQuotientPolynomial q).eval x - q.eval x) = 0 := by
      simpa using hzero
    have hdiff :
        (northZonalSqQuotientPolynomial q).eval x - q.eval x = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hx0
    linarith
  have hpoly :
      northZonalSqQuotientPolynomial q = q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.Ioo (0 : ℝ) 1) ?_
      (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num))
    intro x hx
    exact hfix_eval x hx
  have hpDist :
      sphereCoordMvEval p.1 =
        s2Pullback
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
    calc
      sphereCoordMvEval p.1
          = harmonicDegreeProjectionContinuous n (s2Pullback g) := hpProj.symm
      _ = s2Pullback (ambientSectorProjectionContinuous n g) := by
            simp [s2Pullback_ambientSectorProjectionContinuous_eq_harmonicDegreeProjectionContinuous]
      _ =
          s2Pullback
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) := by
            rw [hgproj]
  let fDist : C(spherePoint3, ℝ) :=
    s2Pullback
      (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
  have hqDist :
      ∀ u : unitIcc,
        sqCenteredNorthZonalProfile fDist u =
          u.1 * q.eval u.1 := by
    intro u
    simpa [fDist, hpDist] using hq u
  exact
    northZonalSqQuotientPolynomial_ne_self_of_even_distinguishedZonalSector_gt_two
      hnEven hn2 q hqDist hpoly

theorem no_northFixed_pointConstraint_witness_of_projected_component_mem_pointConstraint
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2)
    (hprojpc :
      ∀ g : C(S2, ℝ),
        g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 →
        g ∈ northFixedSubmodule →
        ambientSectorProjectionContinuous n g =
          ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) →
        harmonicDegreeProjectionContinuous n (s2Pullback g) ∈
          continuousSphereGreatCirclePointConstraintSubmodule) :
    ¬ ∃ g : C(S2, ℝ),
      g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 ∧
      g ∈ northFixedSubmodule ∧
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) := by
  intro hw
  rcases hw with ⟨g, hgpc, hgnorth, hgproj⟩
  exact
    False_of_northFixed_pointConstraint_witness_of_projected_component_mem_pointConstraint
      hn0 hn2 hgpc hgnorth hgproj (hprojpc g hgpc hgnorth hgproj)

theorem projected_component_not_mem_pointConstraint_of_northFixed_pointConstraint_witness
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2)
    {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgnorth : g ∈ northFixedSubmodule)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    harmonicDegreeProjectionContinuous n (s2Pullback g) ∉
      continuousSphereGreatCirclePointConstraintSubmodule := by
  intro hprojpc
  exact
    False_of_northFixed_pointConstraint_witness_of_projected_component_mem_pointConstraint
      hn0 hn2 hgpc hgnorth hgproj hprojpc

theorem no_northFixed_pointConstraint_witness_of_special_pointConstraint_zero
    {n : ℕ} (hn0 : n ≠ 0) (hnEven : Even n) (hn2 : 2 < n)
    (hspecial :
      ∀ g : C(S2, ℝ),
        g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 →
        g ∈ northFixedSubmodule →
        ambientSectorProjectionContinuous n g =
          ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) →
        ∀ r : Set.Icc (0 : ℝ) 1,
          greatCirclePointConstraintLinear
            (specialXPoint r) sphereE2 (specialZPoint r)
            (specialXPoint_inner_sphereE2 r)
            (specialXPoint_inner_specialZPoint r)
            (sphereE2_inner_specialZPoint r)
            (harmonicDegreeProjectionContinuous n (s2Pullback g)) = 0) :
    ¬ ∃ g : C(S2, ℝ),
      g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 ∧
      g ∈ northFixedSubmodule ∧
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) := by
  intro hw
  rcases hw with ⟨g, hgpc, hgnorth, hgproj⟩
  exact
    False_of_northFixed_pointConstraint_witness_of_special_pointConstraint_zero
      hn0 hnEven hn2 hgpc hgnorth hgproj (hspecial g hgpc hgnorth hgproj)

theorem not_special_pointConstraint_zero_of_northFixed_pointConstraint_witness
    {n : ℕ} (hn0 : n ≠ 0) (hnEven : Even n) (hn2 : 2 < n)
    {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgnorth : g ∈ northFixedSubmodule)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ¬
      (∀ r : Set.Icc (0 : ℝ) 1,
        greatCirclePointConstraintLinear
          (specialXPoint r) sphereE2 (specialZPoint r)
          (specialXPoint_inner_sphereE2 r)
          (specialXPoint_inner_specialZPoint r)
          (sphereE2_inner_specialZPoint r)
          (harmonicDegreeProjectionContinuous n (s2Pullback g)) = 0) := by
  intro hspecial
  exact
    False_of_northFixed_pointConstraint_witness_of_special_pointConstraint_zero
      hn0 hnEven hn2 hgpc hgnorth hgproj hspecial

theorem continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_eq_bot_of_special_pointConstraint_zero
    {n : ℕ} (hn0 : n ≠ 0) (hnEven : Even n) (hn2 : 2 < n)
    (hspecial :
      ∀ g : C(S2, ℝ),
        g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2 →
        g ∈ northFixedSubmodule →
        ambientSectorProjectionContinuous n g =
          ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) →
        ∀ r : Set.Icc (0 : ℝ) 1,
          greatCirclePointConstraintLinear
            (specialXPoint r) sphereE2 (specialZPoint r)
            (specialXPoint_inner_sphereE2 r)
            (specialXPoint_inner_specialZPoint r)
            (sphereE2_inner_specialZPoint r)
            (harmonicDegreeProjectionContinuous n (s2Pullback g)) = 0) :
    continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n = ⊥ := by
  apply
    continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_eq_bot_of_no_northFixed_pointConstraint_witness
  exact
    no_northFixed_pointConstraint_witness_of_special_pointConstraint_zero
      hn0 hnEven hn2 hspecial

end GleasonS2Bridge
