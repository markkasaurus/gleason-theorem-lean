import Gleason.Harmonic.HighDegree.EvenLowSquaredProfile
import Gleason.Harmonic.Profile.DegreeLTSquaredProfileDefectBound
import Gleason.Harmonic.HighDegree.HighEvenUnionClosed
import Gleason.Harmonic.HighDegree.HighEvenUnionClosedPole
import Gleason.Harmonic.HighDegree.HighEvenUnionSquaredProfileNormBridge
import Gleason.Harmonic.Profile.SquaredProfileOperator
import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileFixedContinuousTame
import Gleason.Harmonic.Auxiliary.GlobalLowProjection

noncomputable section

open Complex InnerProductSpace Polynomial

theorem mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_eq_polynomial
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {q : ℝ[X]}
    (hq : ∀ u : Set.Icc (0 : ℝ) 1,
      sqCenteredNorthZonalProfile g u = q.eval u.1) :
    g ∈ lowHarmonicPolyHomogeneousImageSubmodule :=
  mem_lowHarmonicPolyHomogeneousImageSubmodule_of_isNorthZonal_mem_frame_of_sqprofile_polynomial
    hg.2 hgz hq

theorem mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_tameApprox
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (htame :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) <
            η / (8 * (((Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * 3) + 1)) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8) :
    g ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
  have hfix :
      northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap g) =
        sqCenteredNorthZonalContinuousMap g :=
    northZonalSqProfileAverage_sqCenteredNorthZonalContinuousMap_of_mem_frame hg.2 hgz
  have hzero : sqCenteredNorthZonalContinuousMap g zeroUnitIcc = 0 := by
    change sqCenteredNorthZonalProfile g zeroUnitIcc = 0
    rw [sqCenteredNorthZonalProfile_apply]
    have h0 :
        (⟨Real.sqrt (↑zeroUnitIcc), by
          constructor
          · nlinarith [Real.sqrt_nonneg (↑zeroUnitIcc)]
          · have hsq : (Real.sqrt (↑zeroUnitIcc)) ^ 2 = (↑zeroUnitIcc : ℝ) := by
              exact Real.sq_sqrt zeroUnitIcc.2.1
            nlinarith [zeroUnitIcc.2.2, Real.sqrt_nonneg (↑zeroUnitIcc), hsq]⟩
          : Set.Icc (-1 : ℝ) 1) = zeroIcc := by
      apply Subtype.ext
      simp [zeroUnitIcc, zeroIcc]
    rw [h0]
    exact centeredNorthZonalProfile_zero g
  let q : ℝ[X] := C ((sqCenteredNorthZonalContinuousMap g) oneUnitIcc) * X
  have hlinear :
      sqCenteredNorthZonalContinuousMap g =
        (C ((sqCenteredNorthZonalContinuousMap g) oneUnitIcc) * X).toContinuousMapOn unitIcc :=
    northZonalSqProfileAverage_eq_linear_of_fixed_of_eval_zero_of_tameApprox
      (sqCenteredNorthZonalContinuousMap g) hfix hzero htame
  refine
    mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_eq_polynomial
      hg hgz (q := q) ?_
  intro u
  have hlin := congrArg (fun r : C(unitIcc, ℝ) => r u) hlinear
  simpa [q, sqCenteredNorthZonalContinuousMap, oneUnitIcc, Polynomial.eval_X, Polynomial.eval_C] using hlin

theorem eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_tameApprox
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (htame :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) <
            η / (8 * (((Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * 3) + 1)) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8) :
    g = 0 := by
  have hlow :
      g ∈ lowHarmonicPolyHomogeneousImageSubmodule :=
    mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_tameApprox
      hg hgz htame
  have hprojZero :
      GleasonS2Bridge.ambientLowHarmonicProjectionContinuous g = 0 :=
    GleasonS2Bridge.ambientLowHarmonicProjectionContinuous_eq_zero_of_mem_topologicalClosure_highEvenUnion
      hg.1
  have hprojSelf :
      GleasonS2Bridge.ambientLowHarmonicProjectionContinuous g = g :=
    GleasonS2Bridge.ambientLowHarmonicProjectionContinuous_eq_self_of_mem_lowHarmonicPolyHomogeneousImageSubmodule
      hlow
  rw [hprojSelf] at hprojZero
  exact hprojZero

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_tameApprox
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        (∀ {η : ℝ}, 0 < η →
          ∃ p : ℝ[X], ∃ m : ℕ,
            p.eval 0 = 0 ∧
            dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) <
              η / (8 * (((Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * 3) + 1)) ∧
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8)) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  by_contra hne
  rcases exists_nonzero_northZonal_fixed_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz, _⟩
  have hg0 :
      g = 0 :=
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_tameApprox
      hg hgz (htame hg hgz)
  exact hgne hg0

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_preiter_tameApprox
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        (∀ {η : ℝ}, 0 < η →
          ∃ p : ℝ[X], ∃ m : ℕ,
            p.eval 0 = 0 ∧
            dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) <
              η / (8 * (2 : ℝ) ^ m) ∧
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8)) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  refine topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_tameApprox ?_
  intro g hg hgz η hη
  rcases htame hg hgz hη with ⟨p, m, hp0, hdist, htail⟩
  let p' : ℝ[X] := (northZonalSqProfilePolynomial^[m]) p
  have hp0' : p'.eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    dsimp [p']
    have hpcoeff0 : p.coeff 0 = 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0
    simpa [coeff_iter_northZonalSqProfilePolynomial, hpcoeff0]
  have hfixProfile :
      northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap g) =
        sqCenteredNorthZonalContinuousMap g :=
    northZonalSqProfileAverage_sqCenteredNorthZonalContinuousMap_of_mem_frame hg.2 hgz
  have hfixIter :
      (northZonalSqProfileAverage^[m]) (sqCenteredNorthZonalContinuousMap g) =
        sqCenteredNorthZonalContinuousMap g := by
    simpa using Function.iterate_fixed hfixProfile m
  refine ⟨p', 0, hp0', ?_, ?_⟩
  · have hdistIter :
        dist ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p))
            ((northZonalSqProfileAverage^[m]) (sqCenteredNorthZonalContinuousMap g))
          ≤ 2 ^ m * dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) :=
      dist_iterate_northZonalSqProfileAverage_le
        (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) m
    simpa using calc
      dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g)
        = dist ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p))
            ((northZonalSqProfileAverage^[m]) (sqCenteredNorthZonalContinuousMap g)) := by
              simp [sqProfilePolynomialMap, p', iterate_northZonalSqProfileAverage_toContinuousMapOn,
                hfixIter]
      _ ≤ 2 ^ m * dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) :=
            hdistIter
      _ < 2 ^ m * (η / (8 * (2 : ℝ) ^ m)) := by
            exact mul_lt_mul_of_pos_left hdist (by positivity)
      _ = η / 8 := by
            field_simp [pow_ne_zero m (show (2 : ℝ) ≠ 0 by norm_num)]
  · have htailIter :
        sqProfileTailAbsSum p' ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
      simpa [p'] using sqProfileTailAbsSum_iterate_le p m
    simpa using calc
      (3 / 4 : ℝ) ^ 0 * sqProfileTailAbsSum p'
        = sqProfileTailAbsSum p' := by simp
      _ ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := htailIter
      _ < η / 8 := htail

theorem eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_preiter_tameApprox
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (htame :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) <
            η / (8 * (2 : ℝ) ^ m) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8) :
    g = 0 := by
  have htame' :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) <
            η / (8 * (((Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * 3) + 1)) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8 := by
    intro η hη
    rcases htame hη with ⟨p, m, hp0, hdist, htail⟩
    let p' : ℝ[X] := (northZonalSqProfilePolynomial^[m]) p
    have hp0' : p'.eval 0 = 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      dsimp [p']
      have hpcoeff0 : p.coeff 0 = 0 := by
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0
      simpa [coeff_iter_northZonalSqProfilePolynomial, hpcoeff0]
    have hfixProfile :
        northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap g) =
          sqCenteredNorthZonalContinuousMap g :=
      northZonalSqProfileAverage_sqCenteredNorthZonalContinuousMap_of_mem_frame hg.2 hgz
    have hfixIter :
        (northZonalSqProfileAverage^[m]) (sqCenteredNorthZonalContinuousMap g) =
          sqCenteredNorthZonalContinuousMap g := by
      simpa using Function.iterate_fixed hfixProfile m
    have hdistIter :
        dist ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p))
            ((northZonalSqProfileAverage^[m]) (sqCenteredNorthZonalContinuousMap g))
          ≤ 2 ^ m * dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) :=
      dist_iterate_northZonalSqProfileAverage_le
        (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) m
    have hdist' :
        dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g) < η / 8 := by
      calc
        dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g)
          = dist ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p))
              ((northZonalSqProfileAverage^[m]) (sqCenteredNorthZonalContinuousMap g)) := by
                simp [sqProfilePolynomialMap, p',
                  iterate_northZonalSqProfileAverage_toContinuousMapOn, hfixIter]
        _ ≤ 2 ^ m * dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) :=
              hdistIter
        _ < 2 ^ m * (η / (8 * (2 : ℝ) ^ m)) := by
              exact mul_lt_mul_of_pos_left hdist (by positivity)
        _ = η / 8 := by
              field_simp [pow_ne_zero m (show (2 : ℝ) ≠ 0 by norm_num)]
    have htail' :
        (3 / 4 : ℝ) ^ 0 * sqProfileTailAbsSum p' < η / 8 := by
      have htailIter :
          sqProfileTailAbsSum p' ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
        simpa [p'] using sqProfileTailAbsSum_iterate_le p m
      simpa using lt_of_le_of_lt htailIter htail
    exact ⟨p', 0, hp0', by simpa using hdist', by simpa using htail'⟩
  exact
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_tameApprox
      hg hgz htame'

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_preiter_tameApprox_linearized
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        (∀ {η : ℝ}, 0 < η →
          ∃ p : ℝ[X], ∃ m : ℕ,
            p.eval 0 = 0 ∧
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) <
              η / (16 * (2 : ℝ) ^ m) ∧
            dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) <
              η / (16 * (2 : ℝ) ^ m) ∧
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8)) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  refine topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_preiter_tameApprox ?_
  intro g hg hgz η hη
  rcases htame hg hgz hη with ⟨p, m, hp0, hlin, hplin, htail⟩
  refine ⟨p, m, hp0, ?_, htail⟩
  calc
    dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g)
      ≤ dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) +
          dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) := by
            exact dist_triangle _ _ _
    _ < η / (16 * (2 : ℝ) ^ m) + η / (16 * (2 : ℝ) ^ m) := by
          exact add_lt_add hplin hlin
    _ = η / (8 * (2 : ℝ) ^ m) := by ring

theorem eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_preiter_tameApprox_linearized
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (htame :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) <
            η / (16 * (2 : ℝ) ^ m) ∧
          dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) <
            η / (16 * (2 : ℝ) ^ m) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8) :
    g = 0 := by
  have htame' :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) <
            η / (16 * (2 : ℝ) ^ m) ∧
          dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) <
            η / (16 * (2 : ℝ) ^ m) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8 := htame
  have htame'' :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) <
            η / (8 * (2 : ℝ) ^ m) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8 := by
    intro η hη
    rcases htame' hη with ⟨p, m, hp0, hlin, hplin, htail⟩
    refine ⟨p, m, hp0, ?_, htail⟩
    calc
      dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g)
        ≤ dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) +
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) := by
              exact dist_triangle _ _ _
      _ < η / (16 * (2 : ℝ) ^ m) + η / (16 * (2 : ℝ) ^ m) := by
            exact add_lt_add hplin hlin
      _ = η / (8 * (2 : ℝ) ^ m) := by ring
  exact
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_preiter_tameApprox
      hg hgz htame''

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_preiter_tameApprox_linearized_fixedpart
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        (∀ {η : ℝ}, 0 < η →
          ∃ p : ℝ[X], ∃ m : ℕ,
            p.eval 0 = 0 ∧
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16 ∧
            dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) <
              η / (16 * (2 : ℝ) ^ m) ∧
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8)) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  refine topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_tameApprox ?_
  intro g hg hgz η hη
  rcases htame hg hgz hη with ⟨p, m, hp0, hlin, hplin, htail⟩
  let p' : ℝ[X] := (northZonalSqProfilePolynomial^[m]) p
  have hp0' : p'.eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    dsimp [p']
    have hpcoeff0 : p.coeff 0 = 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0
    simpa [coeff_iter_northZonalSqProfilePolynomial, hpcoeff0]
  have hlinFix :
      northZonalSqProfileAverage (sqProfileLinearPart p) = sqProfileLinearPart p := by
    simpa [sqProfileLinearPart] using northZonalSqProfileAverage_C_mul_X (p.coeff 1)
  have hlinFixIter :
      (northZonalSqProfileAverage^[m]) (sqProfileLinearPart p) = sqProfileLinearPart p := by
    simpa using Function.iterate_fixed hlinFix m
  have hdistIter :
      dist ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p))
          ((northZonalSqProfileAverage^[m]) (sqProfileLinearPart p))
        ≤ 2 ^ m * dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) :=
    dist_iterate_northZonalSqProfileAverage_le
      (sqProfilePolynomialMap p) (sqProfileLinearPart p) m
  have hscaled :
      2 ^ m * dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) <
        2 ^ m * (η / (16 * (2 : ℝ) ^ m)) := by
    exact mul_lt_mul_of_pos_left hplin (by positivity)
  have hscaleEq : 2 ^ m * (η / (16 * (2 : ℝ) ^ m)) = η / 16 := by
    field_simp [pow_ne_zero m (show (2 : ℝ) ≠ 0 by norm_num)]
  have hdist' :
      dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g) < η / 8 := by
    calc
      dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g)
        ≤ dist (sqProfilePolynomialMap p') (sqProfileLinearPart p) +
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) := by
              exact dist_triangle _ _ _
      _ = dist ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p))
            ((northZonalSqProfileAverage^[m]) (sqProfileLinearPart p)) +
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) := by
              simp [sqProfilePolynomialMap, p', iterate_northZonalSqProfileAverage_toContinuousMapOn,
                hlinFixIter]
      _ ≤ 2 ^ m * dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) +
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) := by
              gcongr
      _ < 2 ^ m * (η / (16 * (2 : ℝ) ^ m)) + η / 16 := by
            exact add_lt_add hscaled hlin
      _ = η / 16 + η / 16 := by rw [hscaleEq]
      _ = η / 8 := by ring
  have hdist'' :
      dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g) <
        η / (8 * (((Finset.sum (Finset.range 0) fun j => (2 : ℝ) ^ j) * 3) + 1)) := by
    simpa using hdist'
  refine ⟨p', 0, hp0', hdist'', ?_⟩
  · have htailIter :
        sqProfileTailAbsSum p' ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
      simpa [p'] using sqProfileTailAbsSum_iterate_le p m
    simpa using calc
      (3 / 4 : ℝ) ^ 0 * sqProfileTailAbsSum p'
        = sqProfileTailAbsSum p' := by simp
      _ ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := htailIter
      _ < η / 8 := htail

theorem eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_preiter_tameApprox_linearized_fixedpart
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (htame :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16 ∧
          dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) <
            η / (16 * (2 : ℝ) ^ m) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8) :
    g = 0 := by
  have htame' :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16 ∧
          dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) <
            η / (16 * (2 : ℝ) ^ m) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8 := htame
  have htame'' :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) <
            η / (8 * (((Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * 3) + 1)) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8 := by
    intro η hη
    rcases htame' hη with ⟨p, m, hp0, hlin, hplin, htail⟩
    let p' : ℝ[X] := (northZonalSqProfilePolynomial^[m]) p
    have hp0' : p'.eval 0 = 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      dsimp [p']
      have hpcoeff0 : p.coeff 0 = 0 := by
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0
      simpa [coeff_iter_northZonalSqProfilePolynomial, hpcoeff0]
    have hlinFix :
        northZonalSqProfileAverage (sqProfileLinearPart p) = sqProfileLinearPart p := by
      simpa [sqProfileLinearPart] using northZonalSqProfileAverage_C_mul_X (p.coeff 1)
    have hlinFixIter :
        (northZonalSqProfileAverage^[m]) (sqProfileLinearPart p) = sqProfileLinearPart p := by
      simpa using Function.iterate_fixed hlinFix m
    have hdistIter :
        dist ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p))
            ((northZonalSqProfileAverage^[m]) (sqProfileLinearPart p))
          ≤ 2 ^ m * dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) :=
      dist_iterate_northZonalSqProfileAverage_le
        (sqProfilePolynomialMap p) (sqProfileLinearPart p) m
    have hscaled :
        2 ^ m * dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) <
          2 ^ m * (η / (16 * (2 : ℝ) ^ m)) := by
      exact mul_lt_mul_of_pos_left hplin (by positivity)
    have hscaleEq : 2 ^ m * (η / (16 * (2 : ℝ) ^ m)) = η / 16 := by
      field_simp [pow_ne_zero m (show (2 : ℝ) ≠ 0 by norm_num)]
    have hdist' :
        dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g) < η / 8 := by
      calc
        dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g)
          ≤ dist (sqProfilePolynomialMap p') (sqProfileLinearPart p) +
              dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) := by
                exact dist_triangle _ _ _
        _ = dist ((northZonalSqProfileAverage^[m]) (sqProfilePolynomialMap p))
              ((northZonalSqProfileAverage^[m]) (sqProfileLinearPart p)) +
              dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) := by
                simp [sqProfilePolynomialMap, p', iterate_northZonalSqProfileAverage_toContinuousMapOn,
                  hlinFixIter]
        _ ≤ 2 ^ m * dist (sqProfilePolynomialMap p) (sqProfileLinearPart p) +
              dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) := by
                gcongr
        _ < 2 ^ m * (η / (16 * (2 : ℝ) ^ m)) + η / 16 := by
              exact add_lt_add hscaled hlin
        _ = η / 16 + η / 16 := by rw [hscaleEq]
        _ = η / 8 := by ring
    have hdist'' :
        dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g) <
          η / (8 * (((Finset.sum (Finset.range 0) fun j => (2 : ℝ) ^ j) * 3) + 1)) := by
      simpa using hdist'
    have htail' :
        (3 / 4 : ℝ) ^ 0 * sqProfileTailAbsSum p' < η / 8 := by
      have htailIter :
          sqProfileTailAbsSum p' ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
        simpa [p'] using sqProfileTailAbsSum_iterate_le p m
      simpa using lt_of_le_of_lt htailIter htail
    exact ⟨p', 0, hp0', hdist'', by simpa using htail'⟩
  exact
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_tameApprox
      hg hgz htame''

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_preiter_tameApprox_linearized_fixedpart_tailonly
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        (∀ {η : ℝ}, 0 < η →
          ∃ p : ℝ[X], ∃ m : ℕ,
            p.eval 0 = 0 ∧
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16 ∧
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 16)) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  refine topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_tameApprox ?_
  intro g hg hgz η hη
  rcases htame hg hgz hη with ⟨p, m, hp0, hlin, htail⟩
  let p' : ℝ[X] := (northZonalSqProfilePolynomial^[m]) p
  have hp0' : p'.eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    dsimp [p']
    have hpcoeff0 : p.coeff 0 = 0 := by
      simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0
    simpa [coeff_iter_northZonalSqProfilePolynomial, hpcoeff0]
  have hdistToLinear :
      dist (sqProfilePolynomialMap p') (sqProfileLinearPart p) < η / 16 := by
    have hnorm :
        ‖sqProfilePolynomialMap p' - sqProfileLinearPart p‖
          ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
      simpa [sqProfilePolynomialMap, p', iterate_northZonalSqProfileAverage_toContinuousMapOn,
        dist_eq_norm] using
        norm_iterate_northZonalSqProfileAverage_polynomial_sub_linear_le p m hp0
    have hdist_le :
        dist (sqProfilePolynomialMap p') (sqProfileLinearPart p)
          ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
      simpa [dist_eq_norm] using hnorm
    exact lt_of_le_of_lt hdist_le htail
  have hdist' :
      dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g) < η / 8 := by
    calc
      dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g)
        ≤ dist (sqProfilePolynomialMap p') (sqProfileLinearPart p) +
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) := by
              exact dist_triangle _ _ _
      _ < η / 16 + η / 16 := by
            exact add_lt_add hdistToLinear hlin
      _ = η / 8 := by ring
  have hdist'' :
      dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g) <
        η / (8 * (((Finset.sum (Finset.range 0) fun j => (2 : ℝ) ^ j) * 3) + 1)) := by
    simpa using hdist'
  refine ⟨p', 0, hp0', hdist'', ?_⟩
  have htailIter :
      sqProfileTailAbsSum p' ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
    simpa [p'] using sqProfileTailAbsSum_iterate_le p m
  have htail16 :
      sqProfileTailAbsSum p' < η / 16 := by
    exact lt_of_le_of_lt htailIter htail
  have htail8 :
      sqProfileTailAbsSum p' < η / 8 := by
    linarith
  simpa using htail8

theorem eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_preiter_tameApprox_linearized_fixedpart_tailonly
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (htame :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16 ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 16) :
    g = 0 := by
  have htame' :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16 ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 16 := htame
  have htame'' :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X], ∃ m : ℕ,
          p.eval 0 = 0 ∧
          dist (sqProfilePolynomialMap p) (sqCenteredNorthZonalContinuousMap g) <
            η / (8 * (((Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * 3) + 1)) ∧
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 8 := by
    intro η hη
    rcases htame' hη with ⟨p, m, hp0, hlin, htail⟩
    let p' : ℝ[X] := (northZonalSqProfilePolynomial^[m]) p
    have hp0' : p'.eval 0 = 0 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      dsimp [p']
      have hpcoeff0 : p.coeff 0 = 0 := by
        simpa [Polynomial.coeff_zero_eq_eval_zero] using hp0
      simpa [coeff_iter_northZonalSqProfilePolynomial, hpcoeff0]
    have hdistToLinear :
        dist (sqProfilePolynomialMap p') (sqProfileLinearPart p) < η / 16 := by
      have hnorm :
          ‖sqProfilePolynomialMap p' - sqProfileLinearPart p‖
            ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
        simpa [sqProfilePolynomialMap, p', iterate_northZonalSqProfileAverage_toContinuousMapOn,
          dist_eq_norm] using
          norm_iterate_northZonalSqProfileAverage_polynomial_sub_linear_le p m hp0
      have hdist_le :
          dist (sqProfilePolynomialMap p') (sqProfileLinearPart p)
            ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
        simpa [dist_eq_norm] using hnorm
      exact lt_of_le_of_lt hdist_le htail
    have hdist' :
        dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g) < η / 8 := by
      calc
        dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g)
          ≤ dist (sqProfilePolynomialMap p') (sqProfileLinearPart p) +
              dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) := by
                exact dist_triangle _ _ _
        _ < η / 16 + η / 16 := by
              exact add_lt_add hdistToLinear hlin
        _ = η / 8 := by ring
    have hdist'' :
        dist (sqProfilePolynomialMap p') (sqCenteredNorthZonalContinuousMap g) <
          η / (8 * (((Finset.sum (Finset.range 0) fun j => (2 : ℝ) ^ j) * 3) + 1)) := by
      simpa using hdist'
    have htail' :
        (3 / 4 : ℝ) ^ 0 * sqProfileTailAbsSum p' < η / 8 := by
      have htailIter :
          sqProfileTailAbsSum p' ≤ (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p := by
        simpa [p'] using sqProfileTailAbsSum_iterate_le p m
      have htail16 :
          sqProfileTailAbsSum p' < η / 16 := by
        exact lt_of_le_of_lt htailIter htail
      have htail8 : sqProfileTailAbsSum p' < η / 8 := by
        linarith
      simpa using htail8
    exact ⟨p', 0, hp0', hdist'', by simpa using htail'⟩
  exact
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_tameApprox
      hg hgz htame''

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_linearized_fixedpart_approx
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        (∀ {η : ℝ}, 0 < η →
          ∃ p : ℝ[X],
            p.eval 0 = 0 ∧
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16)) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  refine
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_preiter_tameApprox_linearized_fixedpart_tailonly
      ?_
  intro g hg hgz η hη
  rcases htame hg hgz hη with ⟨p, hp0, hlin⟩
  let A : ℝ := sqProfileTailAbsSum p + 1
  have hA : 0 < A := by
    have hnonneg : 0 ≤ sqProfileTailAbsSum p := by
      unfold sqProfileTailAbsSum
      positivity
    dsimp [A]
    linarith
  obtain ⟨m, hm⟩ :=
    exists_pow_lt_of_lt_one (show 0 < (η / 16) / A by positivity)
      (by norm_num : (3 / 4 : ℝ) < 1)
  have htail16 :
      (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 16 := by
    have hAstep : (3 / 4 : ℝ) ^ m * A < η / 16 := by
      have hmul := mul_lt_mul_of_pos_right hm hA
      have hdivmul : ((η / 16) / A) * A = η / 16 := by
        field_simp [ne_of_gt hA]
      calc
        (3 / 4 : ℝ) ^ m * A < ((η / 16) / A) * A := hmul
        _ = η / 16 := hdivmul
    have hAle : sqProfileTailAbsSum p ≤ A := by
      dsimp [A]
      linarith
    exact lt_of_le_of_lt (by gcongr) hAstep
  exact ⟨p, m, hp0, hlin, htail16⟩

theorem eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_linearized_fixedpart_approx
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (htame :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X],
          p.eval 0 = 0 ∧
          dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16) :
    g = 0 := by
  have htame' :
      ∀ {η : ℝ}, 0 < η →
        ∃ p : ℝ[X],
          p.eval 0 = 0 ∧
          dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16 := htame
  refine
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_preiter_tameApprox_linearized_fixedpart_tailonly
      hg hgz ?_
  intro η hη
  rcases htame' hη with ⟨p, hp0, hlin⟩
  let A : ℝ := sqProfileTailAbsSum p + 1
  have hA : 0 < A := by
    have hnonneg : 0 ≤ sqProfileTailAbsSum p := by
      unfold sqProfileTailAbsSum
      positivity
    dsimp [A]
    linarith
  obtain ⟨m, hm⟩ :=
    exists_pow_lt_of_lt_one (show 0 < (η / 16) / A by positivity)
      (by norm_num : (3 / 4 : ℝ) < 1)
  have htail16 :
      (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 16 := by
    have hAstep : (3 / 4 : ℝ) ^ m * A < η / 16 := by
      have hmul := mul_lt_mul_of_pos_right hm hA
      have hdivmul : ((η / 16) / A) * A = η / 16 := by
        field_simp [ne_of_gt hA]
      calc
        (3 / 4 : ℝ) ^ m * A < ((η / 16) / A) * A := hmul
        _ = η / 16 := hdivmul
    have hAle : sqProfileTailAbsSum p ≤ A := by
      dsimp [A]
      linarith
    exact lt_of_le_of_lt (by gcongr) hAstep
  exact ⟨p, m, hp0, hlin, htail16⟩

theorem norm_sphereE3_le_one_add_global_const_mul_dist_sqprofileLinearPart_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (b : ℝ) :
    ‖g sphereE3‖ ≤
      (1 + ‖GleasonS2Bridge.ambientLowHarmonicProjectionContinuous‖) *
        dist ((Polynomial.C b * (Polynomial.X : Polynomial ℝ)).toContinuousMapOn unitIcc)
          (sqCenteredNorthZonalContinuousMap g) := by
  let l : C(spherePoint3, ℝ) := lowSqProfileMode (g sphereE1) b
  have hl : l ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
    exact lowSqProfileMode_mem_lowHarmonicPolyHomogeneousImageSubmodule _ _
  have hlow :
      ‖g sphereE3‖ ≤ (1 + ‖GleasonS2Bridge.ambientLowHarmonicProjectionContinuous‖) * ‖g - l‖ := by
    exact
      GleasonS2Bridge.norm_sphereE3_le_one_add_global_const_mul_norm_sub_of_mem_low_of_mem_topologicalClosure_highEvenUnion
        hl hg.1
  have hnorm :
      ‖g - l‖ =
        dist ((Polynomial.C b * (Polynomial.X : Polynomial ℝ)).toContinuousMapOn unitIcc)
          (sqCenteredNorthZonalContinuousMap g) := by
    rw [norm_sub_lowSqProfileMode_eq_sqprofile_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
      (hg := hg) (hgz := hgz) (b := b)]
    simp [dist_eq_norm, norm_sub_rev]
  rw [hnorm] at hlow
  exact hlow

theorem not_sqprofile_linearized_fixedpart_approx_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_pole_ne_zero
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hgpole : g sphereE3 ≠ 0) :
    ¬ (∀ {η : ℝ}, 0 < η →
          ∃ p : ℝ[X],
            p.eval 0 = 0 ∧
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16) := by
  intro htame
  let K : ℝ := 1 + ‖GleasonS2Bridge.ambientLowHarmonicProjectionContinuous‖
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let η : ℝ := 8 * ‖g sphereE3‖ / K
  have hη : 0 < η := by
    dsimp [η]
    have hgpole_norm : 0 < ‖g sphereE3‖ := norm_pos_iff.mpr hgpole
    positivity
  rcases htame hη with ⟨p, hp0, hlin⟩
  have hbound :
      ‖g sphereE3‖ ≤ K * dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) := by
    simpa [K, sqProfileLinearPart] using
      norm_sphereE3_le_one_add_global_const_mul_dist_sqprofileLinearPart_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
        hg hgz (p.coeff 1)
  have hlt :
      K * dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < ‖g sphereE3‖ := by
    have hKpos : 0 < K := hK
    have hηdiv : η / 16 = ‖g sphereE3‖ / (2 * K) := by
      dsimp [η]
      field_simp [ne_of_gt hK]
      ring
    have hsmall :
        dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) <
          ‖g sphereE3‖ / (2 * K) := by
      simpa [hηdiv] using hlin
    have := mul_lt_mul_of_pos_left hsmall hKpos
    have hmul : K * (‖g sphereE3‖ / (2 * K)) = ‖g sphereE3‖ / 2 := by
      field_simp [ne_of_gt hK]
    have hhalf_lt : ‖g sphereE3‖ / 2 < ‖g sphereE3‖ := by
      have hgpole_norm : 0 < ‖g sphereE3‖ := norm_pos_iff.mpr hgpole
      linarith
    have hmid :
        K * dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) <
          ‖g sphereE3‖ / 2 := by
      calc
        K * dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g)
          < K * (‖g sphereE3‖ / (2 * K)) := this
        _ = ‖g sphereE3‖ / 2 := hmul
    exact lt_trans hmid hhalf_lt
  linarith

theorem exists_fixed_northZonal_not_sqprofile_linearized_fixedpart_approx_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      g sphereE3 ≠ 0 ∧
      ¬ (∀ {η : ℝ}, 0 < η →
            ∃ p : ℝ[X],
              p.eval 0 = 0 ∧
              dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16) := by
  rcases exists_nonzero_northZonal_mem_topologicalClosure_highEvenUnion_inf_frame_with_pole_ne_zero hne with
    ⟨g, hg, hgne, hgz, hgpole⟩
  refine ⟨g, hg, hgne, hgz, hgpole, ?_⟩
  exact
    not_sqprofile_linearized_fixedpart_approx_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_pole_ne_zero
      hg hgz hgpole

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_linearized_degree_defect_approx
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        (∀ {η : ℝ}, 0 < η →
          ∃ ε : ℝ, 0 < ε ∧
          ∃ N : ℕ, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
            h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
            IsNorthZonal h ∧
            (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
            q ∈ Polynomial.degreeLT ℝ N ∧
            ‖h - g‖ < ε ∧
            sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε ∧
            2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε < η / 16)) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  refine
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_linearized_fixedpart_approx ?_
  intro g hg hgz η hη
  rcases htame hg hgz hη with
    ⟨ε, hε, N, h, q, hhN, hhz, hq, hqdeg, hdist, hdefect, hsmall⟩
  refine ⟨(Polynomial.X : Polynomial ℝ) * q, by simp, ?_⟩
  have hhHigh : h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule :=
    Submodule.mem_iSup_of_mem N hhN
  have hpoly :
      sqCenteredNorthZonalContinuousMap h =
        sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) := by
    ext u
    change sqCenteredNorthZonalProfile h u =
      ((Polynomial.X : Polynomial ℝ) * q).eval u.1
    rw [hq u]
    simp
  have hlin_h :
      ‖sqCenteredNorthZonalContinuousMap h -
          sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖
        ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    calc
      ‖sqCenteredNorthZonalContinuousMap h -
          sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖
        = ‖sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) -
            sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖ := by
              rw [hpoly]
      _ ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) *
            sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) := by
              exact
                norm_sqProfilePolynomialMap_X_mul_sub_linear_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect
                  hqdeg
      _ ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) * (6 * ε) := by
            have hconst_nonneg :
                0 ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) := by
              unfold degreeLTSqProfileTailBoundConst
              positivity
            exact mul_le_mul_of_nonneg_left (le_of_lt hdefect) hconst_nonneg
      _ = 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by ring
  have hprofdist :
      dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g) < 2 * ε := by
    calc
      dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g)
        = ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ := by
            simp [dist_eq_norm]
      _ ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
      _ < 2 * ε := by gcongr
  have hlin_h' :
      dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
        (sqCenteredNorthZonalContinuousMap h)
        ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    simpa [dist_eq_norm, norm_sub_rev] using hlin_h
  have hlin :
      dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
        (sqCenteredNorthZonalContinuousMap g) < η / 16 := by
    calc
      dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
          (sqCenteredNorthZonalContinuousMap g)
        ≤ dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
            (sqCenteredNorthZonalContinuousMap h) +
          dist (sqCenteredNorthZonalContinuousMap h)
            (sqCenteredNorthZonalContinuousMap g) := by
              exact dist_triangle _ _ _
      _ < 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε + 2 * ε := by
            have hprofdist_le : dist (sqCenteredNorthZonalContinuousMap h)
                (sqCenteredNorthZonalContinuousMap g) ≤ 2 * ε := le_of_lt hprofdist
            linarith
      _ = 2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by ring
      _ < η / 16 := hsmall
  exact hlin

theorem eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_linearized_degree_defect_approx
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (htame :
      ∀ {η : ℝ}, 0 < η →
        ∃ ε : ℝ, 0 < ε ∧
        ∃ N : ℕ, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          q ∈ Polynomial.degreeLT ℝ N ∧
          ‖h - g‖ < ε ∧
          sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε ∧
          2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε < η / 16) :
    g = 0 := by
  refine
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_linearized_fixedpart_approx
      hg hgz ?_
  intro η hη
  rcases htame hη with ⟨ε, hε, N, h, q, hhN, hhz, hq, hqdeg, hdist, hdefect, hsmall⟩
  refine ⟨(Polynomial.X : Polynomial ℝ) * q, by simp, ?_⟩
  have hhHigh : h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule :=
    Submodule.mem_iSup_of_mem N hhN
  have hpoly :
      sqCenteredNorthZonalContinuousMap h =
        sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) := by
    ext u
    change sqCenteredNorthZonalProfile h u =
      ((Polynomial.X : Polynomial ℝ) * q).eval u.1
    rw [hq u]
    simp
  have hlin_h :
      ‖sqCenteredNorthZonalContinuousMap h -
          sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖
        ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    calc
      ‖sqCenteredNorthZonalContinuousMap h -
          sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖
        = ‖sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) -
            sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖ := by
              rw [hpoly]
      _ ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) *
            sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) := by
              exact
                norm_sqProfilePolynomialMap_X_mul_sub_linear_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect
                  hqdeg
      _ ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) * (6 * ε) := by
            have hconst_nonneg :
                0 ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) := by
              unfold degreeLTSqProfileTailBoundConst
              positivity
            exact mul_le_mul_of_nonneg_left (le_of_lt hdefect) hconst_nonneg
      _ = 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by ring
  have hprofdist :
      dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g) < 2 * ε := by
    calc
      dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g)
        = ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ := by
            simp [dist_eq_norm]
      _ ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
      _ < 2 * ε := by gcongr
  have hlin_h' :
      dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
        (sqCenteredNorthZonalContinuousMap h)
        ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    simpa [dist_eq_norm, norm_sub_rev] using hlin_h
  have hlin :
      dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
        (sqCenteredNorthZonalContinuousMap g) < η / 16 := by
    calc
      dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
          (sqCenteredNorthZonalContinuousMap g)
        ≤ dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
            (sqCenteredNorthZonalContinuousMap h) +
          dist (sqCenteredNorthZonalContinuousMap h)
            (sqCenteredNorthZonalContinuousMap g) := by
              exact dist_triangle _ _ _
      _ < 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε + 2 * ε := by
            have hprofdist_le : dist (sqCenteredNorthZonalContinuousMap h)
                (sqCenteredNorthZonalContinuousMap g) ≤ 2 * ε := le_of_lt hprofdist
            linarith
      _ = 2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by ring
      _ < η / 16 := hsmall
  exact hlin

theorem not_sqprofile_linearized_degree_defect_approx_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g) :
    ¬ (∀ {η : ℝ}, 0 < η →
          ∃ ε : ℝ, 0 < ε ∧
          ∃ N : ℕ, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
            h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
            IsNorthZonal h ∧
            (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
            q ∈ Polynomial.degreeLT ℝ N ∧
            ‖h - g‖ < ε ∧
            sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε ∧
            2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε < η / 16) := by
  intro htame
  have hzero :
      g = 0 :=
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqprofile_linearized_degree_defect_approx
      hg hgz htame
  exact hgne hzero

theorem exists_fixed_northZonal_not_sqprofile_linearized_degree_defect_approx_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      ¬ (∀ {η : ℝ}, 0 < η →
            ∃ ε : ℝ, 0 < ε ∧
            ∃ N : ℕ, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
              h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
              IsNorthZonal h ∧
              (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
              q ∈ Polynomial.degreeLT ℝ N ∧
              ‖h - g‖ < ε ∧
              sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε ∧
              2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε < η / 16) := by
  rcases exists_nonzero_northZonal_fixed_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz, _⟩
  refine ⟨g, hg, hgne, hgz, ?_⟩
  exact
    not_sqprofile_linearized_degree_defect_approx_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal
      hg hgne hgz
