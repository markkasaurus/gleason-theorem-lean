import Gleason.Harmonic.HighDegree.HighEvenUnionSquaredProfileGeneric
import Gleason.Harmonic.HighDegree.HighEvenUnionSquaredProfileAlmostFixed
import Gleason.Harmonic.HighDegree.HighEvenUnionProfilePolyApprox
import Gleason.Harmonic.HighDegree.HighEvenUnionNorthProfileAlmostFixed
import Gleason.Harmonic.HighDegree.EvenBoundedPolyBridge
import Gleason.Harmonic.HighDegree.EvenBoundedProjection
import Gleason.Harmonic.HighDegree.EvenLowConcrete
import Gleason.Harmonic.Profile.DegreeLTSquaredProfileTailBound
import Gleason.Harmonic.Profile.DegreeLTSquaredProfileDefectBound
import Gleason.Harmonic.Profile.DegreeLTSquaredQuotientDefectBound
import Gleason.Harmonic.Profile.SquaredQuotientFactorUniqueness
import Gleason.Harmonic.Auxiliary.GlobalLowProjection

noncomputable section

open Complex InnerProductSpace Polynomial

theorem sphereEvenSymm_eq_of_mem_highEvenUnionHarmonicPolyHomogeneousImageSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule) :
    sphereEvenSymm f = f := by
  have hmono : Directed (· ≤ ·) highEvenBoundedHarmonicPolyHomogeneousImageSubmodule := by
    intro N M
    exact ⟨max N M,
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_left _ _),
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _)⟩
  rw [highEvenUnionHarmonicPolyHomogeneousImageSubmodule] at hf
  rcases (Submodule.mem_iSup_of_directed highEvenBoundedHarmonicPolyHomogeneousImageSubmodule hmono).mp hf with
    ⟨N, hfN⟩
  exact sphereEvenSymm_eq_of_mem_evenBoundedHarmonicPolyHomogeneousImageSubmodule <|
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule
      N hfN

theorem antipode_even_of_mem_highEvenUnionHarmonicPolyHomogeneousImageSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule) :
    ∀ x : spherePoint3, f (sphereAntipode x) = f x := by
  intro x
  have hfix := congrArg (fun g : C(spherePoint3, ℝ) => g x)
    (sphereEvenSymm_eq_of_mem_highEvenUnionHarmonicPolyHomogeneousImageSubmodule hf)
  simp [sphereEvenSymm_apply] at hfix
  linarith

def lowSqProfileMode (a b : ℝ) : C(spherePoint3, ℝ) :=
  (a + b / 3) • (1 : C(spherePoint3, ℝ)) + (-b / 3) • zonalQuadraticMode

lemma lowSqProfileMode_apply (a b : ℝ) (x : spherePoint3) :
    lowSqProfileMode a b x = a + b * sphereCoordZ x ^ 2 := by
  simp [lowSqProfileMode, zonalQuadraticMode_apply, Pi.smul_apply]
  ring

lemma lowSqProfileMode_apply_sphereE1 (a b : ℝ) :
    lowSqProfileMode a b sphereE1 = a := by
  simp [lowSqProfileMode_apply, sphereCoordZ, sphereE1]

lemma lowSqProfileMode_mem_lowHarmonicPolyHomogeneousImageSubmodule (a b : ℝ) :
    lowSqProfileMode a b ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
  change
    (a + b / 3) • (1 : C(spherePoint3, ℝ)) + (-b / 3) • zonalQuadraticMode ∈
      lowHarmonicPolyHomogeneousImageSubmodule
  apply Submodule.add_mem_sup
  · exact Submodule.smul_mem _ (a + b / 3) one_mem_harmonicPolyHomogeneousImageSubmodule_zero
  · exact Submodule.smul_mem _ (-b / 3) zonalQuadraticMode_mem_harmonicPolyHomogeneousImageSubmodule_two

lemma isNorthZonal_lowSqProfileMode (a b : ℝ) :
    IsNorthZonal (lowSqProfileMode a b) := by
  intro t
  ext x
  simp [lowSqProfileMode_apply, spherePrecomp_apply, sphereMap, northRotation_apply, sphereCoordZ]

lemma antipode_even_lowSqProfileMode (a b : ℝ) :
    ∀ x : spherePoint3, lowSqProfileMode a b (sphereAntipode x) = lowSqProfileMode a b x := by
  intro x
  simp [lowSqProfileMode_apply, sphereCoordZ, sphereAntipode]

private theorem norm_northZonalContinuousMap_eq_of_isNorthZonal_local
    {f : C(spherePoint3, ℝ)}
    (hfz : IsNorthZonal f) :
    ‖northZonalContinuousMap f‖ = ‖f‖ := by
  have hle : ‖northZonalContinuousMap f‖ ≤ ‖f‖ := by
    haveI : Nonempty northIcc := ⟨zeroIcc⟩
    refine (ContinuousMap.norm_le_of_nonempty
      (f := northZonalContinuousMap f)
      (M := ‖f‖)).2 ?_
    intro z
    rw [northZonalContinuousMap_apply, northZonalProfile_apply]
    exact f.norm_coe_le_norm _
  have hge : ‖f‖ ≤ ‖northZonalContinuousMap f‖ := by
    haveI : Nonempty spherePoint3 := ⟨sphereE3⟩
    refine (ContinuousMap.norm_le_of_nonempty
      (f := f)
      (M := ‖northZonalContinuousMap f‖)).2 ?_
    intro x
    have hprof :
        northZonalContinuousMap f ⟨sphereCoordZ x, snd_mem_Icc x⟩ = f x := by
      simpa [northZonalContinuousMap_apply] using
        northZonalProfile_eq_of_isNorthZonal hfz x
    calc
      ‖f x‖ = ‖northZonalContinuousMap f ⟨sphereCoordZ x, snd_mem_Icc x⟩‖ := by
          rw [← hprof]
      _ ≤ ‖northZonalContinuousMap f‖ := (northZonalContinuousMap f).norm_coe_le_norm _
  exact le_antisymm hle hge

private lemma centeredNorthZonalProfile_eq_absIcc_of_isNorthZonal_of_antipode_even
    {f : C(spherePoint3, ℝ)}
    (hfz : IsNorthZonal f)
    (hanti : ∀ x : spherePoint3, f (sphereAntipode x) = f x)
    (z : Set.Icc (-1 : ℝ) 1) :
    centeredNorthZonalProfile f (absIcc z) = centeredNorthZonalProfile f z := by
  by_cases hz : 0 ≤ z.1
  · have habs : absIcc z = z := by
      apply Subtype.ext
      simp [absIcc, abs_of_nonneg hz]
    rw [habs]
  · have habs : absIcc z = negIcc z := by
      apply Subtype.ext
      simp [absIcc, negIcc, abs_of_neg (lt_of_not_ge hz)]
    rw [habs]
    exact centeredNorthZonalProfile_even_of_isNorthZonal_of_antipode_even hfz hanti z

theorem norm_eq_norm_sqCenteredNorthZonalContinuousMap_of_isNorthZonal_of_antipode_even_of_sphereE1_eq_zero
    {f : C(spherePoint3, ℝ)}
    (hfz : IsNorthZonal f)
    (hanti : ∀ x : spherePoint3, f (sphereAntipode x) = f x)
    (hf0 : f sphereE1 = 0) :
    ‖f‖ = ‖sqCenteredNorthZonalContinuousMap f‖ := by
  have hzeroE2 : f sphereE2 = 0 := by
    rw [← hf0]
    apply eq_of_isNorthZonal_of_sphereCoordZ_eq hfz
    norm_num [sphereCoordZ, sphereE1, sphereE2]
  have hzeroProf : northZonalProfile f zeroIcc = 0 := by
    simpa [hzeroE2] using northZonalProfile_zero_of_isNorthZonal hfz
  have hle1 : ‖sqCenteredNorthZonalContinuousMap f‖ ≤ ‖northZonalContinuousMap f‖ := by
    haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
    refine (ContinuousMap.norm_le_of_nonempty
      (f := sqCenteredNorthZonalContinuousMap f)
      (M := ‖northZonalContinuousMap f‖)).2 ?_
    intro u
    let zsqrt : northIcc :=
      ⟨Real.sqrt u.1, by
        constructor
        · have : 0 ≤ Real.sqrt u.1 := Real.sqrt_nonneg u.1
          nlinarith
        · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
          have hle : Real.sqrt u.1 ≤ 1 := by
            nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
          simpa using hle⟩
    have hz :
        ‖sqCenteredNorthZonalContinuousMap f u‖ = ‖northZonalContinuousMap f zsqrt‖ := by
          change ‖centeredNorthZonalProfile f zsqrt‖ = ‖northZonalProfile f zsqrt‖
          rw [centeredNorthZonalProfile, hzeroProf]
          simp
    rw [hz]
    exact (northZonalContinuousMap f).norm_coe_le_norm _
  have hle2 : ‖northZonalContinuousMap f‖ ≤ ‖sqCenteredNorthZonalContinuousMap f‖ := by
    haveI : Nonempty northIcc := ⟨zeroIcc⟩
    refine (ContinuousMap.norm_le_of_nonempty
      (f := northZonalContinuousMap f)
      (M := ‖sqCenteredNorthZonalContinuousMap f‖)).2 ?_
    intro z
    have hsq :
        northZonalProfile f z =
          sqCenteredNorthZonalContinuousMap f ⟨z.1 ^ 2, sq_mem_Icc z⟩ := by
      calc
        northZonalProfile f z = centeredNorthZonalProfile f z := by
          rw [centeredNorthZonalProfile, hzeroProf]
          ring
        _ = centeredNorthZonalProfile f (absIcc z) := by
          symm
          exact centeredNorthZonalProfile_eq_absIcc_of_isNorthZonal_of_antipode_even hfz hanti z
        _ = sqCenteredNorthZonalProfile f ⟨z.1 ^ 2, sq_mem_Icc z⟩ := by
          symm
          exact sqCenteredNorthZonalProfile_eq_absProfile f z
        _ = sqCenteredNorthZonalContinuousMap f ⟨z.1 ^ 2, sq_mem_Icc z⟩ := by
          rfl
    have hnormz :
        ‖northZonalContinuousMap f z‖ =
          ‖sqCenteredNorthZonalContinuousMap f ⟨z.1 ^ 2, sq_mem_Icc z⟩‖ := by
      rw [northZonalContinuousMap_apply, hsq]
    rw [hnormz]
    exact (sqCenteredNorthZonalContinuousMap f).norm_coe_le_norm _
  have hnorm :
      ‖northZonalContinuousMap f‖ = ‖sqCenteredNorthZonalContinuousMap f‖ :=
    le_antisymm hle2 hle1
  calc
    ‖f‖ = ‖northZonalContinuousMap f‖ := (norm_northZonalContinuousMap_eq_of_isNorthZonal_local hfz).symm
    _ = ‖sqCenteredNorthZonalContinuousMap f‖ := hnorm

theorem norm_sub_eq_norm_sqCenteredNorthZonalContinuousMap_sub_of_isNorthZonal_of_antipode_even_of_eq_sphereE1
    {f g : C(spherePoint3, ℝ)}
    (hfz : IsNorthZonal f)
    (hgz : IsNorthZonal g)
    (hfeven : ∀ x : spherePoint3, f (sphereAntipode x) = f x)
    (hgeven : ∀ x : spherePoint3, g (sphereAntipode x) = g x)
    (hEq : f sphereE1 = g sphereE1) :
    ‖f - g‖ = ‖sqCenteredNorthZonalContinuousMap f - sqCenteredNorthZonalContinuousMap g‖ := by
  have hsubz : IsNorthZonal (f - g) := by
    intro t
    ext x
    simp [hfz t, hgz t]
  have hsubeven : ∀ x : spherePoint3, (f - g) (sphereAntipode x) = (f - g) x := by
    intro x
    simp [hfeven x, hgeven x]
  have hsub0 : (f - g) sphereE1 = 0 := by
    simp [hEq]
  calc
    ‖f - g‖ = ‖sqCenteredNorthZonalContinuousMap (f - g)‖ :=
      norm_eq_norm_sqCenteredNorthZonalContinuousMap_of_isNorthZonal_of_antipode_even_of_sphereE1_eq_zero
        hsubz hsubeven hsub0
    _ = ‖sqCenteredNorthZonalContinuousMap f - sqCenteredNorthZonalContinuousMap g‖ := by
      congr 1
      ext u
      simp [sqCenteredNorthZonalContinuousMap, sqCenteredNorthZonalProfile,
        centeredNorthZonalProfile, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma sqCenteredNorthZonalContinuousMap_lowSqProfileMode (a b : ℝ) :
    sqCenteredNorthZonalContinuousMap (lowSqProfileMode a b) =
      (C b * X).toContinuousMapOn unitIcc := by
  ext u
  change sqCenteredNorthZonalProfile (lowSqProfileMode a b) u = (C b * X).eval u.1
  let z : northIcc :=
    ⟨Real.sqrt u.1, by
      constructor
      · have : 0 ≤ Real.sqrt u.1 := Real.sqrt_nonneg u.1
        nlinarith
      · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
        have hle : Real.sqrt u.1 ≤ 1 := by
          nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
        simpa using hle⟩
  rw [sqCenteredNorthZonalProfile_apply]
  have hmain :
      lowSqProfileMode a b (northSection z) = a + b * u.1 := by
    rw [lowSqProfileMode_apply]
    have hzsq : sphereCoordZ (northSection z) ^ 2 = u.1 := by
      simp [z, northSection, sphereCoordZ, Real.sq_sqrt u.2.1]
    rw [hzsq]
  have hzero :
      lowSqProfileMode a b (northSection zeroIcc) = a := by
    rw [northSection_zeroIcc_eq_sphereE1, lowSqProfileMode_apply_sphereE1]
  rw [centeredNorthZonalProfile, northZonalProfile_apply, northZonalProfile_apply, hmain, hzero]
  simp

theorem norm_sub_lowSqProfileMode_eq_sqprofile_of_isNorthZonal_of_antipode_even
    {h : C(spherePoint3, ℝ)} {b : ℝ}
    (hhz : IsNorthZonal h)
    (hheven : ∀ x : spherePoint3, h (sphereAntipode x) = h x) :
    ‖h - lowSqProfileMode (h sphereE1) b‖ =
      ‖sqCenteredNorthZonalContinuousMap h - (C b * X).toContinuousMapOn unitIcc‖ := by
  have hlowz : IsNorthZonal (lowSqProfileMode (h sphereE1) b) :=
    isNorthZonal_lowSqProfileMode _ _
  have hloweven :
      ∀ x : spherePoint3,
        lowSqProfileMode (h sphereE1) b (sphereAntipode x) =
          lowSqProfileMode (h sphereE1) b x :=
    antipode_even_lowSqProfileMode _ _
  have hEq :
      h sphereE1 = lowSqProfileMode (h sphereE1) b sphereE1 := by
    rw [lowSqProfileMode_apply_sphereE1]
  rw [norm_sub_eq_norm_sqCenteredNorthZonalContinuousMap_sub_of_isNorthZonal_of_antipode_even_of_eq_sphereE1
    hhz hlowz hheven hloweven hEq]
  rw [sqCenteredNorthZonalContinuousMap_lowSqProfileMode]

theorem norm_sub_lowSqProfileMode_eq_sqprofile
    {h : C(spherePoint3, ℝ)} {q : ℝ[X]}
    (hhHigh : h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule)
    (hhz : IsNorthZonal h) :
    ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ =
      ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖ := by
  have hheven :
      ∀ x : spherePoint3, h (sphereAntipode x) = h x :=
    antipode_even_of_mem_highEvenUnionHarmonicPolyHomogeneousImageSubmodule hhHigh
  simpa [sqProfileLinearPart] using
    norm_sub_lowSqProfileMode_eq_sqprofile_of_isNorthZonal_of_antipode_even
      (hhz := hhz) (hheven := hheven) (b := q.coeff 0)

theorem abs_sqquotientFactor_sub_coeff_zero_le_of_mem_highEvenUnion_of_isNorthZonal
    {h : C(spherePoint3, ℝ)} {q : ℝ[X]} {δ : ℝ}
    (hhHigh : h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule)
    (hhz : IsNorthZonal h)
    (hq : ∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1)
    (hδ : 0 < δ)
    {u : unitIcc}
    (hu : δ ≤ u.1) :
    |q.eval u.1 - q.coeff 0| ≤
      ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ / δ := by
  have hu0 : u.1 ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ hu)
  have huPos : 0 < u.1 := lt_of_lt_of_le hδ hu
  have hlow :
      sqCenteredNorthZonalProfile
          (lowSqProfileMode (h sphereE1) (q.coeff 0)) u =
        u.1 * q.coeff 0 := by
    let z : northIcc :=
      ⟨Real.sqrt u.1, by
        constructor
        · have : 0 ≤ Real.sqrt u.1 := Real.sqrt_nonneg u.1
          nlinarith
        · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
          have hle : Real.sqrt u.1 ≤ 1 := by
            nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]
          simpa using hle⟩
    rw [sqCenteredNorthZonalProfile_apply]
    have hmain :
        lowSqProfileMode (h sphereE1) (q.coeff 0) (northSection z) =
          h sphereE1 + q.coeff 0 * u.1 := by
      rw [lowSqProfileMode_apply]
      have hzsq : sphereCoordZ (northSection z) ^ 2 = u.1 := by
        simp [z, northSection, sphereCoordZ, Real.sq_sqrt u.2.1]
      rw [hzsq]
    have hzero :
        lowSqProfileMode (h sphereE1) (q.coeff 0) (northSection zeroIcc) = h sphereE1 := by
      rw [northSection_zeroIcc_eq_sphereE1, lowSqProfileMode_apply_sphereE1]
    rw [centeredNorthZonalProfile, northZonalProfile_apply, northZonalProfile_apply, hmain, hzero]
    ring
  have hquot :
      q.eval u.1 - q.coeff 0 =
        (sqCenteredNorthZonalProfile h u -
          sqCenteredNorthZonalProfile
            (lowSqProfileMode (h sphereE1) (q.coeff 0)) u) / u.1 := by
    rw [hq u, hlow]
    field_simp [hu0]
  have hpoint :
      |sqCenteredNorthZonalProfile h u -
          sqCenteredNorthZonalProfile
            (lowSqProfileMode (h sphereE1) (q.coeff 0)) u|
        ≤ ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖ := by
    have hpt :=
      (sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)).norm_coe_le_norm u
    have hpt' :
        |sqCenteredNorthZonalProfile h u - u.1 * q.coeff 0|
          ≤ ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖ := by
      have hpoly :
          ((C (q.coeff 0) * X).toContinuousMapOn unitIcc) u = u.1 * q.coeff 0 := by
        change (C (q.coeff 0) * X).eval u.1 = u.1 * q.coeff 0
        rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        ring
      simpa [sqCenteredNorthZonalContinuousMap, sqProfileLinearPart, ContinuousMap.sub_apply,
        Real.norm_eq_abs, hpoly] using hpt
    rw [hlow]
    simpa using hpt'
  rw [hquot, abs_div, abs_of_pos huPos]
  calc
    |sqCenteredNorthZonalProfile h u -
        sqCenteredNorthZonalProfile
          (lowSqProfileMode (h sphereE1) (q.coeff 0)) u| / u.1
      ≤ ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖ / u.1 := by
          gcongr
    _ ≤ ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖ / δ := by
          have hnorm_nonneg :
              0 ≤ ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖ := norm_nonneg _
          have hrecip : 1 / u.1 ≤ 1 / δ := one_div_le_one_div_of_le hδ hu
          calc
            ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖ / u.1
              = ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖ * (1 / u.1) := by
                  rw [div_eq_mul_one_div]
            _ ≤ ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖ * (1 / δ) := by
                  gcongr
            _ = ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖ / δ := by
                  rw [div_eq_mul_one_div]
                  ring
    _ = ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ / δ := by
          rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh hhz]

theorem exists_lowSqProfileMode_near_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε : ℝ}, 0 < ε → ∀ m : ℕ,
      ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
        h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
        IsNorthZonal h ∧
        l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
        ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < ε ∧
        ‖h - l‖ ≤
          (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (3 * ε) +
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
  intro ε hε m
  rcases exists_sqprofile_near_linear_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
      hg hgz hε m with
    ⟨h, q, hhHigh, hhz, hq, hdist, hlin⟩
  let l : C(spherePoint3, ℝ) := lowSqProfileMode (h sphereE1) (q.coeff 0)
  refine ⟨h, q, l, hhHigh, hhz, lowSqProfileMode_mem_lowHarmonicPolyHomogeneousImageSubmodule _ _, hdist, ?_⟩
  change ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ ≤
      (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (3 * ε) +
        (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q)
  rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh hhz]
  simpa [sqProfileLinearPart]
    using hlin

theorem exists_fixed_northZonal_lowSqProfileMode_near_of_nontrivial_tail
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
        ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          ‖h - l‖ ≤
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
  rcases exists_fixed_northZonal_sqprofile_near_linear_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole m
  rcases happ hε hεpole m with
    ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hlin⟩
  let l : C(spherePoint3, ℝ) := lowSqProfileMode (h sphereE1) (q.coeff 0)
  refine ⟨h, q, l, hhHigh, hhz, hhpole,
    lowSqProfileMode_mem_lowHarmonicPolyHomogeneousImageSubmodule _ _, hdist, ?_⟩
  change ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ ≤
      (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
        (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q)
  rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh hhz]
  simpa [sqProfileLinearPart]
    using hlin

theorem exists_lowSqProfileMode_uniform_near_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
        h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
        IsNorthZonal h ∧
        l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
        ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < ε ∧
        ∀ m : ℕ,
          ‖h - l‖ ≤
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (3 * ε) +
              (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
  intro ε hε
  rcases
      exists_sqquotient_poly_almost_fixed_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
        hg hgz hε with
    ⟨h, q, hhHigh, hhz, hq, hdist, hdefect⟩
  let l : C(spherePoint3, ℝ) := lowSqProfileMode (h sphereE1) (q.coeff 0)
  refine ⟨h, q, l, hhHigh, hhz, lowSqProfileMode_mem_lowHarmonicPolyHomogeneousImageSubmodule _ _,
    hdist, ?_⟩
  intro m
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
          (sqProfilePolynomialMap (X * q)) < 3 * ε := by
    simpa [hpoly, dist_eq_norm] using hdefect
  change ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ ≤
      (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (3 * ε) +
        (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q)
  rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh hhz]
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

theorem exists_fixed_northZonal_lowSqProfileMode_uniform_near_of_nontrivial_tail
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
        ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          ∀ m : ℕ,
            ‖h - l‖ ≤
              (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
  rcases exists_fixed_northZonal_sqprofile_almost_fixed_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hdefect⟩
  let l : C(spherePoint3, ℝ) := lowSqProfileMode (h sphereE1) (q.coeff 0)
  refine ⟨h, q, l, hhHigh, hhz, hhpole,
    lowSqProfileMode_mem_lowHarmonicPolyHomogeneousImageSubmodule _ _, hdist, ?_⟩
  intro m
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
  change ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ ≤
      (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
        (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q)
  rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh hhz]
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

theorem exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_factor_of_nontrivial_tail
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
        ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          ∀ m : ℕ,
            ‖h - l‖ ≤
              (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
  rcases exists_fixed_northZonal_sqprofile_almost_fixed_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hdefect⟩
  let l : C(spherePoint3, ℝ) := lowSqProfileMode (h sphereE1) (q.coeff 0)
  refine ⟨h, q, l, hhHigh, hhz, hhpole, hq,
    lowSqProfileMode_mem_lowHarmonicPolyHomogeneousImageSubmodule _ _, hdist, ?_⟩
  intro m
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
  change ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ ≤
      (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
        (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q)
  rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh hhz]
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

theorem exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_factor_degree_tail_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          q ∈ Polynomial.degreeLT ℝ N ∧
          sqProfileTailAbsSum (X * q)
            ≤ degreeLTSqProfileTailBoundConst (N + 1) * ‖sqCenteredNorthZonalContinuousMap h‖ ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          ∀ m : ℕ,
            ‖h - l‖ ≤
              (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
  rcases exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_factor_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨h, q0, l, hhHigh, hhz, hhpole, hq0, hl, hdist, hnear⟩
  have hmono : Directed (· ≤ ·) highEvenBoundedHarmonicPolyHomogeneousImageSubmodule := by
    intro N M
    exact ⟨max N M,
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_left _ _),
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _)⟩
  rw [highEvenUnionHarmonicPolyHomogeneousImageSubmodule] at hhHigh
  rcases (Submodule.mem_iSup_of_directed highEvenBoundedHarmonicPolyHomogeneousImageSubmodule hmono).mp hhHigh with
    ⟨N0, hhN0⟩
  let N : ℕ := max 1 N0
  have hN : 1 ≤ N := le_max_left _ _
  have hhN : h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _) hhN0
  rcases exists_sqquotient_poly_degree_and_tail_bound_of_mem_highEvenBounded_of_isNorthZonal hhN hhz with
    ⟨q, hqdeg, hq, htail⟩
  have hqq : q = q0 := by
    apply sqquotient_factor_polynomial_unique_on_unitIcc
    intro u
    exact (hq u).symm.trans (hq0 u)
  refine ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, htail, hl, hdist, ?_⟩
  intro m
  have hqq' : X * q = X * q0 := by
    rw [hqq]
  calc
    ‖h - l‖
      ≤ (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q0) := hnear m
    _ =
        (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
            rw [← hqq']

theorem exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_factor_degree_defect_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          q ∈ Polynomial.degreeLT ℝ N ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          sqProfilePolynomialDefect (X * q) < 6 * ε ∧
          ‖h - l‖ ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
  rcases exists_fixed_northZonal_sqprofile_almost_fixed_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with ⟨h, q0, hhHigh, hhz, hhpole, hq0, hdist, hdefect⟩
  have hmono : Directed (· ≤ ·) highEvenBoundedHarmonicPolyHomogeneousImageSubmodule := by
    intro N M
    exact ⟨max N M,
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_left _ _),
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _)⟩
  rw [highEvenUnionHarmonicPolyHomogeneousImageSubmodule] at hhHigh
  rcases (Submodule.mem_iSup_of_directed highEvenBoundedHarmonicPolyHomogeneousImageSubmodule hmono).mp hhHigh with
    ⟨N0, hhN0⟩
  let N : ℕ := max 1 N0
  have hN : 1 ≤ N := le_max_left _ _
  have hhN : h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _) hhN0
  rcases exists_sqquotient_poly_degree_and_tail_bound_of_mem_highEvenBounded_of_isNorthZonal hhN hhz with
    ⟨q, hqdeg, hq, htail⟩
  have hqq : q = q0 := by
    apply sqquotient_factor_polynomial_unique_on_unitIcc
    intro u
    exact (hq u).symm.trans (hq0 u)
  let l : C(spherePoint3, ℝ) := lowSqProfileMode (h sphereE1) (q.coeff 0)
  have hp0 : (X * q : ℝ[X]).eval 0 = 0 := by simp
  have hpoly :
      sqCenteredNorthZonalContinuousMap h = sqProfilePolynomialMap (X * q) := by
    ext u
    change sqCenteredNorthZonalProfile h u = (X * q).eval u.1
    rw [hq u]
    simp
  have hdefect' : sqProfilePolynomialDefect (X * q) < 6 * ε := by
    simpa [sqProfilePolynomialDefect, hpoly, dist_eq_norm] using hdefect
  have hlin :
      ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖ ≤
        24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    calc
      ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart (X * q)‖
        = ‖sqProfilePolynomialMap (X * q) - sqProfileLinearPart (X * q)‖ := by
            rw [hpoly]
      _ ≤
          4 * degreeLTSqProfileTailBoundConst (N + 1) * sqProfilePolynomialDefect (X * q) := by
            exact
              norm_sqProfilePolynomialMap_X_mul_sub_linear_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect
                hqdeg
      _ ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) * (6 * ε) := by
            have hconst_nonneg : 0 ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) := by
              have htail_nonneg : 0 ≤ degreeLTSqProfileTailBoundConst (N + 1) := by
                unfold degreeLTSqProfileTailBoundConst
                positivity
              nlinarith
            exact mul_le_mul_of_nonneg_left (le_of_lt hdefect') hconst_nonneg
      _ = 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by ring
  have hnorm :
      ‖h - l‖ ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    have hhHigh : h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule :=
      Submodule.mem_iSup_of_mem N hhN
    change ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ ≤
      24 * degreeLTSqProfileTailBoundConst (N + 1) * ε
    rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh hhz]
    simpa [sqProfileLinearPart] using hlin
  refine ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg,
    lowSqProfileMode_mem_lowHarmonicPolyHomogeneousImageSubmodule _ _, hdist, hdefect', hnorm⟩

theorem exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_factor_degree_bothDefects_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          q ∈ Polynomial.degreeLT ℝ N ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          sqProfilePolynomialDefect (X * q) < 6 * ε ∧
          dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
              (q.toContinuousMapOn unitIcc) ≤
            degreeLTSqMulNormConst N * (6 * ε) ∧
          ‖h - l‖ ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
  rcases exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_factor_degree_defect_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hdefect, hnorm⟩
  have hqdefect :
      dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
          (q.toContinuousMapOn unitIcc) ≤
        degreeLTSqMulNormConst N * (6 * ε) := by
    calc
      dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
          (q.toContinuousMapOn unitIcc)
        ≤ degreeLTSqMulNormConst N * sqProfilePolynomialDefect (X * q) :=
          norm_quotientDefect_le_degreeLTSqMulNormConst_mul_sqprofileDefect hqdeg
      _ ≤ degreeLTSqMulNormConst N * (6 * ε) := by
          have hconst_nonneg : 0 ≤ degreeLTSqMulNormConst N := by
            unfold degreeLTSqMulNormConst
            positivity
          exact mul_le_mul_of_nonneg_left (le_of_lt hdefect) hconst_nonneg
  exact ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hdefect, hqdefect, hnorm⟩

theorem exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          ∀ m : ℕ,
            ‖h - l‖ ≤
              (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
  rcases exists_fixed_northZonal_lowSqProfileMode_uniform_near_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with ⟨h, q, l, hhHigh, hhz, hhpole, hl, hdist, hnear⟩
  have hmono : Directed (· ≤ ·) highEvenBoundedHarmonicPolyHomogeneousImageSubmodule := by
    intro N M
    exact ⟨max N M,
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_left _ _),
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _)⟩
  rw [highEvenUnionHarmonicPolyHomogeneousImageSubmodule] at hhHigh
  rcases (Submodule.mem_iSup_of_directed highEvenBoundedHarmonicPolyHomogeneousImageSubmodule hmono).mp hhHigh with
    ⟨N0, hhN0⟩
  let N : ℕ := max 1 N0
  have hN : 1 ≤ N := le_max_left _ _
  have hhN : h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _) hhN0
  exact ⟨N, hN, h, q, l, hhN, hhz, hhpole, hl, hdist, hnear⟩

theorem exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_and_sphereE3_constant_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          ∃ C : ℝ,
            h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
            IsNorthZonal h ∧
            h sphereE3 ≠ 0 ∧
            l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
            0 < C ∧
            ‖h - g‖ < ε ∧
            (∀ m : ℕ,
              ‖h - l‖ ≤
                (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                  (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q)) ∧
            (∀ m : ℕ,
              ‖h sphereE3‖ ≤
                C *
                  ((Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                    (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q))) := by
  rcases exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with ⟨N, hN, h, q, l, hhN, hhz, hhpole, hl, hdist, hnear⟩
  let C : ℝ := 1 + ‖ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM hN‖
  have hsphere :
      ∃ C : ℝ, 0 < C ∧ ‖h sphereE3‖ ≤ C * ‖h - l‖ := by
    refine ⟨C, ?_, ?_⟩
    · dsimp [C]
      positivity
    · dsimp [C]
      exact norm_sphereE3_le_one_add_const_mul_norm_sub_of_mem_highEvenBounded hN hhN hl
  rcases hsphere with ⟨C, hCpos, hCsphere⟩
  refine ⟨N, hN, h, q, l, C, hhN, hhz, hhpole, hl, hCpos, hdist, hnear, ?_⟩
  intro m
  calc
    ‖h sphereE3‖ ≤ C * ‖h - l‖ := hCsphere
    _ ≤
        C *
          ((Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q)) := by
          gcongr
          exact hnear m

theorem exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_and_pole_lower_bound_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          ∃ C : ℝ,
            h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
            IsNorthZonal h ∧
            h sphereE3 ≠ 0 ∧
            l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
            0 < C ∧
            ‖h - g‖ < ε ∧
            (∀ m : ℕ,
              ‖h - l‖ ≤
                (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                  (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q)) ∧
            (∀ m : ℕ,
              ‖g sphereE3‖ - ε ≤
                C *
                  ((Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                    (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q))) := by
  rcases exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_and_sphereE3_constant_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨N, hN, h, q, l, C, hhN, hhz, hhpole, hl, hCpos, hdist, hnear, hCsphere⟩
  refine ⟨N, hN, h, q, l, C, hhN, hhz, hhpole, hl, hCpos, hdist, hnear, ?_⟩
  intro m
  have hclose :
      ‖g sphereE3 - h sphereE3‖ < ε := by
    calc
      ‖g sphereE3 - h sphereE3‖ = ‖(g - h) sphereE3‖ := by
        simp [ContinuousMap.sub_apply, norm_sub_rev]
      _ ≤ ‖g - h‖ := (g - h).norm_coe_le_norm sphereE3
      _ = ‖h - g‖ := by rw [norm_sub_rev]
      _ < ε := hdist
  have hpole_le : ‖g sphereE3‖ - ε ≤ ‖h sphereE3‖ := by
    have htri : ‖g sphereE3‖ ≤ ‖g sphereE3 - h sphereE3‖ + ‖h sphereE3‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        norm_add_le (g sphereE3 - h sphereE3) (h sphereE3)
    linarith
  exact le_trans hpole_le (hCsphere m)

theorem
    exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_factor_degree_defect_and_pole_lower_bound_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          ∃ C : ℝ,
            h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
            IsNorthZonal h ∧
            h sphereE3 ≠ 0 ∧
            (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
            q ∈ Polynomial.degreeLT ℝ N ∧
            l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
            0 < C ∧
            ‖h - g‖ < ε ∧
            sqProfilePolynomialDefect (X * q) < 6 * ε ∧
            ‖h - l‖ ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε ∧
            ‖g sphereE3‖ - ε ≤
              C * (24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) := by
  rcases
      exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_factor_degree_defect_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hdefect, hnear⟩
  let C : ℝ := 1 + ‖ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM hN‖
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCsphere :
      ‖h sphereE3‖ ≤ C * ‖h - l‖ := by
    dsimp [C]
    exact norm_sphereE3_le_one_add_const_mul_norm_sub_of_mem_highEvenBounded hN hhN hl
  have hclose :
      ‖g sphereE3 - h sphereE3‖ < ε := by
    calc
      ‖g sphereE3 - h sphereE3‖ = ‖(g - h) sphereE3‖ := by
        simp [ContinuousMap.sub_apply, norm_sub_rev]
      _ ≤ ‖g - h‖ := (g - h).norm_coe_le_norm sphereE3
      _ = ‖h - g‖ := by rw [norm_sub_rev]
      _ < ε := hdist
  have hpole_le : ‖g sphereE3‖ - ε ≤ ‖h sphereE3‖ := by
    have htri : ‖g sphereE3‖ ≤ ‖g sphereE3 - h sphereE3‖ + ‖h sphereE3‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        norm_add_le (g sphereE3 - h sphereE3) (h sphereE3)
    linarith
  refine ⟨N, hN, h, q, l, C, hhN, hhz, hhpole, hq, hqdeg, hl, hCpos, hdist, hdefect, hnear, ?_⟩
  calc
    ‖g sphereE3‖ - ε ≤ ‖h sphereE3‖ := hpole_le
    _ ≤ C * ‖h - l‖ := hCsphere
    _ ≤ C * (24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) := by
          gcongr

theorem
    exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_global_pole_constant_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          q ∈ Polynomial.degreeLT ℝ N ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          sqProfilePolynomialDefect (X * q) < 6 * ε ∧
          ‖h - l‖ ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε ∧
          ‖g sphereE3‖ - ε ≤
            (1 + ‖GleasonS2Bridge.ambientLowHarmonicProjectionContinuous‖) *
              (24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) := by
  rcases
      exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_factor_degree_defect_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hdefect, hnear⟩
  have hhcl :
      h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure := by
    exact show h ∈
        ((highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure :
          Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ)) from
      subset_closure (Submodule.mem_iSup_of_mem N hhN)
  have hCsphere :
      ‖h sphereE3‖ ≤
        (1 + ‖GleasonS2Bridge.ambientLowHarmonicProjectionContinuous‖) * ‖h - l‖ := by
    exact
      GleasonS2Bridge.norm_sphereE3_le_one_add_global_const_mul_norm_sub_of_mem_low_of_mem_topologicalClosure_highEvenUnion
        hl hhcl
  have hclose :
      ‖g sphereE3 - h sphereE3‖ < ε := by
    calc
      ‖g sphereE3 - h sphereE3‖ = ‖(g - h) sphereE3‖ := by
        simp [ContinuousMap.sub_apply, norm_sub_rev]
      _ ≤ ‖g - h‖ := (g - h).norm_coe_le_norm sphereE3
      _ = ‖h - g‖ := by rw [norm_sub_rev]
      _ < ε := hdist
  have hpole_le : ‖g sphereE3‖ - ε ≤ ‖h sphereE3‖ := by
    have htri : ‖g sphereE3‖ ≤ ‖g sphereE3 - h sphereE3‖ + ‖h sphereE3‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        norm_add_le (g sphereE3 - h sphereE3) (h sphereE3)
    linarith
  refine ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hdefect, hnear, ?_⟩
  calc
    ‖g sphereE3‖ - ε ≤ ‖h sphereE3‖ := hpole_le
    _ ≤ (1 + ‖GleasonS2Bridge.ambientLowHarmonicProjectionContinuous‖) * ‖h - l‖ := hCsphere
    _ ≤
        (1 + ‖GleasonS2Bridge.ambientLowHarmonicProjectionContinuous‖) *
          (24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) := by
            gcongr

theorem
    exists_fixed_northZonal_degreeLTSqProfileTailBoundConst_mul_eps_lower_bound_of_nontrivial_tail
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
      ∀ {ε : ℝ}, 0 < ε → 2 * ε ≤ ‖g sphereE3‖ →
        ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          q ∈ Polynomial.degreeLT ℝ N ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          sqProfilePolynomialDefect (X * q) < 6 * ε ∧
          ‖g sphereE3‖ /
              (48 * (1 + ‖GleasonS2Bridge.ambientLowHarmonicProjectionContinuous‖)) ≤
            degreeLTSqProfileTailBoundConst (N + 1) * ε := by
  rcases
      exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_global_pole_constant_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hhalf
  have hεpole : ε < ‖g sphereE3‖ := lt_of_lt_of_le (by linarith) hhalf
  rcases happ hε hεpole with
    ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hdefect, hnear, hpole⟩
  refine ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hdefect, ?_⟩
  have hconst_pos : 0 < 48 * (1 + ‖GleasonS2Bridge.ambientLowHarmonicProjectionContinuous‖) := by
    positivity
  have hhalfpole : ‖g sphereE3‖ / 2 ≤ ‖g sphereE3‖ - ε := by
    linarith
  have hbound :
      ‖g sphereE3‖ / 2 ≤
        (1 + ‖GleasonS2Bridge.ambientLowHarmonicProjectionContinuous‖) *
          (24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) := by
    exact le_trans hhalfpole hpole
  have hbound' :
      ‖g sphereE3‖ ≤
        (48 * (1 + ‖GleasonS2Bridge.ambientLowHarmonicProjectionContinuous‖)) *
          (degreeLTSqProfileTailBoundConst (N + 1) * ε) := by
    nlinarith
  refine (div_le_iff₀ hconst_pos).2 ?_
  simpa [mul_comm, mul_left_comm, mul_assoc] using hbound'
