import Gleason.Harmonic.Zonal.NorthZonalSquaredFactor
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Piecewise

noncomputable section

open Complex Filter InnerProductSpace MeasureTheory intervalIntegral Real Topology
open scoped Topology

lemma continuous_northSection : Continuous (northSection : Set.Icc (-1 : ℝ) 1 → spherePoint3) := by
  unfold northSection
  exact
    ((WithLp.prod_continuous_toLp (p := 2) (α := ℂ) (β := ℝ)).comp
      ((Complex.ofRealCLM.continuous.comp
        ((continuous_const.sub (continuous_subtype_val.pow 2)).sqrt)).prodMk
          continuous_subtype_val)).subtype_mk
      (fun z => (northSection z).2)

lemma continuous_northZonalProfile (f : C(spherePoint3, ℝ)) :
    Continuous (northZonalProfile f) := by
  simpa [northZonalProfile] using f.continuous.comp continuous_northSection

lemma continuous_centeredNorthZonalProfile (f : C(spherePoint3, ℝ)) :
    Continuous (centeredNorthZonalProfile f) := by
  unfold centeredNorthZonalProfile
  exact continuous_northZonalProfile f |>.sub continuous_const

lemma continuous_sqProfileLift :
    Continuous (fun u : unitIcc =>
      (⟨Real.sqrt u.1, by
        constructor
        · nlinarith [Real.sqrt_nonneg u.1]
        · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
          nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq]⟩ : Set.Icc (-1 : ℝ) 1)) := by
  exact (continuous_subtype_val.sqrt).subtype_mk (fun u => by
    constructor
    · nlinarith [Real.sqrt_nonneg u.1]
    · have hsq : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
      nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq])

lemma continuous_sqCenteredNorthZonalProfile (f : C(spherePoint3, ℝ)) :
    Continuous (sqCenteredNorthZonalProfile f) := by
  unfold sqCenteredNorthZonalProfile
  exact (continuous_centeredNorthZonalProfile f).comp continuous_sqProfileLift

def sqCenteredNorthZonalProfileRaw (f : C(spherePoint3, ℝ)) : ℝ → ℝ :=
  fun u => sqCenteredNorthZonalProfile f (Set.projIcc 0 1 zero_le_one u)

lemma continuous_sqCenteredNorthZonalProfileRaw (f : C(spherePoint3, ℝ)) :
    Continuous (sqCenteredNorthZonalProfileRaw f) := by
  unfold sqCenteredNorthZonalProfileRaw
  exact (continuous_sqCenteredNorthZonalProfile f).comp continuous_projIcc

lemma sqCenteredNorthZonalProfileRaw_eq
    (f : C(spherePoint3, ℝ)) {u : ℝ} (hu : u ∈ unitIcc) :
    sqCenteredNorthZonalProfileRaw f u = sqCenteredNorthZonalProfile f ⟨u, hu⟩ := by
  unfold sqCenteredNorthZonalProfileRaw
  congr 1
  exact Set.projIcc_val zero_le_one ⟨u, hu⟩

lemma ambientCenteredNorthProfile_iteratedDeriv_two_continuousAt_zero
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ}
    (hf : HarmonicHomogeneousDegree n f) :
    ContinuousAt (iteratedDeriv 2 (ambientCenteredNorthProfile f)) 0 := by
  have hF :
      ContinuousAt (iteratedFDeriv ℝ 2 (ambientCenteredNorthProfile f)) 0 :=
    (ambientCenteredNorthProfile_contDiffAt_zero hf).continuousAt_iteratedFDeriv
      (k := 2) (by norm_num)
  simpa [iteratedDeriv_eq_iteratedFDeriv] using
    (continuous_eval_const (fun _ : Fin 2 => (1 : ℝ))).continuousAt.comp hF

lemma ambientCenteredNorthProfile_div_sq_tendsto_nhdsGT_zero
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree n f)
    (hfg : sphereRestrictionLinear f = g)
    (hgz : IsNorthZonal g)
    (hnEven : Even n) :
    Tendsto (fun z : ℝ => ambientCenteredNorthProfile f z / z ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (((2 : ℝ)⁻¹) * iteratedDeriv 2 (ambientCenteredNorthProfile f) 0)) := by
  let φ : ℝ → ℝ := ambientCenteredNorthProfile f
  let d2 : ℝ → ℝ := iteratedDeriv 2 φ
  let c : ℝ := ((2 : ℝ)⁻¹) * d2 0
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont2 : ContinuousAt d2 0 :=
    ambientCenteredNorthProfile_iteratedDeriv_two_continuousAt_zero hf
  rw [Metric.continuousAt_iff'] at hcont2
  have hnear : {y : ℝ | dist (d2 y) (d2 0) < 2 * ε} ∈ 𝓝 (0 : ℝ) := by
    simpa using hcont2 (2 * ε) (by positivity)
  rcases Metric.mem_nhds_iff.mp hnear with ⟨δ, hδpos, hδsub⟩
  have hsmall : Set.Ioo (0 : ℝ) (min halfRadius δ) ∈ 𝓝[>] (0 : ℝ) := by
    refine mem_nhdsWithin.2 ?_
    refine ⟨Set.Iio (min halfRadius δ), isOpen_Iio, ?_, ?_⟩
    · exact lt_min (by norm_num [halfRadius]) hδpos
    · intro y hy
      exact ⟨hy.2, hy.1⟩
  refine Filter.mem_of_superset hsmall ?_
  intro z hz
  rcases hz with ⟨hzpos, hzlt⟩
  have hzhalf : z < halfRadius := lt_of_lt_of_le hzlt (min_le_left _ _)
  have hzδ : z < δ := lt_of_lt_of_le hzlt (min_le_right _ _)
  have hsubset : Set.Icc (0 : ℝ) z ⊆ halfIcc := by
    intro y hy
    constructor
    · have : (-(1 / 2 : ℝ)) ≤ y := by nlinarith [hy.1]
      simpa [halfRadius] using this
    · have : y ≤ (1 / 2 : ℝ) := by
        have hyhalf : y < halfRadius := lt_of_le_of_lt hy.2 hzhalf
        simpa [halfRadius] using hyhalf.le
      simpa [halfRadius] using this
  have hcontOnz : ContDiffOn ℝ 2 φ (Set.Icc (0 : ℝ) z) :=
    (ambientCenteredNorthProfile_contDiffOn hf).mono hsubset
  obtain ⟨x', hx', hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (x₀ := 0) (x := z) (n := 1) hzpos hcontOnz
  have hderivWithin0 : derivWithin φ (Set.Icc (0 : ℝ) z) 0 = 0 := by
    have huniq0 : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) z) 0 :=
      (uniqueDiffOn_Icc hzpos).uniqueDiffWithinAt ⟨le_rfl, hzpos.le⟩
    have hhasWithin : HasDerivWithinAt φ (deriv φ 0) (Set.Icc (0 : ℝ) z) 0 :=
      (ambientCenteredNorthProfile_hasDerivAt_zero hf).hasDerivWithinAt
    rw [hhasWithin.derivWithin huniq0]
    exact ambientCenteredNorthProfile_deriv_zero_of_rep hf hfg hgz hnEven
  have hTaylor0 : taylorWithinEval φ 1 (Set.Icc (0 : ℝ) z) 0 z = 0 := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDerivWithin_one, hderivWithin0]
    simp [φ, ambientCenteredNorthProfile]
  have hzsqne : z ^ 2 ≠ 0 := pow_ne_zero 2 hzpos.ne'
  have hquot : φ z / z ^ 2 = ((2 : ℝ)⁻¹) * d2 x' := by
    have hEq : φ z = d2 x' * z ^ 2 / 2 := by
      nlinarith [hrem, hTaylor0]
    calc
      φ z / z ^ 2 = (d2 x' * z ^ 2 / 2) / z ^ 2 := by rw [hEq]
      _ = d2 x' / 2 := by
            field_simp [hzsqne]
      _ = ((2 : ℝ)⁻¹) * d2 x' := by ring
  have hx'δ : dist x' 0 < δ := by
    have hx'lt : x' < δ := lt_trans hx'.2 hzδ
    simpa [Real.dist_eq, abs_of_nonneg hx'.1.le] using hx'lt
  have hd2x' : dist (d2 x') (d2 0) < 2 * ε := hδsub hx'δ
  have hd2x'' : |d2 x' - d2 0| < 2 * ε := by
    simpa [Real.dist_eq] using hd2x'
  have hfinal : |((2 : ℝ)⁻¹) * d2 x' - c| < ε := by
    dsimp [c]
    calc
      |((2 : ℝ)⁻¹) * d2 x' - ((2 : ℝ)⁻¹) * d2 0|
          = |((2 : ℝ)⁻¹)| * |d2 x' - d2 0| := by
              rw [← mul_sub_left_distrib, abs_mul]
      _ = ((2 : ℝ)⁻¹) * |d2 x' - d2 0| := by norm_num
      _ < ((2 : ℝ)⁻¹) * (2 * ε) := by
            gcongr
      _ = ε := by ring
  have hfinal' : dist (φ z / z ^ 2) c < ε := by
    simpa [Real.dist_eq, c, hquot] using hfinal
  exact hfinal'

theorem exists_sqCenteredNorthZonalProfile_quotient_of_even_mem_continuousHarmonicSphereDegreeSubmodule
    {n : ℕ} {g : C(spherePoint3, ℝ)}
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hgz : IsNorthZonal g)
    (hnEven : Even n) :
    ∃ q : C(unitIcc, ℝ), ∀ u : unitIcc, sqCenteredNorthZonalProfile g u = u.1 * q u := by
  rcases (show (g : spherePoint3 → ℝ) ∈ harmonicSphereDegreeSubmodule n from hg) with
    ⟨f, hf, hfg⟩
  let c : ℝ := ((2 : ℝ)⁻¹) * iteratedDeriv 2 (ambientCenteredNorthProfile f) 0
  have hsqrtWithin :
      Tendsto (fun u : ℝ => Real.sqrt u) (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) := by
    let hsqrt0 : ContinuousAt (fun u : ℝ => Real.sqrt u) 0 := Real.continuous_sqrt.continuousAt
    simpa using (hsqrt0.continuousWithinAt).tendsto_nhdsWithin (by
      intro u hu
      exact Real.sqrt_pos.2 hu)
  have hsqrt :
      Tendsto (fun u : ℝ => Real.sqrt u) (𝓝[unitIcc \ ({0} : Set ℝ)] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    hsqrtWithin.mono_left <| nhdsWithin_mono _ (by
      intro u hu
      have hu0 : u ≠ 0 := by simpa using hu.2
      exact lt_of_le_of_ne hu.1.1 (Ne.symm hu0))
  have hquotient :
      Tendsto (fun u : ℝ => ambientCenteredNorthProfile f (Real.sqrt u) / (Real.sqrt u) ^ 2)
        (𝓝[unitIcc \ ({0} : Set ℝ)] (0 : ℝ)) (𝓝 c) := by
    simpa [c] using
      (ambientCenteredNorthProfile_div_sq_tendsto_nhdsGT_zero hf hfg hgz hnEven).comp hsqrt
  have hEqFilter :
      (fun u : ℝ => sqCenteredNorthZonalProfileRaw g u / u) =ᶠ[𝓝[unitIcc \ ({0} : Set ℝ)] (0 : ℝ)]
        (fun u : ℝ => ambientCenteredNorthProfile f (Real.sqrt u) / (Real.sqrt u) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have huIcc : u ∈ unitIcc := hu.1
    have hu0 : u ≠ 0 := by simpa using hu.2
    have hraw :
        sqCenteredNorthZonalProfileRaw g u =
          ambientCenteredNorthProfile f (Real.sqrt u) := by
      rw [sqCenteredNorthZonalProfileRaw_eq g huIcc, sqCenteredNorthZonalProfile_apply]
      let z : Set.Icc (-1 : ℝ) 1 := ⟨Real.sqrt u, by
        constructor
        · nlinarith [Real.sqrt_nonneg u]
        · have hsq : (Real.sqrt u) ^ 2 = u := Real.sq_sqrt huIcc.1
          nlinarith [huIcc.2, Real.sqrt_nonneg u, hsq]⟩
      simpa [z] using (ambientCenteredNorthProfile_eq_centeredNorthZonalProfile hgz hfg z).symm
    rw [hraw, Real.sq_sqrt huIcc.1]
  have hlimit :
      Tendsto (fun u : ℝ => sqCenteredNorthZonalProfileRaw g u / u)
        (𝓝[unitIcc \ ({0} : Set ℝ)] (0 : ℝ)) (𝓝 c) :=
    hquotient.congr' hEqFilter.symm
  have hbaseCont :
      ContinuousOn (fun u : ℝ => sqCenteredNorthZonalProfileRaw g u / u) (unitIcc \ ({0} : Set ℝ)) := by
    refine (continuous_sqCenteredNorthZonalProfileRaw g).continuousOn.div continuous_id.continuousOn ?_
    intro u hu
    exact hu.2
  let qRaw : ℝ → ℝ := Function.update (fun u : ℝ => sqCenteredNorthZonalProfileRaw g u / u) 0 c
  have hqRawCont : ContinuousOn qRaw unitIcc := by
    rw [show qRaw = Function.update (fun u : ℝ => sqCenteredNorthZonalProfileRaw g u / u) 0 c by rfl]
    rw [continuousOn_update_iff]
    refine ⟨hbaseCont, ?_⟩
    intro _
    simpa [qRaw] using hlimit
  let q : C(unitIcc, ℝ) := ⟨unitIcc.restrict qRaw, hqRawCont.restrict⟩
  refine ⟨q, ?_⟩
  intro u
  by_cases hu0 : u.1 = 0
  · have huz : u = zeroUnitIcc := by
      apply Subtype.ext
      exact hu0
    subst huz
    have hsqzero : sqCenteredNorthZonalProfile g zeroUnitIcc = 0 := by
      unfold sqCenteredNorthZonalProfile
      have hzero :
          (⟨Real.sqrt (↑zeroUnitIcc), by
            constructor
            · nlinarith [Real.sqrt_nonneg (↑zeroUnitIcc)]
            · have hsq : (Real.sqrt (↑zeroUnitIcc)) ^ 2 = (↑zeroUnitIcc : ℝ) :=
                Real.sq_sqrt zeroUnitIcc.2.1
              nlinarith [zeroUnitIcc.2.2, Real.sqrt_nonneg (↑zeroUnitIcc), hsq]⟩
            : Set.Icc (-1 : ℝ) 1) = zeroIcc := by
        apply Subtype.ext
        norm_num [zeroIcc, zeroUnitIcc]
      rw [hzero]
      exact centeredNorthZonalProfile_zero g
    rw [hsqzero]
    simp [q, qRaw, c, zeroUnitIcc]
  · have hq :
        q u = sqCenteredNorthZonalProfile g u / u.1 := by
      simp [q, qRaw, hu0, sqCenteredNorthZonalProfileRaw_eq g u.2]
    rw [hq]
    field_simp [hu0]

theorem mem_continuousSphereQuadraticSubmodule_of_even_mem_continuousHarmonicSphereDegreeSubmodule
    {n : ℕ} {g : C(spherePoint3, ℝ)}
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hgz : IsNorthZonal g)
    (hnEven : Even n) :
    g ∈ continuousSphereQuadraticSubmodule := by
  rcases exists_sqCenteredNorthZonalProfile_quotient_of_even_mem_continuousHarmonicSphereDegreeSubmodule
    hg hgz hnEven with ⟨q, hq⟩
  exact
    mem_continuousSphereQuadraticSubmodule_of_isNorthZonal_pointConstraint_sqquotient_factor
      hgpc hgz q hq

theorem exists_quadraticMap_of_even_mem_continuousHarmonicSphereDegreeSubmodule
    {n : ℕ} {g : C(spherePoint3, ℝ)}
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hgz : IsNorthZonal g)
    (hnEven : Even n) :
    ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ,
      ∀ x : spherePoint3, g x = Q x.1 := by
  have hmem :
      g ∈ continuousSphereQuadraticSubmodule :=
    mem_continuousSphereQuadraticSubmodule_of_even_mem_continuousHarmonicSphereDegreeSubmodule
      hg hgpc hgz hnEven
  exact hmem

theorem eq_zero_or_mem_continuousSphereQuadraticSubmodule_of_mem_continuousHarmonicSphereDegreeSubmodule
    {n : ℕ} {g : C(spherePoint3, ℝ)}
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hgz : IsNorthZonal g) :
    g = 0 ∨ g ∈ continuousSphereQuadraticSubmodule := by
  by_cases hnEven : Even n
  · right
    exact mem_continuousSphereQuadraticSubmodule_of_even_mem_continuousHarmonicSphereDegreeSubmodule
      hg hgpc hgz hnEven
  · left
    exact
      eq_zero_of_odd_of_mem_continuousHarmonicSphereDegreeSubmodule_of_northZonal_pointConstraint
        (Nat.not_even_iff_odd.mp hnEven) hg hgpc hgz
