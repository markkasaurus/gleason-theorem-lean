import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientEndpoint
import Gleason.Harmonic.Zonal.NorthZonalParity
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Topology
open scoped Topology

def halfRadius : ℝ := (1 / 2 : ℝ)

def halfIcc : Set ℝ := Set.Icc (-halfRadius) halfRadius

lemma zero_mem_halfIcc : (0 : ℝ) ∈ halfIcc := by
  simp [halfIcc, halfRadius]

lemma halfIcc_mem_nhds_zero : halfIcc ∈ 𝓝 (0 : ℝ) := by
  simpa [halfIcc, halfRadius] using
    (Icc_mem_nhds (show (-(1 / 2 : ℝ)) < 0 by norm_num)
      (show (0 : ℝ) < (1 / 2 : ℝ) by norm_num))

lemma mem_Icc_of_mem_halfIcc {z : ℝ} (hz : z ∈ halfIcc) :
    z ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases hz with ⟨hzl, hzu⟩
  have hzl' : (-(1 / 2 : ℝ)) ≤ z := by simpa [halfRadius] using hzl
  have hzu' : z ≤ (1 / 2 : ℝ) := by simpa [halfRadius] using hzu
  constructor <;> linarith

lemma sq_le_quarter_of_mem_halfIcc {z : ℝ} (hz : z ∈ halfIcc) : z ^ 2 ≤ (1 / 4 : ℝ) := by
  rcases hz with ⟨hzl, hzu⟩
  have hzabs : |z| ≤ (1 / 2 : ℝ) := by
    rw [abs_le]
    constructor
    · have : -(1 / 2 : ℝ) ≤ z := by simpa [halfRadius] using hzl
      linarith
    · simpa [halfRadius] using hzu
  have hsq : z ^ 2 = |z| ^ 2 := by rw [sq_abs]
  rw [hsq]
  have hzsq : |z| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [abs_nonneg z, hzabs]
  nlinarith

lemma one_sub_sq_ne_zero_of_mem_halfIcc {z : ℝ} (hz : z ∈ halfIcc) : 1 - z ^ 2 ≠ 0 := by
  have hzsq : z ^ 2 ≤ (1 / 4 : ℝ) := sq_le_quarter_of_mem_halfIcc hz
  nlinarith

def ambientNorthSection (z : ℝ) : WithLp 2 (ℂ × ℝ) :=
  WithLp.toLp 2 ((((Real.sqrt (1 - z ^ 2) : ℝ) : ℂ)), z)

def ambientNorthProfile (f : WithLp 2 (ℂ × ℝ) → ℝ) (z : ℝ) : ℝ :=
  f (ambientNorthSection z)

def ambientCenteredNorthProfile (f : WithLp 2 (ℂ × ℝ) → ℝ) (z : ℝ) : ℝ :=
  ambientNorthProfile f z - ambientNorthProfile f 0

@[simp] lemma ambientNorthSection_eq_northSection (z : Set.Icc (-1 : ℝ) 1) :
    ambientNorthSection z.1 = northSection z := by
  rfl

lemma ambientNorthSection_contDiffOn :
    ContDiffOn ℝ 2 ambientNorthSection halfIcc := by
  unfold ambientNorthSection
  have hsqrt :
      ContDiffOn ℝ 2 (fun z : ℝ => Real.sqrt (1 - z ^ 2)) halfIcc := by
    apply ContDiffOn.sqrt
    · fun_prop
    · intro z hz
      exact one_sub_sq_ne_zero_of_mem_halfIcc hz
  have hfst :
      ContDiffOn ℝ 2 (fun z : ℝ => (((Real.sqrt (1 - z ^ 2) : ℝ) : ℂ))) halfIcc := by
    simpa using Complex.ofRealCLM.contDiff.comp_contDiffOn hsqrt
  have hsnd : ContDiffOn ℝ 2 (fun z : ℝ => z) halfIcc := by
    simpa using (contDiff_id.contDiffOn : ContDiffOn ℝ 2 (fun z : ℝ => z) halfIcc)
  exact WithLp.contDiff_toLp.comp_contDiffOn (hfst.prodMk hsnd)

lemma ambientNorthProfile_contDiffOn
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ}
    (hf : HarmonicHomogeneousDegree n f) :
    ContDiffOn ℝ 2 (ambientNorthProfile f) halfIcc := by
  unfold ambientNorthProfile
  exact (contDiff_two_of_harmonicHomogeneousDegree hf).comp_contDiffOn
    ambientNorthSection_contDiffOn

lemma ambientCenteredNorthProfile_contDiffOn
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ}
    (hf : HarmonicHomogeneousDegree n f) :
    ContDiffOn ℝ 2 (ambientCenteredNorthProfile f) halfIcc := by
  unfold ambientCenteredNorthProfile
  exact (ambientNorthProfile_contDiffOn hf).sub contDiffOn_const

lemma ambientCenteredNorthProfile_eq_centeredNorthZonalProfile
    {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hgz : IsNorthZonal g)
    (hfg : sphereRestrictionLinear f = g)
    (z : Set.Icc (-1 : ℝ) 1) :
    ambientCenteredNorthProfile f z.1 = centeredNorthZonalProfile g z := by
  unfold ambientCenteredNorthProfile ambientNorthProfile centeredNorthZonalProfile northZonalProfile
  rw [ambientNorthSection_eq_northSection]
  rw [show ambientNorthSection (0 : ℝ) = (sphereE1 : spherePoint3).1 by
    apply (WithLp.equiv 2 (ℂ × ℝ)).injective
    simp [ambientNorthSection, sphereE1]]
  have hfg' : ∀ x : spherePoint3, f x.1 = g x := by
    intro x
    exact congrFun hfg x
  have hzero : northSection zeroIcc = sphereE1 := by
    apply Subtype.ext
    apply (WithLp.equiv 2 (ℂ × ℝ)).injective
    simp [northSection, zeroIcc, sphereE1]
  have hsphere : g sphereE2 = g sphereE1 := by
    have hrot := congrArg (fun h : C(spherePoint3, ℝ) => h sphereE1) (hgz (Real.pi / 2))
    simpa [spherePrecomp_apply, sphereMap, northRotation_apply, sphereE1, sphereE2] using hrot
  calc
    f ↑(northSection z) - f ↑sphereE1
      = g (northSection z) - g sphereE1 := by rw [hfg' (northSection z), hfg' sphereE1]
    _ = g (northSection z) - g (northSection zeroIcc) := by rw [hzero, ← hsphere]

lemma ambientCenteredNorthProfile_neg_eq_of_rep
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree n f)
    (hfg : sphereRestrictionLinear f = g)
    (hgz : IsNorthZonal g)
    (hnEven : Even n)
    {z : ℝ} (hz : z ∈ halfIcc) :
    ambientCenteredNorthProfile f (-z) =
      ambientCenteredNorthProfile f z := by
  have hzIcc : (z : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := mem_Icc_of_mem_halfIcc hz
  have hnegIcc : (-z : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hzIcc.1, hzIcc.2]
  let zz : Set.Icc (-1 : ℝ) 1 := ⟨z, hzIcc⟩
  have hg :
      g ∈ continuousHarmonicSphereDegreeSubmodule n := by
    change (g : spherePoint3 → ℝ) ∈ harmonicSphereDegreeSubmodule n
    exact ⟨f, hf, by simpa using hfg⟩
  have hpar :=
    northZonalProfile_parity_of_mem_continuousHarmonicSphereDegreeSubmodule hg hgz zz
  have hpow : (-1 : ℝ) ^ n = 1 := by
    rcases hnEven with ⟨k, rfl⟩
    simp
  have hprof : northZonalProfile g (negIcc zz) = northZonalProfile g zz := by
    simpa [hpow] using hpar
  have hcent :
      centeredNorthZonalProfile g (negIcc zz) = centeredNorthZonalProfile g zz := by
    unfold centeredNorthZonalProfile
    rw [hprof]
  have hnegEq : negIcc zz = ⟨-z, hnegIcc⟩ := by
    ext
    simp [zz, negIcc]
  have hleft :
      ambientCenteredNorthProfile f (-z) =
        centeredNorthZonalProfile g ⟨-z, hnegIcc⟩ := by
    simpa using ambientCenteredNorthProfile_eq_centeredNorthZonalProfile hgz hfg ⟨-z, hnegIcc⟩
  have hright :
      ambientCenteredNorthProfile f z =
        centeredNorthZonalProfile g zz := by
    simpa using ambientCenteredNorthProfile_eq_centeredNorthZonalProfile hgz hfg zz
  rw [hleft, hright]
  simpa [hnegEq] using hcent

lemma ambientCenteredNorthProfile_contDiffAt_zero
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ}
    (hf : HarmonicHomogeneousDegree n f) :
    ContDiffAt ℝ 2 (ambientCenteredNorthProfile f) 0 := by
  exact (contDiffWithinAt_iff_contDiffAt halfIcc_mem_nhds_zero).1
    (ambientCenteredNorthProfile_contDiffOn hf 0 zero_mem_halfIcc)

lemma ambientCenteredNorthProfile_hasDerivAt_zero
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ}
    (hf : HarmonicHomogeneousDegree n f) :
    HasDerivAt (ambientCenteredNorthProfile f)
      (deriv (ambientCenteredNorthProfile f) 0) 0 := by
  exact
    (ambientCenteredNorthProfile_contDiffAt_zero hf).differentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2) |>.hasDerivAt

lemma ambientCenteredNorthProfile_deriv_zero_of_rep
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree n f)
    (hfg : sphereRestrictionLinear f = g)
    (hgz : IsNorthZonal g)
    (hnEven : Even n) :
    deriv (ambientCenteredNorthProfile f) 0 = 0 := by
  have hnegDeriv :
      HasDerivAt (fun z : ℝ => ambientCenteredNorthProfile f (-z))
        (-(deriv (ambientCenteredNorthProfile f) 0)) 0 := by
    have hbase :
        HasDerivAt (ambientCenteredNorthProfile f)
          (deriv (ambientCenteredNorthProfile f) 0) ((0 : ℝ) - 0) := by
      simpa using ambientCenteredNorthProfile_hasDerivAt_zero hf
    simpa using
      HasDerivAt.comp_const_sub (a := (0 : ℝ)) (x := (0 : ℝ))
        hbase
  have hEvenEv :
      (fun z : ℝ => ambientCenteredNorthProfile f (-z)) =ᶠ[𝓝 0]
        ambientCenteredNorthProfile f := by
    filter_upwards [halfIcc_mem_nhds_zero] with z hz
    exact ambientCenteredNorthProfile_neg_eq_of_rep hf hfg hgz hnEven hz
  have hEq :
      deriv (fun z : ℝ => ambientCenteredNorthProfile f (-z)) 0 =
        deriv (ambientCenteredNorthProfile f) 0 :=
    Filter.EventuallyEq.deriv_eq hEvenEv
  rw [hnegDeriv.deriv] at hEq
  linarith

lemma uniqueDiffOn_halfIcc : UniqueDiffOn ℝ halfIcc := by
  simpa [halfIcc, halfRadius] using
    (uniqueDiffOn_Icc (show (-(1 / 2 : ℝ)) < (1 / 2 : ℝ) by norm_num))

lemma ambientCenteredNorthProfile_iteratedDerivWithin_two_eq
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ}
    (hf : HarmonicHomogeneousDegree n f) :
    iteratedDerivWithin 2 (ambientCenteredNorthProfile f) halfIcc 0 =
      iteratedDeriv 2 (ambientCenteredNorthProfile f) 0 := by
  exact iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_halfIcc
    (ambientCenteredNorthProfile_contDiffAt_zero hf) zero_mem_halfIcc

lemma ambientCenteredNorthProfile_taylor_two
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree n f)
    (hfg : sphereRestrictionLinear f = g)
    (hgz : IsNorthZonal g)
    (hnEven : Even n)
    (x : ℝ) :
    taylorWithinEval (ambientCenteredNorthProfile f) 2 halfIcc 0 x =
      (((2 : ℝ)⁻¹ * x ^ 2) : ℝ) * iteratedDeriv 2 (ambientCenteredNorthProfile f) 0 := by
  rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
  rw [iteratedDerivWithin_one]
  rw [derivWithin_of_mem_nhds halfIcc_mem_nhds_zero]
  rw [ambientCenteredNorthProfile_deriv_zero_of_rep hf hfg hgz hnEven]
  rw [ambientCenteredNorthProfile_iteratedDerivWithin_two_eq hf]
  simp [ambientCenteredNorthProfile]
  ring_nf
  simp
