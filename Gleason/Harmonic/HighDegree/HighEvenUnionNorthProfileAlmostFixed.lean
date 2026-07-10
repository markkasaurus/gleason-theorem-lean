import Gleason.Harmonic.HighDegree.HighEvenUnionClosedPole
import Gleason.Harmonic.HighDegree.EvenBoundedQ02
import Gleason.Harmonic.PoleAverage.PoleAverageProfilePoly
import Gleason.Harmonic.Zonal.NorthZonalSquaredFactorBridge

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

abbrev northIcc := Set.Icc (-1 : ℝ) 1

def northZonalContinuousMap (f : C(spherePoint3, ℝ)) : C(northIcc, ℝ) :=
  ⟨northZonalProfile f, continuous_northZonalProfile f⟩

@[simp] theorem northZonalContinuousMap_apply
    (f : C(spherePoint3, ℝ)) (z : northIcc) :
    northZonalContinuousMap f z = northZonalProfile f z := by
  rfl

theorem norm_northZonalContinuousMap_sub_le
    (f g : C(spherePoint3, ℝ)) :
    ‖northZonalContinuousMap f - northZonalContinuousMap g‖ ≤ ‖f - g‖ := by
  haveI : Nonempty northIcc := ⟨zeroIcc⟩
  refine (ContinuousMap.norm_le_of_nonempty
    (f := northZonalContinuousMap f - northZonalContinuousMap g)
    (M := ‖f - g‖)).2 ?_
  intro z
  rw [ContinuousMap.sub_apply, northZonalContinuousMap_apply, northZonalContinuousMap_apply]
  calc
    ‖northZonalProfile f z - northZonalProfile g z‖
        = ‖(f - g) (northSection z)‖ := by
            simp [northZonalProfile, ContinuousMap.sub_apply]
    _ ≤ ‖f - g‖ := (f - g).norm_coe_le_norm _

theorem norm_northZonalContinuousMap_eq_of_isNorthZonal
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

theorem norm_sub_eq_norm_northZonalContinuousMap_sub_of_isNorthZonal
    {f g : C(spherePoint3, ℝ)}
    (hfz : IsNorthZonal f)
    (hgz : IsNorthZonal g) :
    ‖f - g‖ = ‖northZonalContinuousMap f - northZonalContinuousMap g‖ := by
  have hsubz : IsNorthZonal (f - g) := by
    intro t
    ext x
    simp [hfz t, hgz t]
  calc
    ‖f - g‖ = ‖northZonalContinuousMap (f - g)‖ := by
        rw [norm_northZonalContinuousMap_eq_of_isNorthZonal hsubz]
    _ = ‖northZonalContinuousMap f - northZonalContinuousMap g‖ := by
        rfl

private theorem northZonal_average_diff_le
    {f g : C(spherePoint3, ℝ)} (r : Set.Icc (0 : ℝ) 1) :
    |2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi,
          (northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ -
            northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩))|
      ≤ 2 * ‖northZonalContinuousMap f - northZonalContinuousMap g‖ := by
  let k : C(northIcc, ℝ) := northZonalContinuousMap f - northZonalContinuousMap g
  let path : ℝ → northIcc := fun θ => ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpath : Continuous path := by
    continuity
  have hInt :
      IntervalIntegrable (fun θ : ℝ => k (path θ)) volume 0 (2 * Real.pi) := by
    exact (k.continuous.comp hpath).intervalIntegrable 0 (2 * Real.pi)
  have hInt1 :
      IntervalIntegrable (fun θ : ℝ => ‖k (path θ)‖) volume 0 (2 * Real.pi) := by
    exact ((continuous_norm.comp (k.continuous.comp hpath))).intervalIntegrable 0 (2 * Real.pi)
  have hInt2 :
      IntervalIntegrable (fun _ : ℝ => ‖k‖) volume 0 (2 * Real.pi) := by
    exact (continuous_const : Continuous fun _ : ℝ => ‖k‖).intervalIntegrable 0 (2 * Real.pi)
  calc
    |2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi,
          (northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ -
            northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩))|
      = ‖2 * (((2 * Real.pi)⁻¹ : ℝ) * ∫ θ in 0..2 * Real.pi, k (path θ))‖ := by
          simp [k, path, Real.norm_eq_abs, ContinuousMap.sub_apply, northZonalContinuousMap_apply]
    _ = (2 * (2 * Real.pi)⁻¹) * ‖∫ θ in 0..2 * Real.pi, k (path θ)‖ := by
          rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          rw [abs_of_pos, abs_of_pos]
          · ring_nf
          · positivity
          · positivity
    _ ≤ (2 * (2 * Real.pi)⁻¹) * ∫ θ in 0..2 * Real.pi, ‖k (path θ)‖ := by
          gcongr
          exact intervalIntegral.norm_integral_le_integral_norm hpi.le
    _ ≤ (2 * (2 * Real.pi)⁻¹) * ∫ θ in 0..2 * Real.pi, ‖k‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine intervalIntegral.integral_mono_on hpi.le hInt1 hInt2 ?_
          intro θ hθ
          exact k.norm_coe_le_norm _
    _ = 2 * ‖k‖ := by
          have hpi' : (2 * Real.pi : ℝ) ≠ 0 := by positivity
          rw [intervalIntegral.integral_const]
          field_simp [hpi']
          ring_nf
          simp [k, mul_assoc, mul_left_comm, mul_comm]
    _ = 2 * ‖northZonalContinuousMap f - northZonalContinuousMap g‖ := by
          rfl

set_option maxHeartbeats 800000 in
theorem exists_fixed_northZonal_northProfile_poly_almost_fixed_of_nontrivial_tail
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
        ∃ h : C(spherePoint3, ℝ), ∃ p : ℝ[X],
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ z : northIcc, northZonalProfile h z = p.eval z.1) ∧
          ‖northZonalContinuousMap h - northZonalContinuousMap g‖ < ε ∧
          ∀ r : Set.Icc (0 : ℝ) 1,
            |(northZonalScalarPolynomial p).eval r.1 - (p.eval r.1 + p.eval 0)| < 4 * ε := by
  rcases exists_fixed_northZonal_with_highEvenUnion_approx_of_nontrivial_tail_with_pole_ne_zero hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε with ⟨h, hhHigh, hhz, hdist⟩
  have hhpole : h sphereE3 ≠ 0 := by
    intro hh0
    have hdist' : ‖h - g‖ < ε := by
      simpa using hdist
    have hbound : ‖g sphereE3‖ < ε := by
      calc
        ‖g sphereE3‖ = ‖g sphereE3 - h sphereE3‖ := by simp [hh0]
        _ ≤ ‖g - h‖ := by
            simpa [ContinuousMap.sub_apply, norm_sub_rev] using (g - h).norm_coe_le_norm sphereE3
        _ = ‖h - g‖ := by rw [norm_sub_rev]
        _ < ε := hdist'
    exact (not_lt_of_ge (le_of_lt hεpole)) hbound
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
    ⟨q, hqEval, hqEven⟩
  let p : ℝ[X] := northMeridianPolynomial q
  have hpEval : ∀ z : northIcc, northZonalProfile h z = p.eval z.1 := by
    intro z
    simpa [p] using northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal hhz hqEval z
  have hprofdist :
      ‖northZonalContinuousMap h - northZonalContinuousMap g‖ < ε := by
    calc
      ‖northZonalContinuousMap h - northZonalContinuousMap g‖
        ≤ ‖h - g‖ := norm_northZonalContinuousMap_sub_le h g
      _ < ε := by simpa [dist_eq_norm] using hdist
  refine ⟨h, p, hhHigh, hhz, hhpole, hpEval, hprofdist, ?_⟩
  intro r
  have hframeEq :
      2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi,
          northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) =
        northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc := by
    have hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
      rw [continuousSphereGreatCirclePointConstraintSubmodule_eq_continuousSphereFrameSubmodule]
      exact hg.2
    exact northZonalProfile_special_equation_of_mem_pointConstraint hgpc hgz r
  have hpAvg :
      (northZonalScalarPolynomial p).eval r.1 =
        2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            northZonalProfile h ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) := by
    calc
      (northZonalScalarPolynomial p).eval r.1
        = 2 * (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi, p.eval (r.1 * Real.cos θ)) := by
              exact (special_average_polynomial_eval p r).symm
      _ = 2 * (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi,
              northZonalProfile h ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) := by
            refine congrArg (fun t : ℝ => 2 * (((2 * Real.pi)⁻¹ : ℝ) * t)) ?_
            apply intervalIntegral.integral_congr_ae
            filter_upwards with θ hθ
            simpa using (hpEval ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩).symm
  have havgDiff :
      |(northZonalScalarPolynomial p).eval r.1 -
          (northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc)| <
        2 * ε := by
    have hIntH :
        IntervalIntegrable
          (fun θ : ℝ => northZonalProfile h ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
          volume 0 (2 * Real.pi) := by
      let path : ℝ → northIcc := fun θ => ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩
      have hpath : Continuous path := by continuity
      simpa [path, northZonalProfile] using
        ((continuous_northZonalProfile h).comp hpath).intervalIntegrable 0 (2 * Real.pi)
    have hIntG :
        IntervalIntegrable
          (fun θ : ℝ => northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
          volume 0 (2 * Real.pi) := by
      let path : ℝ → northIcc := fun θ => ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩
      have hpath : Continuous path := by continuity
      simpa [path, northZonalProfile] using
        ((continuous_northZonalProfile g).comp hpath).intervalIntegrable 0 (2 * Real.pi)
    rw [hpAvg, ← hframeEq]
    have hsub :
        2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            northZonalProfile h ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
        2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
          =
        2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            (northZonalProfile h ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ -
              northZonalProfile g ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)) := by
      rw [intervalIntegral.integral_sub hIntH hIntG]
      ring_nf
    rw [hsub]
    have hle := northZonal_average_diff_le (f := h) (g := g) r
    exact lt_of_le_of_lt hle (by linarith [hprofdist])
  have hvalNonneg :
      |northZonalProfile g (nonnegIccToIcc r) - northZonalProfile h (nonnegIccToIcc r)| <
        ε := by
    have hle :
        |northZonalProfile g (nonnegIccToIcc r) - northZonalProfile h (nonnegIccToIcc r)|
          ≤ ‖northZonalContinuousMap h - northZonalContinuousMap g‖ := by
      simpa [ContinuousMap.sub_apply, northZonalContinuousMap_apply, Real.norm_eq_abs, abs_sub_comm] using
        ((northZonalContinuousMap h - northZonalContinuousMap g).norm_coe_le_norm (nonnegIccToIcc r))
    exact lt_of_le_of_lt
      hle hprofdist
  have hvalZero :
      |northZonalProfile g zeroIcc - northZonalProfile h zeroIcc| < ε := by
    have hle :
        |northZonalProfile g zeroIcc - northZonalProfile h zeroIcc|
          ≤ ‖northZonalContinuousMap h - northZonalContinuousMap g‖ := by
      simpa [ContinuousMap.sub_apply, northZonalContinuousMap_apply, Real.norm_eq_abs, abs_sub_comm] using
        ((northZonalContinuousMap h - northZonalContinuousMap g).norm_coe_le_norm zeroIcc)
    exact lt_of_le_of_lt
      hle hprofdist
  have hpolyNonneg :
      |northZonalProfile h (nonnegIccToIcc r) - p.eval r.1| = 0 := by
    rw [hpEval (nonnegIccToIcc r)]
    simp
  have hpolyZero :
      |northZonalProfile h zeroIcc - p.eval 0| = 0 := by
    have hz : (zeroIcc : ℝ) = 0 := by simp [zeroIcc]
    rw [hpEval zeroIcc, hz]
    simp
  have hmain :
      |(northZonalScalarPolynomial p).eval r.1 - (p.eval r.1 + p.eval 0)|
        ≤ |(northZonalScalarPolynomial p).eval r.1 -
            (northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc)| +
          |northZonalProfile g (nonnegIccToIcc r) - p.eval r.1| +
          |northZonalProfile g zeroIcc - p.eval 0| := by
    have htri :
        |(northZonalScalarPolynomial p).eval r.1 - (p.eval r.1 + p.eval 0)|
          ≤ |(northZonalScalarPolynomial p).eval r.1 -
                (northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc)| +
              |(northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc) -
                (p.eval r.1 + p.eval 0)| := by
          exact abs_sub_le _ _ _
    refine htri.trans ?_
    have hsplit :
        |(northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc) -
            (p.eval r.1 + p.eval 0)|
          ≤ |northZonalProfile g (nonnegIccToIcc r) - p.eval r.1| +
              |northZonalProfile g zeroIcc - p.eval 0| := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Real.norm_eq_abs] using
        (norm_add_le
          (northZonalProfile g (nonnegIccToIcc r) - p.eval r.1)
          (northZonalProfile g zeroIcc - p.eval 0))
    linarith
  have hcompNonneg :
      |northZonalProfile g (nonnegIccToIcc r) - p.eval r.1|
        ≤ |northZonalProfile g (nonnegIccToIcc r) - northZonalProfile h (nonnegIccToIcc r)| := by
    rw [hpEval (nonnegIccToIcc r)]
    simp
  have hcompZero :
      |northZonalProfile g zeroIcc - p.eval 0|
        ≤ |northZonalProfile g zeroIcc - northZonalProfile h zeroIcc| := by
    have hz : (zeroIcc : ℝ) = 0 := by simp [zeroIcc]
    rw [← hz, hpEval zeroIcc]
  calc
    |(northZonalScalarPolynomial p).eval r.1 - (p.eval r.1 + p.eval 0)|
      ≤ |(northZonalScalarPolynomial p).eval r.1 -
          (northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc)| +
        |northZonalProfile g (nonnegIccToIcc r) - p.eval r.1| +
        |northZonalProfile g zeroIcc - p.eval 0| := hmain
    _ ≤ |(northZonalScalarPolynomial p).eval r.1 -
          (northZonalProfile g (nonnegIccToIcc r) + northZonalProfile g zeroIcc)| +
        |northZonalProfile g (nonnegIccToIcc r) - northZonalProfile h (nonnegIccToIcc r)| +
        |northZonalProfile g zeroIcc - northZonalProfile h zeroIcc| := by
          gcongr
        _ < (2 * ε) + ε + ε := by
              nlinarith [havgDiff, hvalNonneg, hvalZero]
        _ = 4 * ε := by ring_nf
