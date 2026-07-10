import Gleason.Harmonic.HighDegree.HighEvenUnionSquaredQuotientOnPos
import Gleason.Harmonic.HighDegree.HighEvenUnionNorthZonalLowSquaredFactor
import Gleason.Harmonic.Auxiliary.GlobalLowProjection
import Gleason.Harmonic.HighDegree.HighEvenUnionClosed
import Gleason.Harmonic.Profile.SquaredProfileLowmodeAmbient
import Gleason.Harmonic.HighDegree.HighEvenUnionFixedSquaredProfileLinearApprox
import Gleason.Harmonic.Profile.SquaredProfileScaling
import Gleason.Harmonic.Profile.SquaredProfileScalingPoly
import Gleason.Harmonic.Profile.SquaredQuotientShellPoly

noncomputable section

open Complex InnerProductSpace Topology Filter

theorem abs_sqProfileQuotient_sub_le_div_of_profile_linear
    (r : C(unitIcc, ℝ)) {δ c : ℝ} (hδ : 0 < δ)
    {u : unitIcc} (hu : δ ≤ u.1) :
    |r u / u.1 - c|
      ≤ ‖r -
          (((Polynomial.C c * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ / δ := by
  let p : Polynomial ℝ := Polynomial.C c * (Polynomial.X : Polynomial ℝ)
  have hu0 : u.1 ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le hδ hu)
  have huPos : 0 < u.1 := lt_of_lt_of_le hδ hu
  have hEq :
      r u / u.1 - c =
        ((r - p.toContinuousMapOn unitIcc) u) / u.1 := by
    have hlin :
        (p.toContinuousMapOn unitIcc) u = u.1 * c := by
      change p.eval u.1 = u.1 * c
      calc
        p.eval u.1 = (Polynomial.C c * (Polynomial.X : Polynomial ℝ)).eval u.1 := by rfl
        _ = c * u.1 := by simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        _ = u.1 * c := by ring
    have htmp :
        ((r - p.toContinuousMapOn unitIcc) u) =
          r u - u.1 * c := by
      rw [ContinuousMap.sub_apply, hlin]
    rw [htmp]
    field_simp [hu0]
  rw [hEq, abs_div, abs_of_nonneg huPos.le]
  calc
    |(r - p.toContinuousMapOn unitIcc) u| / u.1
      ≤ ‖r - p.toContinuousMapOn unitIcc‖ / u.1 := by
          gcongr
          simpa [Real.norm_eq_abs] using
            (r - p.toContinuousMapOn unitIcc).norm_coe_le_norm u
    _ ≤ ‖r - p.toContinuousMapOn unitIcc‖ / δ := by
          have hnorm_nonneg :
              0 ≤ ‖r - p.toContinuousMapOn unitIcc‖ := by
            exact norm_nonneg _
          rw [div_eq_mul_inv, div_eq_mul_inv]
          have hinv : (u.1)⁻¹ ≤ δ⁻¹ := by
            simpa [one_div] using one_div_le_one_div_of_le hδ hu
          exact mul_le_mul_of_nonneg_left hinv hnorm_nonneg

theorem abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_sqprofile_linear
    (g : C(spherePoint3, ℝ)) {δ c : ℝ} (hδ : 0 < δ)
    {u : unitIcc} (hu : δ ≤ u.1) :
    |sqCenteredNorthZonalQuotientRaw g u - c|
      ≤ ‖sqCenteredNorthZonalContinuousMap g -
          (((Polynomial.C c * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ / δ := by
  let p : Polynomial ℝ := Polynomial.C c * (Polynomial.X : Polynomial ℝ)
  have hu0 : u.1 ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le hδ hu)
  have huPos : 0 < u.1 := lt_of_lt_of_le hδ hu
  have hEq :
      sqCenteredNorthZonalQuotientRaw g u - c =
        ((sqCenteredNorthZonalContinuousMap g -
            p.toContinuousMapOn unitIcc) u) / u.1 := by
    rw [show sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalProfile g u / u.1 by
          simp [sqCenteredNorthZonalQuotientRaw, hu0]]
    have hlin :
        (p.toContinuousMapOn unitIcc) u = u.1 * c := by
      change p.eval u.1 = u.1 * c
      calc
        p.eval u.1 = (Polynomial.C c * (Polynomial.X : Polynomial ℝ)).eval u.1 := by rfl
        _ = c * u.1 := by simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        _ = u.1 * c := by ring
    have htmp :
        ((sqCenteredNorthZonalContinuousMap g - p.toContinuousMapOn unitIcc) u) =
          sqCenteredNorthZonalProfile g u - u.1 * c := by
      rw [ContinuousMap.sub_apply, sqCenteredNorthZonalContinuousMap, hlin]
      rfl
    rw [htmp]
    field_simp [hu0]
  rw [hEq, abs_div, abs_of_nonneg huPos.le]
  calc
    |(sqCenteredNorthZonalContinuousMap g -
        p.toContinuousMapOn unitIcc) u| / u.1
      ≤ ‖sqCenteredNorthZonalContinuousMap g -
          p.toContinuousMapOn unitIcc‖ / u.1 := by
          gcongr
          simpa [Real.norm_eq_abs] using
            (sqCenteredNorthZonalContinuousMap g - p.toContinuousMapOn unitIcc).norm_coe_le_norm u
    _ ≤ ‖sqCenteredNorthZonalContinuousMap g -
          p.toContinuousMapOn unitIcc‖ / δ := by
          have hnorm_nonneg :
              0 ≤ ‖sqCenteredNorthZonalContinuousMap g -
                  p.toContinuousMapOn unitIcc‖ := by
            exact norm_nonneg _
          rw [div_eq_mul_inv, div_eq_mul_inv]
          have hinv : (u.1)⁻¹ ≤ δ⁻¹ := by
            simpa [one_div] using one_div_le_one_div_of_le hδ hu
          exact mul_le_mul_of_nonneg_left hinv hnorm_nonneg

theorem abs_sqCenteredNorthZonalQuotientRaw_scaled_sub_le_two_mul_of_sqprofileRescale_linear
    (g : C(spherePoint3, ℝ)) (a : unitIcc) (ha : 0 < a.1) {c : ℝ}
    {u : unitIcc} (hu : (1 / 2 : ℝ) ≤ u.1) :
    |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) - c|
      ≤
        2 *
          ‖sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g) -
              (((Polynomial.C c * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ := by
  have hu0 : u.1 ≠ 0 := by
    linarith
  have hscaled :
      (sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g)) u / u.1 =
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) := by
    rw [sqProfileRescale_apply]
    change sqCenteredNorthZonalProfile g (sqScaleMap a u) / a.1 / u.1 =
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)
    rw [sqCenteredNorthZonalProfile_eq_mul_sqCenteredNorthZonalQuotientRaw]
    rw [sqScaleMap_apply]
    ring_nf
    field_simp [hu0, show (a.1 : ℝ) ≠ 0 by exact ne_of_gt ha]
  calc
    |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) - c|
      = |(sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g)) u / u.1 - c| := by
          rw [hscaled]
    _ ≤
        ‖sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g) -
            (((Polynomial.C c * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ /
          (1 / 2 : ℝ) :=
        abs_sqProfileQuotient_sub_le_div_of_profile_linear
          (sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g))
          (δ := (1 / 2 : ℝ)) (c := c) (by norm_num) hu
    _ = 2 *
        ‖sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g) -
            (((Polynomial.C c * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ := by
          ring

theorem exists_fixed_northZonal_sqquotientRaw_shell_uniform_near_coeff_zero_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε : ℝ}, 0 < ε → ε < ‖g sphereE3‖ →
        ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ∀ {a u : unitIcc}, 0 < a.1 → (1 / 2 : ℝ) ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) - q.coeff 0|
              ≤ 2 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
  rcases exists_fixed_northZonal_limit_sqprofile_uniform_near_linear_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hsqLin⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  intro a u ha hu
  have hpoly :
      sqCenteredNorthZonalContinuousMap h = sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) := by
    ext v
    change sqCenteredNorthZonalProfile h v = ((Polynomial.X : Polynomial ℝ) * q).eval v.1
    rw [hq v]
    simp
  have hdistProf :
      dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g) < 2 * ε := by
    calc
      dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g)
        = ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ := by
            simp [dist_eq_norm]
      _ ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
      _ < 2 * ε := by
            gcongr
  have hdistScale :
      dist (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q))
          (sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g))
        < (2 * ε) / a.1 := by
    have hlt :
        dist (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q))
            (sqCenteredNorthZonalContinuousMap g) / a.1
          < (2 * ε) / a.1 := by
      have hlt' : dist (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q))
          (sqCenteredNorthZonalContinuousMap g) < 2 * ε := by
        simpa [hpoly] using hdistProf
      field_simp [show (a.1 : ℝ) ≠ 0 by exact ne_of_gt ha]
      exact hlt'
    have hpolyDist :
        dist (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q))
            (sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g))
          ≤
            dist (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q))
              (sqCenteredNorthZonalContinuousMap g) / a.1 := by
      rw [sqProfilePolynomialMap_X_mul_sqQuotientRescalePolynomial]
      exact dist_sqProfileRescale_le_div a ha
        (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q))
        (sqCenteredNorthZonalContinuousMap g)
    exact lt_of_le_of_lt hpolyDist hlt
  have hlinRescaled :
      ‖sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q) -
          sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q)‖
        ≤ a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
    have hp0 :
        (((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q) : Polynomial ℝ).eval 0 = 0 := by
      simp
    calc
      ‖sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q) -
          sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q)‖
        ≤ sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q) := by
            simpa using
              (norm_polynomial_sub_linear_le_of_sqprofile_almost_fixed
                (((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q) : Polynomial ℝ)
                0 hp0)
      _ ≤ a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) :=
            sqProfileTailAbsSum_X_mul_sqQuotientRescalePolynomial_le a q
  have hrescaledLinear :
      ‖sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g) -
          (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖
        ≤ (2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
    have hlinEq :
        sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q) =
          (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc) := by
      ext v
      simp [sqProfileLinearPart, sqQuotientRescalePolynomial_coeff]
    calc
      ‖sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g) -
          (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖
        ≤ dist (sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g))
            (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q)) +
          dist (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q))
            (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc) := by
              simpa [dist_eq_norm, add_comm, add_left_comm, add_assoc] using
                dist_triangle
                  (sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g))
                  (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q))
                  (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)
      _ ≤ (2 * ε) / a.1 +
          ‖sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q) -
            sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q)‖ := by
              have hfirst :
                  dist (sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g))
                      (sqProfilePolynomialMap
                        ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q))
                    ≤ (2 * ε) / a.1 := by
                simpa [dist_comm] using le_of_lt hdistScale
              have hsecond :
                  dist (sqProfilePolynomialMap
                      ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q))
                      (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) :
                        Polynomial ℝ).toContinuousMapOn unitIcc)
                    ≤ ‖sqProfilePolynomialMap
                        ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q) -
                        sqProfileLinearPart
                          ((Polynomial.X : Polynomial ℝ) * sqQuotientRescalePolynomial a q)‖ := by
                simpa [dist_eq_norm, hlinEq]
              exact add_le_add hfirst hsecond
      _ ≤ (2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
              gcongr
  calc
    |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) - q.coeff 0|
      ≤
        2 *
          ‖sqProfileRescale a ha (sqCenteredNorthZonalContinuousMap g) -
              (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ :=
        abs_sqCenteredNorthZonalQuotientRaw_scaled_sub_le_two_mul_of_sqprofileRescale_linear
          g a ha (c := q.coeff 0) hu
    _ ≤ 2 * (((2 * ε) / a.1) + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
        gcongr

theorem exists_fixed_northZonal_sqquotientRaw_dyadic_step_near_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε : ℝ}, 0 < ε → ε < ‖g sphereE3‖ →
        ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ∀ {a : unitIcc}, 0 < a.1 →
            |sqCenteredNorthZonalQuotientRaw g a -
                sqCenteredNorthZonalQuotientRaw g
                  (sqScaleMap a ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩)|
              ≤ 4 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
  rcases exists_fixed_northZonal_sqquotientRaw_shell_uniform_near_coeff_zero_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hshell⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  intro a ha
  have hone :
      |sqCenteredNorthZonalQuotientRaw g a - q.coeff 0|
        ≤ 2 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
    have honeHalf : (1 / 2 : ℝ) ≤ (oneUnitIcc : unitIcc).1 := by
      change (1 / 2 : ℝ) ≤ (1 : ℝ)
      norm_num
    simpa [sqScaleMap, oneUnitIcc] using hshell (a := a) (u := oneUnitIcc) ha honeHalf
  let uHalf : unitIcc := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hhalf :
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a uHalf) - q.coeff 0|
        ≤ 2 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
    have hhalfHalf : (1 / 2 : ℝ) ≤ uHalf.1 := by
      change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
      exact le_rfl
    exact hshell (a := a) (u := uHalf) ha hhalfHalf
  calc
    |sqCenteredNorthZonalQuotientRaw g a -
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a uHalf)|
      ≤ |sqCenteredNorthZonalQuotientRaw g a - q.coeff 0| +
          |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a uHalf) - q.coeff 0| := by
            have htri :=
              abs_sub_le (sqCenteredNorthZonalQuotientRaw g a) (q.coeff 0)
                (sqCenteredNorthZonalQuotientRaw g (sqScaleMap a uHalf))
            calc
              |sqCenteredNorthZonalQuotientRaw g a -
                  sqCenteredNorthZonalQuotientRaw g (sqScaleMap a uHalf)|
                ≤ |sqCenteredNorthZonalQuotientRaw g a - q.coeff 0| +
                    |q.coeff 0 -
                      sqCenteredNorthZonalQuotientRaw g (sqScaleMap a uHalf)| := by
                        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htri
              _ = |sqCenteredNorthZonalQuotientRaw g a - q.coeff 0| +
                    |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a uHalf) - q.coeff 0| := by
                      congr 1
                      exact abs_sub_comm _ _
    _ ≤
        2 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) +
          2 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
            gcongr
    _ = 4 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
          ring

theorem exists_fixed_northZonal_sqquotientRaw_shell_uniform_near_top_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε : ℝ}, 0 < ε → ε < ‖g sphereE3‖ →
        ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ∀ {a u : unitIcc}, 0 < a.1 → (1 / 2 : ℝ) ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
                sqCenteredNorthZonalQuotientRaw g a|
              ≤ 4 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
  rcases exists_fixed_northZonal_sqquotientRaw_shell_uniform_near_coeff_zero_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hshell⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  intro a u ha hu
  have hone :
      |sqCenteredNorthZonalQuotientRaw g a - q.coeff 0|
        ≤ 2 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
    have honeHalf : (1 / 2 : ℝ) ≤ (oneUnitIcc : unitIcc).1 := by
      change (1 / 2 : ℝ) ≤ (1 : ℝ)
      norm_num
    simpa [sqScaleMap, oneUnitIcc] using hshell (a := a) (u := oneUnitIcc) ha honeHalf
  have huShell :
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) - q.coeff 0|
        ≤ 2 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) :=
    hshell (a := a) (u := u) ha hu
  calc
    |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) - sqCenteredNorthZonalQuotientRaw g a|
      ≤ |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) - q.coeff 0| +
          |sqCenteredNorthZonalQuotientRaw g a - q.coeff 0| := by
            have htri :=
              abs_sub_le (sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) (q.coeff 0)
                (sqCenteredNorthZonalQuotientRaw g a)
            calc
              |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) - sqCenteredNorthZonalQuotientRaw g a|
                ≤ |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) - q.coeff 0| +
                    |q.coeff 0 - sqCenteredNorthZonalQuotientRaw g a| := by
                      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htri
              _ = |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) - q.coeff 0| +
                    |sqCenteredNorthZonalQuotientRaw g a - q.coeff 0| := by
                      congr 1
                      exact abs_sub_comm _ _
    _ ≤
        2 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) +
          2 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
            gcongr
    _ = 4 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
          ring

theorem exists_fixed_northZonal_sqquotientRaw_shell_pair_uniform_near_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε : ℝ}, 0 < ε → ε < ‖g sphereE3‖ →
        ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ∀ {a u v : unitIcc}, 0 < a.1 → (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)|
              ≤ 8 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
  rcases exists_fixed_northZonal_sqquotientRaw_shell_uniform_near_top_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hshell⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  intro a u v ha hu hv
  have huTop :
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
          sqCenteredNorthZonalQuotientRaw g a|
        ≤ 4 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) :=
    hshell (a := a) (u := u) ha hu
  have hvTop :
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v) -
          sqCenteredNorthZonalQuotientRaw g a|
        ≤ 4 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) :=
    hshell (a := a) (u := v) ha hv
  calc
    |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)|
      ≤ |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
            sqCenteredNorthZonalQuotientRaw g a| +
          |sqCenteredNorthZonalQuotientRaw g a -
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)| := by
            exact abs_sub_le _ _ _
    _ =
        |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
            sqCenteredNorthZonalQuotientRaw g a| +
          |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v) -
            sqCenteredNorthZonalQuotientRaw g a| := by
            congr 1
            exact abs_sub_comm _ _
    _ ≤
        4 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) +
          4 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
            gcongr
    _ = 8 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
          ring

def dyadicUnitIcc (n : ℕ) : unitIcc := ⟨(1 / 2 : ℝ) ^ n, by
  constructor
  · positivity
  · exact pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)⟩

@[simp] theorem dyadicUnitIcc_val (n : ℕ) :
    (dyadicUnitIcc n : ℝ) = (1 / 2 : ℝ) ^ n := by
  rfl

theorem exists_dyadic_inverse_term_gt
    {ε C : ℝ}
    (hε : 0 < ε)
    (N : ℕ) :
    ∃ n : ℕ, n ≥ N ∧ C < 8 * ε / (dyadicUnitIcc n : ℝ) := by
  by_cases hC : C < 0
  · refine ⟨N, le_rfl, ?_⟩
    have hpos : 0 < 8 * ε / (dyadicUnitIcc N : ℝ) := by
      have hden : 0 < (dyadicUnitIcc N : ℝ) := by
        simp [dyadicUnitIcc_val, pow_pos]
      positivity
    linarith
  · have hCnonneg : 0 ≤ C := le_of_not_gt hC
    obtain ⟨m, hm⟩ := exists_nat_gt (C / (8 * ε))
    let n : ℕ := max N m
    have hmn : m ≤ n := le_max_right _ _
    have hpowm : (m : ℝ) < (2 : ℝ) ^ m := by
      exact_mod_cast (Nat.lt_two_pow_self (n := m))
    have hpowmn : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ n := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hmn
    have hratio : C / (8 * ε) < (2 : ℝ) ^ n := by
      exact lt_of_lt_of_le hm (le_trans hpowm.le hpowmn)
    have h8ε : 0 < 8 * ε := by positivity
    have hmul : C < (2 : ℝ) ^ n * (8 * ε) := by
      exact (div_lt_iff₀ h8ε).mp hratio
    refine ⟨n, le_max_left _ _, ?_⟩
    calc
      C < (2 : ℝ) ^ n * (8 * ε) := hmul
      _ = 8 * ε / (dyadicUnitIcc n : ℝ) := by
            simp [dyadicUnitIcc_val, div_eq_mul_inv, inv_pow]
            ring

theorem not_eventually_le_dyadic_inverse_term
    {ε C : ℝ}
    (hε : 0 < ε) :
    ¬ ∃ N : ℕ, ∀ n ≥ N, 8 * ε / (dyadicUnitIcc n : ℝ) ≤ C := by
  intro hbound
  rcases hbound with ⟨N, hN⟩
  rcases exists_dyadic_inverse_term_gt hε N with ⟨n, hnN, hgt⟩
  exact not_lt_of_ge (hN n hnN) hgt

theorem not_eventually_le_dyadic_inverse_term_add_nonneg
    {ε C : ℝ}
    (hε : 0 < ε)
    {r : ℕ → ℝ}
    (hr : ∀ n : ℕ, 0 ≤ r n) :
    ¬ ∃ N : ℕ, ∀ n ≥ N, 8 * ε / (dyadicUnitIcc n : ℝ) + r n ≤ C := by
  intro hbound
  rcases hbound with ⟨N, hN⟩
  exact
    (not_eventually_le_dyadic_inverse_term (ε := ε) (C := C) hε) <|
      ⟨N, by
        intro n hn
        have hle := hN n hn
        linarith [hr n]⟩

theorem not_eventually_le_dyadic_shell_pair_uniform_near_v2_template
    {ε C : ℝ}
    (hε : 0 < ε)
    {N : ℕ}
    {q : Polynomial ℝ}
    {m : ℕ → ℕ} :
    ¬ ∃ M : ℕ, ∀ n ≥ M,
      8 * ε / (dyadicUnitIcc n : ℝ) +
          2 *
            ((Finset.sum (Finset.range (m n)) fun _ => (1 : ℝ)) *
                (degreeLTSqMulNormConst N * (6 * ε)) +
              (3 / 4 : ℝ) ^ (m n) * ((dyadicUnitIcc n : ℝ) * polyTailAbsSum q))
        ≤ C := by
  apply not_eventually_le_dyadic_inverse_term_add_nonneg (ε := ε) (C := C)
    (r := fun n =>
      2 *
        ((Finset.sum (Finset.range (m n)) fun _ => (1 : ℝ)) *
            (degreeLTSqMulNormConst N * (6 * ε)) +
          (3 / 4 : ℝ) ^ (m n) * ((dyadicUnitIcc n : ℝ) * polyTailAbsSum q)))
    hε
  intro n
  have hconst_nonneg : 0 ≤ degreeLTSqMulNormConst N := by
    unfold degreeLTSqMulNormConst
    positivity
  have htail_nonneg : 0 ≤ polyTailAbsSum q := by
    unfold polyTailAbsSum
    positivity
  have hterm1 :
      0 ≤
        (Finset.sum (Finset.range (m n)) fun _ => (1 : ℝ)) *
          (degreeLTSqMulNormConst N * (6 * ε)) := by
    positivity
  have hterm2 :
      0 ≤ (3 / 4 : ℝ) ^ (m n) * ((dyadicUnitIcc n : ℝ) * polyTailAbsSum q) := by
    have hpow_nonneg : 0 ≤ (3 / 4 : ℝ) ^ (m n) := by positivity
    have hdy_nonneg : 0 ≤ (dyadicUnitIcc n : ℝ) := by
      simp [dyadicUnitIcc_val]
    have hprod_nonneg : 0 ≤ (dyadicUnitIcc n : ℝ) * polyTailAbsSum q := by
      positivity
    exact mul_nonneg hpow_nonneg hprod_nonneg
  have hinner :
      0 ≤
        (Finset.sum (Finset.range (m n)) fun _ => (1 : ℝ)) *
            (degreeLTSqMulNormConst N * (6 * ε)) +
          (3 / 4 : ℝ) ^ (m n) * ((dyadicUnitIcc n : ℝ) * polyTailAbsSum q) := by
    linarith
  positivity

theorem not_eventually_lt_dyadic_shell_pair_uniform_near_v2_template
    {ε C : ℝ}
    (hε : 0 < ε)
    {N : ℕ}
    {q : Polynomial ℝ}
    {m : ℕ → ℕ} :
    ¬ ∃ M : ℕ, ∀ n ≥ M,
      8 * ε / (dyadicUnitIcc n : ℝ) +
          2 *
            ((Finset.sum (Finset.range (m n)) fun _ => (1 : ℝ)) *
                (degreeLTSqMulNormConst N * (6 * ε)) +
              (3 / 4 : ℝ) ^ (m n) * ((dyadicUnitIcc n : ℝ) * polyTailAbsSum q))
        < C := by
  intro hlt
  apply not_eventually_le_dyadic_shell_pair_uniform_near_v2_template (ε := ε) (C := C) hε
    (N := N) (q := q) (m := m)
  rcases hlt with ⟨M, hM⟩
  exact ⟨M, fun n hn => (hM n hn).le⟩

theorem not_summable_const_add_nonneg
    {c : ℝ} {r : ℕ → ℝ}
    (hc : 0 < c)
    (hr : ∀ n : ℕ, 0 ≤ r n) :
    ¬ Summable (fun n : ℕ => c + r n) := by
  intro hs
  have hconst :
      Summable (fun _ : ℕ => c) := by
    refine Summable.of_nonneg_of_le (fun _ => le_of_lt hc) ?_ hs
    intro n
    linarith [hr n]
  have hc0 : c = 0 := by
    simpa [summable_const_iff] using hconst
  linarith

theorem not_summable_package_explicit_step_template
    {ε : ℝ}
    (hε : 0 < ε)
    {M : ℕ → ℕ} :
    ¬ Summable
      (fun n : ℕ =>
        2 * ε +
          degreeLTPolyTailBoundConst (M n) * degreeLTSqMulNormConst (M n) *
            (dyadicUnitIcc n : ℝ) * ε) := by
  apply not_summable_const_add_nonneg (c := 2 * ε)
  · positivity
  · intro n
    have hpoly_nonneg : 0 ≤ degreeLTPolyTailBoundConst (M n) := by
      unfold degreeLTPolyTailBoundConst
      positivity
    have hsq_nonneg : 0 ≤ degreeLTSqMulNormConst (M n) := by
      unfold degreeLTSqMulNormConst
      positivity
    have hdy_nonneg : 0 ≤ (dyadicUnitIcc n : ℝ) := by
      simp [dyadicUnitIcc_val]
    positivity

theorem not_exists_summable_majorant_package_explicit_step_template
    {ε : ℝ}
    (hε : 0 < ε)
    {M : ℕ → ℕ} :
    ¬ ∃ b : ℕ → ℝ,
      Summable b ∧
      (∀ n : ℕ, 0 ≤ b n) ∧
      ∀ n : ℕ,
        2 * ε +
          degreeLTPolyTailBoundConst (M n) * degreeLTSqMulNormConst (M n) *
            (dyadicUnitIcc n : ℝ) * ε ≤ b n := by
  intro hmajor
  rcases hmajor with ⟨b, hbSumm, hbNonneg, hbLe⟩
  have hsumm :
      Summable
        (fun n : ℕ =>
          2 * ε +
            degreeLTPolyTailBoundConst (M n) * degreeLTSqMulNormConst (M n) *
              (dyadicUnitIcc n : ℝ) * ε) := by
    refine Summable.of_nonneg_of_le ?_ hbLe hbSumm
    intro n
    have hpoly_nonneg : 0 ≤ degreeLTPolyTailBoundConst (M n) := by
      unfold degreeLTPolyTailBoundConst
      positivity
    have hsq_nonneg : 0 ≤ degreeLTSqMulNormConst (M n) := by
      unfold degreeLTSqMulNormConst
      positivity
    have hdy_nonneg : 0 ≤ (dyadicUnitIcc n : ℝ) := by
      simp [dyadicUnitIcc_val]
    positivity
  exact (not_summable_package_explicit_step_template (ε := ε) hε (M := M)) hsumm

theorem not_exists_summable_majorant_package_explicit_step_template_tail
    {ε : ℝ}
    (hε : 0 < ε)
    {N : ℕ}
    {M : ℕ → ℕ} :
    ¬ ∃ b : ℕ → ℝ,
      Summable b ∧
      (∀ n : ℕ, 0 ≤ b n) ∧
      ∀ n : ℕ,
        2 * ε +
          degreeLTPolyTailBoundConst (M n) * degreeLTSqMulNormConst (M n) *
            (dyadicUnitIcc (n + N) : ℝ) * ε ≤ b n := by
  intro hmajor
  rcases hmajor with ⟨b, hbSumm, hbNonneg, hbLe⟩
  have hsumm :
      Summable
        (fun n : ℕ =>
          2 * ε +
            degreeLTPolyTailBoundConst (M n) * degreeLTSqMulNormConst (M n) *
              (dyadicUnitIcc (n + N) : ℝ) * ε) := by
    refine Summable.of_nonneg_of_le ?_ hbLe hbSumm
    intro n
    have hpoly_nonneg : 0 ≤ degreeLTPolyTailBoundConst (M n) := by
      unfold degreeLTPolyTailBoundConst
      positivity
    have hsq_nonneg : 0 ≤ degreeLTSqMulNormConst (M n) := by
      unfold degreeLTSqMulNormConst
      positivity
    have hdy_nonneg : 0 ≤ (dyadicUnitIcc (n + N) : ℝ) := by
      simp [dyadicUnitIcc_val]
    positivity
  exact
    (not_summable_const_add_nonneg (c := 2 * ε) (r := fun n : ℕ =>
      degreeLTPolyTailBoundConst (M n) * degreeLTSqMulNormConst (M n) *
        (dyadicUnitIcc (n + N) : ℝ) * ε) (by positivity) (by
          intro n
          have hpoly_nonneg : 0 ≤ degreeLTPolyTailBoundConst (M n) := by
            unfold degreeLTPolyTailBoundConst
            positivity
          have hsq_nonneg : 0 ≤ degreeLTSqMulNormConst (M n) := by
            unfold degreeLTSqMulNormConst
            positivity
          have hdy_nonneg : 0 ≤ (dyadicUnitIcc (n + N) : ℝ) := by
            simp [dyadicUnitIcc_val]
          positivity)) hsumm

theorem not_exists_summable_majorant_eventual_package_explicit_step_template
    {ε : ℝ}
    (hε : 0 < ε)
    {N : ℕ}
    {M : ℕ → ℕ} :
    ¬ ∃ b : ℕ → ℝ,
      Summable b ∧
      (∀ n : ℕ, 0 ≤ b n) ∧
      ∀ n ≥ N,
        2 * ε +
          degreeLTPolyTailBoundConst (M n) * degreeLTSqMulNormConst (M n) *
            (dyadicUnitIcc n : ℝ) * ε ≤ b n := by
  intro hmajor
  rcases hmajor with ⟨b, hbSumm, hbNonneg, hbLe⟩
  let bTail : ℕ → ℝ := fun n => b (n + N)
  let MTail : ℕ → ℕ := fun n => M (n + N)
  have hbTailSumm : Summable bTail := by
    dsimp [bTail]
    exact (summable_nat_add_iff N).mpr hbSumm
  have hbTailNonneg : ∀ n : ℕ, 0 ≤ bTail n := by
    intro n
    exact hbNonneg (n + N)
  have hbTailLe :
      ∀ n : ℕ,
        2 * ε +
          degreeLTPolyTailBoundConst (MTail n) * degreeLTSqMulNormConst (MTail n) *
            (dyadicUnitIcc (n + N) : ℝ) * ε ≤ bTail n := by
    intro n
    simpa [bTail, MTail, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      hbLe (n + N) (Nat.le_add_left N n)
  exact
    (not_exists_summable_majorant_package_explicit_step_template_tail
      (ε := ε) hε (N := N) (M := MTail))
      ⟨bTail, hbTailSumm, hbTailNonneg, hbTailLe⟩

theorem not_exists_eventual_next_anchor_explicit_step_bound_with_summable_majorant
    {g : C(spherePoint3, ℝ)}
    {ε : ℝ}
    (hε : 0 < ε)
    {N : ℕ}
    {M : ℕ → ℕ} :
    ¬ ∃ b : ℕ → ℝ,
      Summable b ∧
      (∀ n : ℕ, 0 ≤ b n) ∧
      ∀ n ≥ N,
        let B : ℝ :=
          2 * ε +
            degreeLTPolyTailBoundConst (M n) * degreeLTSqMulNormConst (M n) *
              (dyadicUnitIcc n : ℝ) * ε
        dist (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
            (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2))) ≤ B ∧
          B ≤ b n := by
  intro hmajor
  rcases hmajor with ⟨b, hbSumm, hbNonneg, hb⟩
  exact
    (not_exists_summable_majorant_eventual_package_explicit_step_template
      (ε := ε) hε (N := N) (M := M))
      ⟨b, hbSumm, hbNonneg, by
        intro n hn
        exact (hb n hn).2⟩

@[simp] theorem sqScaleMap_halfUnitIcc
    (a : unitIcc) :
    sqScaleMap a halfUnitIcc = ⟨a.1 / 2, by
      constructor
      · exact div_nonneg a.2.1 (by positivity)
      · have ha1 : a.1 ≤ 1 := a.2.2
        nlinarith⟩ := by
  apply Subtype.ext
  simp [sqScaleMap, halfUnitIcc]
  ring

@[simp] theorem sqScaleMap_dyadicUnitIcc_halfUnitIcc
    (n : ℕ) :
    sqScaleMap (dyadicUnitIcc n) halfUnitIcc = dyadicUnitIcc (n + 1) := by
  apply Subtype.ext
  simp [sqScaleMap, dyadicUnitIcc_val, halfUnitIcc, pow_succ]

lemma exists_nat_dyadic_shell_mem_from
    {u : unitIcc} (huPos : 0 < u.1) {N : ℕ}
    (huLt : u.1 < (dyadicUnitIcc (N + 1) : unitIcc).1) :
    ∃ m : ℕ, N ≤ m ∧
      ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧ sqScaleMap (dyadicUnitIcc m) v = u := by
  have hex : ∃ k : ℕ, ((1 / 2 : ℝ) ^ k) < u.1 := by
    simpa using exists_pow_lt_of_lt_one huPos (by norm_num : (1 / 2 : ℝ) < 1)
  let k : ℕ := Nat.find hex
  have hk_lt : ((1 / 2 : ℝ) ^ k) < u.1 := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hk0
    have hk1 : (1 : ℝ) < u.1 := by
      simpa [k, hk0] using hk_lt
    linarith [u.2.2]
  let m : ℕ := k - 1
  have hmk : m + 1 = k := by
    dsimp [m]
    exact Nat.succ_pred_eq_of_pos (Nat.pos_iff_ne_zero.mpr hk0)
  have hm_lt : ((1 / 2 : ℝ) ^ (m + 1)) < u.1 := by
    simpa [hmk] using hk_lt
  have hu_le_m : u.1 ≤ (1 / 2 : ℝ) ^ m := by
    have hnot : ¬ ((1 / 2 : ℝ) ^ m < u.1) := by
      exact Nat.find_min hex (m := m) (by omega)
    linarith
  have hNle : N ≤ m := by
    by_contra hlt
    have hmlt' : m + 1 ≤ N := Nat.succ_le_of_lt (lt_of_not_ge hlt)
    have hpow_le : (1 / 2 : ℝ) ^ (N + 1) ≤ (1 / 2 : ℝ) ^ (m + 1) := by
      exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (le_trans hmlt' (Nat.le_succ N))
    have : (1 / 2 : ℝ) ^ (N + 1) < u.1 := lt_of_le_of_lt hpow_le hm_lt
    exact not_lt_of_ge huLt.le this
  let v : unitIcc := ⟨u.1 / (dyadicUnitIcc m).1, by
    constructor
    · have hden : 0 < (dyadicUnitIcc m).1 := by
        simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
      positivity
    · have hden : 0 < (dyadicUnitIcc m).1 := by
        simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
      exact (div_le_iff₀ hden).2 (by simpa [dyadicUnitIcc_val] using hu_le_m)⟩
  have hvHalf : (1 / 2 : ℝ) ≤ v.1 := by
    change (1 / 2 : ℝ) ≤ u.1 / (dyadicUnitIcc m).1
    have hden : 0 < (dyadicUnitIcc m).1 := by
      simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
    have hpow :
        (1 / 2 : ℝ) * (dyadicUnitIcc m).1 = (1 / 2 : ℝ) ^ (m + 1) := by
      simp [dyadicUnitIcc_val, pow_succ]
      ring
    have hnum : (1 / 2 : ℝ) * (dyadicUnitIcc m).1 ≤ u.1 := by
      calc
        (1 / 2 : ℝ) * (dyadicUnitIcc m).1 = (1 / 2 : ℝ) ^ (m + 1) := hpow
        _ ≤ u.1 := hm_lt.le
    exact (le_div_iff₀ hden).2 hnum
  have hEqScale : sqScaleMap (dyadicUnitIcc m) v = u := by
    apply Subtype.ext
    change (dyadicUnitIcc m).1 * v.1 = u.1
    simp [v]
    field_simp [show ((dyadicUnitIcc m).1 : ℝ) ≠ 0 by
      simp [dyadicUnitIcc, pow_pos]]
  exact ⟨m, hNle, v, hvHalf, hEqScale⟩

theorem exists_fixed_northZonal_sqquotientRaw_dyadic_step_near_v2_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ _hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          ∃ l : C(spherePoint3, ℝ),
            h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
            IsNorthZonal h ∧
            h sphereE3 ≠ 0 ∧
            (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
            q ∈ Polynomial.degreeLT ℝ N ∧
            l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
            ‖h - g‖ < ε ∧
            ∀ m : ℕ, ∀ {a : unitIcc}, 0 < a.1 →
              |sqCenteredNorthZonalQuotientRaw g a -
                  sqCenteredNorthZonalQuotientRaw g (sqScaleMap a halfUnitIcc)|
                ≤
                  8 * ε / a.1 +
                    2 *
                      ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                          (degreeLTSqMulNormConst N * (6 * ε)) +
                        (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by
  rcases exists_fixed_northZonal_sqquotientRaw_shell_pair_uniform_near_v2_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hshell⟩
  refine ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, ?_⟩
  intro m a ha
  have honeHalf : (1 / 2 : ℝ) ≤ (oneUnitIcc : unitIcc).1 := by
    change (1 / 2 : ℝ) ≤ (1 : ℝ)
    norm_num
  have hhalfHalf : (1 / 2 : ℝ) ≤ (halfUnitIcc : unitIcc).1 := by
    change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
    exact le_rfl
  simpa [sqScaleMap, oneUnitIcc, halfUnitIcc] using
    hshell m (a := a) (u := oneUnitIcc) (v := halfUnitIcc) ha honeHalf hhalfHalf

theorem exists_fixed_northZonal_sqquotientRaw_shell_uniform_near_half_v2_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ _hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          ∃ l : C(spherePoint3, ℝ),
            h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
            IsNorthZonal h ∧
            h sphereE3 ≠ 0 ∧
            (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
            q ∈ Polynomial.degreeLT ℝ N ∧
            l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
            ‖h - g‖ < ε ∧
            ∀ m : ℕ, ∀ {a u : unitIcc}, 0 < a.1 → (1 / 2 : ℝ) ≤ u.1 →
              |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
                  sqCenteredNorthZonalQuotientRaw g (sqScaleMap a halfUnitIcc)|
                ≤
                  8 * ε / a.1 +
                    2 *
                      ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                          (degreeLTSqMulNormConst N * (6 * ε)) +
                        (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by
  rcases exists_fixed_northZonal_sqquotientRaw_shell_pair_uniform_near_v2_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hshell⟩
  refine ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, ?_⟩
  intro m a u ha hu
  have hhalfHalf : (1 / 2 : ℝ) ≤ (halfUnitIcc : unitIcc).1 := by
    change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
    exact le_rfl
  exact hshell m (a := a) (u := u) (v := halfUnitIcc) ha hu hhalfHalf

theorem exists_fixed_northZonal_dyadic_anchor_step_bound_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε : ℝ}, 0 < ε → ε < ‖g sphereE3‖ →
        ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ∀ n : ℕ,
            dist (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
              (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2)))
              ≤
                4 *
                  (2 * ε / ((dyadicUnitIcc (n + 1) : unitIcc).1) +
                    ((dyadicUnitIcc (n + 1) : unitIcc).1) *
                      sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
  rcases exists_fixed_northZonal_sqquotientRaw_dyadic_step_near_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hstep⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  intro n
  have ha : 0 < (dyadicUnitIcc (n + 1) : unitIcc).1 := by
    simp [dyadicUnitIcc, pow_pos]
  let uHalf : unitIcc := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hle :=
    hstep (a := dyadicUnitIcc (n + 1)) ha
  have hscale :
      sqScaleMap (dyadicUnitIcc (n + 1)) uHalf = dyadicUnitIcc (n + 2) := by
    apply Subtype.ext
    simp [uHalf, sqScaleMap, dyadicUnitIcc_val, pow_succ]
  have hle' :
      |sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)) -
          sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2))|
        ≤
          4 *
            (2 * ε / ((dyadicUnitIcc (n + 1) : unitIcc).1) +
              ((dyadicUnitIcc (n + 1) : unitIcc).1) *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
    calc
      |sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)) -
          sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2))|
        =
          |sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)) -
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (n + 1)) uHalf)| := by
                rw [hscale]
      _ ≤
          4 *
            (2 * ε / ((dyadicUnitIcc (n + 1) : unitIcc).1) +
              ((dyadicUnitIcc (n + 1) : unitIcc).1) *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
                  simpa [uHalf] using hle
  simpa [Real.dist_eq] using hle'

theorem exists_fixed_northZonal_dyadic_anchor_step_geometric_bound_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ n : ℕ,
        ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ <
            min (‖g sphereE3‖ / 2)
              (((dyadicUnitIcc (n + 1) : unitIcc).1) ^ 2 / 8) ∧
          dist (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
            (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2)))
            ≤
              (dyadicUnitIcc (n + 1) : unitIcc).1 +
                4 *
                  ((dyadicUnitIcc (n + 1) : unitIcc).1 *
                    sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
  rcases exists_fixed_northZonal_dyadic_anchor_step_bound_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro n
  let ε : ℝ :=
    min (‖g sphereE3‖ / 2) (((dyadicUnitIcc (n + 1) : unitIcc).1) ^ 2 / 8)
  have hpoleNorm : 0 < ‖g sphereE3‖ := norm_pos_iff.mpr hgpole
  have haPos : 0 < (dyadicUnitIcc (n + 1) : unitIcc).1 := by
    simp [dyadicUnitIcc, pow_pos]
  have hεpos : 0 < ε := by
    dsimp [ε]
    apply lt_min
    · have : 0 < ‖g sphereE3‖ / 2 := by nlinarith
      exact this
    · have : 0 < (((dyadicUnitIcc (n + 1) : unitIcc).1) ^ 2) / 8 := by positivity
      exact this
  have hεpole : ε < ‖g sphereE3‖ := by
    dsimp [ε]
    have hmin : min (‖g sphereE3‖ / 2) (((dyadicUnitIcc (n + 1) : unitIcc).1) ^ 2 / 8)
        ≤ ‖g sphereE3‖ / 2 := min_le_left _ _
    have hhalf : ‖g sphereE3‖ / 2 < ‖g sphereE3‖ := by
      linarith
    exact lt_of_le_of_lt hmin hhalf
  rcases happ hεpos hεpole with ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hstep⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  have hεle :
      ε ≤ (((dyadicUnitIcc (n + 1) : unitIcc).1) ^ 2) / 8 := by
    dsimp [ε]
    exact min_le_right _ _
  calc
    dist (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
        (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2)))
      ≤
        4 *
          (2 * ε / ((dyadicUnitIcc (n + 1) : unitIcc).1) +
            ((dyadicUnitIcc (n + 1) : unitIcc).1) *
              sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := hstep n
    _ ≤
        4 *
          ((((dyadicUnitIcc (n + 1) : unitIcc).1) ^ 2 / 4) /
              ((dyadicUnitIcc (n + 1) : unitIcc).1) +
            ((dyadicUnitIcc (n + 1) : unitIcc).1) *
              sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
            have hinter :
                2 * ε / ((dyadicUnitIcc (n + 1) : unitIcc).1) ≤
                  (((dyadicUnitIcc (n + 1) : unitIcc).1) ^ 2 / 4) /
                    ((dyadicUnitIcc (n + 1) : unitIcc).1) := by
              have hnum :
                  2 * ε ≤ ((dyadicUnitIcc (n + 1) : unitIcc).1) ^ 2 / 4 := by
                linarith
              exact div_le_div_of_nonneg_right hnum haPos.le
            have htail_nonneg :
                0 ≤
                  ((dyadicUnitIcc (n + 1) : unitIcc).1) *
                    sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
              have htail0 :
                  0 ≤ sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
                unfold sqProfileTailAbsSum
                positivity
              exact mul_nonneg haPos.le htail0
            have hsum :
                2 * ε / ((dyadicUnitIcc (n + 1) : unitIcc).1) +
                    ((dyadicUnitIcc (n + 1) : unitIcc).1) *
                      sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)
                  ≤
                (((dyadicUnitIcc (n + 1) : unitIcc).1) ^ 2 / 4) /
                    ((dyadicUnitIcc (n + 1) : unitIcc).1) +
                  ((dyadicUnitIcc (n + 1) : unitIcc).1) *
                    sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
              linarith
            exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ =
        4 *
          (((dyadicUnitIcc (n + 1) : unitIcc).1) / 4 +
            ((dyadicUnitIcc (n + 1) : unitIcc).1) *
              sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
            field_simp [show ((dyadicUnitIcc (n + 1) : unitIcc).1 : ℝ) ≠ 0 by exact ne_of_gt haPos]
    _ =
        (dyadicUnitIcc (n + 1) : unitIcc).1 +
          4 *
            ((dyadicUnitIcc (n + 1) : unitIcc).1 *
              sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
            ring

theorem summable_dyadicUnitIcc_val_succ :
    Summable (fun n : ℕ => (dyadicUnitIcc (n + 1) : unitIcc).1) := by
  simpa [dyadicUnitIcc_val, pow_succ, mul_comm, mul_left_comm, mul_assoc] using
    (summable_geometric_two.mul_left ((1 / 2 : ℝ)))

theorem exists_eq_const_on_dyadic_shell_of_le_ge
    {g : C(spherePoint3, ℝ)} {c : ℝ} {n : ℕ}
    {u v : unitIcc}
    (hu : (1 / 2 : ℝ) ≤ u.1)
    (hv : (1 / 2 : ℝ) ≤ v.1)
    (hule : sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤ c)
    (hcve : c ≤ sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) :
    ∃ w : unitIcc, (1 / 2 : ℝ) ≤ w.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) w) = c := by
  let a : unitIcc := if h : u.1 ≤ v.1 then u else v
  let b : unitIcc := if h : u.1 ≤ v.1 then v else u
  have hab : a.1 ≤ b.1 := by
    by_cases h : u.1 ≤ v.1
    · simp [a, b, h]
    · simp [a, b, h, le_of_not_ge h]
  have haHalf : (1 / 2 : ℝ) ≤ a.1 := by
    by_cases h : u.1 ≤ v.1
    · simpa [a, h] using hu
    · simpa [a, h] using hv
  have hbHalf : (1 / 2 : ℝ) ≤ b.1 := le_trans haHalf hab
  have hcontShell :
      ContinuousOn
        (fun x : unitIcc => sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) x))
        (Set.uIcc a b) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := by
      rw [Set.mem_uIcc] at hx
      rcases hx with hx | hx
      · exact hx
      · exact ⟨le_trans hab hx.1, le_trans hx.2 hab⟩
    have hxPos : 0 < (sqScaleMap (dyadicUnitIcc n) x).1 := by
      have hdy : 0 < (dyadicUnitIcc n : unitIcc).1 := by
        simp [dyadicUnitIcc, pow_pos]
      have hxhalf' : (1 / 2 : ℝ) ≤ x.1 := le_trans haHalf hxIcc.1
      have hxhalf : 0 < x.1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hxhalf'
      change 0 < (dyadicUnitIcc n : unitIcc).1 * x.1
      exact mul_pos hdy hxhalf
    have hscale : Continuous fun y : unitIcc => sqScaleMap (dyadicUnitIcc n) y := by
      exact Continuous.subtype_mk
        (by
          simpa [sqScaleMap] using
            ((continuous_const : Continuous fun _ : unitIcc => (dyadicUnitIcc n : unitIcc).1).mul
              continuous_subtype_val))
        (fun y => (sqScaleMap (dyadicUnitIcc n) y).2)
    have hquot :
        ContinuousAt
          (fun y : unitIcc =>
            sqCenteredNorthZonalProfile g (sqScaleMap (dyadicUnitIcc n) y) /
              (sqScaleMap (dyadicUnitIcc n) y).1) x :=
      ((continuous_sqCenteredNorthZonalProfile g).comp hscale).continuousAt.div
        (continuous_subtype_val.comp hscale).continuousAt (show (sqScaleMap (dyadicUnitIcc n) x).1 ≠ 0 by linarith)
    have hEq :
        (fun y : unitIcc => sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) y)) =ᶠ[𝓝 x]
          (fun y : unitIcc =>
            sqCenteredNorthZonalProfile g (sqScaleMap (dyadicUnitIcc n) y) /
              (sqScaleMap (dyadicUnitIcc n) y).1) := by
      have hpos :
          {y : unitIcc | 0 < (sqScaleMap (dyadicUnitIcc n) y).1} ∈ 𝓝 x := by
        exact IsOpen.mem_nhds
          (isOpen_lt continuous_const (continuous_subtype_val.comp hscale)) hxPos
      filter_upwards [hpos] with y hy
      rw [sqCenteredNorthZonalQuotientRaw, if_neg (show (sqScaleMap (dyadicUnitIcc n) y).1 ≠ 0 by exact ne_of_gt hy)]
    exact (ContinuousAt.congr hquot hEq.symm).continuousWithinAt
  have hc_mem :
      c ∈ Set.uIcc
        (sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) a))
        (sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) b)) := by
    rw [Set.mem_uIcc]
    by_cases h : u.1 ≤ v.1
    · left
      simpa [a, b, h] using And.intro hule hcve
    · right
      have hble : sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) b) ≤ c := by
        simpa [b, h] using hule
      have hcgea : c ≤ sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) a) := by
        simpa [a, h] using hcve
      simpa [a, b, h] using And.intro hble hcgea
  rcases intermediate_value_uIcc hcontShell hc_mem with ⟨w, hwab, hwc⟩
  have hwIcc : w ∈ Set.Icc a b := by
    rw [Set.mem_uIcc] at hwab
    rcases hwab with hwab | hwab
    · exact hwab
    · exact ⟨le_trans hab hwab.1, le_trans hwab.2 hab⟩
  exact ⟨w, le_trans haHalf hwIcc.1, hwc⟩

theorem forall_gt_or_forall_lt_on_dyadic_shell_of_not_bracket
    {g : C(spherePoint3, ℝ)} {c : ℝ} {n : ℕ}
    (hno :
      ¬ ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤ c ∧
        c ≤ sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) :
    (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
      c < sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u)) ∨
    (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) < c) := by
  by_cases hlow :
      ∃ u : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤ c
  · right
    intro u hu
    have hnotge :
        ¬ c ≤ sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) := by
      intro hcu
      rcases hlow with ⟨v, hv, hvle⟩
      exact hno ⟨v, u, hv, hu, hvle, hcu⟩
    linarith
  · left
    intro u hu
    have hnotle :
        ¬ sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤ c := by
      intro huc
      exact hlow ⟨u, hu, huc⟩
    linarith

theorem forall_gt_on_next_dyadic_shell_of_forall_gt_of_not_bracket
    {g : C(spherePoint3, ℝ)} {c : ℝ} {n : ℕ}
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
        c < sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u))
    (hno :
      ¬ ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (n + 1)) u) ≤ c ∧
        c ≤ sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (n + 1)) v)) :
    ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
      c < sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (n + 1)) u) := by
  rcases forall_gt_or_forall_lt_on_dyadic_shell_of_not_bracket (g := g) (c := c) (n := n + 1) hno with
    hnext | hnext
  · exact hnext
  · have hboundary :
        sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)) < c := by
      have honeScale :
          sqScaleMap (dyadicUnitIcc (n + 1)) oneUnitIcc = dyadicUnitIcc (n + 1) := by
        apply Subtype.ext
        simp [sqScaleMap, oneUnitIcc]
      have hone : (1 / 2 : ℝ) ≤ (oneUnitIcc : unitIcc).1 := by
        change (1 / 2 : ℝ) ≤ (1 : ℝ)
        norm_num
      have hlt := hnext (u := oneUnitIcc) hone
      simpa [honeScale] using hlt
    have hboundary' :
        c < sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)) := by
      have hhalf : (1 / 2 : ℝ) ≤ (halfUnitIcc : unitIcc).1 := by
        change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
        exact le_rfl
      have hscale : sqScaleMap (dyadicUnitIcc n) halfUnitIcc = dyadicUnitIcc (n + 1) :=
        sqScaleMap_dyadicUnitIcc_halfUnitIcc n
      have hgt' :
          c < sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) halfUnitIcc) :=
        hgt (u := halfUnitIcc) hhalf
      simpa [hscale] using hgt'
    have : False := by linarith
    intro u hu
    exact False.elim this

theorem forall_lt_on_next_dyadic_shell_of_forall_lt_of_not_bracket
    {g : C(spherePoint3, ℝ)} {c : ℝ} {n : ℕ}
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) < c)
    (hno :
      ¬ ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (n + 1)) u) ≤ c ∧
        c ≤ sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (n + 1)) v)) :
    ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (n + 1)) u) < c := by
  rcases forall_gt_or_forall_lt_on_dyadic_shell_of_not_bracket (g := g) (c := c) (n := n + 1) hno with
    hnext | hnext
  · have hboundary :
        c < sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)) := by
      have honeScale :
          sqScaleMap (dyadicUnitIcc (n + 1)) oneUnitIcc = dyadicUnitIcc (n + 1) := by
        apply Subtype.ext
        simp [sqScaleMap, oneUnitIcc]
      have hone : (1 / 2 : ℝ) ≤ (oneUnitIcc : unitIcc).1 := by
        change (1 / 2 : ℝ) ≤ (1 : ℝ)
        norm_num
      have hgt := hnext (u := oneUnitIcc) hone
      simpa [honeScale] using hgt
    have hboundary' :
        sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)) < c := by
      have hhalf : (1 / 2 : ℝ) ≤ (halfUnitIcc : unitIcc).1 := by
        change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
        exact le_rfl
      have hscale : sqScaleMap (dyadicUnitIcc n) halfUnitIcc = dyadicUnitIcc (n + 1) :=
        sqScaleMap_dyadicUnitIcc_halfUnitIcc n
      have hlt' :
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) halfUnitIcc) < c :=
        hlt (u := halfUnitIcc) hhalf
      simpa [hscale] using hlt'
    have : False := by linarith
    intro u hu
    exact False.elim this
  · exact hnext

theorem dyadic_shell_bracket_value_at_lower_anchor_or_forall_gt_of_bracket_value_at_anchor_or_forall_gt
    {g : C(spherePoint3, ℝ)} {u0 x : unitIcc} {n : ℕ}
    (hxc :
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g u0)
    (hcase :
      (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
          sqCenteredNorthZonalQuotientRaw g u0 ∧
        sqCenteredNorthZonalQuotientRaw g u0 ≤
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
      (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u))) :
    (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
        sqCenteredNorthZonalQuotientRaw g x ∧
      sqCenteredNorthZonalQuotientRaw g x ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
    (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u)) := by
  rcases hcase with hbr | hgt
  · rcases hbr with ⟨u, v, hu, hv, hule, hcve⟩
    by_cases hlow :
        ∃ w : unitIcc, (1 / 2 : ℝ) ≤ w.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) w) ≤
            sqCenteredNorthZonalQuotientRaw g x
    · rcases hlow with ⟨w, hw, hwle⟩
      exact Or.inl ⟨w, v, hw, hv, hwle, le_trans hxc.le hcve⟩
    · exact Or.inr <| by
        intro w hw
        have hnotle :
            ¬ sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) w) ≤
              sqCenteredNorthZonalQuotientRaw g x := by
          intro hwle
          exact hlow ⟨w, hw, hwle⟩
        linarith
  · exact Or.inr <| by
      intro u hu
      linarith [hgt hu, hxc]

theorem dyadic_shell_bracket_value_at_upper_anchor_or_forall_lt_of_bracket_value_at_anchor_or_forall_lt
    {g : C(spherePoint3, ℝ)} {u0 x : unitIcc} {n : ℕ}
    (hu0x :
      sqCenteredNorthZonalQuotientRaw g u0 <
        sqCenteredNorthZonalQuotientRaw g x)
    (hcase :
      (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
          sqCenteredNorthZonalQuotientRaw g u0 ∧
        sqCenteredNorthZonalQuotientRaw g u0 ≤
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
      (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
          sqCenteredNorthZonalQuotientRaw g u0)) :
    (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
        sqCenteredNorthZonalQuotientRaw g x ∧
      sqCenteredNorthZonalQuotientRaw g x ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
    (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
        sqCenteredNorthZonalQuotientRaw g x) := by
  rcases hcase with hbr | hlt
  · rcases hbr with ⟨u, v, hu, hv, hule, hcve⟩
    by_cases hhigh :
        ∃ w : unitIcc, (1 / 2 : ℝ) ≤ w.1 ∧
          sqCenteredNorthZonalQuotientRaw g x ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) w)
    · rcases hhigh with ⟨w, hw, hwge⟩
      exact Or.inl ⟨u, w, hu, hw, le_trans hule hu0x.le, hwge⟩
    · exact Or.inr <| by
        intro w hw
        have hnotge :
            ¬ sqCenteredNorthZonalQuotientRaw g x ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) w) := by
          intro hwge
          exact hhigh ⟨w, hw, hwge⟩
        linarith
  · exact Or.inr <| by
      intro u hu
      linarith [hlt hu, hu0x]

theorem dyadic_shell_tail_bracket_value_at_lower_anchor_or_forall_gt_of_tail_bracket_value_at_anchor_or_forall_gt
    {g : C(spherePoint3, ℝ)} {u0 x : unitIcc}
    (hxc :
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g u0)
    (htail :
      ∃ N : ℕ,
        ∀ n ≥ N,
          (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g u0 ∧
            sqCenteredNorthZonalQuotientRaw g u0 ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
          (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g u0 <
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u))) :
    ∃ N : ℕ,
      ∀ n ≥ N,
        (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
            sqCenteredNorthZonalQuotientRaw g x ∧
          sqCenteredNorthZonalQuotientRaw g x ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u)) := by
  rcases htail with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact
    dyadic_shell_bracket_value_at_lower_anchor_or_forall_gt_of_bracket_value_at_anchor_or_forall_gt
      hxc (hN n hn)

theorem dyadic_shell_tail_bracket_value_at_upper_anchor_or_forall_lt_of_tail_bracket_value_at_anchor_or_forall_lt
    {g : C(spherePoint3, ℝ)} {u0 x : unitIcc}
    (hu0x :
      sqCenteredNorthZonalQuotientRaw g u0 <
        sqCenteredNorthZonalQuotientRaw g x)
    (htail :
      ∃ N : ℕ,
        ∀ n ≥ N,
          (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g u0 ∧
            sqCenteredNorthZonalQuotientRaw g u0 ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
          (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
              sqCenteredNorthZonalQuotientRaw g u0)) :
    ∃ N : ℕ,
      ∀ n ≥ N,
        (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
            sqCenteredNorthZonalQuotientRaw g x ∧
          sqCenteredNorthZonalQuotientRaw g x ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
            sqCenteredNorthZonalQuotientRaw g x) := by
  rcases htail with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact
    dyadic_shell_bracket_value_at_upper_anchor_or_forall_lt_of_bracket_value_at_anchor_or_forall_lt
      hu0x (hN n hn)

theorem dyadic_shell_bracket_value_at_lower_anchor_arbitrarily_far_of_tail_bracket_value_at_anchor_or_forall_gt
    {g : C(spherePoint3, ℝ)} {u0 x : unitIcc}
    (hxc :
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g u0)
    (htail :
      ∃ N : ℕ,
        ∀ n ≥ N,
          (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g u0 ∧
            sqCenteredNorthZonalQuotientRaw g u0 ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
          (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g u0 <
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u)))
    (hnotgt :
      ¬ ∃ N : ℕ,
        ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u)) :
    ∀ M : ℕ,
      ∃ n : ℕ, n ≥ M ∧
        ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
            sqCenteredNorthZonalQuotientRaw g x ∧
          sqCenteredNorthZonalQuotientRaw g x ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) := by
  intro M
  by_contra hfar
  have hfar' :
      ∀ n : ℕ, n ≥ M →
        ¬ ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
            sqCenteredNorthZonalQuotientRaw g x ∧
          sqCenteredNorthZonalQuotientRaw g x ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) := by
    intro n hn hbr
    exact hfar ⟨n, hn, hbr⟩
  rcases
      dyadic_shell_tail_bracket_value_at_lower_anchor_or_forall_gt_of_tail_bracket_value_at_anchor_or_forall_gt
        hxc htail with
    ⟨N, hN⟩
  have hgtTail :
      ∃ N0 : ℕ,
        ∀ n ≥ N0, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) := by
    refine ⟨max M N, ?_⟩
    intro n hn u hu
    rcases hN n (le_trans (le_max_right _ _) hn) with hbr | hgt
    · exfalso
      exact hfar' n (le_trans (le_max_left _ _) hn) hbr
    · exact hgt hu
  exact hnotgt hgtTail

theorem dyadic_shell_bracket_value_at_upper_anchor_arbitrarily_far_of_tail_bracket_value_at_anchor_or_forall_lt
    {g : C(spherePoint3, ℝ)} {u0 x : unitIcc}
    (hu0x :
      sqCenteredNorthZonalQuotientRaw g u0 <
        sqCenteredNorthZonalQuotientRaw g x)
    (htail :
      ∃ N : ℕ,
        ∀ n ≥ N,
          (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g u0 ∧
            sqCenteredNorthZonalQuotientRaw g u0 ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
          (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
              sqCenteredNorthZonalQuotientRaw g u0))
    (hnotlt :
      ¬ ∃ N : ℕ,
        ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
            sqCenteredNorthZonalQuotientRaw g x) :
    ∀ M : ℕ,
      ∃ n : ℕ, n ≥ M ∧
        ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
            sqCenteredNorthZonalQuotientRaw g x ∧
          sqCenteredNorthZonalQuotientRaw g x ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) := by
  intro M
  by_contra hfar
  have hfar' :
      ∀ n : ℕ, n ≥ M →
        ¬ ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
            sqCenteredNorthZonalQuotientRaw g x ∧
          sqCenteredNorthZonalQuotientRaw g x ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) := by
    intro n hn hbr
    exact hfar ⟨n, hn, hbr⟩
  rcases
      dyadic_shell_tail_bracket_value_at_upper_anchor_or_forall_lt_of_tail_bracket_value_at_anchor_or_forall_lt
        hu0x htail with
    ⟨N, hN⟩
  have hltTail :
      ∃ N0 : ℕ,
        ∀ n ≥ N0, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
            sqCenteredNorthZonalQuotientRaw g x := by
    refine ⟨max M N, ?_⟩
    intro n hn u hu
    rcases hN n (le_trans (le_max_right _ _) hn) with hbr | hlt
    · exfalso
      exact hfar' n (le_trans (le_max_left _ _) hn) hbr
    · exact hlt hu
  exact hnotlt hltTail

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_no_dyadic_shell_bracket_value_at_anchor
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    {u0 : unitIcc}
    (hu0 : 0 < u0.1)
    (hno :
      ∃ N : ℕ,
        ∀ n ≥ N,
          ¬ ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g u0 ∧
            sqCenteredNorthZonalQuotientRaw g u0 ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) :
    False := by
  rcases hno with ⟨N, hN⟩
  have hsplit :=
    forall_gt_or_forall_lt_on_dyadic_shell_of_not_bracket
      (g := g) (c := sqCenteredNorthZonalQuotientRaw g u0) (n := N) (hN N le_rfl)
  rcases hsplit with hgtN | hltN
  · have hgtAll :
      ∀ m : ℕ, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (N + m)) u) >
          sqCenteredNorthZonalQuotientRaw g u0 := by
      intro m
      induction' m with m hm
      · intro u hu
        simpa using hgtN (u := u) hu
      · intro u hu
        have hnoNext :
            ¬ ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (N + (m + 1))) u) ≤
                sqCenteredNorthZonalQuotientRaw g u0 ∧
              sqCenteredNorthZonalQuotientRaw g u0 ≤
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (N + (m + 1))) v) := by
          exact hN (N + (m + 1)) (by omega)
        exact forall_gt_on_next_dyadic_shell_of_forall_gt_of_not_bracket
          (g := g) (c := sqCenteredNorthZonalQuotientRaw g u0) (n := N + m) hm hnoNext hu
    have hevent :
        ∃ δ : ℝ, 0 < δ ∧
          ∀ {u : unitIcc}, 0 < u.1 → u.1 < δ →
            sqCenteredNorthZonalQuotientRaw g u0 < sqCenteredNorthZonalQuotientRaw g u := by
      refine ⟨(dyadicUnitIcc (N + 1) : unitIcc).1, by simp [dyadicUnitIcc, pow_pos], ?_⟩
      intro u hu huδ
      have hdecomp := exists_nat_dyadic_shell_mem_from hu huδ
      rcases hdecomp with ⟨m, hmN, v, hvHalf, hEq⟩
      have hgt := hgtAll (m - N) (u := v) hvHalf
      have hmEq : N + (m - N) = m := by omega
      simpa [hEq, hmEq] using hgt
    have hconst :
        ∀ {u : unitIcc}, 0 < u.1 →
          sqCenteredNorthZonalQuotientRaw g u = sqCenteredNorthZonalQuotientRaw g u0 :=
      sqCenteredNorthZonalQuotientRaw_eq_value_at_anchor_of_eventually_gt_near_zero
        (g := g) hg.2 hgz hu0 rfl hevent
    have hu :
        sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (N + 1)) =
          sqCenteredNorthZonalQuotientRaw g u0 := by
      have hpos : 0 < (dyadicUnitIcc (N + 1) : unitIcc).1 := by
        simp [dyadicUnitIcc, pow_pos]
      exact hconst (u := dyadicUnitIcc (N + 1)) hpos
    have hgtBoundary :
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (N + 1)) := by
      have hhalf : (1 / 2 : ℝ) ≤ (halfUnitIcc : unitIcc).1 := by
        change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
        exact le_rfl
      have hscale : sqScaleMap (dyadicUnitIcc N) halfUnitIcc = dyadicUnitIcc (N + 1) :=
        sqScaleMap_dyadicUnitIcc_halfUnitIcc N
      have hgtNBoundary :
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc N) halfUnitIcc) :=
        hgtN (u := halfUnitIcc) hhalf
      simpa [hscale] using hgtNBoundary
    linarith
  · have hltAll :
      ∀ m : ℕ, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (N + m)) u) <
          sqCenteredNorthZonalQuotientRaw g u0 := by
      intro m
      induction' m with m hm
      · intro u hu
        simpa using hltN (u := u) hu
      · intro u hu
        have hnoNext :
            ¬ ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (N + (m + 1))) u) ≤
                sqCenteredNorthZonalQuotientRaw g u0 ∧
              sqCenteredNorthZonalQuotientRaw g u0 ≤
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc (N + (m + 1))) v) := by
          exact hN (N + (m + 1)) (by omega)
        exact forall_lt_on_next_dyadic_shell_of_forall_lt_of_not_bracket
          (g := g) (c := sqCenteredNorthZonalQuotientRaw g u0) (n := N + m) hm hnoNext hu
    have hevent :
        ∃ δ : ℝ, 0 < δ ∧
          ∀ {u : unitIcc}, 0 < u.1 → u.1 < δ →
            sqCenteredNorthZonalQuotientRaw g u < sqCenteredNorthZonalQuotientRaw g u0 := by
      refine ⟨(dyadicUnitIcc (N + 1) : unitIcc).1, by simp [dyadicUnitIcc, pow_pos], ?_⟩
      intro u hu huδ
      have hdecomp := exists_nat_dyadic_shell_mem_from hu huδ
      rcases hdecomp with ⟨m, hmN, v, hvHalf, hEq⟩
      have hlt := hltAll (m - N) (u := v) hvHalf
      have hmEq : N + (m - N) = m := by omega
      simpa [hEq, hmEq] using hlt
    have hconst :
        ∀ {u : unitIcc}, 0 < u.1 →
          sqCenteredNorthZonalQuotientRaw g u = sqCenteredNorthZonalQuotientRaw g u0 :=
      sqCenteredNorthZonalQuotientRaw_eq_value_at_anchor_of_eventually_lt_near_zero
        (g := g) hg.2 hgz hu0 rfl hevent
    have hu :
        sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (N + 1)) =
          sqCenteredNorthZonalQuotientRaw g u0 := by
      have hpos : 0 < (dyadicUnitIcc (N + 1) : unitIcc).1 := by
        simp [dyadicUnitIcc, pow_pos]
      exact hconst (u := dyadicUnitIcc (N + 1)) hpos
    have hltBoundary :
        sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (N + 1)) <
          sqCenteredNorthZonalQuotientRaw g u0 := by
      have hhalf : (1 / 2 : ℝ) ≤ (halfUnitIcc : unitIcc).1 := by
        change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
        exact le_rfl
      have hscale : sqScaleMap (dyadicUnitIcc N) halfUnitIcc = dyadicUnitIcc (N + 1) :=
        sqScaleMap_dyadicUnitIcc_halfUnitIcc N
      have hltNBoundary :
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc N) halfUnitIcc) <
            sqCenteredNorthZonalQuotientRaw g u0 :=
        hltN (u := halfUnitIcc) hhalf
      simpa [hscale] using hltNBoundary
    linarith

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_no_dyadic_shell_bracket_value_at_one
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hno :
      ∃ N : ℕ,
        ∀ n ≥ N,
          ¬ ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) :
    False := by
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_no_dyadic_shell_bracket_value_at_anchor
      (g := g) hg hgne hgz (u0 := oneUnitIcc) (by simp [oneUnitIcc]) hno

theorem tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_uniform_near
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hnear :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ {u : unitIcc}, 0 < u.1 → u.1 < δ →
            |sqCenteredNorthZonalQuotientRaw g u - c| < ε) :
    Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
      (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases hnear hε with ⟨δ, hδ, hnearδ⟩
  refine mem_nhdsWithin.2 ?_
  refine ⟨{u : unitIcc | u.1 < δ}, ?_, ?_, ?_⟩
  · exact isOpen_lt continuous_subtype_val continuous_const
  · simpa [zeroUnitIcc] using hδ
  · intro u hu
    rcases hu with ⟨huδ, hupos⟩
    have hlt : u.1 < δ := huδ
    have hpos : 0 < u.1 := hupos
    simpa [Real.dist_eq] using hnearδ hpos hlt

theorem tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_shell_uniform_near
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ {a : unitIcc}, 0 < a.1 → a.1 < δ →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a halfUnitIcc) - c| < ε) :
    Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
      (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c) := by
  apply tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_uniform_near
  intro ε hε
  rcases hshell hε with ⟨δ, hδ, hshellδ⟩
  refine ⟨min (δ / 2) (1 / 2 : ℝ), by
    refine lt_min ?_ (by norm_num)
    positivity, ?_⟩
  intro u huPos huLt
  let a : unitIcc := ⟨2 * u.1, by
    constructor
    · positivity
    · have huHalf : u.1 < (1 / 2 : ℝ) := lt_of_lt_of_le huLt (min_le_right _ _)
      nlinarith⟩
  have haPos : 0 < a.1 := by
    change 0 < 2 * u.1
    positivity
  have haLt : a.1 < δ := by
    change 2 * u.1 < δ
    have huHalfδ : u.1 < δ / 2 := lt_of_lt_of_le huLt (min_le_left _ _)
    nlinarith
  have hEq : sqScaleMap a halfUnitIcc = u := by
    apply Subtype.ext
    change a.1 * (1 / 2 : ℝ) = u.1
    simp [a]
    ring
  simpa [hEq] using hshellδ haPos haLt

theorem tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_uniform_near
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) - c| < ε) :
    Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
      (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c) := by
  apply tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_uniform_near
  intro ε hε
  rcases hshell hε with ⟨N, hN⟩
  refine ⟨(1 / 2 : ℝ) ^ (N + 1), by positivity, ?_⟩
  intro u huPos huLt
  have hex : ∃ k : ℕ, ((1 / 2 : ℝ) ^ k) < u.1 := by
    simpa using exists_pow_lt_of_lt_one huPos (by norm_num : (1 / 2 : ℝ) < 1)
  let k : ℕ := Nat.find hex
  have hk_lt : ((1 / 2 : ℝ) ^ k) < u.1 := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hk0
    have hk1 : (1 : ℝ) < u.1 := by
      simpa [k, hk0] using hk_lt
    linarith [u.2.2]
  let n : ℕ := k - 1
  have hnk : n + 1 = k := by
    dsimp [n]
    exact Nat.succ_pred_eq_of_pos (Nat.pos_iff_ne_zero.mpr hk0)
  have hn_lt : ((1 / 2 : ℝ) ^ (n + 1)) < u.1 := by
    simpa [hnk] using hk_lt
  have hn_le : u.1 ≤ (1 / 2 : ℝ) ^ n := by
    have hnot : ¬ ((1 / 2 : ℝ) ^ n < u.1) := by
      exact Nat.find_min hex (m := n) (by omega)
    linarith
  have hNle : N ≤ n := by
    by_contra hlt
    have hnlt' : n + 1 ≤ N := Nat.succ_le_of_lt (lt_of_not_ge hlt)
    have hpow_le : (1 / 2 : ℝ) ^ (N + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (le_trans hnlt' (Nat.le_succ N))
    have : (1 / 2 : ℝ) ^ (N + 1) < u.1 := lt_of_le_of_lt hpow_le hn_lt
    exact not_lt_of_ge huLt.le this
  let v : unitIcc := ⟨u.1 / (dyadicUnitIcc n).1, by
    constructor
    · have hden : 0 < (dyadicUnitIcc n).1 := by
        simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
      positivity
    · have hden : 0 < (dyadicUnitIcc n).1 := by
        simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
      exact (div_le_iff₀ hden).2 (by simpa [dyadicUnitIcc_val] using hn_le)⟩
  have hvHalf : (1 / 2 : ℝ) ≤ v.1 := by
    change (1 / 2 : ℝ) ≤ u.1 / (dyadicUnitIcc n).1
    have hden : 0 < (dyadicUnitIcc n).1 := by
      simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
    have hpow :
        (1 / 2 : ℝ) * (dyadicUnitIcc n).1 = (1 / 2 : ℝ) ^ (n + 1) := by
      simp [dyadicUnitIcc_val, pow_succ]
      ring
    have hnum : (1 / 2 : ℝ) * (dyadicUnitIcc n).1 ≤ u.1 := by
      calc
        (1 / 2 : ℝ) * (dyadicUnitIcc n).1 = (1 / 2 : ℝ) ^ (n + 1) := hpow
        _ ≤ u.1 := hn_lt.le
    exact (le_div_iff₀ hden).2 hnum
  have hEq : sqScaleMap (dyadicUnitIcc n) v = u := by
    apply Subtype.ext
    change (dyadicUnitIcc n).1 * v.1 = u.1
    simp [v]
    field_simp [show ((dyadicUnitIcc n).1 : ℝ) ≠ 0 by
      simp [dyadicUnitIcc, pow_pos]]
  simpa [hEq] using hN n hNle hvHalf

theorem tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_pair_uniform_near_of_eventually_shell_value
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (hvalue :
      ∃ N : ℕ,
        ∀ n ≥ N, ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) = c) :
    Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
      (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c) := by
  apply tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_uniform_near
  intro ε hε
  rcases hshell hε with ⟨N₁, hN₁⟩
  rcases hvalue with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn u hu
  have hn₁ : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ N₂ := le_trans (le_max_right _ _) hn
  rcases hN₂ n hn₂ with ⟨v, hv, hvc⟩
  have hpair := hN₁ n hn₁ hu hv
  calc
    |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) - c|
      = |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| := by
            rw [hvc]
    _ < ε := hpair

theorem tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_pair_uniform_near_of_eventually_shell_near
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (hnear :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) - c| < ε) :
    Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
      (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c) := by
  apply tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_uniform_near
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rcases hshell hε2 with ⟨N₁, hN₁⟩
  rcases hnear hε2 with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn u hu
  have hn₁ : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ N₂ := le_trans (le_max_right _ _) hn
  rcases hN₂ n hn₂ with ⟨v, hv, hvc⟩
  have hpair := hN₁ n hn₁ hu hv
  calc
    |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) - c|
      ≤
        |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| +
          |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) - c| := by
            exact abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

theorem tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_uniform_near_anchor
    {g : C(spherePoint3, ℝ)} {c : ℕ → ℝ} {L : ℝ}
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) - c n| < ε)
    (hanchor : Filter.Tendsto c Filter.atTop (𝓝 L)) :
    Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
      (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 L) := by
  apply tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_uniform_near
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rcases hshell hε2 with ⟨N₁, hN₁⟩
  have hanchorev : ∀ᶠ n : ℕ in Filter.atTop, dist (c n) L < ε / 2 :=
    (Metric.tendsto_nhds.mp hanchor) (ε / 2) hε2
  rcases Filter.eventually_atTop.1 hanchorev with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn u hu
  have hn₁ : n ≥ N₁ := le_trans (le_max_left _ _) hn
  have hn₂ : n ≥ N₂ := le_trans (le_max_right _ _) hn
  have hs : |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) - c n| < ε / 2 :=
    hN₁ n hn₁ hu
  have hc : |c n - L| < ε / 2 := by
    simpa [Real.dist_eq] using hN₂ n hn₂
  calc
    |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) - L|
      ≤ |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) - c n| + |c n - L| := by
          exact abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hs hc
    _ = ε := by ring

theorem tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_uniform_near_half
    {g : C(spherePoint3, ℝ)} {L : ℝ}
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1))| < ε)
    (hanchor :
      Filter.Tendsto (fun n : ℕ => sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
        Filter.atTop (𝓝 L)) :
    Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
      (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 L) := by
  apply tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_uniform_near_anchor
    (c := fun n : ℕ => sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
  · intro ε hε
    rcases hshell hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn u hu
    simpa [sqScaleMap_halfUnitIcc, dyadicUnitIcc_val, pow_succ] using hN n hn hu
  · exact hanchor

theorem exists_tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_uniform_near_half_of_summable_anchor_step
    {g : C(spherePoint3, ℝ)}
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1))| < ε)
    (hsumm :
      Summable (fun n : ℕ =>
        dist (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
          (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2))))) :
    ∃ L : ℝ,
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 L) := by
  let c : ℕ → ℝ := fun n => sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1))
  have hcauchy : CauchySeq c := by
    simpa [c] using cauchySeq_of_summable_dist hsumm
  rcases cauchySeq_tendsto_of_complete hcauchy with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  exact tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_uniform_near_half hshell hL

theorem exists_fixed_northZonal_sqquotientRaw_uniform_near_coeff_zero_on_Icc_of_nontrivial_tail
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
      ∀ {ε δ : ℝ}, 0 < ε → ε < ‖g sphereE3‖ → 0 < δ →
        ∃ N : ℕ, ∃ _hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          q ∈ Polynomial.degreeLT ℝ N ∧
          ‖h - g‖ < ε ∧
          sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε ∧
          ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖
            ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε ∧
          ∀ {u : unitIcc}, δ ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0|
              ≤ (2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) / δ := by
  rcases
      exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_factor_degree_defect_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε δ hε hεpole hδ
  rcases happ hε hεpole with
    ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hdefect, hnear⟩
  have hnear' :
      ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖
        ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    have hhHigh : h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule :=
      Submodule.mem_iSup_of_mem N hhN
    change ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ ≤
      24 * degreeLTSqProfileTailBoundConst (N + 1) * ε
    rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh hhz]
    have hpoly :
        sqCenteredNorthZonalContinuousMap h =
          sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) := by
      ext u
      change sqCenteredNorthZonalProfile h u =
        ((Polynomial.X : Polynomial ℝ) * q).eval u.1
      rw [hq u]
      simp
    have hlin :
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
                have htail_nonneg : 0 ≤ degreeLTSqProfileTailBoundConst (N + 1) := by
                  unfold degreeLTSqProfileTailBoundConst
                  positivity
                nlinarith
              exact mul_le_mul_of_nonneg_left (le_of_lt hdefect) hconst_nonneg
        _ = 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by ring
    simpa [sqProfileLinearPart] using hlin
  refine ⟨N, hN, h, q, hhN, hhz, hhpole, hq, hqdeg, hdist, hdefect, hnear', ?_⟩
  intro u hu
  have hdist_l :
      dist (lowSqProfileMode (h sphereE1) (q.coeff 0))
          (lowSqProfileMode (g sphereE1) (q.coeff 0)) ≤ dist h g := by
    simpa [dist_eq_norm] using
      norm_lowSqProfileMode_sub_leftParam_le_of_dist (h := h) (g := g) (q.coeff 0)
  have hglDist :
      dist g (lowSqProfileMode (g sphereE1) (q.coeff 0))
        ≤ 2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    calc
      dist g (lowSqProfileMode (g sphereE1) (q.coeff 0))
        ≤ dist g h +
            dist h (lowSqProfileMode (h sphereE1) (q.coeff 0)) +
            dist (lowSqProfileMode (h sphereE1) (q.coeff 0))
              (lowSqProfileMode (g sphereE1) (q.coeff 0)) := by
              calc
                dist g (lowSqProfileMode (g sphereE1) (q.coeff 0))
                  ≤ dist g h + dist h (lowSqProfileMode (g sphereE1) (q.coeff 0)) :=
                    dist_triangle _ _ _
                _ ≤ dist g h +
                      (dist h (lowSqProfileMode (h sphereE1) (q.coeff 0)) +
                        dist (lowSqProfileMode (h sphereE1) (q.coeff 0))
                          (lowSqProfileMode (g sphereE1) (q.coeff 0))) := by
                    gcongr
                    exact dist_triangle _ _ _
                _ =
                    dist g h +
                      dist h (lowSqProfileMode (h sphereE1) (q.coeff 0)) +
                      dist (lowSqProfileMode (h sphereE1) (q.coeff 0))
                        (lowSqProfileMode (g sphereE1) (q.coeff 0)) := by
                          ring
      _ ≤ dist g h +
            dist h (lowSqProfileMode (h sphereE1) (q.coeff 0)) +
            dist h g := by
            gcongr
      _ ≤ 2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
            have hdist' : dist h g < ε := by
              simpa [dist_eq_norm] using hdist
            have hdist'' : dist g h < ε := by simpa [dist_comm] using hdist'
            have hnear'' :
                dist h (lowSqProfileMode (h sphereE1) (q.coeff 0))
                  ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
              simpa [dist_eq_norm] using hnear'
            linarith
  have hsqLin :
      ‖sqCenteredNorthZonalContinuousMap g -
          (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖
        ≤ 2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    rw [← norm_sub_lowSqProfileMode_eq_sqprofile_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
      (hg := hg) (hgz := hgz) (b := q.coeff 0)]
    simpa [dist_eq_norm] using hglDist
  calc
    |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0|
      ≤ ‖sqCenteredNorthZonalContinuousMap g -
          (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ / δ :=
        abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_sqprofile_linear g hδ hu
    _ ≤ (2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) / δ := by
        have hδnonneg : 0 ≤ δ := le_of_lt hδ
        exact div_le_div_of_nonneg_right hsqLin hδnonneg

theorem exists_fixed_northZonal_sqquotientRaw_uniform_near_coeff_zero_of_sqprofile_linearApprox_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε δ : ℝ}, 0 < ε → ε < ‖g sphereE3‖ → 0 < δ → ∀ m : ℕ,
        ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ∀ {u : unitIcc}, δ ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0|
              ≤
                (2 * ε +
                  (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                    (3 / 4 : ℝ) ^ m *
                      sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ := by
  rcases exists_fixed_northZonal_limit_sqprofile_near_linear_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro ε δ hε hεpole hδ m
  rcases happ hε hεpole m with
    ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hsqLin⟩
  have hsqLin' :
      ‖sqCenteredNorthZonalContinuousMap g -
          (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖
        ≤
          2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
    simpa [sqProfileLinearPart] using hsqLin
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  intro u hu
  calc
    |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0|
      ≤ ‖sqCenteredNorthZonalContinuousMap g -
          (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ / δ :=
        abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_sqprofile_linear g hδ hu
    _ ≤
        (2 * ε +
          (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
            (3 / 4 : ℝ) ^ m *
              sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ := by
          have hδnonneg : 0 ≤ δ := le_of_lt hδ
          exact div_le_div_of_nonneg_right hsqLin' hδnonneg

theorem exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_on_Icc_of_nontrivial_tail
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
      ∀ {ε δ : ℝ}, 0 < ε → ε < ‖g sphereE3‖ → 0 < δ →
        ∃ N : ℕ, ∃ _hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          q ∈ Polynomial.degreeLT ℝ N ∧
          ‖h - g‖ < ε ∧
          sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε ∧
          ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖
            ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε ∧
          ∀ {u : unitIcc}, δ ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g u - sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
              ≤ 2 * ((2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) / δ) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_coeff_zero_on_Icc_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε δ hε hεpole hδ
  rcases happ hε hεpole hδ with
    ⟨N, hN, h, q, hhN, hhz, hhpole, hq, hqdeg, hdist, hdefect, hnear, hraw⟩
  refine ⟨N, hN, h, q, hhN, hhz, hhpole, hq, hqdeg, hdist, hdefect, hnear, ?_⟩
  intro u hu
  have hδ1 : δ ≤ 1 := le_trans hu u.2.2
  have hone :
      |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0|
        ≤ (2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) / δ := by
    exact hraw (u := oneUnitIcc) hδ1
  calc
    |sqCenteredNorthZonalQuotientRaw g u - sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
      ≤ |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
          |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0| := by
            have htri :=
              abs_sub_le (sqCenteredNorthZonalQuotientRaw g u) (q.coeff 0)
                (sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
            calc
              |sqCenteredNorthZonalQuotientRaw g u - sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
                ≤ |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
                    |q.coeff 0 - sqCenteredNorthZonalQuotientRaw g oneUnitIcc| := by
                      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htri
              _ = |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
                    |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0| := by
                      congr 1
                      exact abs_sub_comm _ _
    _ ≤
        (2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) / δ +
          (2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) / δ := by
            gcongr
            exact hraw hu
    _ = 2 * ((2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε) / δ) := by ring

theorem exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε δ : ℝ}, 0 < ε → ε < ‖g sphereE3‖ → 0 < δ → ∀ m : ℕ,
        ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ∀ {u : unitIcc}, δ ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g u - sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
              ≤
                2 *
                  ((2 * ε +
                    (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                      (3 / 4 : ℝ) ^ m *
                        sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_coeff_zero_of_sqprofile_linearApprox_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro ε δ hε hεpole hδ m
  rcases happ hε hεpole hδ m with
    ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hraw⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  intro u hu
  have hδ1 : δ ≤ 1 := le_trans hu u.2.2
  have hone :
      |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0|
        ≤
          (2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ := by
    exact hraw (u := oneUnitIcc) hδ1
  calc
    |sqCenteredNorthZonalQuotientRaw g u - sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
      ≤ |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
          |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0| := by
            have htri :=
              abs_sub_le (sqCenteredNorthZonalQuotientRaw g u) (q.coeff 0)
                (sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
            calc
              |sqCenteredNorthZonalQuotientRaw g u - sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
                ≤ |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
                    |q.coeff 0 - sqCenteredNorthZonalQuotientRaw g oneUnitIcc| := by
                      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htri
              _ = |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
                    |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0| := by
                      congr 1
                      exact abs_sub_comm _ _
    _ ≤
        ((2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) +
          ((2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) := by
            gcongr
            exact hraw hu
    _ =
        2 *
          ((2 * ε +
              (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                (3 / 4 : ℝ) ^ m *
                  sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) := by
          ring

theorem exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε δ : ℝ}, 0 < ε → ε < ‖g sphereE3‖ → 0 < δ →
        ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ∀ m : ℕ, ∀ {u : unitIcc}, δ ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g u - sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
              ≤
                2 *
                  ((2 * ε +
                    (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                      (3 / 4 : ℝ) ^ m *
                        sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) := by
  rcases
      exists_fixed_northZonal_limit_sqprofile_uniform_near_linear_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro ε δ hε hεpole hδ
  rcases happ hε hεpole with
    ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hsqLin⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  intro m u hu
  have hsqLin' :
      ‖sqCenteredNorthZonalContinuousMap g -
          (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖
        ≤
          2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
    simpa [sqProfileLinearPart] using hsqLin m
  have hraw :
      |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0|
        ≤
          (2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ := by
    calc
      |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0|
        ≤ ‖sqCenteredNorthZonalContinuousMap g -
            (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ / δ :=
          abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_sqprofile_linear g hδ hu
      _ ≤
          (2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ := by
            have hδnonneg : 0 ≤ δ := le_of_lt hδ
            exact div_le_div_of_nonneg_right hsqLin' hδnonneg
  have hδ1 : δ ≤ 1 := le_trans hu u.2.2
  have hone :
      |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0|
        ≤
          (2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ := by
    calc
      |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0|
        ≤ ‖sqCenteredNorthZonalContinuousMap g -
            (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ / δ :=
          abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_sqprofile_linear g hδ hδ1
      _ ≤
          (2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ := by
            have hδnonneg : 0 ≤ δ := le_of_lt hδ
            exact div_le_div_of_nonneg_right hsqLin' hδnonneg
  calc
    |sqCenteredNorthZonalQuotientRaw g u - sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
      ≤ |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
          |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0| := by
            have htri :=
              abs_sub_le (sqCenteredNorthZonalQuotientRaw g u) (q.coeff 0)
                (sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
            calc
              |sqCenteredNorthZonalQuotientRaw g u - sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
                ≤ |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
                    |q.coeff 0 - sqCenteredNorthZonalQuotientRaw g oneUnitIcc| := by
                      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htri
              _ = |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
                    |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0| := by
                      congr 1
                      exact abs_sub_comm _ _
    _ ≤
        ((2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) +
          ((2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) := by
          gcongr
    _ =
        2 *
          ((2 * ε +
              (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                (3 / 4 : ℝ) ^ m *
                  sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) := by
          ring

lemma continuousAt_sqCenteredNorthZonalQuotientRaw_of_pos
    (g : C(spherePoint3, ℝ)) {u : unitIcc}
    (hu : 0 < u.1) :
    ContinuousAt (sqCenteredNorthZonalQuotientRaw g) u := by
  have hquot :
      ContinuousAt (fun v : unitIcc => sqCenteredNorthZonalProfile g v / v.1) u :=
    (continuous_sqCenteredNorthZonalProfile g).continuousAt.div
      continuous_subtype_val.continuousAt (show u.1 ≠ 0 by linarith)
  have hEq :
      sqCenteredNorthZonalQuotientRaw g =ᶠ[𝓝 u]
        (fun v : unitIcc => sqCenteredNorthZonalProfile g v / v.1) := by
    have hpos :
        {v : unitIcc | 0 < v.1} ∈ 𝓝 u := by
      exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_subtype_val) hu
    filter_upwards [hpos] with v hv
    simp [sqCenteredNorthZonalQuotientRaw, ne_of_gt hv]
  exact ContinuousAt.congr hquot hEq.symm

lemma continuous_sqCenteredNorthZonalQuotientRaw_of_continuousAt_zero
    {g : C(spherePoint3, ℝ)}
    (hzero : ContinuousAt (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc) :
    Continuous (sqCenteredNorthZonalQuotientRaw g) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = zeroUnitIcc
  · simpa [hu] using hzero
  · have hu0 : u.1 ≠ 0 := by
      intro hu0'
      apply hu
      exact Subtype.ext hu0'
    have huPos : 0 < u.1 := lt_of_le_of_ne u.2.1 (Ne.symm hu0)
    exact continuousAt_sqCenteredNorthZonalQuotientRaw_of_pos g huPos

theorem exists_sqquotient_factor_of_continuousAt_sqCenteredNorthZonalQuotientRaw_zero
    {g : C(spherePoint3, ℝ)}
    (hzero : ContinuousAt (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc) :
    ∃ q : C(unitIcc, ℝ),
      ∀ u : unitIcc, sqCenteredNorthZonalProfile g u = u.1 * q u := by
  let q : C(unitIcc, ℝ) :=
    ⟨sqCenteredNorthZonalQuotientRaw g,
      continuous_sqCenteredNorthZonalQuotientRaw_of_continuousAt_zero hzero⟩
  refine ⟨q, ?_⟩
  intro u
  simpa [q, sqMulContinuousMap_apply] using
    sqCenteredNorthZonalProfile_eq_mul_sqCenteredNorthZonalQuotientRaw g u

theorem exists_sqquotient_factor_of_tendsto_sqCenteredNorthZonalQuotientRaw_zero
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hlim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c)) :
    ∃ q : C(unitIcc, ℝ),
      ∀ u : unitIcc, sqCenteredNorthZonalProfile g u = u.1 * q u := by
  have hposSet :
      ({zeroUnitIcc}ᶜ : Set unitIcc) = {u : unitIcc | 0 < u.1} := by
    ext u
    constructor
    · intro hu
      have hu0 : u.1 ≠ 0 := by
        intro hu0
        apply hu
        exact Subtype.ext hu0
      exact lt_of_le_of_ne u.2.1 hu0.symm
    · intro hu huz
      subst huz
      simp [zeroUnitIcc] at hu
  let qRaw : unitIcc → ℝ := Function.update (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc c
  have hqRawCont : Continuous qRaw := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u = zeroUnitIcc
    · subst hu
      change ContinuousAt
        (Function.update (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc c) zeroUnitIcc
      rw [continuousAt_update_same]
      simpa [hposSet] using hlim
    · have hu0 : u.1 ≠ 0 := by
        intro hu0
        apply hu
        exact Subtype.ext (by simpa [zeroUnitIcc] using hu0)
      have huPos : 0 < u.1 := lt_of_le_of_ne u.2.1 hu0.symm
      change ContinuousAt
        (Function.update (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc c) u
      exact
        (continuousAt_update_of_ne (f := sqCenteredNorthZonalQuotientRaw g)
          (x := zeroUnitIcc) (x' := u) (y := c) hu).2
          (continuousAt_sqCenteredNorthZonalQuotientRaw_of_pos g huPos)
  let q : C(unitIcc, ℝ) := ⟨qRaw, hqRawCont⟩
  refine ⟨q, ?_⟩
  intro u
  by_cases hu : u = zeroUnitIcc
  · subst hu
    rw [sqCenteredNorthZonalProfile_zero_eq_zero]
    simp [q, qRaw, zeroUnitIcc]
  · have hu0 : u.1 ≠ 0 := by
        intro hu0
        apply hu
        exact Subtype.ext (by simpa [zeroUnitIcc] using hu0)
    have huPos : 0 < u.1 := lt_of_le_of_ne u.2.1 hu0.symm
    have hq :
        q u = sqCenteredNorthZonalQuotientRaw g u := by
      simp [q, qRaw, hu]
    rw [hq]
    exact sqCenteredNorthZonalProfile_eq_mul_sqCenteredNorthZonalQuotientRaw g u

theorem exists_const_sqquotient_factor_of_tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_mem_frame
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hlim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c)) :
    ∃ q : C(unitIcc, ℝ),
      q = ContinuousMap.const unitIcc c ∧
      ∀ u : unitIcc, sqCenteredNorthZonalProfile g u = u.1 * q u := by
  refine ⟨ContinuousMap.const unitIcc c, rfl, ?_⟩
  intro u
  by_cases hu : 0 < u.1
  · have hq :
        sqCenteredNorthZonalQuotientRaw g u = c :=
      sqCenteredNorthZonalQuotientRaw_eq_limit_of_tendsto_zero hgframe hgz hlim hu
    rw [sqCenteredNorthZonalProfile_eq_mul_sqCenteredNorthZonalQuotientRaw, hq]
    simp
  · have hu0 : u.1 = 0 := by
      have hle : u.1 ≤ 0 := le_of_not_gt hu
      linarith [u.2.1]
    have huz : u = zeroUnitIcc := by
      apply Subtype.ext
      simpa [zeroUnitIcc] using hu0
    subst huz
    rw [sqCenteredNorthZonalProfile_zero_eq_zero]
    change (0 : ℝ) = zeroUnitIcc.1 * c
    simp [zeroUnitIcc]

theorem mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hlim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c)) :
    g ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
  rcases exists_const_sqquotient_factor_of_tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_mem_frame
      (g := g) hg.2 hgz hlim with ⟨q, -, hq⟩
  exact
    mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotient_factor
      hg hgz hq

theorem eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hlim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c)) :
    g = 0 := by
  have hlow :
      g ∈ lowHarmonicPolyHomogeneousImageSubmodule :=
    mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
      hg hgz hlim
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

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hlim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c)) :
    False := by
  exact hgne <|
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
      hg hgz hlim

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_eventually_shell_value
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (hvalue :
      ∃ N : ℕ,
        ∀ n ≥ N, ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) = c) :
    False := by
  have hlim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c) :=
    tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_pair_uniform_near_of_eventually_shell_value
      hshell hvalue
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
      hg hgne hgz hlim

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_eventually_eq_value_at_one
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (hvalue :
      ∃ N : ℕ,
        ∀ n ≥ N, ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) =
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc) :
    False := by
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_eventually_shell_value
      hg hgne hgz hshell hvalue

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_eventually_near_value_at_one
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (hnear :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) -
                sqCenteredNorthZonalQuotientRaw g oneUnitIcc| < ε) :
    False := by
  have hlim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc)
        (𝓝 (sqCenteredNorthZonalQuotientRaw g oneUnitIcc)) :=
    tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_pair_uniform_near_of_eventually_shell_near
      hshell hnear
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
      hg hgne hgz hlim

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_dyadic_shell_pair_uniform_near_and_eventually_shell_value
    (hshell :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {ε : ℝ}, 0 < ε →
          ∃ N : ℕ,
            ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
              |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                  sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (hvalue :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        g ≠ 0 →
        IsNorthZonal g →
        ∃ c : ℝ, ∃ N : ℕ,
          ∀ n ≥ N, ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) = c) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  by_contra hne
  rcases exists_nonzero_northZonal_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz⟩
  rcases hvalue hg hgne hgz with ⟨c, N, hN⟩
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_eventually_shell_value
      hg hgne hgz (hshell hg hgz) ⟨N, hN⟩

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_dyadic_shell_pair_uniform_near_and_eventually_eq_value_at_one
    (hshell :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {ε : ℝ}, 0 < ε →
          ∃ N : ℕ,
            ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
              |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                  sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (hvalue :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        g ≠ 0 →
        IsNorthZonal g →
        ∃ N : ℕ,
          ∀ n ≥ N, ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) =
              sqCenteredNorthZonalQuotientRaw g oneUnitIcc) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  apply topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_dyadic_shell_pair_uniform_near_and_eventually_shell_value
    hshell
  intro g hg hgne hgz
  refine ⟨sqCenteredNorthZonalQuotientRaw g oneUnitIcc, ?_⟩
  exact hvalue hg hgne hgz

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_dyadic_shell_pair_uniform_near_and_eventually_near_value_at_one
    (hshell :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {ε : ℝ}, 0 < ε →
          ∃ N : ℕ,
            ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
              |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                  sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (hnear :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        g ≠ 0 →
        IsNorthZonal g →
        ∀ {ε : ℝ}, 0 < ε →
          ∃ N : ℕ,
            ∀ n ≥ N, ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧
              |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) -
                  sqCenteredNorthZonalQuotientRaw g oneUnitIcc| < ε) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  by_contra hne
  rcases exists_nonzero_northZonal_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz⟩
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_eventually_near_value_at_one
      hg hgne hgz (hshell hg hgz) (hnear hg hgne hgz)

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_dyadic_shell_pair_uniform_near_and_eventually_bracket_value_at_one
    (hshell :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {ε : ℝ}, 0 < ε →
          ∃ N : ℕ,
            ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
              |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                  sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (hbracket :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        g ≠ 0 →
        IsNorthZonal g →
        ∃ N : ℕ,
          ∀ n ≥ N,
            ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
                sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
              sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  apply topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_dyadic_shell_pair_uniform_near_and_eventually_eq_value_at_one
    hshell
  intro g hg hgne hgz
  rcases hbracket hg hgne hgz with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rcases hN n hn with ⟨u, v, hu, hv, hule, hcve⟩
  rcases exists_eq_const_on_dyadic_shell_of_le_ge (g := g) (c := sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
      hu hv hule hcve with ⟨w, hw, hwc⟩
  exact ⟨w, hw, hwc⟩

theorem exists_fixed_northZonal_eq_value_at_one_near_zero_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {δ : ℝ}, 0 < δ →
        ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧
          sqCenteredNorthZonalQuotientRaw g u = sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro δ hδ
  by_cases hconst :
      ∀ {u : unitIcc}, 0 < u.1 →
        sqCenteredNorthZonalQuotientRaw g u = sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  · have hlim :
        Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
          (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc)
          (𝓝 (sqCenteredNorthZonalQuotientRaw g oneUnitIcc)) := by
      apply tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_uniform_near
      intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro u hu hu1
      rw [hconst hu]
      simpa using hε
    exact False.elim <|
      False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
        hg hgne hgz hlim
  · push_neg at hconst
    exact exists_eq_value_at_one_near_zero_of_not_const_of_mem_frame hg.2 hgz hconst hδ

theorem exists_fixed_northZonal_bracket_value_at_one_near_zero_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {δ : ℝ}, 0 < δ →
        (∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧
          sqCenteredNorthZonalQuotientRaw g u ≤ sqCenteredNorthZonalQuotientRaw g oneUnitIcc) ∧
        (∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤ sqCenteredNorthZonalQuotientRaw g u) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro δ hδ
  by_cases hconst :
      ∀ {u : unitIcc}, 0 < u.1 →
        sqCenteredNorthZonalQuotientRaw g u = sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  · have hlim :
        Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
          (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc)
          (𝓝 (sqCenteredNorthZonalQuotientRaw g oneUnitIcc)) := by
      apply tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_uniform_near
      intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro u hu hu1
      rw [hconst hu]
      simpa using hε
    exact False.elim <|
      False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
        hg hgne hgz hlim
  · push_neg at hconst
    exact
      exists_le_ge_value_at_one_near_zero_of_not_const_of_mem_frame
        hg.2 hgz hconst hδ

theorem exists_fixed_northZonal_eq_value_at_anchor_near_zero_of_ne_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 : unitIcc}, 0 < u0.1 →
        sqCenteredNorthZonalQuotientRaw g u0 ≠
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        ∀ {δ : ℝ}, 0 < δ →
          ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧
            sqCenteredNorthZonalQuotientRaw g u =
              sqCenteredNorthZonalQuotientRaw g u0 := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 hu0 hune δ hδ
  exact
    exists_eq_value_at_anchor_near_zero_of_ne_value_at_one_of_mem_frame
      hg.2 hgz hu0 hune hδ

theorem exists_fixed_northZonal_eq_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g u0 := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hgt
  exact
    exists_eq_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
      hg.2 hgz hu0 ha haEq hgt

theorem exists_fixed_northZonal_eq_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g u0) →
        ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g u0 := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hlt
  exact
    exists_eq_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell
      hg.2 hgz hu0 ha haEq hlt

theorem exists_fixed_northZonal_eq_value_at_anchor_below_half_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
            sqCenteredNorthZonalQuotientRaw g u0 <
              sqCenteredNorthZonalQuotientRaw g v := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hgt
  exact
    exists_eq_value_at_anchor_below_half_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
      hg.2 hgz hu0 ha haEq hgt

theorem exists_fixed_northZonal_eq_value_at_anchor_below_half_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g u0) →
        ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
            sqCenteredNorthZonalQuotientRaw g v <
              sqCenteredNorthZonalQuotientRaw g u0 := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hlt
  exact
    exists_eq_value_at_anchor_below_half_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell
      hg.2 hgz hu0 ha haEq hlt

theorem exists_fixed_northZonal_lt_value_at_anchor_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          ∀ {δ : ℝ}, 0 < δ →
            ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
              sqCenteredNorthZonalQuotientRaw g y =
                sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hgt
  exact
    exists_lt_value_at_anchor_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_gt_on_halfShell
      hg.2 hgz hu0 ha haEq hgt

theorem exists_fixed_northZonal_gt_value_at_anchor_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g u0) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g x ∧
          ∀ {δ : ℝ}, 0 < δ →
            ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
              sqCenteredNorthZonalQuotientRaw g y =
                sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hlt
  exact
    exists_gt_value_at_anchor_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_lt_on_halfShell
      hg.2 hgz hu0 ha haEq hlt

theorem exists_fixed_northZonal_lt_value_at_anchor_below_half_without_punctured_lower_bound_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          ¬ ∃ δ : ℝ, 0 < δ ∧
              ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
                sqCenteredNorthZonalQuotientRaw g x <
                  sqCenteredNorthZonalQuotientRaw g y := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hgt
  exact
    exists_lt_value_at_anchor_below_half_without_punctured_lower_bound_of_eq_value_at_scale_of_forall_gt_on_halfShell
      hg.2 hgz hu0 ha haEq hgt

theorem exists_fixed_northZonal_gt_value_at_anchor_below_half_without_punctured_upper_bound_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g u0) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g x ∧
          ¬ ∃ δ : ℝ, 0 < δ ∧
              ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
                sqCenteredNorthZonalQuotientRaw g y <
                  sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hlt
  exact
    exists_gt_value_at_anchor_below_half_without_punctured_upper_bound_of_eq_value_at_scale_of_forall_lt_on_halfShell
      hg.2 hgz hu0 ha haEq hlt

theorem exists_fixed_northZonal_next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          sqCenteredNorthZonalQuotientRaw g u0 ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
        (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g u0) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hgt
  exact
    next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_of_eq_value_at_scale_of_forall_gt_on_halfShell
      hg.2 hgz hu0 ha haEq hgt

theorem exists_fixed_northZonal_next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          sqCenteredNorthZonalQuotientRaw g u0 ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
        (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
            sqCenteredNorthZonalQuotientRaw g u0 <
              sqCenteredNorthZonalQuotientRaw g v) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hgt
  exact
    next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
      hg.2 hgz hu0 ha haEq hgt

theorem exists_fixed_northZonal_next_halfShell_bracket_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_punctured_lower_bound_above_below_half_anchor_witnesses_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        (∀ {x : unitIcc}, 0 < x.1 → x.1 < a.1 / 2 →
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g u0 →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
              sqCenteredNorthZonalQuotientRaw g x <
                sqCenteredNorthZonalQuotientRaw g y) →
        ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          sqCenteredNorthZonalQuotientRaw g u0 ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hgt hpre
  exact
    next_halfShell_bracket_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_punctured_lower_bound_above_below_half_anchor_witnesses
      hg.2 hgz hu0 ha haEq hgt hpre

theorem exists_fixed_northZonal_next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g u0) →
        (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          sqCenteredNorthZonalQuotientRaw g u0 ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
        (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g u0) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hlt
  exact
    next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_of_eq_value_at_scale_of_forall_lt_on_halfShell
      hg.2 hgz hu0 ha haEq hlt

theorem exists_fixed_northZonal_next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g u0) →
        (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          sqCenteredNorthZonalQuotientRaw g u0 ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
        (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
            sqCenteredNorthZonalQuotientRaw g v <
              sqCenteredNorthZonalQuotientRaw g u0) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hlt
  exact
    next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell
      hg.2 hgz hu0 ha haEq hlt

theorem exists_fixed_northZonal_next_halfShell_bracket_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_punctured_upper_bound_below_below_half_anchor_witnesses_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g u0) →
        (∀ {x : unitIcc}, 0 < x.1 → x.1 < a.1 / 2 →
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g x →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
              sqCenteredNorthZonalQuotientRaw g y <
                sqCenteredNorthZonalQuotientRaw g x) →
        ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          sqCenteredNorthZonalQuotientRaw g u0 ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hlt hpre
  exact
    next_halfShell_bracket_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_punctured_upper_bound_below_below_half_anchor_witnesses
      hg.2 hgz hu0 ha haEq hlt hpre

theorem exists_fixed_northZonal_eq_value_at_one_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hgt
  exact
    exists_eq_value_at_one_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
      hg.2 hgz ha haEq hgt

theorem exists_fixed_northZonal_eq_value_at_one_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc) →
        ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hlt
  exact
    exists_eq_value_at_one_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell
      hg.2 hgz ha haEq hlt

theorem exists_fixed_northZonal_lt_value_at_one_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          ∀ {δ : ℝ}, 0 < δ →
            ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
              sqCenteredNorthZonalQuotientRaw g y =
                sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hgt
  exact
    exists_lt_value_at_one_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_gt_on_halfShell
      hg.2 hgz ha haEq hgt

theorem exists_fixed_northZonal_gt_value_at_one_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g x ∧
          ∀ {δ : ℝ}, 0 < δ →
            ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
              sqCenteredNorthZonalQuotientRaw g y =
                sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hlt
  exact
    exists_gt_value_at_one_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_lt_on_halfShell
      hg.2 hgz ha haEq hlt

theorem exists_fixed_northZonal_lt_value_at_one_below_half_without_punctured_lower_bound_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          ¬ ∃ δ : ℝ, 0 < δ ∧
              ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
                sqCenteredNorthZonalQuotientRaw g x <
                  sqCenteredNorthZonalQuotientRaw g y := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hgt
  exact
    exists_lt_value_at_one_below_half_without_punctured_lower_bound_of_eq_value_at_scale_of_forall_gt_on_halfShell
      hg.2 hgz ha haEq hgt

theorem exists_fixed_northZonal_gt_value_at_one_below_half_without_punctured_upper_bound_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g x ∧
          ¬ ∃ δ : ℝ, 0 < δ ∧
              ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
                sqCenteredNorthZonalQuotientRaw g y <
                  sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hlt
  exact
    exists_gt_value_at_one_below_half_without_punctured_upper_bound_of_eq_value_at_scale_of_forall_lt_on_halfShell
      hg.2 hgz ha haEq hlt

theorem exists_fixed_northZonal_next_halfShell_bracket_or_eq_value_at_one_below_quarter_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
        (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hgt
  exact
    next_halfShell_bracket_or_eq_value_at_one_below_quarter_of_eq_value_at_scale_of_forall_gt_on_halfShell
      hg.2 hgz ha haEq hgt

theorem exists_fixed_northZonal_next_halfShell_bracket_or_eq_value_at_one_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
        (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
              sqCenteredNorthZonalQuotientRaw g v) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hgt
  exact
    next_halfShell_bracket_or_eq_value_at_one_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
      hg.2 hgz ha haEq hgt

theorem exists_fixed_northZonal_next_halfShell_bracket_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_punctured_lower_bound_above_below_half_witnesses_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        (∀ {x : unitIcc}, 0 < x.1 → x.1 < a.1 / 2 →
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
              sqCenteredNorthZonalQuotientRaw g x <
                sqCenteredNorthZonalQuotientRaw g y) →
        ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hgt hpre
  exact
    next_halfShell_bracket_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_punctured_lower_bound_above_below_half_witnesses
      hg.2 hgz ha haEq hgt hpre

theorem exists_fixed_northZonal_next_halfShell_bracket_or_eq_value_at_one_below_quarter_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc) →
        (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
        (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hlt
  exact
    next_halfShell_bracket_or_eq_value_at_one_below_quarter_of_eq_value_at_scale_of_forall_lt_on_halfShell
      hg.2 hgz ha haEq hlt

theorem exists_fixed_northZonal_next_halfShell_bracket_or_eq_value_at_one_below_quarter_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc) →
        (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
        (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
          sqCenteredNorthZonalQuotientRaw g u =
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
            sqCenteredNorthZonalQuotientRaw g v <
              sqCenteredNorthZonalQuotientRaw g oneUnitIcc) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hlt
  exact
    next_halfShell_bracket_or_eq_value_at_one_below_quarter_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell
      hg.2 hgz ha haEq hlt

theorem exists_fixed_northZonal_next_halfShell_bracket_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_punctured_upper_bound_below_below_half_witnesses_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc) →
        (∀ {x : unitIcc}, 0 < x.1 → x.1 < a.1 / 2 →
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g x →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
              sqCenteredNorthZonalQuotientRaw g y <
                sqCenteredNorthZonalQuotientRaw g x) →
        ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hlt hpre
  exact
    next_halfShell_bracket_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_punctured_upper_bound_below_below_half_witnesses
      hg.2 hgz ha haEq hlt hpre

theorem exists_fixed_northZonal_small_shell_uniform_near_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε δ : ℝ}, 0 < ε → ε < ‖g sphereE3‖ → 0 < δ →
        ∃ a : unitIcc, ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
          0 < a.1 ∧
          a.1 < δ ∧
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          sqCenteredNorthZonalQuotientRaw g a = sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
                sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
              ≤ 4 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
  rcases exists_fixed_northZonal_sqquotientRaw_shell_uniform_near_top_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, hshell⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro ε δ hε hεpole hδ
  rcases hshell hε hεpole with ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hshellhq⟩
  by_cases hconst :
      ∀ {u : unitIcc}, 0 < u.1 →
        sqCenteredNorthZonalQuotientRaw g u = sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  · let a : unitIcc := ⟨min (δ / 2) (1 / 2 : ℝ), by
        constructor
        · exact le_of_lt (lt_min (by positivity) (by norm_num))
        · exact le_trans (min_le_right _ _) (by norm_num)⟩
    have haPos : 0 < a.1 := by
      dsimp [a]
      exact lt_min (by positivity) (by norm_num)
    have haLt : a.1 < δ := by
      dsimp [a]
      have hle : min (δ / 2) (1 / 2 : ℝ) ≤ δ / 2 := min_le_left _ _
      linarith
    refine ⟨a, h, q, haPos, haLt, hhHigh, hhz, hhpole, hq, hdist, ?_, ?_⟩
    · exact hconst haPos
    · intro u hu
      have huPos : 0 < u.1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hu
      have hsPos : 0 < (sqScaleMap a u).1 := by
        change 0 < a.1 * u.1
        exact mul_pos haPos huPos
      rw [hconst hsPos]
      have hnonneg :
          0 ≤ 4 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) := by
        have htail_nonneg : 0 ≤ sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
          unfold sqProfileTailAbsSum
          exact Finset.sum_nonneg (by intro n hn; exact abs_nonneg _)
        have hinner_nonneg :
            0 ≤ (2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
          have hdiv_nonneg : 0 ≤ (2 * ε) / a.1 := by positivity
          have hmul_nonneg : 0 ≤ a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
            exact mul_nonneg (le_of_lt haPos) htail_nonneg
          linarith
        nlinarith
      simpa using hnonneg
  · push_neg at hconst
    rcases exists_eq_value_at_one_near_zero_of_not_const_of_mem_frame hg.2 hgz hconst hδ with
      ⟨a, haPos, haLt, haEq⟩
    refine ⟨a, h, q, haPos, haLt, hhHigh, hhz, hhpole, hq, hdist, haEq, ?_⟩
    intro u hu
    calc
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
        =
          |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
              sqCenteredNorthZonalQuotientRaw g a| := by rw [haEq]
      _ ≤ 4 * ((2 * ε) / a.1 + a.1 * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) :=
        hshellhq haPos hu

theorem exists_fixed_northZonal_dyadic_shell_eq_value_at_one_arbitrarily_far_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ N : ℕ,
        ∃ n : ℕ, n ≥ N ∧
          ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) =
              sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  rcases exists_fixed_northZonal_eq_value_at_one_near_zero_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, hroot⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro N
  let δ : ℝ := (1 / 2 : ℝ) ^ (N + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  rcases hroot hδ with ⟨u, huPos, huLt, huEq⟩
  have hex : ∃ k : ℕ, ((1 / 2 : ℝ) ^ k) < u.1 := by
    simpa using exists_pow_lt_of_lt_one huPos (by norm_num : (1 / 2 : ℝ) < 1)
  let k : ℕ := Nat.find hex
  have hk_lt : ((1 / 2 : ℝ) ^ k) < u.1 := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hk0
    have : (1 : ℝ) < u.1 := by simpa [k, hk0] using hk_lt
    linarith [u.2.2]
  let n : ℕ := k - 1
  have hnk : n + 1 = k := by
    dsimp [n]
    exact Nat.succ_pred_eq_of_pos (Nat.pos_iff_ne_zero.mpr hk0)
  have hn_lt_u : ((1 / 2 : ℝ) ^ (n + 1)) < u.1 := by
    simpa [hnk] using hk_lt
  have hu_le_n : u.1 ≤ (1 / 2 : ℝ) ^ n := by
    have hnot : ¬ ((1 / 2 : ℝ) ^ n < u.1) := by
      exact Nat.find_min hex (m := n) (by omega)
    linarith
  have hNle : N ≤ n := by
    have huLt' : u.1 < (1 / 2 : ℝ) ^ (N + 1) := by
      simpa [δ] using huLt
    by_contra hlt
    have hnlt' : n + 1 ≤ N := Nat.succ_le_of_lt (lt_of_not_ge hlt)
    have hpow_le : (1 / 2 : ℝ) ^ (N + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (le_trans hnlt' (Nat.le_succ N))
    have : u.1 < (1 / 2 : ℝ) ^ (n + 1) := lt_of_lt_of_le huLt' hpow_le
    exact not_lt_of_ge this.le hn_lt_u
  let v : unitIcc := ⟨u.1 / (dyadicUnitIcc n).1, by
    constructor
    · have hden : 0 < (dyadicUnitIcc n).1 := by
        simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
      positivity
    · have hden : 0 < (dyadicUnitIcc n).1 := by
        simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
      exact (div_le_iff₀ hden).2 (by simpa [dyadicUnitIcc_val] using hu_le_n)⟩
  have hvHalf : (1 / 2 : ℝ) ≤ v.1 := by
    change (1 / 2 : ℝ) ≤ u.1 / (dyadicUnitIcc n).1
    have hden : 0 < (dyadicUnitIcc n).1 := by
      simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
    have hpow :
        (1 / 2 : ℝ) * (dyadicUnitIcc n).1 = (1 / 2 : ℝ) ^ (n + 1) := by
      simp [dyadicUnitIcc_val, pow_succ]
      ring
    have hnum : (1 / 2 : ℝ) * (dyadicUnitIcc n).1 ≤ u.1 := by
      calc
        (1 / 2 : ℝ) * (dyadicUnitIcc n).1 = (1 / 2 : ℝ) ^ (n + 1) := hpow
        _ ≤ u.1 := hn_lt_u.le
    exact (le_div_iff₀ hden).2 hnum
  have hEqScale : sqScaleMap (dyadicUnitIcc n) v = u := by
    apply Subtype.ext
    change (dyadicUnitIcc n).1 * v.1 = u.1
    simp [v]
    field_simp [show ((dyadicUnitIcc n).1 : ℝ) ≠ 0 by
      simp [dyadicUnitIcc, pow_pos]]
  refine ⟨n, hNle, v, hvHalf, ?_⟩
  simpa [hEqScale] using huEq

theorem exists_fixed_northZonal_dyadic_shell_bracket_value_at_one_arbitrarily_far_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ N : ℕ,
        ∃ n : ℕ, n ≥ N ∧
          ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) := by
  rcases exists_fixed_northZonal_dyadic_shell_eq_value_at_one_arbitrarily_far_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, hvalue⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro N
  rcases hvalue N with ⟨n, hn, v, hv, hvEq⟩
  refine ⟨n, hn, v, v, hv, hv, ?_, ?_⟩
  · simpa [hvEq]
  · simpa [hvEq]

theorem exists_fixed_northZonal_dyadic_shell_eq_value_at_anchor_arbitrarily_far_of_ne_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 : unitIcc}, 0 < u0.1 →
        sqCenteredNorthZonalQuotientRaw g u0 ≠
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        ∀ N : ℕ,
          ∃ n : ℕ, n ≥ N ∧
            ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) =
                sqCenteredNorthZonalQuotientRaw g u0 := by
  rcases exists_fixed_northZonal_eq_value_at_anchor_near_zero_of_ne_value_at_one_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, hroot⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 hu0 hune N
  let δ : ℝ := (1 / 2 : ℝ) ^ (N + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  rcases hroot hu0 hune hδ with ⟨u, huPos, huLt, huEq⟩
  have hex : ∃ k : ℕ, ((1 / 2 : ℝ) ^ k) < u.1 := by
    simpa using exists_pow_lt_of_lt_one huPos (by norm_num : (1 / 2 : ℝ) < 1)
  let k : ℕ := Nat.find hex
  have hk_lt : ((1 / 2 : ℝ) ^ k) < u.1 := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hk0
    have : (1 : ℝ) < u.1 := by simpa [k, hk0] using hk_lt
    linarith [u.2.2]
  let n : ℕ := k - 1
  have hnk : n + 1 = k := by
    dsimp [n]
    exact Nat.succ_pred_eq_of_pos (Nat.pos_iff_ne_zero.mpr hk0)
  have hn_lt_u : ((1 / 2 : ℝ) ^ (n + 1)) < u.1 := by
    simpa [hnk] using hk_lt
  have hu_le_n : u.1 ≤ (1 / 2 : ℝ) ^ n := by
    have hnot : ¬ ((1 / 2 : ℝ) ^ n < u.1) := by
      exact Nat.find_min hex (m := n) (by omega)
    linarith
  have hNle : N ≤ n := by
    have huLt' : u.1 < (1 / 2 : ℝ) ^ (N + 1) := by
      simpa [δ] using huLt
    by_contra hlt
    have hnlt' : n + 1 ≤ N := Nat.succ_le_of_lt (lt_of_not_ge hlt)
    have hpow_le : (1 / 2 : ℝ) ^ (N + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (le_trans hnlt' (Nat.le_succ N))
    have : u.1 < (1 / 2 : ℝ) ^ (n + 1) := lt_of_lt_of_le huLt' hpow_le
    exact not_lt_of_ge this.le hn_lt_u
  let v : unitIcc := ⟨u.1 / (dyadicUnitIcc n).1, by
    constructor
    · have hden : 0 < (dyadicUnitIcc n).1 := by
        simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
      positivity
    · have hden : 0 < (dyadicUnitIcc n).1 := by
        simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
      exact (div_le_iff₀ hden).2 (by simpa [dyadicUnitIcc_val] using hu_le_n)⟩
  have hvHalf : (1 / 2 : ℝ) ≤ v.1 := by
    change (1 / 2 : ℝ) ≤ u.1 / (dyadicUnitIcc n).1
    have hden : 0 < (dyadicUnitIcc n).1 := by
      simp [dyadicUnitIcc, dyadicUnitIcc_val, pow_pos]
    have hpow :
        (1 / 2 : ℝ) * (dyadicUnitIcc n).1 = (1 / 2 : ℝ) ^ (n + 1) := by
      simp [dyadicUnitIcc_val, pow_succ]
      ring
    have hnum : (1 / 2 : ℝ) * (dyadicUnitIcc n).1 ≤ u.1 := by
      calc
        (1 / 2 : ℝ) * (dyadicUnitIcc n).1 = (1 / 2 : ℝ) ^ (n + 1) := hpow
        _ ≤ u.1 := hn_lt_u.le
    exact (le_div_iff₀ hden).2 hnum
  have hEqScale : sqScaleMap (dyadicUnitIcc n) v = u := by
    apply Subtype.ext
    change (dyadicUnitIcc n).1 * v.1 = u.1
    simp [v]
    field_simp [show ((dyadicUnitIcc n).1 : ℝ) ≠ 0 by
      simp [dyadicUnitIcc, pow_pos]]
  refine ⟨n, hNle, v, hvHalf, ?_⟩
  simpa [hEqScale] using huEq

theorem exists_fixed_northZonal_dyadic_shell_bracket_value_at_anchor_arbitrarily_far_of_ne_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 : unitIcc}, 0 < u0.1 →
        sqCenteredNorthZonalQuotientRaw g u0 ≠
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        ∀ N : ℕ,
          ∃ n : ℕ, n ≥ N ∧
            ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
                sqCenteredNorthZonalQuotientRaw g u0 ∧
              sqCenteredNorthZonalQuotientRaw g u0 ≤
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) := by
  rcases
      exists_fixed_northZonal_dyadic_shell_eq_value_at_anchor_arbitrarily_far_of_ne_value_at_one_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, hvalue⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 hu0 hune N
  rcases hvalue hu0 hune N with ⟨n, hn, v, hv, hvEq⟩
  refine ⟨n, hn, v, v, hv, hv, ?_, ?_⟩
  · simpa [hvEq]
  · simpa [hvEq]

theorem exists_fixed_northZonal_not_eventually_no_dyadic_shell_bracket_value_at_anchor_of_ne_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 : unitIcc}, 0 < u0.1 →
        sqCenteredNorthZonalQuotientRaw g u0 ≠
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        ¬ ∃ N : ℕ,
          ∀ n ≥ N,
            ¬ ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
                sqCenteredNorthZonalQuotientRaw g u0 ∧
              sqCenteredNorthZonalQuotientRaw g u0 ≤
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 hu0 hune hno
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_no_dyadic_shell_bracket_value_at_anchor
      (g := g) hg hgne hgz hu0 hno

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_gt_on_dyadic_shell_value_at_anchor
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    {u0 : unitIcc}
    (hu0 : 0 < u0.1)
    (hgt :
      ∃ N : ℕ,
        ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u)) :
    False := by
  rcases hgt with ⟨N, hN⟩
  apply
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_no_dyadic_shell_bracket_value_at_anchor
      (g := g) hg hgne hgz hu0
  refine ⟨N, ?_⟩
  intro n hn hbr
  rcases hbr with ⟨u, v, hu, hv, hule, hcve⟩
  have hgtu :
      sqCenteredNorthZonalQuotientRaw g u0 <
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) :=
    hN n hn hu
  linarith

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_lt_on_dyadic_shell_value_at_anchor
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    {u0 : unitIcc}
    (hu0 : 0 < u0.1)
    (hlt :
      ∃ N : ℕ,
        ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
            sqCenteredNorthZonalQuotientRaw g u0) :
    False := by
  rcases hlt with ⟨N, hN⟩
  apply
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_no_dyadic_shell_bracket_value_at_anchor
      (g := g) hg hgne hgz hu0
  refine ⟨N, ?_⟩
  intro n hn hbr
  rcases hbr with ⟨u, v, hu, hv, hule, hcve⟩
  have hltv :
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) <
        sqCenteredNorthZonalQuotientRaw g u0 :=
    hN n hn hv
  linarith

theorem eventually_forall_gt_on_dyadic_shell_value_at_lower_anchor_of_dyadic_shell_pair_uniform_near_and_tail_bracket_value_at_anchor_or_forall_gt
    {g : C(spherePoint3, ℝ)} {u0 x : unitIcc}
    (hxc :
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g u0)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (htail :
      ∃ N : ℕ,
        ∀ n ≥ N,
          (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g u0 ∧
            sqCenteredNorthZonalQuotientRaw g u0 ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
          (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g u0 <
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u))) :
    ∃ N : ℕ,
      ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
        sqCenteredNorthZonalQuotientRaw g x <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) := by
  let ε : ℝ :=
    (sqCenteredNorthZonalQuotientRaw g u0 - sqCenteredNorthZonalQuotientRaw g x) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  rcases hshell hε with ⟨N0, hN0⟩
  rcases htail with ⟨N1, hN1⟩
  refine ⟨max N0 N1, ?_⟩
  intro n hn u hu
  rcases hN1 n (le_trans (le_max_right _ _) hn) with hbr | hgt
  · rcases hbr with ⟨u0', v0', hu0', hv0', hule, hcve⟩
    have hclose :=
      hN0 n (le_trans (le_max_left _ _) hn) (u := u) (v := v0') hu hv0'
    have hlower :
        sqCenteredNorthZonalQuotientRaw g u0 - ε <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) := by
      have hleft := (abs_lt.mp hclose).1
      linarith
    dsimp [ε] at hlower
    linarith
  · exact lt_trans hxc (hgt hu)

theorem eventually_forall_lt_on_dyadic_shell_value_at_upper_anchor_of_dyadic_shell_pair_uniform_near_and_tail_bracket_value_at_anchor_or_forall_lt
    {g : C(spherePoint3, ℝ)} {u0 x : unitIcc}
    (hu0x :
      sqCenteredNorthZonalQuotientRaw g u0 <
        sqCenteredNorthZonalQuotientRaw g x)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (htail :
      ∃ N : ℕ,
        ∀ n ≥ N,
          (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g u0 ∧
            sqCenteredNorthZonalQuotientRaw g u0 ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
          (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
              sqCenteredNorthZonalQuotientRaw g u0)) :
    ∃ N : ℕ,
      ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
          sqCenteredNorthZonalQuotientRaw g x := by
  let ε : ℝ :=
    (sqCenteredNorthZonalQuotientRaw g x - sqCenteredNorthZonalQuotientRaw g u0) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  rcases hshell hε with ⟨N0, hN0⟩
  rcases htail with ⟨N1, hN1⟩
  refine ⟨max N0 N1, ?_⟩
  intro n hn u hu
  rcases hN1 n (le_trans (le_max_right _ _) hn) with hbr | hlt
  · rcases hbr with ⟨u0', v0', hu0', hv0', hule, hcve⟩
    have hclose :=
      hN0 n (le_trans (le_max_left _ _) hn) (u := u) (v := u0') hu hu0'
    have hupper :
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
          sqCenteredNorthZonalQuotientRaw g u0 + ε := by
      have hright := (abs_lt.mp hclose).2
      linarith
    dsimp [ε] at hupper
    linarith
  · exact lt_trans (hlt hu) hu0x

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_tail_bracket_value_at_anchor_or_forall_gt
    {g : C(spherePoint3, ℝ)} {u0 x : unitIcc}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hx : 0 < x.1)
    (hxc :
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g u0)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (htail :
      ∃ N : ℕ,
        ∀ n ≥ N,
          (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g u0 ∧
            sqCenteredNorthZonalQuotientRaw g u0 ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
          (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g u0 <
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u))) :
    False := by
  have hgt :=
    eventually_forall_gt_on_dyadic_shell_value_at_lower_anchor_of_dyadic_shell_pair_uniform_near_and_tail_bracket_value_at_anchor_or_forall_gt
      hxc hshell htail
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_gt_on_dyadic_shell_value_at_anchor
      (g := g) hg hgne hgz hx hgt

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_tail_bracket_value_at_anchor_or_forall_lt
    {g : C(spherePoint3, ℝ)} {u0 x : unitIcc}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hx : 0 < x.1)
    (hu0x :
      sqCenteredNorthZonalQuotientRaw g u0 <
        sqCenteredNorthZonalQuotientRaw g x)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (htail :
      ∃ N : ℕ,
        ∀ n ≥ N,
          (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g u0 ∧
            sqCenteredNorthZonalQuotientRaw g u0 ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
          (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
              sqCenteredNorthZonalQuotientRaw g u0)) :
    False := by
  have hlt :=
    eventually_forall_lt_on_dyadic_shell_value_at_upper_anchor_of_dyadic_shell_pair_uniform_near_and_tail_bracket_value_at_anchor_or_forall_lt
      hu0x hshell htail
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_lt_on_dyadic_shell_value_at_anchor
      (g := g) hg hgne hgz hx hlt

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_eq_value_at_scale_of_forall_gt_on_halfShell_and_tail_bracket_value_at_anchor_or_forall_gt
    {g : C(spherePoint3, ℝ)} {u0 a : unitIcc}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u))
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (htail :
      ∃ N : ℕ,
        ∀ n ≥ N,
          (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g u0 ∧
            sqCenteredNorthZonalQuotientRaw g u0 ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
          (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g u0 <
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u))) :
    False := by
  rcases
      exists_lt_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hg.2 hgz ha haEq hgt with
    ⟨x, hxPos, _, hxLt⟩
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_tail_bracket_value_at_anchor_or_forall_gt
      (g := g) hg hgne hgz hxPos hxLt hshell
      htail

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_eq_value_at_scale_of_forall_lt_on_halfShell_and_tail_bracket_value_at_anchor_or_forall_lt
    {g : C(spherePoint3, ℝ)} {u0 a : unitIcc}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g u0)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (htail :
      ∃ N : ℕ,
        ∀ n ≥ N,
          (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
              sqCenteredNorthZonalQuotientRaw g u0 ∧
            sqCenteredNorthZonalQuotientRaw g u0 ≤
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
          (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
              sqCenteredNorthZonalQuotientRaw g u0)) :
    False := by
  rcases
      exists_gt_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell
        hg.2 hgz ha haEq hlt with
    ⟨x, hxPos, _, hxGt⟩
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_pair_uniform_near_and_tail_bracket_value_at_anchor_or_forall_lt
      (g := g) hg hgne hgz hxPos hxGt hshell
      htail

theorem exists_fixed_northZonal_not_eventually_forall_gt_on_dyadic_shell_value_at_anchor_of_ne_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 : unitIcc}, 0 < u0.1 →
        sqCenteredNorthZonalQuotientRaw g u0 ≠
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        ¬ ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g u0 <
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 hu0 hune hgt
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_gt_on_dyadic_shell_value_at_anchor
      (g := g) hg hgne hgz hu0 hgt

theorem exists_fixed_northZonal_not_eventually_forall_lt_on_dyadic_shell_value_at_anchor_of_ne_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 : unitIcc}, 0 < u0.1 →
        sqCenteredNorthZonalQuotientRaw g u0 ≠
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        ¬ ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
              sqCenteredNorthZonalQuotientRaw g u0 := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 hu0 hune hlt
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_lt_on_dyadic_shell_value_at_anchor
      (g := g) hg hgne hgz hu0 hlt

theorem exists_fixed_northZonal_not_eventually_forall_gt_on_dyadic_shell_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ¬ ∃ N : ℕ,
        ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro hgt
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_gt_on_dyadic_shell_value_at_anchor
      (g := g) hg hgne hgz (by norm_num [oneUnitIcc]) hgt

theorem exists_fixed_northZonal_not_eventually_forall_lt_on_dyadic_shell_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ¬ ∃ N : ℕ,
        ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro hlt
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_lt_on_dyadic_shell_value_at_anchor
      (g := g) hg hgne hgz (by norm_num [oneUnitIcc]) hlt

def DyadicShellBracketValueAt (g : C(spherePoint3, ℝ)) (c : ℝ) (n : ℕ) : Prop :=
  ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
    sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤ c ∧
    c ≤ sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)

def DyadicShellForallGtValueAt (g : C(spherePoint3, ℝ)) (c : ℝ) (n : ℕ) : Prop :=
  ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
    c < sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u)

def DyadicShellForallLtValueAt (g : C(spherePoint3, ℝ)) (c : ℝ) (n : ℕ) : Prop :=
  ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
    sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) < c

def DyadicShellTailBracketOrForallGtAt (g : C(spherePoint3, ℝ)) (c : ℝ) : Prop :=
  ∃ N : ℕ,
    ∀ n ≥ N, DyadicShellBracketValueAt g c n ∨ DyadicShellForallGtValueAt g c n

def DyadicShellTailBracketOrForallLtAt (g : C(spherePoint3, ℝ)) (c : ℝ) : Prop :=
  ∃ N : ℕ,
    ∀ n ≥ N, DyadicShellBracketValueAt g c n ∨ DyadicShellForallLtValueAt g c n

theorem exists_fixed_northZonal_not_eventually_no_dyadic_shell_bracket_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ¬ ∃ N : ℕ,
        ∀ n ≥ N,
          ¬ DyadicShellBracketValueAt
            g
            (sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
            n := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro hno
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_no_dyadic_shell_bracket_value_at_one
      hg hgne hgz (by simpa [DyadicShellBracketValueAt] using hno)

theorem arbitrarily_far_aligned_small_upper_half_bound_around_value_at_anchor_of_dyadic_shell_pair_uniform_near_and_not_eventually_no_dyadic_shell_bracket_value_at_anchor
    {g : C(spherePoint3, ℝ)} {u0 : unitIcc}
    (hu0 : 0 < u0.1)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε)
    (hnotNoBracket :
      ¬ ∃ N : ℕ,
        ∀ n ≥ N, ¬ DyadicShellBracketValueAt g (sqCenteredNorthZonalQuotientRaw g u0) n) :
    ∀ {ε : ℝ}, 0 < ε → ∀ N : ℕ,
      ∃ n : ℕ, n ≥ N ∧
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
              sqCenteredNorthZonalQuotientRaw g u0| < ε) ∧
        DyadicShellBracketValueAt g (sqCenteredNorthZonalQuotientRaw g u0) n := by
  intro ε hε N
  rcases hshell hε with ⟨Nshell, hNshell⟩
  have hbrExists :
      ∃ n : ℕ, n ≥ max N Nshell ∧
        DyadicShellBracketValueAt g (sqCenteredNorthZonalQuotientRaw g u0) n := by
    by_contra hno
    apply hnotNoBracket
    refine ⟨max N Nshell, ?_⟩
    intro n hn hbr
    exact hno ⟨n, hn, hbr⟩
  rcases hbrExists with ⟨n, hn, hbr⟩
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_, hbr⟩
  intro u hu
  rcases hbr with ⟨u', v', hu', hv', hu'le, hcv'⟩
  rcases
      exists_eq_const_on_dyadic_shell_of_le_ge
        (g := g)
        (c := sqCenteredNorthZonalQuotientRaw g u0)
        (n := n)
        hu' hv' hu'le hcv' with
    ⟨v, hv, hvEq⟩
  have hpair := hNshell n (le_trans (le_max_right _ _) hn) hu hv
  simpa [hvEq] using hpair

theorem arbitrarily_far_aligned_small_upper_half_bound_around_value_at_one_of_dyadic_shell_pair_uniform_near_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u v : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)| < ε) :
    ∀ {ε : ℝ}, 0 < ε → ∀ N : ℕ,
      ∃ n : ℕ, n ≥ N ∧
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
              sqCenteredNorthZonalQuotientRaw g oneUnitIcc| < ε) ∧
        DyadicShellBracketValueAt g (sqCenteredNorthZonalQuotientRaw g oneUnitIcc) n := by
  have hnotNoBracket :
      ¬ ∃ N : ℕ,
        ∀ n ≥ N,
          ¬ DyadicShellBracketValueAt
            g
            (sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
            n := by
    intro hno
    exact
      False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_no_dyadic_shell_bracket_value_at_one
        hg hgne hgz (by simpa [DyadicShellBracketValueAt] using hno)
  intro ε hε N
  simpa using
    (arbitrarily_far_aligned_small_upper_half_bound_around_value_at_anchor_of_dyadic_shell_pair_uniform_near_and_not_eventually_no_dyadic_shell_bracket_value_at_anchor
      (g := g)
      (u0 := oneUnitIcc)
      (hu0 := by simp [oneUnitIcc])
      hshell
      hnotNoBracket
      (ε := ε)
      hε
      N)

theorem dyadic_shell_bracket_or_forall_gt_on_next_of_forall_gt
    {g : C(spherePoint3, ℝ)} {c : ℝ} {n : ℕ}
    (hgt : DyadicShellForallGtValueAt g c n) :
    DyadicShellBracketValueAt g c (n + 1) ∨
      DyadicShellForallGtValueAt g c (n + 1) := by
  by_cases hbr : DyadicShellBracketValueAt g c (n + 1)
  · exact Or.inl hbr
  · right
    intro u hu
    exact
      forall_gt_on_next_dyadic_shell_of_forall_gt_of_not_bracket
        (g := g) (c := c) (n := n)
        (by
          intro v hv
          exact hgt hv)
        (by simpa [DyadicShellBracketValueAt] using hbr)
        (u := u)
        hu

theorem dyadic_shell_bracket_or_forall_lt_on_next_of_forall_lt
    {g : C(spherePoint3, ℝ)} {c : ℝ} {n : ℕ}
    (hlt : DyadicShellForallLtValueAt g c n) :
    DyadicShellBracketValueAt g c (n + 1) ∨
      DyadicShellForallLtValueAt g c (n + 1) := by
  by_cases hbr : DyadicShellBracketValueAt g c (n + 1)
  · exact Or.inl hbr
  · right
    intro u hu
    exact
      forall_lt_on_next_dyadic_shell_of_forall_lt_of_not_bracket
        (g := g) (c := c) (n := n)
        (by
          intro v hv
          exact hlt hv)
        (by simpa [DyadicShellBracketValueAt] using hbr)
        (u := u)
        hu

theorem arbitrarily_far_forall_gt_or_arbitrarily_far_forall_lt_of_not_eventually_bracket
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (hnotBracket :
      ¬ ∃ N : ℕ, ∀ n ≥ N, DyadicShellBracketValueAt g c n) :
    (∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧ DyadicShellForallGtValueAt g c n) ∨
      (∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧ DyadicShellForallLtValueAt g c n) := by
  classical
  by_cases hgtInf :
      ∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧ DyadicShellForallGtValueAt g c n
  · exact Or.inl hgtInf
  · push_neg at hgtInf
    by_cases hltInf :
        ∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧ DyadicShellForallLtValueAt g c n
    · exact Or.inr hltInf
    · push_neg at hltInf
      rcases hgtInf with ⟨Ngt, hNgt⟩
      rcases hltInf with ⟨Nlt, hNlt⟩
      exfalso
      apply hnotBracket
      refine ⟨max Ngt Nlt, ?_⟩
      intro n hn
      by_contra hbr
      rcases
          forall_gt_or_forall_lt_on_dyadic_shell_of_not_bracket
            (g := g) (c := c) (n := n)
            (by simpa [DyadicShellBracketValueAt] using hbr) with hgt | hlt
      · exact
          (hNgt n (le_trans (le_max_left _ _) hn))
            (by
              intro u hu
              exact hgt hu)
      · exact
          (hNlt n (le_trans (le_max_right _ _) hn))
            (by
              intro u hu
              exact hlt hu)

theorem exists_forall_gt_run_then_next_bracket_from_bad_shell
    {g : C(spherePoint3, ℝ)} {c : ℝ} {q : ℕ}
    (hnotEventual :
      ¬ ∃ N : ℕ, ∀ n ≥ N, DyadicShellForallGtValueAt g c n)
    (hgtq : DyadicShellForallGtValueAt g c q) :
    ∃ n : ℕ, n ≥ q ∧
      (∀ k : ℕ, q ≤ k → k ≤ n → DyadicShellForallGtValueAt g c k) ∧
      DyadicShellBracketValueAt g c (n + 1) := by
  classical
  have hbrExists : ∃ m : ℕ, m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := by
    by_contra hno
    have hno' : ∀ m : ℕ, m ≥ q + 1 → ¬ DyadicShellBracketValueAt g c m := by
      intro m hm hbr
      exact hno ⟨m, hm, hbr⟩
    have hgtTailFromQ : ∀ n : ℕ, n ≥ q → DyadicShellForallGtValueAt g c n := by
      intro n hnq
      have hgtFromOffset : ∀ t : ℕ, DyadicShellForallGtValueAt g c (q + t) := by
        intro t
        induction' t with t ht
        · intro u hu
          exact hgtq hu
        · have hnext :=
            dyadic_shell_bracket_or_forall_gt_on_next_of_forall_gt
              (n := q + t) ht
          rcases hnext with hbr | hgtNext
          · exfalso
            exact hno' (q + t + 1) (by omega) hbr
          · intro u hu
            exact hgtNext hu
      intro u hu
      have hEq : q + (n - q) = n := by omega
      have h := hgtFromOffset (n - q) (u := u) hu
      rw [hEq] at h
      exact h
    exact hnotEventual ⟨q, hgtTailFromQ⟩
  let m : ℕ := Nat.find hbrExists
  have hmProp : m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := Nat.find_spec hbrExists
  have hmBr : DyadicShellBracketValueAt g c m := hmProp.2
  refine ⟨m - 1, by omega, ?_, ?_⟩
  · intro k hkq hkm
    have hgtRunFromOffset :
        ∀ t : ℕ, q + t ≤ m - 1 → DyadicShellForallGtValueAt g c (q + t) := by
      intro t
      induction' t with t ht
      · intro _ u hu
        exact hgtq hu
      · intro hle
        have hprevLe : q + t ≤ m - 1 := by omega
        have hnext :=
          dyadic_shell_bracket_or_forall_gt_on_next_of_forall_gt
            (n := q + t) (ht hprevLe)
        rcases hnext with hbr | hgtNext
        · exfalso
          have hnotPair :
              ¬ (q + t + 1 ≥ q + 1 ∧ DyadicShellBracketValueAt g c (q + t + 1)) := by
            exact Nat.find_min hbrExists (m := q + t + 1) (by omega)
          exact hnotPair ⟨by omega, hbr⟩
        · intro u hu
          exact hgtNext hu
    intro u hu
    have hkEq : q + (k - q) = k := by omega
    have h := hgtRunFromOffset (k - q) (by omega) (u := u) hu
    rw [hkEq] at h
    exact h
  · have hmEq : m - 1 + 1 = m := by omega
    simpa only [hmEq] using hmBr

theorem exists_forall_lt_run_then_next_bracket_from_bad_shell
    {g : C(spherePoint3, ℝ)} {c : ℝ} {q : ℕ}
    (hnotEventual :
      ¬ ∃ N : ℕ, ∀ n ≥ N, DyadicShellForallLtValueAt g c n)
    (hltq : DyadicShellForallLtValueAt g c q) :
    ∃ n : ℕ, n ≥ q ∧
      (∀ k : ℕ, q ≤ k → k ≤ n → DyadicShellForallLtValueAt g c k) ∧
      DyadicShellBracketValueAt g c (n + 1) := by
  classical
  have hbrExists : ∃ m : ℕ, m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := by
    by_contra hno
    have hno' : ∀ m : ℕ, m ≥ q + 1 → ¬ DyadicShellBracketValueAt g c m := by
      intro m hm hbr
      exact hno ⟨m, hm, hbr⟩
    have hltTailFromQ : ∀ n : ℕ, n ≥ q → DyadicShellForallLtValueAt g c n := by
      intro n hnq
      have hltFromOffset : ∀ t : ℕ, DyadicShellForallLtValueAt g c (q + t) := by
        intro t
        induction' t with t ht
        · intro u hu
          exact hltq hu
        · have hnext :=
            dyadic_shell_bracket_or_forall_lt_on_next_of_forall_lt
              (n := q + t) ht
          rcases hnext with hbr | hltNext
          · exfalso
            exact hno' (q + t + 1) (by omega) hbr
          · intro u hu
            exact hltNext hu
      intro u hu
      have hEq : q + (n - q) = n := by omega
      have h := hltFromOffset (n - q) (u := u) hu
      rw [hEq] at h
      exact h
    exact hnotEventual ⟨q, hltTailFromQ⟩
  let m : ℕ := Nat.find hbrExists
  have hmProp : m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := Nat.find_spec hbrExists
  have hmBr : DyadicShellBracketValueAt g c m := hmProp.2
  refine ⟨m - 1, by omega, ?_, ?_⟩
  · intro k hkq hkm
    have hltRunFromOffset :
        ∀ t : ℕ, q + t ≤ m - 1 → DyadicShellForallLtValueAt g c (q + t) := by
      intro t
      induction' t with t ht
      · intro _ u hu
        exact hltq hu
      · intro hle
        have hprevLe : q + t ≤ m - 1 := by omega
        have hnext :=
          dyadic_shell_bracket_or_forall_lt_on_next_of_forall_lt
            (n := q + t) (ht hprevLe)
        rcases hnext with hbr | hltNext
        · exfalso
          have hnotPair :
              ¬ (q + t + 1 ≥ q + 1 ∧ DyadicShellBracketValueAt g c (q + t + 1)) := by
            exact Nat.find_min hbrExists (m := q + t + 1) (by omega)
          exact hnotPair ⟨by omega, hbr⟩
        · intro u hu
          exact hltNext hu
    intro u hu
    have hkEq : q + (k - q) = k := by omega
    have h := hltRunFromOffset (k - q) (by omega) (u := u) hu
    rw [hkEq] at h
    exact h
  · have hmEq : m - 1 + 1 = m := by omega
    simpa only [hmEq] using hmBr

theorem exists_forall_gt_then_next_bracket_of_tail_bracket_or_forall_gt
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (htail : DyadicShellTailBracketOrForallGtAt g c)
    (hnotEventual :
      ¬ ∃ N : ℕ, ∀ n ≥ N, DyadicShellForallGtValueAt g c n)
    (hgtInf :
      ∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧ DyadicShellForallGtValueAt g c n) :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      DyadicShellForallGtValueAt g c n ∧
      DyadicShellBracketValueAt g c (n + 1) := by
  classical
  rcases htail with ⟨Ntail, htailN⟩
  intro N
  rcases hgtInf (max N Ntail) with ⟨q, hqGe, hgtq⟩
  have hqN : q ≥ N := le_trans (le_max_left _ _) hqGe
  have hqTail : q ≥ Ntail := le_trans (le_max_right _ _) hqGe
  have hbrExists : ∃ m : ℕ, m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := by
    by_contra hno
    have hno' : ∀ m : ℕ, m ≥ q + 1 → ¬ DyadicShellBracketValueAt g c m := by
      intro m hm hbr
      exact hno ⟨m, hm, hbr⟩
    have hgtTailFromQ : ∀ n : ℕ, n ≥ q → DyadicShellForallGtValueAt g c n := by
      intro n hnq
      by_cases hnEq : n = q
      · simpa [hnEq] using hgtq
      · have hnq1 : n ≥ q + 1 := by omega
        rcases htailN n (le_trans hqTail hnq) with hbr | hgt
        · exfalso
          exact hno' n hnq1 hbr
        · exact hgt
    exact hnotEventual ⟨q, hgtTailFromQ⟩
  let m : ℕ := Nat.find hbrExists
  have hmProp : m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := Nat.find_spec hbrExists
  have hmGe : m ≥ q + 1 := hmProp.1
  have hmBr : DyadicShellBracketValueAt g c m := hmProp.2
  have hmPos : 0 < m := by
    omega
  refine ⟨m - 1, ?_, ?_, ?_⟩
  · omega
  · have hmPredGeQ : m - 1 ≥ q := by omega
    have hprevGeTail : m - 1 ≥ Ntail := le_trans hqTail hmPredGeQ
    have hprevNotBr : ¬ DyadicShellBracketValueAt g c (m - 1) := by
      intro hbrPrev
      by_cases hprevGeQ1 : m - 1 ≥ q + 1
      · have hnotPrev : ¬ ((m - 1) ≥ q + 1 ∧ DyadicShellBracketValueAt g c (m - 1)) := by
          exact Nat.find_min hbrExists (m := m - 1) (by omega)
        exact hnotPrev ⟨hprevGeQ1, hbrPrev⟩
      · have hprevEqQ : m - 1 = q := by omega
        rcases hbrPrev with ⟨u, v, hu, hv, hlu, _⟩
        have hgtu :
            c <
              sqCenteredNorthZonalQuotientRaw g
                (sqScaleMap (dyadicUnitIcc (m - 1)) u) := by
          simpa [hprevEqQ] using hgtq hu
        linarith
    rcases htailN (m - 1) hprevGeTail with hbrPrev | hgtPrev
    · exfalso
      exact hprevNotBr hbrPrev
    · intro u hu
      exact hgtPrev hu
  · have hmEq : m - 1 + 1 = m := by omega
    simpa [hmEq] using hmBr

theorem exists_forall_gt_run_then_next_bracket_of_tail_bracket_or_forall_gt
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (htail : DyadicShellTailBracketOrForallGtAt g c)
    (hnotEventual :
      ¬ ∃ N : ℕ, ∀ n ≥ N, DyadicShellForallGtValueAt g c n)
    (hgtInf :
      ∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧ DyadicShellForallGtValueAt g c n) :
    ∀ N : ℕ, ∃ q n : ℕ, q ≥ N ∧ n ≥ q ∧
      DyadicShellForallGtValueAt g c q ∧
      (∀ k : ℕ, q ≤ k → k ≤ n → DyadicShellForallGtValueAt g c k) ∧
      DyadicShellBracketValueAt g c (n + 1) := by
  classical
  rcases htail with ⟨Ntail, htailN⟩
  intro N
  rcases hgtInf (max N Ntail) with ⟨q, hqGe, hgtq⟩
  have hqN : q ≥ N := le_trans (le_max_left _ _) hqGe
  have hqTail : q ≥ Ntail := le_trans (le_max_right _ _) hqGe
  have hbrExists : ∃ m : ℕ, m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := by
    by_contra hno
    have hno' : ∀ m : ℕ, m ≥ q + 1 → ¬ DyadicShellBracketValueAt g c m := by
      intro m hm hbr
      exact hno ⟨m, hm, hbr⟩
    have hgtTailFromQ : ∀ n : ℕ, n ≥ q → DyadicShellForallGtValueAt g c n := by
      intro n hnq
      by_cases hnEq : n = q
      · simpa [hnEq] using hgtq
      · have hnq1 : n ≥ q + 1 := by omega
        rcases htailN n (le_trans hqTail hnq) with hbr | hgt
        · exfalso
          exact hno' n hnq1 hbr
        · exact hgt
    exact hnotEventual ⟨q, hgtTailFromQ⟩
  let m : ℕ := Nat.find hbrExists
  have hmProp : m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := Nat.find_spec hbrExists
  have hmBr : DyadicShellBracketValueAt g c m := hmProp.2
  have hrun :
      ∀ k : ℕ, q ≤ k → k ≤ m - 1 → DyadicShellForallGtValueAt g c k := by
    intro k hkq hkm1
    by_cases hkEq : k = q
    · simpa [hkEq] using hgtq
    · have hkq1 : k ≥ q + 1 := by omega
      have hkTail : k ≥ Ntail := le_trans hqTail hkq
      have hkNotBr : ¬ DyadicShellBracketValueAt g c k := by
        intro hbrk
        have hkltm : k < m := by omega
        have hnotPair : ¬ (k ≥ q + 1 ∧ DyadicShellBracketValueAt g c k) := by
          exact Nat.find_min hbrExists (m := k) hkltm
        exact hnotPair ⟨hkq1, hbrk⟩
      rcases htailN k hkTail with hbr | hgt
      · exfalso
        exact hkNotBr hbr
      · exact hgt
  refine ⟨q, m - 1, hqN, ?_, hgtq, hrun, ?_⟩
  · omega
  · have hmEq : m - 1 + 1 = m := by omega
    simpa [hmEq] using hmBr

theorem exists_forall_lt_then_next_bracket_of_tail_bracket_or_forall_lt
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (htail : DyadicShellTailBracketOrForallLtAt g c)
    (hnotEventual :
      ¬ ∃ N : ℕ, ∀ n ≥ N, DyadicShellForallLtValueAt g c n)
    (hltInf :
      ∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧ DyadicShellForallLtValueAt g c n) :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      DyadicShellForallLtValueAt g c n ∧
      DyadicShellBracketValueAt g c (n + 1) := by
  classical
  rcases htail with ⟨Ntail, htailN⟩
  intro N
  rcases hltInf (max N Ntail) with ⟨q, hqGe, hltq⟩
  have hqN : q ≥ N := le_trans (le_max_left _ _) hqGe
  have hqTail : q ≥ Ntail := le_trans (le_max_right _ _) hqGe
  have hbrExists : ∃ m : ℕ, m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := by
    by_contra hno
    have hno' : ∀ m : ℕ, m ≥ q + 1 → ¬ DyadicShellBracketValueAt g c m := by
      intro m hm hbr
      exact hno ⟨m, hm, hbr⟩
    have hltTailFromQ : ∀ n : ℕ, n ≥ q → DyadicShellForallLtValueAt g c n := by
      intro n hnq
      by_cases hnEq : n = q
      · simpa [hnEq] using hltq
      · have hnq1 : n ≥ q + 1 := by omega
        rcases htailN n (le_trans hqTail hnq) with hbr | hlt
        · exfalso
          exact hno' n hnq1 hbr
        · exact hlt
    exact hnotEventual ⟨q, hltTailFromQ⟩
  let m : ℕ := Nat.find hbrExists
  have hmProp : m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := Nat.find_spec hbrExists
  have hmGe : m ≥ q + 1 := hmProp.1
  have hmBr : DyadicShellBracketValueAt g c m := hmProp.2
  have hmPos : 0 < m := by
    omega
  refine ⟨m - 1, ?_, ?_, ?_⟩
  · omega
  · have hmPredGeQ : m - 1 ≥ q := by omega
    have hprevGeTail : m - 1 ≥ Ntail := le_trans hqTail hmPredGeQ
    have hprevNotBr : ¬ DyadicShellBracketValueAt g c (m - 1) := by
      intro hbrPrev
      by_cases hprevGeQ1 : m - 1 ≥ q + 1
      · have hnotPrev : ¬ ((m - 1) ≥ q + 1 ∧ DyadicShellBracketValueAt g c (m - 1)) := by
          exact Nat.find_min hbrExists (m := m - 1) (by omega)
        exact hnotPrev ⟨hprevGeQ1, hbrPrev⟩
      · have hprevEqQ : m - 1 = q := by omega
        rcases hbrPrev with ⟨u, v, hu, hv, _, huv⟩
        have hltv :
            sqCenteredNorthZonalQuotientRaw g
                (sqScaleMap (dyadicUnitIcc (m - 1)) v) < c := by
          simpa [hprevEqQ] using hltq hv
        linarith
    rcases htailN (m - 1) hprevGeTail with hbrPrev | hltPrev
    · exfalso
      exact hprevNotBr hbrPrev
    · intro u hu
      exact hltPrev hu
  · have hmEq : m - 1 + 1 = m := by omega
    simpa [hmEq] using hmBr

theorem exists_forall_gt_run_then_next_bracket_from_bad_shell_of_tail_data
    {g : C(spherePoint3, ℝ)} {c : ℝ} {Ntail q : ℕ}
    (htailN : ∀ n ≥ Ntail,
      DyadicShellBracketValueAt g c n ∨ DyadicShellForallGtValueAt g c n)
    (hnotEventual :
      ¬ ∃ N : ℕ, ∀ n ≥ N, DyadicShellForallGtValueAt g c n)
    (hqTail : q ≥ Ntail)
    (hgtq : DyadicShellForallGtValueAt g c q) :
    ∃ n : ℕ, n ≥ q ∧
      (∀ k : ℕ, q ≤ k → k ≤ n → DyadicShellForallGtValueAt g c k) ∧
      DyadicShellBracketValueAt g c (n + 1) := by
  classical
  have hbrExists : ∃ m : ℕ, m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := by
    by_contra hno
    have hno' : ∀ m : ℕ, m ≥ q + 1 → ¬ DyadicShellBracketValueAt g c m := by
      intro m hm hbr
      exact hno ⟨m, hm, hbr⟩
    have hgtTailFromQ : ∀ n : ℕ, n ≥ q → DyadicShellForallGtValueAt g c n := by
      intro n hnq
      by_cases hnEq : n = q
      · simpa [hnEq] using hgtq
      · have hnq1 : n ≥ q + 1 := by omega
        rcases htailN n (le_trans hqTail hnq) with hbr | hgt
        · exfalso
          exact hno' n hnq1 hbr
        · exact hgt
    exact hnotEventual ⟨q, hgtTailFromQ⟩
  let m : ℕ := Nat.find hbrExists
  have hmProp : m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := Nat.find_spec hbrExists
  have hmGe : m ≥ q + 1 := hmProp.1
  have hmBr : DyadicShellBracketValueAt g c m := hmProp.2
  refine ⟨m - 1, by omega, ?_, ?_⟩
  · intro k hkq hkm
    by_cases hkEq : k = q
    · simpa [hkEq] using hgtq
    · have hkq1 : k ≥ q + 1 := by omega
      have hkTail : k ≥ Ntail := le_trans hqTail hkq
      rcases htailN k hkTail with hbr | hgt
      · exfalso
        have hnotk : ¬ (k ≥ q + 1 ∧ DyadicShellBracketValueAt g c k) := by
          exact Nat.find_min hbrExists (m := k) (by omega)
        exact hnotk ⟨hkq1, hbr⟩
      · exact hgt
  · have hmEq : m - 1 + 1 = m := by omega
    simpa [hmEq] using hmBr

theorem exists_forall_lt_run_then_next_bracket_of_tail_bracket_or_forall_lt
    {g : C(spherePoint3, ℝ)} {c : ℝ}
    (htail : DyadicShellTailBracketOrForallLtAt g c)
    (hnotEventual :
      ¬ ∃ N : ℕ, ∀ n ≥ N, DyadicShellForallLtValueAt g c n)
    (hltInf :
      ∀ M : ℕ, ∃ n : ℕ, n ≥ M ∧ DyadicShellForallLtValueAt g c n) :
    ∀ N : ℕ, ∃ q n : ℕ, q ≥ N ∧ n ≥ q ∧
      DyadicShellForallLtValueAt g c q ∧
      (∀ k : ℕ, q ≤ k → k ≤ n → DyadicShellForallLtValueAt g c k) ∧
      DyadicShellBracketValueAt g c (n + 1) := by
  classical
  rcases htail with ⟨Ntail, htailN⟩
  intro N
  rcases hltInf (max N Ntail) with ⟨q, hqGe, hltq⟩
  have hqN : q ≥ N := le_trans (le_max_left _ _) hqGe
  have hqTail : q ≥ Ntail := le_trans (le_max_right _ _) hqGe
  have hbrExists : ∃ m : ℕ, m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := by
    by_contra hno
    have hno' : ∀ m : ℕ, m ≥ q + 1 → ¬ DyadicShellBracketValueAt g c m := by
      intro m hm hbr
      exact hno ⟨m, hm, hbr⟩
    have hltTailFromQ : ∀ n : ℕ, n ≥ q → DyadicShellForallLtValueAt g c n := by
      intro n hnq
      by_cases hnEq : n = q
      · simpa [hnEq] using hltq
      · have hnq1 : n ≥ q + 1 := by omega
        rcases htailN n (le_trans hqTail hnq) with hbr | hlt
        · exfalso
          exact hno' n hnq1 hbr
        · exact hlt
    exact hnotEventual ⟨q, hltTailFromQ⟩
  let m : ℕ := Nat.find hbrExists
  have hmProp : m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := Nat.find_spec hbrExists
  have hmBr : DyadicShellBracketValueAt g c m := hmProp.2
  have hrun :
      ∀ k : ℕ, q ≤ k → k ≤ m - 1 → DyadicShellForallLtValueAt g c k := by
    intro k hkq hkm1
    by_cases hkEq : k = q
    · simpa [hkEq] using hltq
    · have hkq1 : k ≥ q + 1 := by omega
      have hkTail : k ≥ Ntail := le_trans hqTail hkq
      have hkNotBr : ¬ DyadicShellBracketValueAt g c k := by
        intro hbrk
        have hkltm : k < m := by omega
        have hnotPair : ¬ (k ≥ q + 1 ∧ DyadicShellBracketValueAt g c k) := by
          exact Nat.find_min hbrExists (m := k) hkltm
        exact hnotPair ⟨hkq1, hbrk⟩
      rcases htailN k hkTail with hbr | hlt
      · exfalso
        exact hkNotBr hbr
      · exact hlt
  refine ⟨q, m - 1, hqN, ?_, hltq, hrun, ?_⟩
  · omega
  · have hmEq : m - 1 + 1 = m := by omega
    simpa [hmEq] using hmBr

theorem exists_forall_lt_run_then_next_bracket_from_bad_shell_of_tail_data
    {g : C(spherePoint3, ℝ)} {c : ℝ} {Ntail q : ℕ}
    (htailN : ∀ n ≥ Ntail,
      DyadicShellBracketValueAt g c n ∨ DyadicShellForallLtValueAt g c n)
    (hnotEventual :
      ¬ ∃ N : ℕ, ∀ n ≥ N, DyadicShellForallLtValueAt g c n)
    (hqTail : q ≥ Ntail)
    (hltq : DyadicShellForallLtValueAt g c q) :
    ∃ n : ℕ, n ≥ q ∧
      (∀ k : ℕ, q ≤ k → k ≤ n → DyadicShellForallLtValueAt g c k) ∧
      DyadicShellBracketValueAt g c (n + 1) := by
  classical
  have hbrExists : ∃ m : ℕ, m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := by
    by_contra hno
    have hno' : ∀ m : ℕ, m ≥ q + 1 → ¬ DyadicShellBracketValueAt g c m := by
      intro m hm hbr
      exact hno ⟨m, hm, hbr⟩
    have hltTailFromQ : ∀ n : ℕ, n ≥ q → DyadicShellForallLtValueAt g c n := by
      intro n hnq
      by_cases hnEq : n = q
      · simpa [hnEq] using hltq
      · have hnq1 : n ≥ q + 1 := by omega
        rcases htailN n (le_trans hqTail hnq) with hbr | hlt
        · exfalso
          exact hno' n hnq1 hbr
        · exact hlt
    exact hnotEventual ⟨q, hltTailFromQ⟩
  let m : ℕ := Nat.find hbrExists
  have hmProp : m ≥ q + 1 ∧ DyadicShellBracketValueAt g c m := Nat.find_spec hbrExists
  have hmGe : m ≥ q + 1 := hmProp.1
  have hmBr : DyadicShellBracketValueAt g c m := hmProp.2
  refine ⟨m - 1, by omega, ?_, ?_⟩
  · intro k hkq hkm
    by_cases hkEq : k = q
    · simpa [hkEq] using hltq
    · have hkq1 : k ≥ q + 1 := by omega
      have hkTail : k ≥ Ntail := le_trans hqTail hkq
      rcases htailN k hkTail with hbr | hlt
      · exfalso
        have hnotk : ¬ (k ≥ q + 1 ∧ DyadicShellBracketValueAt g c k) := by
          exact Nat.find_min hbrExists (m := k) (by omega)
        exact hnotk ⟨hkq1, hbr⟩
      · exact hlt
  · have hmEq : m - 1 + 1 = m := by omega
    simpa [hmEq] using hmBr

theorem exists_fixed_northZonal_dyadic_shell_tail_bracket_value_at_lower_anchor_or_forall_gt_of_tail_bracket_value_at_anchor_or_forall_gt_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 x : unitIcc}, 0 < u0.1 → 0 < x.1 →
        sqCenteredNorthZonalQuotientRaw g x <
          sqCenteredNorthZonalQuotientRaw g u0 →
        DyadicShellTailBracketOrForallGtAt g (sqCenteredNorthZonalQuotientRaw g u0) →
        DyadicShellTailBracketOrForallGtAt g (sqCenteredNorthZonalQuotientRaw g x) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 x hu0 hx hxu htail
  simpa [DyadicShellTailBracketOrForallGtAt, DyadicShellBracketValueAt, DyadicShellForallGtValueAt] using
    dyadic_shell_tail_bracket_value_at_lower_anchor_or_forall_gt_of_tail_bracket_value_at_anchor_or_forall_gt
      hxu htail

theorem exists_fixed_northZonal_dyadic_shell_tail_bracket_value_at_upper_anchor_or_forall_lt_of_tail_bracket_value_at_anchor_or_forall_lt_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 x : unitIcc}, 0 < u0.1 → 0 < x.1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g x →
        DyadicShellTailBracketOrForallLtAt g (sqCenteredNorthZonalQuotientRaw g u0) →
        DyadicShellTailBracketOrForallLtAt g (sqCenteredNorthZonalQuotientRaw g x) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 x hu0 hx hu0x htail
  simpa [DyadicShellTailBracketOrForallLtAt, DyadicShellBracketValueAt, DyadicShellForallLtValueAt] using
    dyadic_shell_tail_bracket_value_at_upper_anchor_or_forall_lt_of_tail_bracket_value_at_anchor_or_forall_lt
      hu0x htail

theorem exists_fixed_northZonal_recursive_lower_anchor_tail_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        DyadicShellTailBracketOrForallGtAt g (sqCenteredNorthZonalQuotientRaw g u0) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g u0 ∧
          (∀ {δ : ℝ}, 0 < δ →
            ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
              sqCenteredNorthZonalQuotientRaw g y =
                sqCenteredNorthZonalQuotientRaw g x) ∧
          DyadicShellTailBracketOrForallGtAt g (sqCenteredNorthZonalQuotientRaw g x) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hgt htail
  rcases
      exists_lt_value_at_anchor_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hg.2 hgz hu0 ha haEq hgt with
    ⟨x, hxPos, hxLtHalf, hxLt, hnear⟩
  refine ⟨x, hxPos, hxLtHalf, hxLt, hnear, ?_⟩
  exact
    dyadic_shell_tail_bracket_value_at_lower_anchor_or_forall_gt_of_tail_bracket_value_at_anchor_or_forall_gt
      hxLt htail

theorem exists_fixed_northZonal_recursive_upper_anchor_tail_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 a : unitIcc}, 0 < u0.1 → 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g u0 →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g u0) →
        DyadicShellTailBracketOrForallLtAt g (sqCenteredNorthZonalQuotientRaw g u0) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g u0 <
            sqCenteredNorthZonalQuotientRaw g x ∧
          (∀ {δ : ℝ}, 0 < δ →
            ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
              sqCenteredNorthZonalQuotientRaw g y =
                sqCenteredNorthZonalQuotientRaw g x) ∧
          DyadicShellTailBracketOrForallLtAt g (sqCenteredNorthZonalQuotientRaw g x) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 a hu0 ha haEq hlt htail
  rcases
      exists_gt_value_at_anchor_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_lt_on_halfShell
        hg.2 hgz hu0 ha haEq hlt with
    ⟨x, hxPos, hxLtHalf, hxGt, hnear⟩
  refine ⟨x, hxPos, hxLtHalf, hxGt, hnear, ?_⟩
  exact
    dyadic_shell_tail_bracket_value_at_upper_anchor_or_forall_lt_of_tail_bracket_value_at_anchor_or_forall_lt
      hxGt htail

theorem exists_fixed_northZonal_recursive_lower_anchor_bracket_arbitrarily_far_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) →
        DyadicShellTailBracketOrForallGtAt g (sqCenteredNorthZonalQuotientRaw g oneUnitIcc) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          (∀ {δ : ℝ}, 0 < δ →
            ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
              sqCenteredNorthZonalQuotientRaw g y =
                sqCenteredNorthZonalQuotientRaw g x) ∧
          ∀ M : ℕ,
            ∃ n : ℕ, n ≥ M ∧ DyadicShellBracketValueAt g (sqCenteredNorthZonalQuotientRaw g x) n := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hgt htail
  rcases
      exists_lt_value_at_one_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hg.2 hgz ha haEq hgt with
    ⟨x, hxPos, hxLtHalf, hxLt, hnear⟩
  have htailx :
      DyadicShellTailBracketOrForallGtAt g (sqCenteredNorthZonalQuotientRaw g x) :=
    dyadic_shell_tail_bracket_value_at_lower_anchor_or_forall_gt_of_tail_bracket_value_at_anchor_or_forall_gt
      hxLt htail
  have hnotgt :
      ¬ ∃ N : ℕ,
        ∀ n ≥ N, DyadicShellForallGtValueAt g (sqCenteredNorthZonalQuotientRaw g x) n := by
    intro hgtTail
    exact
      False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_gt_on_dyadic_shell_value_at_anchor
        (g := g) hg hgne hgz hxPos (by simpa [DyadicShellForallGtValueAt] using hgtTail)
  refine ⟨x, hxPos, hxLtHalf, hxLt, hnear, ?_⟩
  intro M
  rcases
      dyadic_shell_bracket_value_at_lower_anchor_arbitrarily_far_of_tail_bracket_value_at_anchor_or_forall_gt
        hxLt (by simpa [DyadicShellTailBracketOrForallGtAt, DyadicShellBracketValueAt, DyadicShellForallGtValueAt] using htail)
        (by
          intro hgtTail
          exact hnotgt (by simpa [DyadicShellForallGtValueAt] using hgtTail)) M with
    ⟨n, hnM, hbr⟩
  exact ⟨n, hnM, by simpa [DyadicShellBracketValueAt] using hbr⟩

theorem exists_fixed_northZonal_recursive_upper_anchor_bracket_arbitrarily_far_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {a : unitIcc}, 0 < a.1 →
        sqCenteredNorthZonalQuotientRaw g a =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc) →
        DyadicShellTailBracketOrForallLtAt g (sqCenteredNorthZonalQuotientRaw g oneUnitIcc) →
        ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
            sqCenteredNorthZonalQuotientRaw g x ∧
          (∀ {δ : ℝ}, 0 < δ →
            ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
              sqCenteredNorthZonalQuotientRaw g y =
                sqCenteredNorthZonalQuotientRaw g x) ∧
          ∀ M : ℕ,
            ∃ n : ℕ, n ≥ M ∧ DyadicShellBracketValueAt g (sqCenteredNorthZonalQuotientRaw g x) n := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro a ha haEq hlt htail
  rcases
      exists_gt_value_at_one_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_lt_on_halfShell
        hg.2 hgz ha haEq hlt with
    ⟨x, hxPos, hxLtHalf, hxGt, hnear⟩
  have htailx :
      DyadicShellTailBracketOrForallLtAt g (sqCenteredNorthZonalQuotientRaw g x) :=
    dyadic_shell_tail_bracket_value_at_upper_anchor_or_forall_lt_of_tail_bracket_value_at_anchor_or_forall_lt
      hxGt htail
  have hnotlt :
      ¬ ∃ N : ℕ,
        ∀ n ≥ N, DyadicShellForallLtValueAt g (sqCenteredNorthZonalQuotientRaw g x) n := by
    intro hltTail
    exact
      False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_lt_on_dyadic_shell_value_at_anchor
        (g := g) hg hgne hgz hxPos (by simpa [DyadicShellForallLtValueAt] using hltTail)
  refine ⟨x, hxPos, hxLtHalf, hxGt, hnear, ?_⟩
  intro M
  rcases
      dyadic_shell_bracket_value_at_upper_anchor_arbitrarily_far_of_tail_bracket_value_at_anchor_or_forall_lt
        hxGt (by simpa [DyadicShellTailBracketOrForallLtAt, DyadicShellBracketValueAt, DyadicShellForallLtValueAt] using htail)
        (by
          intro hltTail
          exact hnotlt (by simpa [DyadicShellForallLtValueAt] using hltTail)) M with
    ⟨n, hnM, hbr⟩
  exact ⟨n, hnM, by simpa [DyadicShellBracketValueAt] using hbr⟩

theorem exists_fixed_northZonal_dyadic_shell_bracket_value_at_lower_anchor_arbitrarily_far_of_tail_bracket_value_at_anchor_or_forall_gt_of_ne_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 x : unitIcc}, 0 < u0.1 → 0 < x.1 →
        sqCenteredNorthZonalQuotientRaw g x <
          sqCenteredNorthZonalQuotientRaw g u0 →
        sqCenteredNorthZonalQuotientRaw g x ≠
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∃ N : ℕ,
          ∀ n ≥ N,
            (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
                sqCenteredNorthZonalQuotientRaw g u0 ∧
              sqCenteredNorthZonalQuotientRaw g u0 ≤
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
            (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
              sqCenteredNorthZonalQuotientRaw g u0 <
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u))) →
        ∀ M : ℕ,
          ∃ n : ℕ, n ≥ M ∧
            ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
                sqCenteredNorthZonalQuotientRaw g x ∧
              sqCenteredNorthZonalQuotientRaw g x ≤
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 x hu0 hx hxu hxne htail M
  have hnotgt :
      ¬ ∃ N : ℕ,
        ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) := by
    intro hgt
    exact
      False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_gt_on_dyadic_shell_value_at_anchor
        (g := g) hg hgne hgz hx hgt
  exact
    dyadic_shell_bracket_value_at_lower_anchor_arbitrarily_far_of_tail_bracket_value_at_anchor_or_forall_gt
      hxu htail hnotgt M

theorem exists_fixed_northZonal_dyadic_shell_bracket_value_at_upper_anchor_arbitrarily_far_of_tail_bracket_value_at_anchor_or_forall_lt_of_ne_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 x : unitIcc}, 0 < u0.1 → 0 < x.1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g x →
        sqCenteredNorthZonalQuotientRaw g x ≠
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        (∃ N : ℕ,
          ∀ n ≥ N,
            (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
                sqCenteredNorthZonalQuotientRaw g u0 ∧
              sqCenteredNorthZonalQuotientRaw g u0 ≤
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v)) ∨
            (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
                sqCenteredNorthZonalQuotientRaw g u0)) →
        ∀ M : ℕ,
          ∃ n : ℕ, n ≥ M ∧
            ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
                sqCenteredNorthZonalQuotientRaw g x ∧
              sqCenteredNorthZonalQuotientRaw g x ≤
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 x hu0 hx hu0x hxne htail M
  have hnotlt :
      ¬ ∃ N : ℕ,
        ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) <
            sqCenteredNorthZonalQuotientRaw g x := by
    intro hlt
    exact
      False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_lt_on_dyadic_shell_value_at_anchor
        (g := g) hg hgne hgz hx hlt
  exact
    dyadic_shell_bracket_value_at_upper_anchor_arbitrarily_far_of_tail_bracket_value_at_anchor_or_forall_lt
      hu0x htail hnotlt M

theorem exists_fixed_northZonal_forall_gt_then_next_bracket_at_lower_anchor_of_tail_bracket_value_at_anchor_or_forall_gt_of_ne_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 x : unitIcc}, 0 < u0.1 → 0 < x.1 →
        sqCenteredNorthZonalQuotientRaw g x <
          sqCenteredNorthZonalQuotientRaw g u0 →
        sqCenteredNorthZonalQuotientRaw g x ≠
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        DyadicShellTailBracketOrForallGtAt g (sqCenteredNorthZonalQuotientRaw g u0) →
        (∀ M : ℕ,
          ∃ n : ℕ, n ≥ M ∧
            DyadicShellForallGtValueAt g (sqCenteredNorthZonalQuotientRaw g u0) n) →
        ∀ M : ℕ,
          ∃ n : ℕ, n ≥ M ∧
            DyadicShellForallGtValueAt g (sqCenteredNorthZonalQuotientRaw g x) n ∧
            DyadicShellBracketValueAt g (sqCenteredNorthZonalQuotientRaw g x) (n + 1) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 x hu0 hx hxu hxne htail hgtInf M
  have htailx :
      DyadicShellTailBracketOrForallGtAt g (sqCenteredNorthZonalQuotientRaw g x) :=
    dyadic_shell_tail_bracket_value_at_lower_anchor_or_forall_gt_of_tail_bracket_value_at_anchor_or_forall_gt
      hxu htail
  have hnotgtx :
      ¬ ∃ N : ℕ,
        ∀ n ≥ N, DyadicShellForallGtValueAt g (sqCenteredNorthZonalQuotientRaw g x) n := by
    intro hgtTail
    exact
      False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_gt_on_dyadic_shell_value_at_anchor
        (g := g) hg hgne hgz hx (by simpa [DyadicShellForallGtValueAt] using hgtTail)
  have hgtInfx :
      ∀ M : ℕ,
        ∃ n : ℕ, n ≥ M ∧ DyadicShellForallGtValueAt g (sqCenteredNorthZonalQuotientRaw g x) n := by
    intro M
    rcases hgtInf M with ⟨n, hnM, hgtu0⟩
    refine ⟨n, hnM, ?_⟩
    intro u hu
    have hgtu0u := hgtu0 hu
    linarith
  exact exists_forall_gt_then_next_bracket_of_tail_bracket_or_forall_gt htailx hnotgtx hgtInfx M

theorem exists_fixed_northZonal_forall_lt_then_next_bracket_at_upper_anchor_of_tail_bracket_value_at_anchor_or_forall_lt_of_ne_value_at_one_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      (∀ x : spherePoint3, g (sphereAntipode x) = g x) ∧
      g sphereE3 ≠ 0 ∧
      ∀ {u0 x : unitIcc}, 0 < u0.1 → 0 < x.1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g x →
        sqCenteredNorthZonalQuotientRaw g x ≠
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        DyadicShellTailBracketOrForallLtAt g (sqCenteredNorthZonalQuotientRaw g u0) →
        (∀ M : ℕ,
          ∃ n : ℕ, n ≥ M ∧
            DyadicShellForallLtValueAt g (sqCenteredNorthZonalQuotientRaw g u0) n) →
        ∀ M : ℕ,
          ∃ n : ℕ, n ≥ M ∧
            DyadicShellForallLtValueAt g (sqCenteredNorthZonalQuotientRaw g x) n ∧
            DyadicShellBracketValueAt g (sqCenteredNorthZonalQuotientRaw g x) (n + 1) := by
  rcases
      exists_fixed_northZonal_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, _⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro u0 x hu0 hx hu0x hxne htail hltInf M
  have htailx :
      DyadicShellTailBracketOrForallLtAt g (sqCenteredNorthZonalQuotientRaw g x) :=
    dyadic_shell_tail_bracket_value_at_upper_anchor_or_forall_lt_of_tail_bracket_value_at_anchor_or_forall_lt
      hu0x htail
  have hnotltx :
      ¬ ∃ N : ℕ,
        ∀ n ≥ N, DyadicShellForallLtValueAt g (sqCenteredNorthZonalQuotientRaw g x) n := by
    intro hltTail
    exact
      False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_eventually_forall_lt_on_dyadic_shell_value_at_anchor
        (g := g) hg hgne hgz hx (by simpa [DyadicShellForallLtValueAt] using hltTail)
  have hltInfx :
      ∀ M : ℕ,
        ∃ n : ℕ, n ≥ M ∧ DyadicShellForallLtValueAt g (sqCenteredNorthZonalQuotientRaw g x) n := by
    intro M
    rcases hltInf M with ⟨n, hnM, hltu0⟩
    refine ⟨n, hnM, ?_⟩
    intro u hu
    have hltu0u := hltu0 hu
    linarith
  exact exists_forall_lt_then_next_bracket_of_tail_bracket_or_forall_lt htailx hnotltx hltInfx M

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_uniform_near_half_and_anchor_tendsto
    {g : C(spherePoint3, ℝ)} {L : ℝ}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1))| < ε)
    (hanchor :
      Filter.Tendsto (fun n : ℕ => sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
        Filter.atTop (𝓝 L)) :
    False := by
  have hlim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 L) :=
    tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_uniform_near_half hshell hanchor
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
      hg hgne hgz hlim

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_uniform_near_half_and_summable_anchor_step
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1))| < ε)
    (hsumm :
      Summable (fun n : ℕ =>
        dist (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
          (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2))))) :
    False := by
  rcases
      exists_tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_dyadic_shell_uniform_near_half_of_summable_anchor_step
        hshell hsumm with
    ⟨L, hlim⟩
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
      hg hgne hgz hlim

theorem False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_uniform_near_half_and_anchor_step_bound
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g)
    (hshell :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ N : ℕ,
          ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1))| < ε)
    (hbound :
      ∃ b : ℕ → ℝ,
        Summable b ∧
        (∀ n : ℕ, 0 ≤ b n) ∧
        ∀ n : ℕ,
          dist (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
            (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2))) ≤ b n) :
    False := by
  rcases hbound with ⟨b, hbSumm, hbNonneg, hbLe⟩
  have hsumm :
      Summable (fun n : ℕ =>
        dist (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
          (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2)))) := by
    exact Summable.of_nonneg_of_le
      (fun n => dist_nonneg)
      hbLe
      hbSumm
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_uniform_near_half_and_summable_anchor_step
      hg hgne hgz hshell hsumm

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_dyadic_shell_uniform_near_half_and_anchor_tendsto
    (hcont :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∃ L : ℝ,
          (∀ {ε : ℝ}, 0 < ε →
            ∃ N : ℕ,
              ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
                |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                    sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1))| < ε) ∧
          Filter.Tendsto
            (fun n : ℕ => sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
            Filter.atTop (𝓝 L)) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  by_contra hne
  rcases exists_nonzero_northZonal_fixed_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz, _⟩
  rcases hcont hg hgz with ⟨L, hshell, hanchor⟩
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_uniform_near_half_and_anchor_tendsto
      hg hgne hgz hshell hanchor

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_dyadic_shell_uniform_near_half_and_summable_anchor_step
    (hcont :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        (∃ hshell :
          ∀ {ε : ℝ}, 0 < ε →
            ∃ N : ℕ,
              ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
                |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                    sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1))| < ε,
          Summable (fun n : ℕ =>
            dist (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
              (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2)))))) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  by_contra hne
  rcases exists_nonzero_northZonal_fixed_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz, _⟩
  rcases hcont hg hgz with ⟨hshell, hsumm⟩
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_uniform_near_half_and_summable_anchor_step
      hg hgne hgz hshell hsumm

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_dyadic_shell_uniform_near_half_and_anchor_step_bound
    (hcont :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        (∃ hshell :
          ∀ {ε : ℝ}, 0 < ε →
            ∃ N : ℕ,
              ∀ n ≥ N, ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
                |sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) -
                    sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1))| < ε,
          ∃ b : ℕ → ℝ,
            Summable b ∧
            (∀ n : ℕ, 0 ≤ b n) ∧
            ∀ n : ℕ,
              dist (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 1)))
                (sqCenteredNorthZonalQuotientRaw g (dyadicUnitIcc (n + 2))) ≤ b n)) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  by_contra hne
  rcases exists_nonzero_northZonal_fixed_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz, _⟩
  rcases hcont hg hgz with ⟨hshell, hb⟩
  exact
    False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_dyadic_shell_uniform_near_half_and_anchor_step_bound
      hg hgne hgz hshell hb

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqquotientRaw_tendsto_zero
    (hcont :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∃ c : ℝ,
          Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
            (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c)) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  by_contra hne
  rcases exists_nonzero_northZonal_fixed_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz, _⟩
  rcases hcont hg hgz with ⟨c, hlim⟩
  have hg0 :
      g = 0 :=
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
      hg hgz hlim
  exact hgne hg0

theorem mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotientRaw_continuousAt_zero
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hzero : ContinuousAt (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc) :
    g ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
  rcases exists_sqquotient_factor_of_continuousAt_sqCenteredNorthZonalQuotientRaw_zero
      (g := g) hzero with ⟨q, hq⟩
  exact
    mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotient_factor
      hg hgz hq

theorem eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotientRaw_continuousAt_zero
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hzero : ContinuousAt (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc) :
    g = 0 := by
  have hlow :
      g ∈ lowHarmonicPolyHomogeneousImageSubmodule :=
    mem_lowHarmonicPolyHomogeneousImageSubmodule_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotientRaw_continuousAt_zero
      hg hgz hzero
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

theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqquotientRaw_continuousAt_zero
    (hcont :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ContinuousAt (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  by_contra hne
  rcases exists_nonzero_northZonal_fixed_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz, _⟩
  have hzero :
      ContinuousAt (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc :=
    hcont hg hgz
  have hg0 :
      g = 0 :=
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotientRaw_continuousAt_zero
      hg hgz hzero
  exact hgne hg0
