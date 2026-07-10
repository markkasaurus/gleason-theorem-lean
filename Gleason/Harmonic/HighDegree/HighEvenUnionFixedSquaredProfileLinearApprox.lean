import Gleason.Harmonic.HighDegree.HighEvenUnionSquaredProfileNormBridge

noncomputable section

open Complex InnerProductSpace Polynomial

lemma norm_lowSqProfileMode_sub_leftParam_le (a a' b : ℝ) :
    ‖lowSqProfileMode a b - lowSqProfileMode a' b‖ ≤ |a - a'| := by
  have hEq :
      lowSqProfileMode a b - lowSqProfileMode a' b =
        (a - a') • (1 : C(spherePoint3, ℝ)) := by
    ext x
    simp [lowSqProfileMode_apply]
  rw [hEq, norm_smul]
  haveI : Nonempty spherePoint3 := ⟨sphereE1⟩
  simp

lemma norm_lowSqProfileMode_sub_leftParam_le_of_dist
    {h g : C(spherePoint3, ℝ)} (b : ℝ) :
    ‖lowSqProfileMode (h sphereE1) b - lowSqProfileMode (g sphereE1) b‖ ≤ dist h g := by
  calc
    ‖lowSqProfileMode (h sphereE1) b - lowSqProfileMode (g sphereE1) b‖
      ≤ |h sphereE1 - g sphereE1| :=
        norm_lowSqProfileMode_sub_leftParam_le (h sphereE1) (g sphereE1) b
    _ = dist (h sphereE1) (g sphereE1) := by rw [Real.dist_eq]
    _ ≤ dist h g := ContinuousMap.dist_apply_le_dist (f := h) (g := g) sphereE1

theorem exists_fixed_northZonal_limit_sqprofile_near_linear_of_nontrivial_tail
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
      ∀ {ε : ℝ}, 0 < ε → ε < ‖g sphereE3‖ → ∀ m : ℕ,
        ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ‖sqCenteredNorthZonalContinuousMap g - sqProfileLinearPart (X * q)‖ ≤
            2 * ε +
              (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
  rcases exists_fixed_northZonal_sqprofile_near_linear_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  have hgeven :
      ∀ x : spherePoint3, g (sphereAntipode x) = g x :=
    antipode_even_of_mem_topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule hg.1
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro ε hε hεpole m
  rcases happ hε hεpole m with
    ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hnear⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  let l : C(spherePoint3, ℝ) := lowSqProfileMode (h sphereE1) (q.coeff 0)
  have hlow :
      ‖h - l‖ ≤
        (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
    change ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ ≤ _
    rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh hhz]
    simpa [sqProfileLinearPart] using hnear
  have hgl :
      ‖g - lowSqProfileMode (g sphereE1) (q.coeff 0)‖ ≤
        2 * ε +
          (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
    have hglDist :
        dist g (lowSqProfileMode (g sphereE1) (q.coeff 0)) ≤
          2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
      calc
      dist g (lowSqProfileMode (g sphereE1) (q.coeff 0))
        ≤ dist g h + dist h l +
            dist l (lowSqProfileMode (g sphereE1) (q.coeff 0)) := by
              calc
                dist g (lowSqProfileMode (g sphereE1) (q.coeff 0))
                  ≤ dist g h + dist h (lowSqProfileMode (g sphereE1) (q.coeff 0)) :=
                    dist_triangle _ _ _
                _ ≤ dist g h + (dist h l + dist l (lowSqProfileMode (g sphereE1) (q.coeff 0))) := by
                    gcongr
                    exact dist_triangle _ _ _
                _ = dist g h + dist h l + dist l (lowSqProfileMode (g sphereE1) (q.coeff 0)) := by ring
      _ ≤ dist g h + dist h l + dist h g := by
            gcongr
            simpa [l, dist_eq_norm] using
              norm_lowSqProfileMode_sub_leftParam_le_of_dist (h := h) (g := g) (q.coeff 0)
      _ ≤ 2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
            have hlow' : dist h l ≤
                (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                  (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
              simpa [dist_eq_norm] using hlow
            have hdist' : dist h g < ε := by simpa [dist_eq_norm] using hdist
            have hdist'' : dist g h < ε := by simpa [dist_comm] using hdist'
            linarith
    simpa [dist_eq_norm] using hglDist
  rw [norm_sub_lowSqProfileMode_eq_sqprofile_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    (hg := hg) (hgz := hgz) (b := q.coeff 0)] at hgl
  simpa [sqProfileLinearPart] using hgl

theorem exists_fixed_northZonal_limit_sqprofile_uniform_near_linear_of_nontrivial_tail
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
        ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          ‖h - g‖ < ε ∧
          ∀ m : ℕ,
            ‖sqCenteredNorthZonalContinuousMap g - sqProfileLinearPart (X * q)‖ ≤
              2 * ε +
                (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                  (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
  rcases exists_fixed_northZonal_sqprofile_almost_fixed_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  have hgeven :
      ∀ x : spherePoint3, g (sphereAntipode x) = g x :=
    antipode_even_of_mem_topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule hg.1
  refine ⟨g, hg, hgne, hgz, hfix, hgeven, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, hdefect⟩
  refine ⟨h, q, hhHigh, hhz, hhpole, hq, hdist, ?_⟩
  intro m
  let l : C(spherePoint3, ℝ) := lowSqProfileMode (h sphereE1) (q.coeff 0)
  have hlow :
      ‖h - l‖ ≤
        (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
    change ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ ≤ _
    rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh hhz]
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
  have hgl :
      ‖g - lowSqProfileMode (g sphereE1) (q.coeff 0)‖ ≤
        2 * ε +
          (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
    have hglDist :
        dist g (lowSqProfileMode (g sphereE1) (q.coeff 0)) ≤
          2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
      calc
      dist g (lowSqProfileMode (g sphereE1) (q.coeff 0))
        ≤ dist g h + dist h l +
            dist l (lowSqProfileMode (g sphereE1) (q.coeff 0)) := by
              calc
                dist g (lowSqProfileMode (g sphereE1) (q.coeff 0))
                  ≤ dist g h + dist h (lowSqProfileMode (g sphereE1) (q.coeff 0)) :=
                    dist_triangle _ _ _
                _ ≤ dist g h + (dist h l + dist l (lowSqProfileMode (g sphereE1) (q.coeff 0))) := by
                    gcongr
                    exact dist_triangle _ _ _
                _ = dist g h + dist h l + dist l (lowSqProfileMode (g sphereE1) (q.coeff 0)) := by
                    ring
      _ ≤ dist g h + dist h l + dist h g := by
            gcongr
            simpa [l, dist_eq_norm] using
              norm_lowSqProfileMode_sub_leftParam_le_of_dist (h := h) (g := g) (q.coeff 0)
      _ ≤ 2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
            have hlow' : dist h l ≤
                (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                  (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum (X * q) := by
              simpa [dist_eq_norm] using hlow
            have hdist' : dist h g < ε := by
              simpa [dist_eq_norm] using hdist
            have hdist'' : dist g h < ε := by
              simpa [dist_comm] using hdist'
            linarith
    simpa [dist_eq_norm] using hglDist
  rw [norm_sub_lowSqProfileMode_eq_sqprofile_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    (hg := hg) (hgz := hgz) (b := q.coeff 0)] at hgl
  simpa [sqProfileLinearPart] using hgl
