import Gleason.Harmonic.Profile.SquaredProfileLowmodeAmbient
import Gleason.Harmonic.HighDegree.HighEvenUnionSquaredQuotientOnPos
import Gleason.Harmonic.Profile.SquaredQuotientScaling

noncomputable section

open Complex InnerProductSpace Polynomial

lemma sqCenteredNorthZonalQuotientRaw_eq_eval_of_factor
    {h : C(spherePoint3, ℝ)} {q : ℝ[X]}
    (hq : ∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1)
    {u : unitIcc} (hu : 0 < u.1) :
    sqCenteredNorthZonalQuotientRaw h u = q.eval u.1 := by
  have hu0 : u.1 ≠ 0 := ne_of_gt hu
  rw [sqCenteredNorthZonalQuotientRaw, if_neg hu0, hq u]
  field_simp [hu0]

theorem abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_profile_dist
    (f g : C(spherePoint3, ℝ)) {δ : ℝ} (hδ : 0 < δ)
    {u : unitIcc} (hu : δ ≤ u.1) :
    |sqCenteredNorthZonalQuotientRaw f u - sqCenteredNorthZonalQuotientRaw g u|
      ≤ ‖sqCenteredNorthZonalContinuousMap f - sqCenteredNorthZonalContinuousMap g‖ / δ := by
  have hu0 : u.1 ≠ 0 := ne_of_gt (lt_of_lt_of_le hδ hu)
  have huPos : 0 < u.1 := lt_of_lt_of_le hδ hu
  have hEq :
      sqCenteredNorthZonalQuotientRaw f u - sqCenteredNorthZonalQuotientRaw g u =
        ((sqCenteredNorthZonalContinuousMap f -
            sqCenteredNorthZonalContinuousMap g) u) / u.1 := by
    rw [show sqCenteredNorthZonalQuotientRaw f u =
        sqCenteredNorthZonalProfile f u / u.1 by simp [sqCenteredNorthZonalQuotientRaw, hu0]]
    rw [show sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalProfile g u / u.1 by simp [sqCenteredNorthZonalQuotientRaw, hu0]]
    rw [ContinuousMap.sub_apply]
    simp [sqCenteredNorthZonalContinuousMap]
    field_simp [hu0]
  rw [hEq, abs_div, abs_of_nonneg huPos.le]
  calc
    |(sqCenteredNorthZonalContinuousMap f - sqCenteredNorthZonalContinuousMap g) u| / u.1
      ≤ ‖sqCenteredNorthZonalContinuousMap f - sqCenteredNorthZonalContinuousMap g‖ / u.1 := by
          gcongr
          simpa [Real.norm_eq_abs] using
            (sqCenteredNorthZonalContinuousMap f - sqCenteredNorthZonalContinuousMap g).norm_coe_le_norm u
    _ ≤ ‖sqCenteredNorthZonalContinuousMap f - sqCenteredNorthZonalContinuousMap g‖ / δ := by
          have hnorm_nonneg :
              0 ≤ ‖sqCenteredNorthZonalContinuousMap f - sqCenteredNorthZonalContinuousMap g‖ := by
            exact norm_nonneg _
          rw [div_eq_mul_inv, div_eq_mul_inv]
          have hinv : (u.1)⁻¹ ≤ δ⁻¹ := by
            simpa [one_div] using one_div_le_one_div_of_le hδ hu
          exact mul_le_mul_of_nonneg_left hinv hnorm_nonneg

theorem exists_fixed_northZonal_sqquotientPoly_shell_pair_uniform_near_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ _hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          q ∈ Polynomial.degreeLT ℝ N ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          ∀ m : ℕ, ∀ {a u v : unitIcc},
            |(sqQuotientRescalePolynomial a q).eval u.1 -
                (sqQuotientRescalePolynomial a q).eval v.1|
              ≤
                2 *
                  ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                      (degreeLTSqMulNormConst N * (6 * ε)) +
                    (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by
  rcases
      exists_fixed_northZonal_lowSqProfileMode_uniform_near_with_stage_factor_degree_bothDefects_of_nontrivial_tail
        hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hsqdef, hqdef, hnorm⟩
  refine ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, ?_⟩
  intro m a u v
  exact abs_sqQuotientRescalePolynomial_eval_sub_eval_le_of_almost_fixed
    a q (hδ := by
      have hconst_nonneg : 0 ≤ degreeLTSqMulNormConst N := by
        unfold degreeLTSqMulNormConst
        positivity
      positivity)
    (halmost := by
      calc
        dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
            (q.toContinuousMapOn unitIcc)
          ≤ degreeLTSqMulNormConst N * (6 * ε) := hqdef)
    m u v

theorem exists_fixed_northZonal_highEvenBounded_shell_pair_uniform_near_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ _hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          q ∈ Polynomial.degreeLT ℝ N ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          ∀ m : ℕ, ∀ {a u v : unitIcc}, 0 < a.1 → 0 < u.1 → 0 < v.1 →
            |sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u) -
                sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)|
              ≤
                2 *
                  ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                      (degreeLTSqMulNormConst N * (6 * ε)) +
                    (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by
  rcases exists_fixed_northZonal_sqquotientPoly_shell_pair_uniform_near_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hshell⟩
  refine ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, ?_⟩
  intro m a u v ha hu hv
  have huScale : 0 < (sqScaleMap a u).1 := by
    simpa [sqScaleMap_apply] using mul_pos ha hu
  have hvScale : 0 < (sqScaleMap a v).1 := by
    simpa [sqScaleMap_apply] using mul_pos ha hv
  rw [sqCenteredNorthZonalQuotientRaw_eq_eval_of_factor hq huScale,
    sqCenteredNorthZonalQuotientRaw_eq_eval_of_factor hq hvScale]
  simpa [sqQuotientRescalePolynomial_eval, sqScaleMap_apply, mul_comm, mul_left_comm, mul_assoc] using
    hshell m (a := a) (u := u) (v := v)

theorem exists_fixed_northZonal_sqquotientRaw_shell_pair_uniform_near_v2_of_nontrivial_tail
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
        ∃ N : ℕ, ∃ _hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
          h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
          q ∈ Polynomial.degreeLT ℝ N ∧
          l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
          ‖h - g‖ < ε ∧
          ∀ m : ℕ, ∀ {a u v : unitIcc}, 0 < a.1 → (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
            |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)|
              ≤
                8 * ε / a.1 +
                  2 *
                    ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                        (degreeLTSqMulNormConst N * (6 * ε)) +
                      (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by
  rcases exists_fixed_northZonal_sqquotientPoly_shell_pair_uniform_near_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with
    ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, hshell⟩
  refine ⟨N, hN, h, q, l, hhN, hhz, hhpole, hq, hqdeg, hl, hdist, ?_⟩
  intro m a u v ha hu hv
  have hprof :
      ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < 2 * ε := by
    calc
      ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖
        ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
      _ < 2 * ε := by gcongr
  have huShell : a.1 / 2 ≤ (sqScaleMap a u).1 := by
    simp [sqScaleMap_apply]
    nlinarith
  have hvShell : a.1 / 2 ≤ (sqScaleMap a v).1 := by
    simp [sqScaleMap_apply]
    nlinarith
  have huErr :
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
          sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u)|
        ≤ 4 * ε / a.1 := by
    have hle :
        |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
            sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u)|
          ≤ ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ / (a.1 / 2) :=
      abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_profile_dist g h (by positivity) huShell
    have hnorm :
        ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ ≤ 2 * ε := by
      have hle' : ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ ≤ 2 * ε := le_of_lt hprof
      simpa [norm_sub_rev] using hle'
    calc
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
          sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u)|
        ≤ ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ / (a.1 / 2) := hle
      _ ≤ (2 * ε) / (a.1 / 2) := by
            have hden : 0 ≤ a.1 / 2 := by positivity
            exact div_le_div_of_nonneg_right hnorm hden
      _ = 4 * ε / a.1 := by
            field_simp [show (a.1 : ℝ) ≠ 0 by exact ne_of_gt ha]
            ring
  have hvErr :
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v) -
          sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)|
        ≤ 4 * ε / a.1 := by
    have hle :
        |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v) -
            sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)|
          ≤ ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ / (a.1 / 2) :=
      abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_profile_dist g h (by positivity) hvShell
    have hnorm :
        ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ ≤ 2 * ε := by
      have hle' : ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ ≤ 2 * ε := le_of_lt hprof
      simpa [norm_sub_rev] using hle'
    calc
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v) -
          sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)|
        ≤ ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ / (a.1 / 2) := hle
      _ ≤ (2 * ε) / (a.1 / 2) := by
            have hden : 0 ≤ a.1 / 2 := by positivity
            exact div_le_div_of_nonneg_right hnorm hden
      _ = 4 * ε / a.1 := by
            field_simp [show (a.1 : ℝ) ≠ 0 by exact ne_of_gt ha]
            ring
  have hpairh :
      |sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u) -
          sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)|
        ≤
          2 *
            ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                (degreeLTSqMulNormConst N * (6 * ε)) +
              (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) :=
    by
      have huPos : 0 < (sqScaleMap a u).1 := by
        simp [sqScaleMap_apply]
        nlinarith
      have hvPos : 0 < (sqScaleMap a v).1 := by
        simp [sqScaleMap_apply]
        nlinarith
      simpa [sqCenteredNorthZonalQuotientRaw_eq_eval_of_factor hq huPos,
        sqCenteredNorthZonalQuotientRaw_eq_eval_of_factor hq hvPos] using
        hshell m (a := a) (u := u) (v := v)
  calc
    |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)|
      ≤ |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
            sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u)| +
          |sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u) -
            sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)| +
          |sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v) -
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)| := by
              let x :=
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
                  sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u)
              let y :=
                sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u) -
                  sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)
              let z :=
                sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v) -
                  sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)
              have habs :
                  |x + y + z| ≤ |x| + |y| + |z| := by
                have hxy : |x + y| ≤ |x| + |y| := by
                  simpa [Real.norm_eq_abs] using norm_add_le x y
                have hxyz : |(x + y) + z| ≤ |x + y| + |z| := by
                  simpa [Real.norm_eq_abs] using norm_add_le (x + y) z
                calc
                  |x + y + z| = |(x + y) + z| := by ring
                  _ ≤ |x + y| + |z| := hxyz
                  _ ≤ (|x| + |y|) + |z| := by linarith
                  _ = |x| + |y| + |z| := by ring
              simpa [x, y, z] using habs
    _ ≤ 4 * ε / a.1 +
          (2 *
            ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                (degreeLTSqMulNormConst N * (6 * ε)) +
              (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q))) +
          4 * ε / a.1 := by
            have hvErr' :
                |sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v) -
                    sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)|
                  ≤ 4 * ε / a.1 := by
              simpa [abs_sub_comm] using hvErr
            linarith
    _ = 8 * ε / a.1 +
          2 *
            ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                (degreeLTSqMulNormConst N * (6 * ε)) +
              (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by ring
