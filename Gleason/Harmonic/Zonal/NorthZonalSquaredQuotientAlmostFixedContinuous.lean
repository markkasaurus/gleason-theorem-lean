import Gleason.Harmonic.Zonal.NorthZonalSquaredQuotientFixedContinuous

noncomputable section
set_option maxHeartbeats 800000

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

theorem dist_northZonalSqQuotientAverage_iterate_succ_le
    (f : C(unitIcc, ℝ)) (m : ℕ) :
    dist ((northZonalSqQuotientAverage^[m]) f)
        ((northZonalSqQuotientAverage^[m.succ]) f)
      ≤ dist (northZonalSqQuotientAverage f) f := by
  have hiter :
      northZonalSqQuotientAverage ((northZonalSqQuotientAverage^[m]) f) =
        (northZonalSqQuotientAverage^[m]) (northZonalSqQuotientAverage f) := by
    induction m with
    | zero =>
        simp
    | succ m hm =>
        simp [Function.iterate_succ_apply', hm]
  rw [show (northZonalSqQuotientAverage^[m.succ]) f =
      northZonalSqQuotientAverage ((northZonalSqQuotientAverage^[m]) f) by
        rw [Function.iterate_succ_apply'],
      hiter]
  simpa [dist_comm] using
    dist_iterate_northZonalSqQuotientAverage_le f (northZonalSqQuotientAverage f) m

theorem dist_polynomial_to_iterate_northZonalSqQuotientAverage_le_of_almost_fixed
    (p : ℝ[X]) (m : ℕ) :
    dist (p.toContinuousMapOn unitIcc)
        ((northZonalSqQuotientAverage^[m]) (p.toContinuousMapOn unitIcc))
      ≤
        (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
          dist (northZonalSqQuotientAverage (p.toContinuousMapOn unitIcc))
            (p.toContinuousMapOn unitIcc) := by
  induction m with
  | zero =>
      simp
  | succ m hm =>
      calc
        dist (p.toContinuousMapOn unitIcc)
            ((northZonalSqQuotientAverage^[m.succ]) (p.toContinuousMapOn unitIcc))
          ≤ dist (p.toContinuousMapOn unitIcc)
                ((northZonalSqQuotientAverage^[m]) (p.toContinuousMapOn unitIcc)) +
              dist ((northZonalSqQuotientAverage^[m]) (p.toContinuousMapOn unitIcc))
                ((northZonalSqQuotientAverage^[m.succ]) (p.toContinuousMapOn unitIcc)) := by
                  exact dist_triangle _ _ _
        _ ≤
            (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                dist (northZonalSqQuotientAverage (p.toContinuousMapOn unitIcc))
                  (p.toContinuousMapOn unitIcc) +
              dist (northZonalSqQuotientAverage (p.toContinuousMapOn unitIcc))
                (p.toContinuousMapOn unitIcc) := by
                  gcongr
                  exact dist_northZonalSqQuotientAverage_iterate_succ_le
                    (p.toContinuousMapOn unitIcc) m
        _ =
            (Finset.sum (Finset.range m.succ) fun _ => (1 : ℝ)) *
              dist (northZonalSqQuotientAverage (p.toContinuousMapOn unitIcc))
                (p.toContinuousMapOn unitIcc) := by
                  rw [Finset.sum_range_succ]
                  ring

theorem dist_to_iterate_northZonalSqQuotientAverage_le_of_almost_fixed
    (f : C(unitIcc, ℝ)) (m : ℕ) :
    dist f ((northZonalSqQuotientAverage^[m]) f)
      ≤
        (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
          dist (northZonalSqQuotientAverage f) f := by
  induction m with
  | zero =>
      simp
  | succ m hm =>
      calc
        dist f ((northZonalSqQuotientAverage^[m.succ]) f)
          ≤ dist f ((northZonalSqQuotientAverage^[m]) f) +
              dist ((northZonalSqQuotientAverage^[m]) f)
                ((northZonalSqQuotientAverage^[m.succ]) f) := by
                  exact dist_triangle _ _ _
        _ ≤
            (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                dist (northZonalSqQuotientAverage f) f +
              dist (northZonalSqQuotientAverage f) f := by
                  gcongr
                  exact dist_northZonalSqQuotientAverage_iterate_succ_le f m
        _ =
            (Finset.sum (Finset.range m.succ) fun _ => (1 : ℝ)) *
              dist (northZonalSqQuotientAverage f) f := by
                rw [Finset.sum_range_succ]
                ring

theorem northZonalSqQuotientAverage_near_const_of_almost_fixed_iterate
    (f : C(unitIcc, ℝ))
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hδ : 0 ≤ δ)
    (halmost : dist (northZonalSqQuotientAverage f) f ≤ δ)
    (m : ℕ) :
    ∃ p : ℝ[X],
      dist f (p.toContinuousMapOn unitIcc) < ε ∧
      dist f (ContinuousMap.const _ (p.coeff 0))
        ≤ ε + (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
            (3 / 4 : ℝ) ^ m * polyTailAbsSum p := by
  haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 f ε hε
  let pMap : C(unitIcc, ℝ) := p.toContinuousMapOn unitIcc
  refine ⟨p, ?_, ?_⟩
  · simpa [pMap, dist_eq_norm, norm_sub_rev] using hp
  · have hdistfp : dist f pMap < ε := by
      simpa [pMap, dist_eq_norm, norm_sub_rev] using hp
    have hiterf :
        dist f ((northZonalSqQuotientAverage^[m]) f)
          ≤ (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ := by
      calc
        dist f ((northZonalSqQuotientAverage^[m]) f)
          ≤ (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
              dist (northZonalSqQuotientAverage f) f :=
            dist_to_iterate_northZonalSqQuotientAverage_le_of_almost_fixed f m
        _ ≤ (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ := by
              gcongr
    have hiterpf :
        dist ((northZonalSqQuotientAverage^[m]) f)
            ((northZonalSqQuotientAverage^[m]) pMap) ≤ dist f pMap := by
      exact dist_iterate_northZonalSqQuotientAverage_le f pMap m
    have hiterpconst :
        dist ((northZonalSqQuotientAverage^[m]) pMap)
            (ContinuousMap.const _ (p.coeff 0))
          ≤ (3 / 4 : ℝ) ^ m * polyTailAbsSum p := by
      simpa [pMap, dist_eq_norm] using
        norm_iterate_northZonalSqQuotientAverage_polynomial_sub_const_le p m
    calc
      dist f (ContinuousMap.const _ (p.coeff 0))
        ≤ dist f ((northZonalSqQuotientAverage^[m]) f) +
            dist ((northZonalSqQuotientAverage^[m]) f)
              ((northZonalSqQuotientAverage^[m]) pMap) +
            dist ((northZonalSqQuotientAverage^[m]) pMap)
              (ContinuousMap.const _ (p.coeff 0)) := by
                nlinarith [dist_triangle f ((northZonalSqQuotientAverage^[m]) f)
                  (ContinuousMap.const _ (p.coeff 0)),
                  dist_triangle ((northZonalSqQuotientAverage^[m]) f)
                    ((northZonalSqQuotientAverage^[m]) pMap)
                    (ContinuousMap.const _ (p.coeff 0))]
      _ ≤ (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
            dist f pMap +
            (3 / 4 : ℝ) ^ m * polyTailAbsSum p := by
              gcongr
      _ ≤ ε + (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
            (3 / 4 : ℝ) ^ m * polyTailAbsSum p := by
              linarith

theorem northZonalSqQuotientPolynomial_near_const_of_almost_fixed_iterate
    (p : ℝ[X]) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (halmost :
      dist (northZonalSqQuotientAverage (p.toContinuousMapOn unitIcc))
        (p.toContinuousMapOn unitIcc) ≤ δ)
    (m : ℕ) :
    dist (p.toContinuousMapOn unitIcc) (ContinuousMap.const _ (p.coeff 0))
      ≤
        (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
          (3 / 4 : ℝ) ^ m * polyTailAbsSum p := by
  have hiterf :
      dist (p.toContinuousMapOn unitIcc)
          ((northZonalSqQuotientAverage^[m]) (p.toContinuousMapOn unitIcc))
        ≤ (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ := by
    calc
      dist (p.toContinuousMapOn unitIcc)
          ((northZonalSqQuotientAverage^[m]) (p.toContinuousMapOn unitIcc))
        ≤ (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
            dist (northZonalSqQuotientAverage (p.toContinuousMapOn unitIcc))
              (p.toContinuousMapOn unitIcc) :=
          dist_to_iterate_northZonalSqQuotientAverage_le_of_almost_fixed
            (p.toContinuousMapOn unitIcc) m
      _ ≤ (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ := by
            gcongr
  have hiterpconst :
      dist ((northZonalSqQuotientAverage^[m]) (p.toContinuousMapOn unitIcc))
          (ContinuousMap.const _ (p.coeff 0))
        ≤ (3 / 4 : ℝ) ^ m * polyTailAbsSum p := by
    simpa [dist_eq_norm] using
      norm_iterate_northZonalSqQuotientAverage_polynomial_sub_const_le p m
  calc
    dist (p.toContinuousMapOn unitIcc) (ContinuousMap.const _ (p.coeff 0))
      ≤ dist (p.toContinuousMapOn unitIcc)
            ((northZonalSqQuotientAverage^[m]) (p.toContinuousMapOn unitIcc)) +
          dist ((northZonalSqQuotientAverage^[m]) (p.toContinuousMapOn unitIcc))
            (ContinuousMap.const _ (p.coeff 0)) := by
              exact dist_triangle _ _ _
    _ ≤ (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
          (3 / 4 : ℝ) ^ m * polyTailAbsSum p := by
            gcongr

theorem northZonalSqQuotientAverage_near_const_of_almost_fixed
    (f : C(unitIcc, ℝ))
    {ε δ : ℝ}
    (hε : 0 < ε)
    (hδ : 0 ≤ δ)
    (halmost : dist (northZonalSqQuotientAverage f) f ≤ δ) :
    ∃ p : ℝ[X], ∃ m : ℕ,
      dist f (p.toContinuousMapOn unitIcc) < ε ∧
      dist f (ContinuousMap.const _ (p.coeff 0))
        ≤ 3 * ε + (Finset.sum (Finset.range m) fun _ => (1 : ℝ)) * δ +
            (3 / 4 : ℝ) ^ m * polyTailAbsSum p := by
  haveI : Nonempty unitIcc := ⟨zeroUnitIcc⟩
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 f ε hε
  let pMap : C(unitIcc, ℝ) := p.toContinuousMapOn unitIcc
  refine ⟨p, 0, ?_, ?_⟩
  · simpa [pMap, dist_eq_norm, norm_sub_rev] using hp
  · have hp0eval : p.coeff 0 = pMap zeroUnitIcc := by
      change p.coeff 0 = p.eval 0
      simpa using p.coeff_zero_eq_eval_zero
    have hconstle :
        dist (ContinuousMap.const unitIcc (p.coeff 0))
            (ContinuousMap.const unitIcc (f zeroUnitIcc)) ≤
          dist pMap f := by
      have hconst0 :
          dist (ContinuousMap.const unitIcc (p.coeff 0))
              (ContinuousMap.const unitIcc (f zeroUnitIcc))
            = |p.coeff 0 - f zeroUnitIcc| := by
        rw [dist_eq_norm]
        let c : C(unitIcc, ℝ) := ContinuousMap.const unitIcc (p.coeff 0 - f zeroUnitIcc)
        have hc :
            ContinuousMap.const unitIcc (p.coeff 0) -
                ContinuousMap.const unitIcc (f zeroUnitIcc) = c := by
          ext u
          simp [c]
        rw [hc]
        have hle : ‖c‖ ≤ |p.coeff 0 - f zeroUnitIcc| := by
          refine (ContinuousMap.norm_le_of_nonempty
            (f := c) (M := |p.coeff 0 - f zeroUnitIcc|)).2 ?_
          intro u
          simp [c, Real.norm_eq_abs]
        have hge : |p.coeff 0 - f zeroUnitIcc| ≤ ‖c‖ := by
          simpa [c, Real.norm_eq_abs] using c.norm_coe_le_norm zeroUnitIcc
        exact le_antisymm hle hge
      rw [hconst0]
      rw [hp0eval]
      exact ContinuousMap.dist_apply_le_dist (f := pMap) (g := f) zeroUnitIcc
    have hdistpf : dist pMap f < ε := by
      simpa [pMap, dist_eq_norm] using hp
    have hdistfp : dist f pMap < ε := by
      simpa [dist_comm] using hdistpf
    calc
      dist f (ContinuousMap.const _ (p.coeff 0))
        ≤ dist f pMap + dist pMap (ContinuousMap.const _ (p.coeff 0)) := by
            exact dist_triangle _ _ _
      _ ≤ dist f pMap + polyTailAbsSum p := by
            gcongr
            simpa [pMap, dist_eq_norm] using norm_toContinuousMapOn_sub_const_le_polyTailAbsSum p
      _ ≤ 3 * ε + (Finset.sum (Finset.range 0) fun _ => (1 : ℝ)) * δ +
            (3 / 4 : ℝ) ^ 0 * polyTailAbsSum p := by
            simp
            linarith
