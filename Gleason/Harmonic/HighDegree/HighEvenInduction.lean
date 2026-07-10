import Gleason.Harmonic.HighDegree.HighEvenBoundedClosure
import Gleason.Harmonic.Sectors.LowHarmonicRepresentation
import Gleason.Harmonic.Fischer.FischerDirect
import Gleason.Harmonic.Fischer.FischerBasic

noncomputable section

open Complex InnerProductSpace

def highEvenHarmonicPolySubmodule (N : ℕ) :
    Submodule ℝ (MvPolynomial (Fin 3) ℝ) :=
  (Finset.Icc 2 N).sup fun k => harmonicPolyHomogeneousSubmodule (2 * k)

private theorem finset_sup_harmonicPolyImage_eq_map_finset_sup_harmonicPoly
    (s : Finset ℕ) :
    s.sup (fun k => harmonicPolyHomogeneousImageSubmodule (2 * k)) =
      (s.sup fun k => harmonicPolyHomogeneousSubmodule (2 * k)).map sphereCoordMvEval.toLinearMap := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert a s ha ih =>
      rw [Finset.sup_insert, Finset.sup_insert, Submodule.map_sup]
      rw [ih]
      rfl

theorem highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_map_highEvenHarmonicPolySubmodule
    (N : ℕ) :
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N =
      (highEvenHarmonicPolySubmodule N).map sphereCoordMvEval.toLinearMap := by
  unfold highEvenBoundedHarmonicPolyHomogeneousImageSubmodule highEvenHarmonicPolySubmodule
  exact finset_sup_harmonicPolyImage_eq_map_finset_sup_harmonicPoly (Finset.Icc 2 N)

theorem exists_highEven_harmonic_mvPolynomial_of_mem_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      p ∈ highEvenHarmonicPolySubmodule N ∧
      sphereCoordMvEval p = f := by
  rw [highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_map_highEvenHarmonicPolySubmodule] at hf
  exact hf

theorem highEvenHarmonicPolySubmodule_eq_bot_of_lt_two
    {N : ℕ} (hN : N < 2) :
    highEvenHarmonicPolySubmodule N = ⊥ := by
  unfold highEvenHarmonicPolySubmodule
  have hIcc : Finset.Icc 2 N = ∅ := by
    ext k
    simp [Finset.mem_Icc]
    omega
  simp [hIcc]

theorem highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_bot_of_lt_two
    {N : ℕ} (hN : N < 2) :
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N = ⊥ := by
  rw [highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_map_highEvenHarmonicPolySubmodule]
  simp [highEvenHarmonicPolySubmodule_eq_bot_of_lt_two hN]

theorem highEvenHarmonicPolySubmodule_succ_succ (N : ℕ) :
    highEvenHarmonicPolySubmodule (N + 2) =
      harmonicPolyHomogeneousSubmodule (2 * (N + 2)) ⊔
        highEvenHarmonicPolySubmodule (N + 1) := by
  unfold highEvenHarmonicPolySubmodule
  have hIcc :
      Finset.Icc 2 (N + 2) = insert (N + 2) (Finset.Icc 2 (N + 1)) := by
    ext k
    simp [Finset.mem_Icc]
    omega
  have hmem : N + 2 ∉ Finset.Icc 2 (N + 1) := by
    simp [Finset.mem_Icc]
  rw [hIcc]
  simp [hmem]

theorem highEvenHarmonicPolySubmodule_le_restrictTotalDegree
    (N : ℕ) :
    highEvenHarmonicPolySubmodule N ≤
      MvPolynomial.restrictTotalDegree (Fin 3) ℝ (2 * N) := by
  unfold highEvenHarmonicPolySubmodule
  refine Finset.sup_le ?_
  intro k hk p hp
  exact (MvPolynomial.mem_restrictTotalDegree (σ := Fin 3) (R := ℝ) (m := 2 * N) p).2 <|
    le_trans hp.1.totalDegree_le (by
      have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
      omega)

theorem homogeneousImage_two_mul_mono
    {k N : ℕ} (hkN : k ≤ N) :
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * k)).map sphereCoordMvEval.toLinearMap ≤
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * N)).map sphereCoordMvEval.toLinearMap := by
  induction hkN with
  | refl =>
      exact le_rfl
  | @step N hk ih =>
      exact ih.trans <| by
        rintro f ⟨p, hp, rfl⟩
        refine ⟨rhoPoly * p, ?_, ?_⟩
        · have hrhoHom : rhoPoly.IsHomogeneous 2 := by
              simpa [MvPolynomial.mem_homogeneousSubmodule, rhoPoly, add_assoc, add_left_comm, add_comm] using
                (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 0 2).add
                  ((MvPolynomial.isHomogeneous_X_pow (R := ℝ) 1 2).add
                    (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 2 2))
          simpa [two_mul, add_assoc, add_left_comm, add_comm] using hrhoHom.mul hp
        · simpa [sphereCoordMvEval_rhoPoly_mul]

theorem evenBoundedHarmonicPolyHomogeneousImageSubmodule_le_homogeneousImage_top
    (N : ℕ) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N ≤
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * N)).map sphereCoordMvEval.toLinearMap := by
  unfold evenBoundedHarmonicPolyHomogeneousImageSubmodule
  refine iSup_le ?_
  intro i
  exact (harmonicPolyHomogeneousImageSubmodule_le_homogeneousImage (2 * i.1)).trans <|
    homogeneousImage_two_mul_mono i.2

theorem lowHarmonicPolyHomogeneousImageSubmodule_le_homogeneousImage_two_mul
    {N : ℕ} (hN : 1 ≤ N) :
    lowHarmonicPolyHomogeneousImageSubmodule ≤
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * N)).map sphereCoordMvEval.toLinearMap := by
  calc
    lowHarmonicPolyHomogeneousImageSubmodule
        ≤ evenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
          refine sup_le ?_ ?_
          · exact le_iSup (fun i : Set.Iic N => harmonicPolyHomogeneousImageSubmodule (2 * i.1))
              ⟨0, Nat.zero_le _⟩
          · exact le_iSup (fun i : Set.Iic N => harmonicPolyHomogeneousImageSubmodule (2 * i.1))
              ⟨1, hN⟩
    _ ≤ (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * N)).map sphereCoordMvEval.toLinearMap :=
      evenBoundedHarmonicPolyHomogeneousImageSubmodule_le_homogeneousImage_top N

theorem highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_homogeneousImage_two_mul
    (N : ℕ) :
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ≤
      (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * N)).map sphereCoordMvEval.toLinearMap := by
  calc
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N
        ≤ evenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule N
    _ ≤ (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * N)).map sphereCoordMvEval.toLinearMap :=
      evenBoundedHarmonicPolyHomogeneousImageSubmodule_le_homogeneousImage_top N

theorem eq_zero_of_mem_lowHarmonicPolyHomogeneousImageSubmodule_and_mem_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} {g : C(spherePoint3, ℝ)}
    (hgLow : g ∈ lowHarmonicPolyHomogeneousImageSubmodule)
    (hgHigh : g ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    g = 0 := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
      by_cases hN : N < 2
      · have hbot := highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_bot_of_lt_two hN
        simpa [hbot] using hgHigh
      · rcases exists_highEven_harmonic_mvPolynomial_of_mem_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule
          hgHigh with ⟨p, hpHigh, hpEval⟩
        rcases exists_low_harmonic_mvPolynomial_of_mem_lowHarmonicPolyHomogeneousImageSubmodule hgLow with
          ⟨r, hrdeg, hrΔ, hrEval⟩
        have hN' : 2 ≤ N := by omega
        rcases Nat.exists_eq_add_of_le hN' with ⟨M, rfl⟩
        have hpHigh' : p ∈ highEvenHarmonicPolySubmodule (M + 2) := by
          simpa [add_assoc, add_left_comm, add_comm] using hpHigh
        rw [highEvenHarmonicPolySubmodule_succ_succ] at hpHigh'
        rcases Submodule.mem_sup.mp hpHigh' with ⟨pTop, hpTop, pRest, hpRest, hpSplit⟩
        have hTopEval :
            sphereCoordMvEval pTop =
              sphereCoordMvEval (r - pRest) := by
          have hsplitEval :
              sphereCoordMvEval pTop + sphereCoordMvEval pRest = sphereCoordMvEval p := by
            calc
              sphereCoordMvEval pTop + sphereCoordMvEval pRest
                  = sphereCoordMvEval (pTop + pRest) := by rw [map_add]
              _ = sphereCoordMvEval p := by rw [hpSplit]
          calc
            sphereCoordMvEval pTop = sphereCoordMvEval p - sphereCoordMvEval pRest := by
              rw [← hsplitEval]
              abel
            _ = g - sphereCoordMvEval pRest := by rw [hpEval]
            _ = sphereCoordMvEval r - sphereCoordMvEval pRest := by rw [hrEval]
            _ = sphereCoordMvEval (r - pRest) := by rw [map_sub]
        have hRestEval :
            sphereCoordMvEval (r - pRest) ∈
              (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * (M + 1))).map
                sphereCoordMvEval.toLinearMap := by
          have hgLow' : sphereCoordMvEval r ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
            simpa [hrEval] using hgLow
          have hrLift :
              sphereCoordMvEval r ∈
                (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * (M + 1))).map
                  sphereCoordMvEval.toLinearMap :=
            lowHarmonicPolyHomogeneousImageSubmodule_le_homogeneousImage_two_mul (N := M + 1) (by omega) hgLow'
          have hpRestLift :
              sphereCoordMvEval pRest ∈
                (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * (M + 1))).map
                  sphereCoordMvEval.toLinearMap := by
            exact highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_homogeneousImage_two_mul
              (N := M + 1) <|
              by
                rw [highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_map_highEvenHarmonicPolySubmodule]
                exact ⟨pRest, hpRest, rfl⟩
          simpa [map_sub] using Submodule.sub_mem _ hrLift hpRestLift
        have hzeroTopEval :
            sphereCoordMvEval pTop = 0 := by
          have hdisj :
              Disjoint
                (harmonicPolyHomogeneousImageSubmodule (2 * (M + 2)))
                ((MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (2 * (M + 1))).map
                  sphereCoordMvEval.toLinearMap) :=
            harmonicPolyHomogeneousImageSubmodule_disjoint_prev_homogeneousImage (n := 2 * (M + 2))
              (by omega)
          exact (Submodule.disjoint_def.mp hdisj) _ ⟨pTop, hpTop, rfl⟩ (by simpa [hTopEval] using hRestEval)
        have hpTopZero : pTop = 0 := by
          exact eq_zero_of_sphereCoordMvEval_eq_zero_of_mem_homogeneousSubmodule hpTop.1 hzeroTopEval
        subst hpTopZero
        have hpRestEval : sphereCoordMvEval pRest = g := by
          calc
            sphereCoordMvEval pRest = sphereCoordMvEval (0 + pRest) := by simp
            _ = sphereCoordMvEval p := by simpa [hpSplit] using congrArg sphereCoordMvEval hpSplit
            _ = g := hpEval
        have hgRest :
            g ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule (M + 1) := by
          rw [← hpRestEval]
          rw [highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_map_highEvenHarmonicPolySubmodule]
          exact ⟨pRest, hpRest, rfl⟩
        exact ih (M + 1) (by omega) hgRest

theorem lowHarmonicPolyHomogeneousImageSubmodule_inf_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_bot
    (N : ℕ) :
    lowHarmonicPolyHomogeneousImageSubmodule ⊓
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  exact
    eq_zero_of_mem_lowHarmonicPolyHomogeneousImageSubmodule_and_mem_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule
      hg.1 hg.2
