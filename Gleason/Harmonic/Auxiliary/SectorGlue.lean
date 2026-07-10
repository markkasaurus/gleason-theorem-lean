import Gleason.Harmonic.Auxiliary.SingleWitness
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Order.SupIndep

noncomputable section

open Set
open scoped BigOperators
open InnerProductSpace

def equatorRestrictionLinear :
    (WithLp 2 (ℂ × ℝ) → ℝ) →ₗ[ℝ] (ℝ → ℝ) where
  toFun := equatorRestrictionL2
  map_add' := by
    intro f g
    funext θ
    rfl
  map_smul' := by
    intro c f
    funext θ
    rfl

def frameAdmissibleCircleSubmodule : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | circleFrameFunction f}
  zero_mem' := by
    simpa using circleFrameFunction_const (0 : ℝ)
  add_mem' := by
    intro f g hf hg
    exact circleFrameFunction_add hf hg
  smul_mem' := by
    intro c f hf
    simpa [Pi.smul_apply] using circleFrameFunction_smul c hf

def harmonicHomogeneousDegreeSubmodule (n : ℕ) :
    Submodule ℝ (WithLp 2 (ℂ × ℝ) → ℝ) where
  carrier := {f | HarmonicHomogeneousDegree n f}
  zero_mem' := by
    constructor
    · intro p
      simpa [Pi.zero_apply] using
        HarmonicAt.const_smul (c := (0 : ℝ)) (surfaceModeAL2_harmonicAt 0 p)
    · intro t p
      simp
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨hfHarm, hfHom⟩
    rcases hg with ⟨hgHarm, hgHom⟩
    constructor
    · intro p
      simpa [Pi.add_apply] using HarmonicAt.add (hfHarm p) (hgHarm p)
    · intro t p
      simp [hfHom t p, hgHom t p, mul_add]
  smul_mem' := by
    intro c f hf
    rcases hf with ⟨hfHarm, hfHom⟩
    constructor
    · intro p
      simpa [Pi.smul_apply] using HarmonicAt.const_smul (c := c) (hfHarm p)
    · intro t p
      simpa [Pi.smul_apply, smul_eq_mul, hfHom t p, mul_assoc, mul_left_comm, mul_comm]

theorem not_harmonicHomogeneousDegreeSubmodule_le_frameAdmissible {n : ℕ} (hn : 2 < n) :
    ¬ harmonicHomogeneousDegreeSubmodule n ≤
        (frameAdmissibleCircleSubmodule.comap equatorRestrictionLinear) := by
  intro hle
  exact not_all_harmonicHomogeneousDegree_have_circleFrame hn <| by
    intro f hf
    exact hle hf

theorem mem_of_le_iSup_subtype_of_nonbot_of_iSupIndep
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : ℕ → Submodule ℝ V} (hQind : iSupIndep Q) (hQnontriv : ∀ n, Q n ≠ ⊥)
    {s : Set ℕ} {n : ℕ}
    (hle : Q n ≤ ⨆ i : s, Q i) :
    n ∈ s := by
  by_contra hns
  have hdisj :
      Disjoint (Q n) (⨆ j, ⨆ (_ : j ≠ n), Q j) := hQind n
  have hs_le :
      (⨆ i : s, Q i) ≤ ⨆ j, ⨆ (_ : j ≠ n), Q j := by
    refine iSup_le ?_
    intro i
    refine le_iSup_of_le i.1 ?_
    refine le_iSup_of_le ?_ le_rfl
    intro hi
    exact hns (hi ▸ i.2)
  have hdisj' : Disjoint (Q n) (⨆ i : s, Q i) := hdisj.mono_right hs_le
  exact hQnontriv n (hdisj'.eq_bot_of_le hle)

theorem eq_sup_zero_two_of_independent_sector_decomposition
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {Q : ℕ → Submodule ℝ V} (hQind : iSupIndep Q) (hQnontriv : ∀ n, Q n ≠ ⊥)
    {F : Submodule ℝ V} {s : Set ℕ}
    (hF : F = ⨆ i : s, Q i)
    (hQ0 : Q 0 ≤ F) (hQ2 : Q 2 ≤ F)
    (hQ1 : ¬ Q 1 ≤ F)
    (hQgt2 : ∀ n, 2 < n → ¬ Q n ≤ F) :
    F = Q 0 ⊔ Q 2 := by
  have hs0 : 0 ∈ s := by
    apply mem_of_le_iSup_subtype_of_nonbot_of_iSupIndep hQind hQnontriv
    simpa [hF] using hQ0
  have hs2 : 2 ∈ s := by
    apply mem_of_le_iSup_subtype_of_nonbot_of_iSupIndep hQind hQnontriv
    simpa [hF] using hQ2
  have hs_subset : s ⊆ ({0, 2} : Set ℕ) := by
    intro n hn
    have hQn : Q n ≤ F := by
      rw [hF]
      exact le_iSup (fun i : s => Q i) ⟨n, hn⟩
    cases n with
    | zero =>
        simp
    | succ n =>
        cases n with
        | zero =>
            exact (hQ1 hQn).elim
        | succ n' =>
            cases n' with
            | zero =>
                simp
            | succ n'' =>
                have hgt : 2 < Nat.succ (Nat.succ (Nat.succ n'')) := by omega
                exact (hQgt2 _ hgt hQn).elim
  have hs_eq : s = ({0, 2} : Set ℕ) := by
    ext n
    constructor
    · intro hn
      exact hs_subset hn
    · intro hn
      rcases hn with rfl | rfl
      · exact hs0
      · exact hs2
  rw [hF, hs_eq]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    rintro ⟨i, hi⟩
    rcases hi with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · rw [sup_le_iff]
    constructor
    · exact le_iSup (fun i : ({0, 2} : Set ℕ) => Q i) ⟨0, by simp⟩
    · exact le_iSup (fun i : ({0, 2} : Set ℕ) => Q i) ⟨2, by simp⟩
