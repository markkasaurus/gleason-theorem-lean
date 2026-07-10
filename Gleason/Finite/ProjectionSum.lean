
import Mathlib
import Gleason.Finite.FrameFunction

noncomputable section

open scoped BigOperators

namespace Projection

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

variable {ι : Type*}

/--
Left-multiplication distributes over `Finset.sum`.

We keep this lemma local so we don't depend on a particular Mathlib lemma name.
-/
lemma mul_finset_sum {α β : Type*} [Semiring α]
    (a : α) (s : Finset β) (f : β → α) :
    a * Finset.sum s f = Finset.sum s (fun i => a * f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro x t hx ih
    simp [hx, ih, mul_add]

/-- Existence of a projection whose underlying operator is the finite sum of a pairwise-orthogonal family. -/
theorem sum_exists (s : Finset ι) (P : ι → Projection H)
    (h : ∀ i j, i ≠ j → Projection.orthogonal (P i) (P j)) :
    ∃ Q : Projection H, Q.1 = Finset.sum s (fun i => (P i).1) := by
  classical
  refine Finset.induction_on s ?base ?step
  · refine ⟨Projection.zero (H := H), ?_⟩
    simp [Projection.zero]
  · intro a t ha ih
    rcases ih with ⟨Q, hQ⟩

    have hOrth : Projection.orthogonal (P a) Q := by
      unfold Projection.orthogonal
      rw [hQ]
      -- distribute multiplication over the finite sum
      have hm :
          (P a).1 * Finset.sum t (fun i => (P i).1)
            = Finset.sum t (fun i => (P a).1 * (P i).1) := by
        simpa using (mul_finset_sum (a := (P a).1) (s := t) (f := fun i => (P i).1))
      rw [hm]
      -- each term is zero by pairwise orthogonality
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hai : a ≠ i := by
        intro hEq
        subst hEq
        exact ha hi
      have hAi : Projection.orthogonal (P a) (P i) := h a i hai
      simpa [Projection.orthogonal] using hAi

    refine ⟨Projection.add (H := H) (P a) Q hOrth, ?_⟩
    -- underlying operator is the finset sum
    simp [Projection.add, hQ, Finset.sum_insert, ha]

/-- Sum of a finite family of pairwise orthogonal projections. -/
def sum (s : Finset ι) (P : ι → Projection H)
    (h : ∀ i j, i ≠ j → Projection.orthogonal (P i) (P j)) : Projection H :=
  Classical.choose (sum_exists (H := H) (s := s) (P := P) (h := h))

@[simp] lemma sum_coe (s : Finset ι) (P : ι → Projection H)
    (h : ∀ i j, i ≠ j → Projection.orthogonal (P i) (P j)) :
    (Projection.sum (H := H) (ι := ι) s P h).1 = Finset.sum s (fun i => (P i).1) := by
  classical
  simpa [Projection.sum] using
    (Classical.choose_spec (sum_exists (H := H) (s := s) (P := P) (h := h)))

/-- Partial sums remain orthogonal to the next element. -/
lemma orthogonal_left_sum (s : Finset ι) (P : ι → Projection H)
    (h : ∀ i j, i ≠ j → Projection.orthogonal (P i) (P j))
    (a : ι) (ha : a ∉ s) :
    Projection.orthogonal (P a) (Projection.sum (H := H) (ι := ι) s P h) := by
  classical
  unfold Projection.orthogonal
  rw [Projection.sum_coe (H := H) (ι := ι) (s := s) (P := P) (h := h)]
  have hm :
      (P a).1 * Finset.sum s (fun i => (P i).1)
        = Finset.sum s (fun i => (P a).1 * (P i).1) := by
    simpa using (mul_finset_sum (a := (P a).1) (s := s) (f := fun i => (P i).1))
  rw [hm]
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hai : a ≠ i := by
    intro hEq
    subst hEq
    exact ha hi
  have hAi : Projection.orthogonal (P a) (P i) := h a i hai
  simpa [Projection.orthogonal] using hAi

end Projection

namespace FrameFunction

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

variable {ι : Type*}

/-- Any frame function sends the zero projection to `0`. -/
lemma map_zero (μ : FrameFunction H) : μ.μ (Projection.zero (H := H)) = 0 := by
  classical
  have h00 : Projection.orthogonal (Projection.zero (H := H)) (Projection.zero (H := H)) := by
    unfold Projection.orthogonal
    simp [Projection.zero]
  have hadd := μ.additive (Projection.zero (H := H)) (Projection.zero (H := H)) h00
  have hz :
      Projection.add (H := H) (Projection.zero (H := H)) (Projection.zero (H := H)) h00
        =
      Projection.zero (H := H) := by
    apply Subtype.ext
    simp [Projection.add, Projection.zero]
  have heq :
      μ.μ (Projection.zero (H := H))
        = μ.μ (Projection.zero (H := H)) + μ.μ (Projection.zero (H := H)) := by
    simpa [hz] using hadd
  linarith

/-- Frame functions are additive over finite sums of pairwise orthogonal projections. -/
theorem map_sum (μ : FrameFunction H) (s : Finset ι) (P : ι → Projection H)
    (h : ∀ i j, i ≠ j → Projection.orthogonal (P i) (P j)) :
    μ.μ (Projection.sum (H := H) (ι := ι) s P h)
      =
    Finset.sum s (fun i => μ.μ (P i)) := by
  classical
  refine Finset.induction_on s ?base ?step
  · -- empty set
    have hs0 :
      Projection.sum (H := H) (ι := ι) (∅ : Finset ι) P h = Projection.zero (H := H) := by
      apply Subtype.ext
      simp [Projection.sum_coe, Projection.zero]
    simpa [hs0, FrameFunction.map_zero (H := H) μ]
  · intro a t ha ih
    have hOrth :
        Projection.orthogonal (P a) (Projection.sum (H := H) (ι := ι) t P h) :=
      Projection.orthogonal_left_sum (H := H) (ι := ι) (s := t) (P := P) (h := h) a ha

    have hsum :
        Projection.sum (H := H) (ι := ι) (insert a t) P h
          =
        Projection.add (H := H) (P a) (Projection.sum (H := H) (ι := ι) t P h) hOrth := by
      apply Subtype.ext
      -- reduce to a Finset.sum_insert statement
      simp [Projection.sum_coe, Projection.add, Finset.sum_insert, ha]

    calc
      μ.μ (Projection.sum (H := H) (ι := ι) (insert a t) P h)
          = μ.μ (Projection.add (H := H) (P a)
                (Projection.sum (H := H) (ι := ι) t P h) hOrth) := by
              simpa [hsum]
      _   = μ.μ (P a) + μ.μ (Projection.sum (H := H) (ι := ι) t P h) :=
              μ.additive (P a) (Projection.sum (H := H) (ι := ι) t P h) hOrth
      _   = μ.μ (P a) + Finset.sum t (fun i => μ.μ (P i)) := by
              simpa [ih]
      _   = Finset.sum (insert a t) (fun i => μ.μ (P i)) := by
              simp [Finset.sum_insert, ha]

end FrameFunction
