import Gleason.Separable.ProjectionMeasure

/-!
# Countable Hilbert-Basis Decompositions

In a separable Hilbert space every orthonormal family is countable. Rank-one
projections associated to a Hilbert basis are pairwise orthogonal and converge
strongly to the projection onto the closed span of that basis.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe u v

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The index type of a Hilbert basis in a separable Hilbert space is countable. -/
theorem HilbertBasis.index_countable [TopologicalSpace.SeparableSpace H]
    {ι : Type v} (b : HilbertBasis ι 𝕜 H) : Countable ι := by
  let B : ι → Set H := fun i => Metric.ball (b i) (1 / 2 : ℝ)
  apply Pairwise.countable_of_isOpen_disjoint (s := B)
  · intro i j hij
    apply Metric.ball_disjoint_ball
    have hsq : ‖b i - b j‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := 𝕜), b.orthonormal.inner_eq_zero hij]
      simp [b.orthonormal.norm_eq_one]
      norm_num
    have hnorm : 1 ≤ ‖b i - b j‖ := by
      nlinarith [norm_nonneg (b i - b j)]
    change (1 / 2 : ℝ) + 1 / 2 ≤ dist (b i) (b j)
    rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, dist_eq_norm]
    exact hnorm
  · intro i
    exact Metric.isOpen_ball
  · intro i
    exact ⟨b i, Metric.mem_ball_self (by norm_num)⟩

namespace OrthogonalProjection

theorem rankOne_hilbertBasis_pairwise {ι : Type v} (b : HilbertBasis ι 𝕜 H) :
    Pairwise (fun i j =>
      (rankOne (𝕜 := 𝕜) (b i)).1 * (rankOne (𝕜 := 𝕜) (b j)).1 = 0) := by
  intro i j hij
  ext x
  rw [ContinuousLinearMap.mul_apply,
    rankOne_apply_of_unit _ (b.orthonormal.norm_eq_one i),
    rankOne_apply_of_unit _ (b.orthonormal.norm_eq_one j)]
  simp [inner_smul_right, b.orthonormal.inner_eq_zero hij]

theorem hasSum_rankOne_hilbertBasis {ι : Type v}
    (b : HilbertBasis ι 𝕜 H) (x : H) :
    HasSum (fun i => (rankOne (𝕜 := 𝕜) (b i)).1 x) x := by
  have hsum := b.hasSum_repr x
  have hfun :
      (fun i => (rankOne (𝕜 := 𝕜) (b i)).1 x) =
        (fun i => b.repr x i • b i) := by
    funext i
    rw [rankOne_apply_of_unit _ (b.orthonormal.norm_eq_one i),
      b.repr_apply_apply]
  rw [hfun]
  exact hsum

theorem rankOne_basis_pairwise {U : Submodule 𝕜 H} [CompleteSpace U]
    {ι : Type v} (b : HilbertBasis ι 𝕜 U) :
    Pairwise (fun i j =>
      (rankOne (𝕜 := 𝕜) ((b i : U) : H)).1 *
        (rankOne (𝕜 := 𝕜) ((b j : U) : H)).1 = 0) := by
  intro i j hij
  ext x
  have hi : ‖((b i : U) : H)‖ = 1 := b.orthonormal.norm_eq_one i
  have hj : ‖((b j : U) : H)‖ = 1 := b.orthonormal.norm_eq_one j
  have hij0 : inner 𝕜 ((b i : U) : H) ((b j : U) : H) = 0 :=
    b.orthonormal.inner_eq_zero hij
  rw [ContinuousLinearMap.mul_apply,
    rankOne_apply_of_unit _ hi,
    rankOne_apply_of_unit _ hj]
  simp [inner_smul_right, hij0]

theorem hasSum_rankOne_basis {U : Submodule 𝕜 H} [CompleteSpace U]
    {ι : Type v} (b : HilbertBasis ι 𝕜 U) (x : H) :
    HasSum
      (fun i => (rankOne (𝕜 := 𝕜) ((b i : U) : H)).1 x)
      (U.starProjection x) := by
  have hsum := (b.hasSum_orthogonalProjection x).mapL U.subtypeL
  change HasSum
    (fun i => (rankOne (𝕜 := 𝕜) ((b i : U) : H)).1 x)
    (U.subtypeL (U.orthogonalProjection x))
  have hfun :
      (fun i => (rankOne (𝕜 := 𝕜) ((b i : U) : H)).1 x) =
        (fun i => U.subtypeL (inner 𝕜 ((b i : U) : H) x • b i)) := by
    funext i
    have hi : ‖((b i : U) : H)‖ = 1 := b.orthonormal.norm_eq_one i
    rw [rankOne_apply_of_unit _ hi]
    rfl
  rw [hfun]
  exact hsum

theorem hasSum_rankOne_range (P : OrthogonalProjection 𝕜 H)
    {ι : Type v} (b : HilbertBasis ι 𝕜 (LinearMap.range P.1)) (x : H) :
    HasSum
      (fun i =>
        (rankOne (𝕜 := 𝕜)
          ((b i : LinearMap.range P.1) : H)).1 x)
      (P.1 x) := by
  letI : CompleteSpace (LinearMap.range P.1) :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      P.2.isIdempotentElem).completeSpace_coe
  letI : (LinearMap.range P.1).HasOrthogonalProjection :=
    (isStarProjection_iff_eq_starProjection_range.mp P.2).choose
  have hP : P.1 = (LinearMap.range P.1).starProjection :=
    (isStarProjection_iff_eq_starProjection_range.mp P.2).choose_spec
  have hsum := hasSum_rankOne_basis (𝕜 := 𝕜) b x
  have htarget : (LinearMap.range P.1).starProjection x = P.1 x := by
    rw [← hP]
  exact htarget ▸ hsum

end OrthogonalProjection

end ClassicalGleason.Separable
