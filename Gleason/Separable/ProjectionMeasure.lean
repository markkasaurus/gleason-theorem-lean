import GleasonStatement

/-!
# Countably Additive Projection Measures

Elementary projection operations, finite additivity, rank-one projections, and
the associated homogeneous quadratic function.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe u v

variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

namespace OrthogonalProjection

@[ext]
theorem ext {P Q : OrthogonalProjection 𝕜 H} (h : P.1 = Q.1) : P = Q :=
  Subtype.ext h

/-- Sum of two orthogonal projections. -/
def add (P Q : OrthogonalProjection 𝕜 H) (hPQ : P.1 * Q.1 = 0) :
    OrthogonalProjection 𝕜 H :=
  ⟨P.1 + Q.1, P.2.add Q.2 hPQ⟩

@[simp]
theorem add_val (P Q : OrthogonalProjection 𝕜 H) (hPQ : P.1 * Q.1 = 0) :
    (add P Q hPQ).1 = P.1 + Q.1 :=
  rfl

theorem orthogonal_comm {P Q : OrthogonalProjection 𝕜 H}
    (hPQ : P.1 * Q.1 = 0) : Q.1 * P.1 = 0 := by
  have h := congrArg star hPQ
  simpa [star_mul, P.2.isSelfAdjoint.star_eq, Q.2.isSelfAdjoint.star_eq] using h

/-- Orthogonal complement of a projection. -/
def complement (P : OrthogonalProjection 𝕜 H) : OrthogonalProjection 𝕜 H :=
  ⟨1 - P.1, P.2.one_sub⟩

@[simp]
theorem complement_val (P : OrthogonalProjection 𝕜 H) :
    (complement P).1 = 1 - P.1 :=
  rfl

theorem orthogonal_complement (P : OrthogonalProjection 𝕜 H) :
    P.1 * (complement P).1 = 0 :=
  P.2.mul_one_sub_self

@[simp]
theorem add_complement (P : OrthogonalProjection 𝕜 H) :
    add P (complement P) (orthogonal_complement P) = 1 := by
  apply ext
  change P.1 + (1 - P.1) = (1 : H →L[𝕜] H)
  abel

/-- Orthogonal projection onto the line spanned by `x`. -/
def rankOne (x : H) : OrthogonalProjection 𝕜 H := by
  let K : Submodule 𝕜 H := 𝕜 ∙ x
  letI : CompleteSpace K := FiniteDimensional.complete 𝕜 K
  exact ⟨K.starProjection, isStarProjection_starProjection⟩

@[simp]
theorem rankOne_val (x : H) :
    (rankOne (𝕜 := 𝕜) x).1 = (𝕜 ∙ x).starProjection :=
  rfl

@[simp]
theorem rankOne_zero : rankOne (𝕜 := 𝕜) (0 : H) = 0 := by
  apply ext
  change (𝕜 ∙ (0 : H)).starProjection = (0 : H →L[𝕜] H)
  simp [Submodule.span_zero_singleton]

theorem rankOne_smul {c : 𝕜} (hc : c ≠ 0) (x : H) :
    rankOne (c • x) = rankOne (𝕜 := 𝕜) x := by
  apply ext
  apply ContinuousLinearMap.IsStarProjection.ext (rankOne (𝕜 := 𝕜) (c • x)).2
    (rankOne (𝕜 := 𝕜) x).2
  simp only [rankOne_val, Submodule.range_starProjection]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) x

theorem rankOne_apply_of_unit (x : H) (hx : ‖x‖ = 1) (y : H) :
    (rankOne (𝕜 := 𝕜) x).1 y = inner 𝕜 x y • x := by
  simpa [rankOne_val] using Submodule.starProjection_unit_singleton 𝕜 hx y

end OrthogonalProjection

namespace ProjectionMeasure

variable (m : ProjectionMeasure 𝕜 H)

/-- Countable additivity implies ordinary additivity on an orthogonal pair. -/
theorem additive (P Q : OrthogonalProjection 𝕜 H) (hPQ : P.1 * Q.1 = 0) :
    m.μ (OrthogonalProjection.add P Q hPQ) = m.μ P + m.μ Q := by
  let A : ULift.{v} (Fin 2) → OrthogonalProjection 𝕜 H := fun i => ![P, Q] i.down
  have hA : Pairwise (fun i j => (A i).1 * (A j).1 = 0) := by
    intro i j hij
    obtain ⟨i⟩ := i
    obtain ⟨j⟩ := j
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [A] using hPQ
    · simpa [A] using OrthogonalProjection.orthogonal_comm hPQ
    · exact (hij rfl).elim
  have hsum :
      ∀ x : H,
        HasSum (fun i => (A i).1 x)
          ((OrthogonalProjection.add P Q hPQ).1 x) := by
    intro x
    have hbase :
        HasSum (fun i : Fin 2 => (![P, Q] i).1 x) (P.1 x + Q.1 x) := by
      simpa [Fin.sum_univ_two] using
        (hasSum_fintype (f := fun i : Fin 2 => (![P, Q] i).1 x))
    simpa [A, OrthogonalProjection.add] using
      ((Equiv.ulift : ULift.{v} (Fin 2) ≃ Fin 2).hasSum_iff.mpr hbase)
  have h := m.countably_additive A (OrthogonalProjection.add P Q hPQ) hA hsum
  have hbase : HasSum (fun i : Fin 2 => m.μ (![P, Q] i)) (m.μ P + m.μ Q) := by
    simpa [Fin.sum_univ_two] using
      (hasSum_fintype (f := fun i : Fin 2 => m.μ (![P, Q] i)))
  have hfinite : HasSum (fun i => m.μ (A i)) (m.μ P + m.μ Q) := by
    simpa [A] using
      ((Equiv.ulift : ULift.{v} (Fin 2) ≃ Fin 2).hasSum_iff.mpr hbase)
  exact h.unique hfinite

@[simp]
theorem zero : m.μ 0 = 0 := by
  have horth : (0 : OrthogonalProjection 𝕜 H).1 * (0 : OrthogonalProjection 𝕜 H).1 = 0 := by
    change (0 : H →L[𝕜] H) * 0 = 0
    simp
  have h := m.additive (0 : OrthogonalProjection 𝕜 H) 0 horth
  have hadd : OrthogonalProjection.add (0 : OrthogonalProjection 𝕜 H) 0 horth = 0 := by
    apply OrthogonalProjection.ext
    change (0 : H →L[𝕜] H) + 0 = 0
    simp
  rw [hadd] at h
  linarith

theorem le_one (P : OrthogonalProjection 𝕜 H) : m.μ P ≤ m.μ 1 := by
  have hadd := m.additive P (OrthogonalProjection.complement P)
    (OrthogonalProjection.orthogonal_complement P)
  rw [OrthogonalProjection.add_complement] at hadd
  linarith [m.nonneg (OrthogonalProjection.complement P)]

/-- The homogeneous quadratic function associated to rank-one values. -/
def quadraticValue (x : H) : ℝ :=
  m.μ (OrthogonalProjection.rankOne (𝕜 := 𝕜) x) * ‖x‖ ^ 2

@[simp]
theorem quadraticValue_zero : m.quadraticValue (0 : H) = 0 := by
  simp [quadraticValue]

theorem quadraticValue_nonneg (x : H) : 0 ≤ m.quadraticValue x :=
  mul_nonneg (m.nonneg _) (sq_nonneg ‖x‖)

theorem quadraticValue_le (x : H) :
    m.quadraticValue x ≤ m.μ 1 * ‖x‖ ^ 2 := by
  exact mul_le_mul_of_nonneg_right (m.le_one _) (sq_nonneg ‖x‖)

theorem abs_quadraticValue_le (x : H) :
    |m.quadraticValue x| ≤ m.μ 1 * ‖x‖ ^ 2 := by
  rw [abs_of_nonneg (m.quadraticValue_nonneg x)]
  exact m.quadraticValue_le x

theorem quadraticValue_smul (c : 𝕜) (x : H) :
    m.quadraticValue (c • x) = ‖c‖ ^ 2 * m.quadraticValue x := by
  by_cases hc : c = 0
  · subst c
    simp
  rw [quadraticValue, quadraticValue, OrthogonalProjection.rankOne_smul hc]
  simp only [norm_smul]
  ring

end ProjectionMeasure

end ClassicalGleason.Separable
