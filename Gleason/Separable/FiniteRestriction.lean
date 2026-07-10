import Gleason.Separable.ProjectionMeasure
import Gleason.Finite.Theorem

/-!
# Restriction to Finite-Dimensional Subspaces

Operators and projection measures are transported between a finite-dimensional
closed subspace and the ambient Hilbert space. This is the local-to-global
bridge for the separable theorem.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FiniteRestriction

variable (K : Submodule ℂ H) [FiniteDimensional ℂ K]

/-- Extend an operator on `K` by zero on `Kᗮ`. -/
def extendOperator (T : K →L[ℂ] K) : H →L[ℂ] H :=
  K.subtypeL ∘L T ∘L K.orthogonalProjection

@[simp]
theorem extendOperator_apply (T : K →L[ℂ] K) (x : H) :
    extendOperator K T x = T (K.orthogonalProjection x) :=
  rfl

@[simp]
theorem extendOperator_zero : extendOperator K (0 : K →L[ℂ] K) = 0 := by
  ext x
  simp [extendOperator]

@[simp]
theorem extendOperator_add (S T : K →L[ℂ] K) :
    extendOperator K (S + T) = extendOperator K S + extendOperator K T := by
  ext x
  simp [extendOperator]

@[simp]
theorem extendOperator_sub (S T : K →L[ℂ] K) :
    extendOperator K (S - T) = extendOperator K S - extendOperator K T := by
  ext x
  simp [extendOperator]

@[simp]
theorem extendOperator_mul (S T : K →L[ℂ] K) :
    extendOperator K (S * T) = extendOperator K S * extendOperator K T := by
  ext x
  simp [extendOperator, ContinuousLinearMap.mul_apply]

theorem range_extendOperator (T : K →L[ℂ] K) :
    LinearMap.range (extendOperator K T) =
      (LinearMap.range T).map K.subtype := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨T (K.orthogonalProjection x), LinearMap.mem_range_self _ _, rfl⟩
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    refine ⟨(w : H), ?_⟩
    simp [extendOperator]

theorem extendOperator_isStarProjection {P : K →L[ℂ] K}
    (hP : IsStarProjection P) : IsStarProjection (extendOperator K P) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, ← extendOperator_mul, hP.isIdempotentElem.eq]
  · rw [isSelfAdjoint_iff]
    have hPadj : ContinuousLinearMap.adjoint P = P := by
      simpa [← ContinuousLinearMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
    simp [ContinuousLinearMap.star_eq_adjoint, extendOperator,
      ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL,
      Submodule.adjoint_orthogonalProjection, hPadj]
    rfl

/-- Lift an orthogonal projection on `K` to the ambient space. -/
def extendProjection (P : OrthogonalProjection ℂ K) : OrthogonalProjection ℂ H :=
  ⟨extendOperator K P.1, extendOperator_isStarProjection K P.2⟩

@[simp]
theorem extendProjection_val (P : OrthogonalProjection ℂ K) :
    (extendProjection K P).1 = extendOperator K P.1 :=
  rfl

@[simp]
theorem extendProjection_zero :
    extendProjection K (0 : OrthogonalProjection ℂ K) = 0 := by
  apply OrthogonalProjection.ext
  exact extendOperator_zero K

theorem extendProjection_add (P Q : OrthogonalProjection ℂ K)
    (hPQ : P.1 * Q.1 = 0) :
    extendProjection K (OrthogonalProjection.add P Q hPQ) =
      OrthogonalProjection.add (extendProjection K P) (extendProjection K Q)
        (by simpa [extendProjection_val, ← extendOperator_mul] using
          congrArg (extendOperator K) hPQ) := by
  apply OrthogonalProjection.ext
  exact extendOperator_add K P.1 Q.1

theorem extendProjection_orthogonal {P Q : OrthogonalProjection ℂ K}
    (hPQ : P.1 * Q.1 = 0) :
    (extendProjection K P).1 * (extendProjection K Q).1 = 0 := by
  change extendOperator K P.1 * extendOperator K Q.1 = 0
  rw [← extendOperator_mul]
  simpa using congrArg (extendOperator K) hPQ

/-- Projection onto `K`, regarded as an ambient bundled projection. -/
def subspaceProjection : OrthogonalProjection ℂ H :=
  ⟨K.starProjection, isStarProjection_starProjection⟩

@[simp]
theorem subspaceProjection_val : (subspaceProjection K).1 = K.starProjection :=
  rfl

@[simp]
theorem extendProjection_one :
    extendProjection K (1 : OrthogonalProjection ℂ K) = subspaceProjection K := by
  apply OrthogonalProjection.ext
  ext x
  rfl

theorem measure_extendProjection_le (m : ProjectionMeasure ℂ H)
    (P : OrthogonalProjection ℂ K) :
    m.μ (extendProjection K P) ≤ m.μ (subspaceProjection K) := by
  have horth := OrthogonalProjection.orthogonal_complement P
  have hadd := m.additive (extendProjection K P)
    (extendProjection K (OrthogonalProjection.complement P))
    (extendProjection_orthogonal K horth)
  rw [← extendProjection_add K P (OrthogonalProjection.complement P) horth,
    OrthogonalProjection.add_complement, extendProjection_one] at hadd
  linarith [m.nonneg (extendProjection K (OrthogonalProjection.complement P))]

/-- Convert the project's finite-dimensional bundled projection to Mathlib's
star-projection predicate and extend it to the ambient space. -/
def extendBundledProjection (P : Projection K) : OrthogonalProjection ℂ H :=
  extendProjection K
    ⟨P.1, ⟨by simpa [IsIdempotentElem] using P.2.1,
      ClassicalGleason.isSelfAdjoint_of_projection (H := K) P⟩⟩

@[simp]
theorem extendBundledProjection_val (P : Projection K) :
    (extendBundledProjection K P).1 = extendOperator K P.1 :=
  rfl

theorem extendBundledProjection_orthogonal {P Q : Projection K}
    (hPQ : Projection.orthogonal P Q) :
    (extendBundledProjection K P).1 * (extendBundledProjection K Q).1 = 0 :=
  extendProjection_orthogonal K hPQ

theorem extendBundledProjection_add (P Q : Projection K)
    (hPQ : Projection.orthogonal P Q) :
    extendBundledProjection K (Projection.add P Q hPQ) =
      OrthogonalProjection.add (extendBundledProjection K P)
        (extendBundledProjection K Q)
        (extendBundledProjection_orthogonal K hPQ) := by
  apply OrthogonalProjection.ext
  exact extendOperator_add K P.1 Q.1

@[simp]
theorem extendBundledProjection_one :
    extendBundledProjection K (Projection.one (H := K)) = subspaceProjection K := by
  apply OrthogonalProjection.ext
  ext x
  simp [extendBundledProjection, extendProjection, extendOperator,
    Projection.one, subspaceProjection]

theorem extendBundled_rankOne (z : K) (hz : z ≠ 0) :
    extendBundledProjection K (RankOne.rankOneProjection (H := K) z hz) =
      OrthogonalProjection.rankOne (𝕜 := ℂ) (z : H) := by
  apply OrthogonalProjection.ext
  apply ContinuousLinearMap.IsStarProjection.ext
    (extendBundledProjection K (RankOne.rankOneProjection (H := K) z hz)).2
    (OrthogonalProjection.rankOne (𝕜 := ℂ) (z : H)).2
  rw [extendBundledProjection_val, range_extendOperator]
  simp [RankOne.rankOneProjection, OrthogonalProjection.rankOne]

theorem quadraticValue_coe_eq_zero_of_subspace_measure_eq_zero
    (m : ProjectionMeasure ℂ H) (hK : m.μ (subspaceProjection K) = 0) (z : K) :
    m.quadraticValue (z : H) = 0 := by
  by_cases hz : z = 0
  · subst z
    simp
  let P : OrthogonalProjection ℂ K :=
    ⟨(RankOne.rankOneProjection (H := K) z hz).1,
      ⟨by
        simpa [IsIdempotentElem] using
          (RankOne.rankOneProjection (H := K) z hz).2.1,
        ClassicalGleason.isSelfAdjoint_of_projection (H := K)
          (RankOne.rankOneProjection (H := K) z hz)⟩⟩
  have hle := measure_extendProjection_le K m P
  have hP : extendProjection K P =
      OrthogonalProjection.rankOne (𝕜 := ℂ) (z : H) := by
    simpa [P, extendBundledProjection] using extendBundled_rankOne K z hz
  rw [hP, hK] at hle
  have hzero : m.μ (OrthogonalProjection.rankOne (𝕜 := ℂ) (z : H)) = 0 :=
    le_antisymm hle (m.nonneg _)
  simp [ProjectionMeasure.quadraticValue, hzero]

/-- Normalize the restriction of a nonzero measure to `K`. -/
def frameFunction (m : ProjectionMeasure ℂ H)
    (hK : 0 < m.μ (subspaceProjection K)) : FrameFunction K where
  μ P := m.μ (extendBundledProjection K P) / m.μ (subspaceProjection K)
  nonneg P := div_nonneg (m.nonneg _) hK.le
  additive P Q hPQ := by
    have h := m.additive (extendBundledProjection K P) (extendBundledProjection K Q)
      (extendBundledProjection_orthogonal K hPQ)
    rw [← extendBundledProjection_add K P Q hPQ] at h
    simpa [div_eq_mul_inv, add_mul] using congrArg (fun r => r / m.μ (subspaceProjection K)) h
  normalized := by
    rw [show extendBundledProjection K (Projection.one (H := K)) = subspaceProjection K from
      extendBundledProjection_one K]
    exact div_self hK.ne'

theorem frame_quadratic_eq_div (m : ProjectionMeasure ℂ H)
    (hK : 0 < m.μ (subspaceProjection K)) (z : K) :
    frame_quadratic (frameFunction K m hK) z =
      m.quadraticValue (z : H) / m.μ (subspaceProjection K) := by
  by_cases hz : z = 0
  · subst z
    simp [frame_quadratic, ProjectionMeasure.quadraticValue]
  rw [frame_quadratic]
  simp only [dif_neg hz]
  change
    (m.μ (extendBundledProjection K (RankOne.rankOneProjection (H := K) z hz)) /
        m.μ (subspaceProjection K)) * ‖z‖ ^ 2 =
      m.quadraticValue (z : H) / m.μ (subspaceProjection K)
  rw [show extendBundledProjection K (RankOne.rankOneProjection (H := K) z hz) =
      OrthogonalProjection.rankOne (𝕜 := ℂ) (z : H) from extendBundled_rankOne K z hz]
  simp [ProjectionMeasure.quadraticValue, div_mul_eq_mul_div]

end FiniteRestriction

end ClassicalGleason.Separable
