import Gleason.Separable.LocalQuadratic

/-!
# The Representing Operator over the Complex Field

Polarization and the Riesz representation theorem turn the global bounded
quadratic form into a unique bounded positive operator.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ProjectionMeasure

/-- The operator obtained from the polarized rank-one quadratic function. -/
def representingOperator (m : ProjectionMeasure ℂ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℂ H) : H →L[ℂ] H :=
  (polarization_eq_inner_product m.quadraticValue
    (m.quadraticValue_isBoundedQuadraticForm hdim)).choose

theorem polarization_eq_inner_representingOperator
    (m : ProjectionMeasure ℂ H) (hdim : (3 : Cardinal) ≤ Module.rank ℂ H)
    (x y : H) :
    polarization m.quadraticValue x y = inner ℂ y (m.representingOperator hdim x) :=
  (polarization_eq_inner_product m.quadraticValue
    (m.quadraticValue_isBoundedQuadraticForm hdim)).choose_spec.1 x y

theorem quadraticValue_eq_inner_representingOperator
    (m : ProjectionMeasure ℂ H) (hdim : (3 : Cardinal) ≤ Module.rank ℂ H)
    (x : H) :
    m.quadraticValue x = (inner ℂ x (m.representingOperator hdim x)).re :=
  (polarization_eq_inner_product m.quadraticValue
    (m.quadraticValue_isBoundedQuadraticForm hdim)).choose_spec.2 x

theorem representingOperator_isSelfAdjoint
    (m : ProjectionMeasure ℂ H) (hdim : (3 : Cardinal) ≤ Module.rank ℂ H) :
    IsSelfAdjoint (m.representingOperator hdim) := by
  let q := m.quadraticValue
  let hq := m.quadraticValue_isBoundedQuadraticForm hdim
  let T := m.representingOperator hdim
  have hrepr : ∀ x y : H, polarization q x y = inner ℂ y (T x) := by
    intro x y
    exact m.polarization_eq_inner_representingOperator hdim x y
  have hadj : ContinuousLinearMap.adjoint T = T := by
    ext x
    apply ext_inner_left ℂ
    intro y
    have hconj := polarization_conj_symm (H := H) (q := q) hq x y
    calc
      inner ℂ y ((ContinuousLinearMap.adjoint T) x) = inner ℂ (T y) x :=
        ContinuousLinearMap.adjoint_inner_right (𝕜 := ℂ) T y x
      _ = star (inner ℂ x (T y)) := by simp
      _ = star (polarization q y x) := by rw [hrepr y x]
      _ = polarization q x y := by rw [hconj]; simp
      _ = inner ℂ y (T x) := hrepr x y
  simpa [T] using hadj

theorem representingOperator_isPositive
    (m : ProjectionMeasure ℂ H) (hdim : (3 : Cardinal) ≤ Module.rank ℂ H) :
    (m.representingOperator hdim).IsPositive := by
  refine (ContinuousLinearMap.isPositive_def'
    (T := m.representingOperator hdim)).2 ⟨m.representingOperator_isSelfAdjoint hdim, ?_⟩
  intro x
  change 0 ≤ (inner ℂ (m.representingOperator hdim x) x).re
  have hdiag :
      (inner ℂ (m.representingOperator hdim x) x).re = m.quadraticValue x := by
    calc
      (inner ℂ (m.representingOperator hdim x) x).re =
          (inner ℂ x (m.representingOperator hdim x)).re := by
            exact congrArg Complex.re
              (ClassicalGleason.inner_left_eq_inner_right_of_isSelfAdjoint
                (H := H) (m.representingOperator_isSelfAdjoint hdim) x x)
      _ = m.quadraticValue x :=
        (m.quadraticValue_eq_inner_representingOperator hdim x).symm
  rw [hdiag]
  exact m.quadraticValue_nonneg x

end ProjectionMeasure

end ClassicalGleason.Separable
