import Mathlib

noncomputable section

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A real-valued quadratic form on a complex inner product space that is
homogeneous of degree 2, satisfies the parallelogram law, and is bounded by `C * ‖x‖^2`. -/
structure IsBoundedQuadraticForm (q : H → ℝ) : Prop where
  sq_hom : ∀ (c : ℂ) (x : H), q (c • x) = ‖c‖ ^ 2 * q x
  parallelogram : ∀ x y : H, q (x + y) + q (x - y) = 2 * q x + 2 * q y
  bounded : ∃ C : ℝ, ∀ x : H, |q x| ≤ C * ‖x‖ ^ 2
