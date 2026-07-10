import Mathlib

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Polarization of a real-valued quadratic form on a complex vector space. -/
def polarization (q : H → ℝ) (x y : H) : ℂ :=
  let RePart : ℝ := (q (x + y) - q (x - y)) / 4
  let ImPart : ℝ := (q (x + Complex.I • y) - q (x - Complex.I • y)) / 4
  Complex.mk RePart ImPart
