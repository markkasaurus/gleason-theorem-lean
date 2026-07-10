import Mathlib
import Gleason.Finite.Polarization.BoundedQuadraticForm
import Gleason.Finite.Polarization.Definition

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- From square-homogeneity, `q` is even: `q (-x) = q x`. -/
private lemma q_neg (q : H → ℝ) (hq : IsBoundedQuadraticForm (H := H) q) (x : H) :
    q (-x) = q x := by
  simpa [neg_one_smul] using (hq.sq_hom (-1 : ℂ) x)

theorem polarization_zero_left (q : H → ℝ) (hq : IsBoundedQuadraticForm (H := H) q) (y : H) :
    polarization q 0 y = 0 := by
  classical
  apply Complex.ext
  · -- real part
    simp [polarization, q_neg (H := H) q hq, sub_eq_add_neg] <;> ring_nf
  · -- imag part
    simp [polarization, q_neg (H := H) q hq, sub_eq_add_neg] <;> ring_nf

theorem polarization_zero_right (q : H → ℝ) (hq : IsBoundedQuadraticForm (H := H) q) (x : H) :
    polarization q x 0 = 0 := by
  classical
  apply Complex.ext <;> simp [polarization, sub_eq_add_neg] <;> ring_nf

theorem polarization_neg_left (q : H → ℝ) (hq : IsBoundedQuadraticForm (H := H) q) (x y : H) :
    polarization q (-x) y = -polarization q x y := by
  classical
  apply Complex.ext
  · -- real part
    have hx1' : (-x) + y = -(x - y) := by abel
    have hx2' : (-x) - y = -(x + y) := by abel
    have hx3' : (-x) + (-y) = -(x + y) := by abel
    have hx1 : q ((-x) + y) = q (x - y) := by
      simpa [hx1'] using (q_neg (H := H) q hq (x - y))
    have hx2 : q ((-x) - y) = q (x + y) := by
      simpa [hx2'] using (q_neg (H := H) q hq (x + y))
    have hx3 : q ((-x) + (-y)) = q (x + y) := by
      simpa [hx3'] using (q_neg (H := H) q hq (x + y))
    simp [polarization, hx1, hx2, hx3, sub_eq_add_neg] <;> ring_nf
  · -- imag part
    have hI1' : (-x) + Complex.I • y = -(x - Complex.I • y) := by abel
    have hI2' : (-x) - Complex.I • y = -(x + Complex.I • y) := by abel
    have hI3' : (-x) + (-(Complex.I • y)) = -(x + Complex.I • y) := by abel
    have hI1 : q ((-x) + Complex.I • y) = q (x - Complex.I • y) := by
      simpa [hI1'] using (q_neg (H := H) q hq (x - Complex.I • y))
    have hI2 : q ((-x) - Complex.I • y) = q (x + Complex.I • y) := by
      simpa [hI2'] using (q_neg (H := H) q hq (x + Complex.I • y))
    have hI3 : q ((-x) + (-(Complex.I • y))) = q (x + Complex.I • y) := by
      simpa [hI3'] using (q_neg (H := H) q hq (x + Complex.I • y))
    simp [polarization, hI1, hI2, hI3, sub_eq_add_neg] <;> ring_nf
