import Mathlib
import Gleason.Finite.Polarization.BoundedQuadraticForm
import Gleason.Finite.Polarization.Definition

noncomputable section
set_option maxRecDepth 4096

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Evenness from square-homogeneity: `q (-x) = q x`. -/
private lemma q_neg (q : H → ℝ) (hq : IsBoundedQuadraticForm (H := H) q) (x : H) :
    q (-x) = q x := by
  have h : q ((-1 : ℂ) • x) = ‖(-1 : ℂ)‖ ^ 2 * q x := hq.sq_hom (-1 : ℂ) x
  have h' : q (-x) = ‖(-1 : ℂ)‖ ^ 2 * q x := by
    -- avoid big simp: just rewrite (-1)•x
    simpa [neg_one_smul] using h
  have hn : ‖(-1 : ℂ)‖ ^ 2 = (1 : ℝ) := by norm_num
  calc
    q (-x) = ‖(-1 : ℂ)‖ ^ 2 * q x := h'
    _ = q x := by simp [hn]

/-- Swap subtraction using evenness: `q (a - b) = q (b - a)`. -/
private lemma q_sub_comm (q : H → ℝ) (hq : IsBoundedQuadraticForm (H := H) q) (a b : H) :
    q (a - b) = q (b - a) := by
  have h : a - b = -(b - a) := by abel
  -- rewrite and use evenness
  rw [h]
  exact q_neg (H := H) q hq (b - a)

/--
Key difference identity from parallelogram:
`q(x+(y+z)) - q(x-(y+z)) = (q(x+y)-q(x-y)) + (q(x+z)-q(x-z))`.
-/
private lemma q_diff_add (q : H → ℝ) (hq : IsBoundedQuadraticForm (H := H) q)
    (x y z : H) :
    q (x + (y + z)) - q (x - (y + z)) =
      (q (x + y) - q (x - y)) + (q (x + z) - q (x - z)) := by
  -- shorthand scalars
  let A : ℝ := q (x + (y + z))
  let E : ℝ := q (x - (y + z))
  let B : ℝ := q (x + y - z)
  let C : ℝ := q (x - y + z)
  let D : ℝ := q (x - y - z)

  have hDE : D = E := by
    have : x - y - z = x - (y + z) := by abel
    simpa [D, E, this]

  have p1 : q (x + (y + z)) + q (x + y - z) = 2 * q (x + y) + 2 * q z := by
    simpa [add_assoc, sub_eq_add_neg, add_comm, add_left_comm] using hq.parallelogram (x + y) z
  have p2 : q (x - y + z) + q (x - y - z) = 2 * q (x - y) + 2 * q z := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hq.parallelogram (x - y) z
  have p3 : q (x + (y + z)) + q (x - y + z) = 2 * q (x + z) + 2 * q y := by
    simpa [add_assoc, sub_eq_add_neg, add_comm, add_left_comm] using hq.parallelogram (x + z) y
  have p4 : q (x + y - z) + q (x - (y + z)) = 2 * q (x - z) + 2 * q y := by
    simpa [add_assoc, sub_eq_add_neg, add_comm, add_left_comm] using hq.parallelogram (x - z) y

  have EqA : A + B - C - E = 2 * (q (x + y) - q (x - y)) := by
    have p2' : C + E = 2 * q (x - y) + 2 * q z := by
      simpa [C, D, E, hDE] using p2
    have p1' : A + B = 2 * q (x + y) + 2 * q z := by
      simpa [A, B] using p1
    linarith [p1', p2']
  have EqB : A + C - B - E = 2 * (q (x + z) - q (x - z)) := by
    have p3' : A + C = 2 * q (x + z) + 2 * q y := by
      simpa [A, C] using p3
    have p4' : B + E = 2 * q (x - z) + 2 * q y := by
      simpa [B, E] using p4
    linarith [p3', p4']

  have Two :
      2 * (A - E) =
        2 * ((q (x + y) - q (x - y)) + (q (x + z) - q (x - z))) := by
    linarith [EqA, EqB]

  have : A - E = (q (x + y) - q (x - y)) + (q (x + z) - q (x - z)) := by
    linarith [Two]
  simpa [A, E] using this

/-- Additivity of the "difference term" in the left slot. -/
private lemma q_diff_add_left (q : H → ℝ) (hq : IsBoundedQuadraticForm (H := H) q)
    (x y b : H) :
    q ((x + y) + b) - q ((x + y) - b) =
      (q (x + b) - q (x - b)) + (q (y + b) - q (y - b)) := by
  have h := q_diff_add (H := H) q hq b x y
  have hbxy : q (b + (x + y)) = q ((x + y) + b) := by
    simpa [add_assoc, add_comm, add_left_comm]
  have hbxy' : q (b - (x + y)) = q ((x + y) - b) := by
    simpa using (q_sub_comm (H := H) q hq b (x + y))
  have hbx : q (b + x) = q (x + b) := by simpa [add_comm]
  have hby : q (b + y) = q (y + b) := by simpa [add_comm]
  have hbsx : q (b - x) = q (x - b) := by simpa using (q_sub_comm (H := H) q hq b x)
  have hbsy : q (b - y) = q (y - b) := by simpa using (q_sub_comm (H := H) q hq b y)
  simpa [hbxy, hbxy', hbx, hby, hbsx, hbsy] using h

theorem polarization_add_right (q : H → ℝ) (hq : IsBoundedQuadraticForm (H := H) q)
    (x y z : H) :
    polarization q x (y + z) = polarization q x y + polarization q x z := by
  classical
  apply Complex.ext
  · -- re part
    simp [polarization]
    have hre := q_diff_add (H := H) q hq x y z
    have hdiv := congrArg (fun t : ℝ => t / 4) hre
    simpa [add_div] using hdiv
  · -- im part
    simp [polarization]
    have him0 := q_diff_add (H := H) q hq x (Complex.I • y) (Complex.I • z)
    have him :
        q (x + (Complex.I • (y + z))) - q (x - (Complex.I • (y + z))) =
          (q (x + Complex.I • y) - q (x - Complex.I • y)) +
            (q (x + Complex.I • z) - q (x - Complex.I • z)) := by
      simpa [smul_add, add_assoc] using him0
    have hdiv := congrArg (fun t : ℝ => t / 4) him
    simpa [add_div] using hdiv

theorem polarization_add_left (q : H → ℝ) (hq : IsBoundedQuadraticForm (H := H) q)
    (x y z : H) :
    polarization q (x + y) z = polarization q x z + polarization q y z := by
  classical
  apply Complex.ext
  · -- re part
    simp [polarization]
    have hre := q_diff_add_left (H := H) q hq x y z
    have hdiv := congrArg (fun t : ℝ => t / 4) hre
    simpa [add_div] using hdiv
  · -- im part
    simp [polarization]
    have him := q_diff_add_left (H := H) q hq x y (Complex.I • z)
    have hdiv := congrArg (fun t : ℝ => t / 4) him
    simpa [add_div] using hdiv
