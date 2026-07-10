import Mathlib
import Gleason.Finite.Polarization.BoundedQuadraticForm
import Gleason.Finite.Polarization.Definition
import Gleason.Finite.Polarization.LeftScalar

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

open scoped ComplexConjugate

private lemma q_neg (q : H → ℝ) (hq : IsBoundedQuadraticForm q) (u : H) :
    q (-u) = q u := by
  have h := hq.sq_hom (-1 : ℂ) u
  simpa [neg_one_smul] using h

private lemma q_smul_I (q : H → ℝ) (hq : IsBoundedQuadraticForm q) (u : H) :
    q (Complex.I • u) = q u := by
  have h := hq.sq_hom Complex.I u
  simpa [Complex.norm_I] using h

private lemma q_smul_negI (q : H → ℝ) (hq : IsBoundedQuadraticForm q) (u : H) :
    q ((-Complex.I) • u) = q u := by
  have h := hq.sq_hom (-Complex.I) u
  simpa [Complex.norm_I] using h

theorem polarization_conj_symm (q : H → ℝ) (hq : IsBoundedQuadraticForm q) (x y : H) :
    polarization q y x = conj (polarization q x y) := by
  classical
  apply Complex.ext
  · -- real part
    -- reduce to re equality; conj fixes re
    -- avoid simp loops; only rewrite re of conj
    change (polarization q y x).re = (polarization q x y).re
    -- unfold the `re` parts directly
    have hyx : q (y - x) = q (x - y) := by
      have h : y - x = -(x - y) := by abel
      have hq1 : q (y - x) = q (-(x - y)) := congrArg q h
      calc
        q (y - x) = q (-(x - y)) := hq1
        _ = q (x - y) := q_neg (q := q) hq (x - y)
    have hsum : y + x = x + y := by ac_rfl
    -- unfold re(polarization) on both sides and rewrite
    dsimp [polarization]
    -- now a pure real equality
    simp [hsum, hyx]
  · -- imaginary part
    -- conj negates im
    simp
    -- goal: (polarization q y x).im = -(polarization q x y).im
    have hx1 : y + Complex.I • x = Complex.I • (x - Complex.I • y) := by
      -- prove RHS = LHS, then symm
      have : Complex.I • (x - Complex.I • y) = y + Complex.I • x := by
        calc
          Complex.I • (x - Complex.I • y)
              = Complex.I • x - Complex.I • (Complex.I • y) := by simp [smul_sub]
          _ = Complex.I • x - (Complex.I * Complex.I) • y := by simp [smul_smul]
          _ = Complex.I • x - (-1 : ℂ) • y := by simp
          _ = Complex.I • x + y := by simp [sub_eq_add_neg]
          _ = y + Complex.I • x := by ac_rfl
      exact this.symm
    have hx2 : y - Complex.I • x = (-Complex.I) • (x + Complex.I • y) := by
      have : (-Complex.I) • (x + Complex.I • y) = y - Complex.I • x := by
        calc
          (-Complex.I) • (x + Complex.I • y)
              = (-Complex.I) • x + (-Complex.I) • (Complex.I • y) := by simp [smul_add]
          _ = (-(Complex.I • x)) + ((-Complex.I) * Complex.I) • y := by
                simp [neg_smul, smul_smul]
          _ = (-(Complex.I • x)) + (1 : ℂ) • y := by simp
          _ = y - Complex.I • x := by simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      exact this.symm
    have h1 : q (y + Complex.I • x) = q (x - Complex.I • y) := by
      calc
        q (y + Complex.I • x) = q (Complex.I • (x - Complex.I • y)) := by simpa [hx1]
        _ = q (x - Complex.I • y) := q_smul_I (q := q) hq (x - Complex.I • y)
    have h2 : q (y - Complex.I • x) = q (x + Complex.I • y) := by
      calc
        q (y - Complex.I • x) = q ((-Complex.I) • (x + Complex.I • y)) := by simpa [hx2]
        _ = q (x + Complex.I • y) := q_smul_negI (q := q) hq (x + Complex.I • y)
    -- unfold imag parts, rewrite q-terms, then ring
    have hyIx : y + -(Complex.I • x) = y - Complex.I • x := by simp [sub_eq_add_neg]
    have hxIy : x + -(Complex.I • y) = x - Complex.I • y := by simp [sub_eq_add_neg]
    -- after dsimp, the numerator is q(y+I•x) - q(y-I•x)
    dsimp [polarization]
    -- rewrite the numerator using h1/h2 in a controlled way
    have hnumer :
        q (y + Complex.I • x) - q (y - Complex.I • x) =
          q (x - Complex.I • y) - q (x + Complex.I • y) := by
      simpa [h1, h2]
    -- avoid simp loops: rewrite y - I•x and x - I•y explicitly then finish by ring_nf
    -- expand the let-bound ImPart and use hnumer
    -- after dsimp [polarization], the goal is a ring identity in ℝ
    -- we rewrite with hnumer and normalize
    -- (no simp with sub_eq_add_neg)
    have : (q (y + Complex.I • x) - q (y - Complex.I • x)) / 4 = -( (q (x + Complex.I • y) - q (x - Complex.I • y)) / 4 ) := by
      -- use hnumer and ring
      -- rewrite hnumer into /4 form
      nlinarith [hnumer]
    -- discharge the goal
    simpa [hyIx, hxIy] using this

theorem polarization_smul_right (q : H → ℝ) (hq : IsBoundedQuadraticForm q) (c : ℂ) (x y : H) :
    polarization q x (c • y) = conj c * polarization q x y := by
  classical
  have hs : polarization q (c • y) x = c * polarization q y x :=
    polarization_smul_left q hq c y x
  have hswap : polarization q x (c • y) = conj (polarization q (c • y) x) := by
    simpa using (polarization_conj_symm (q := q) hq (c • y) x)
  have hconj_yx : conj (polarization q y x) = polarization q x y := by
    have h := polarization_conj_symm (q := q) hq x y
    simpa using congrArg conj h
  calc
    polarization q x (c • y)
        = conj (polarization q (c • y) x) := hswap
    _   = conj (c * polarization q y x) := by simpa [hs]
    _   = conj c * conj (polarization q y x) := by simp
    _   = conj c * polarization q x y := by simpa [hconj_yx]
