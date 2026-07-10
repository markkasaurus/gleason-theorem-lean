import Gleason.Harmonic.HighDegree.HighEvenUnionSquaredQuotientPolyApprox
import Mathlib.Order.Interval.Set.Infinite

noncomputable section

open Complex InnerProductSpace Polynomial

theorem sqquotient_factor_polynomial_unique_on_unitIcc
    {q q' : ℝ[X]}
    (h :
      ∀ u : Set.Icc (0 : ℝ) 1,
        u.1 * q.eval u.1 = u.1 * q'.eval u.1) :
    q = q' := by
  have hmul :
      X * q = X * q' := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.Icc (0 : ℝ) 1) ?_
      (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num))
    intro x hx
    let u : Set.Icc (0 : ℝ) 1 := ⟨x, hx⟩
    have hu := h u
    change (X * q).eval x = (X * q').eval x
    simpa [u, Polynomial.eval_mul, Polynomial.eval_X, mul_comm, mul_left_comm, mul_assoc] using hu
  ext n
  simpa [Polynomial.coeff_X_mul] using
    congrArg (fun r : ℝ[X] => r.coeff (n + 1)) hmul
