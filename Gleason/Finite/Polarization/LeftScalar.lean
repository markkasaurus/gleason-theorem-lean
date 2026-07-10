import Mathlib
import Gleason.Finite.Polarization.BoundedQuadraticForm
import Gleason.Finite.Polarization.Definition
import Gleason.Finite.Polarization.Symmetry
import Gleason.Finite.Polarization.Additivity

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

open scoped Real
open Complex

/-- Polarization respects real scalar multiplication in the left argument. -/
lemma polarization_smul_left_real
    (q : H → ℝ) (hq : IsBoundedQuadraticForm q) (r : ℝ) (x y : H) :
    polarization q (r • x) y = r * polarization q x y := by
  classical

  -- Additive map f(t) = polarization q (t•x) y
  let f : ℝ →+ ℂ :=
    { toFun := fun t => polarization q (t • x) y
      map_zero' := by
        -- f 0 = polarization q 0 y
        simpa [zero_smul] using (polarization_zero_left q hq y)
      map_add' := by
        intro a b
        simpa [add_smul] using (polarization_add_left q hq (a • x) (b • x) y) }

  -- global quadratic bound
  rcases hq.bounded with ⟨C, hC⟩
  let C0 : ℝ := max C 0
  have hC0 : 0 ≤ C0 := le_max_right _ _
  have hCle : C ≤ C0 := le_max_left _ _

  let K : ℝ := ‖x‖ + ‖y‖
  have hK0 : 0 ≤ K := by nlinarith [norm_nonneg x, norm_nonneg y]
  let R : ℝ := C0 * K ^ 2

  -- If ‖z‖ ≤ K, then |q z| ≤ R
  have hq_bound : ∀ z : H, ‖z‖ ≤ K → |q z| ≤ R := by
    intro z hz
    have hz2 : ‖z‖ ^ 2 ≤ K ^ 2 := by
      have := mul_le_mul hz hz (norm_nonneg z) hK0
      simpa [pow_two] using this
    have hq1 : |q z| ≤ C * ‖z‖ ^ 2 := hC z
    have hq2 : C * ‖z‖ ^ 2 ≤ C0 * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hCle (pow_nonneg (norm_nonneg z) 2)
    have hq3 : |q z| ≤ C0 * ‖z‖ ^ 2 := le_trans hq1 hq2
    have hq4 : C0 * ‖z‖ ^ 2 ≤ C0 * K ^ 2 := mul_le_mul_of_nonneg_left hz2 hC0
    exact le_trans hq3 (by simpa [R] using hq4)

  -- Boundedness of f on ball(0,1)
  have hsubset : Set.image (fun t : ℝ => f t) (Metric.ball (0 : ℝ) 1) ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩

    have ht1 : ‖t‖ ≤ (1 : ℝ) := by
      have : dist t 0 < (1 : ℝ) := by simpa [Metric.mem_ball] using ht
      simpa [dist_eq_norm] using le_of_lt this

    have htx : ‖t • x‖ ≤ ‖x‖ := by
      calc
        ‖t • x‖ = ‖t‖ * ‖x‖ := by simpa using (norm_smul t x)
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ht1 (norm_nonneg x)
        _ = ‖x‖ := by simp

    have h1n : ‖t • x + y‖ ≤ K := by
      have hA : ‖t • x + y‖ ≤ ‖t • x‖ + ‖y‖ := norm_add_le _ _
      have hB : ‖t • x‖ + ‖y‖ ≤ K := by simpa [K] using add_le_add_right htx ‖y‖
      exact le_trans hA hB
    have h2n : ‖t • x - y‖ ≤ K := by
      have hA : ‖t • x - y‖ ≤ ‖t • x‖ + ‖y‖ := norm_sub_le _ _
      have hB : ‖t • x‖ + ‖y‖ ≤ K := by simpa [K] using add_le_add_right htx ‖y‖
      exact le_trans hA hB

    have hIy : ‖(Complex.I : ℂ) • y‖ = ‖y‖ := by
      calc
        ‖(Complex.I : ℂ) • y‖ = ‖(Complex.I : ℂ)‖ * ‖y‖ := by simpa using (norm_smul Complex.I y)
        _ = ‖y‖ := by simp

    have h3n : ‖t • x + Complex.I • y‖ ≤ K := by
      have hA : ‖t • x + Complex.I • y‖ ≤ ‖t • x‖ + ‖Complex.I • y‖ := norm_add_le _ _
      have hB : ‖t • x‖ + ‖Complex.I • y‖ ≤ K := by
        simpa [K, hIy] using add_le_add_right htx ‖y‖
      exact le_trans hA hB
    have h4n : ‖t • x - Complex.I • y‖ ≤ K := by
      have hA : ‖t • x - Complex.I • y‖ ≤ ‖t • x‖ + ‖Complex.I • y‖ := norm_sub_le _ _
      have hB : ‖t • x‖ + ‖Complex.I • y‖ ≤ K := by
        simpa [K, hIy] using add_le_add_right htx ‖y‖
      exact le_trans hA hB

    have hqa : |q (t • x + y)| ≤ R := hq_bound _ h1n
    have hqb : |q (t • x - y)| ≤ R := hq_bound _ h2n
    have hqc : |q (t • x + Complex.I • y)| ≤ R := hq_bound _ h3n
    have hqd : |q (t • x - Complex.I • y)| ≤ R := hq_bound _ h4n

    -- bounds on re part
    have hre : |(polarization q (t • x) y).re| ≤ R / 2 := by
      have hre_def : (polarization q (t • x) y).re = (q (t • x + y) - q (t • x - y)) / 4 := by
        simp [polarization]
      rw [hre_def]
      let diff : ℝ := q (t • x + y) - q (t • x - y)
      have habs : |diff| ≤ |q (t • x + y)| + |q (t • x - y)| := by
        -- |a-b| ≤ |a| + |b|
        have := abs_sub_le (q (t • x + y)) 0 (q (t • x - y))
        simpa [diff] using this
      have habsR : |diff| ≤ R + R := le_trans habs (by linarith [hqa, hqb])
      have h4pos : (0 : ℝ) < 4 := by norm_num
      have hdiv : |diff| / 4 ≤ (R + R) / 4 := by
        nlinarith [habsR]
      have hdiv' : |diff / 4| ≤ (R + R) / 4 := by
        have : |diff / 4| = |diff| / 4 := by simp [abs_div, abs_of_pos h4pos]
        simpa [this] using hdiv
      have hRR : (R + R) / 4 = R / 2 := by ring
      have : |diff / 4| ≤ R / 2 := by simpa [hRR] using hdiv'
      simpa [diff] using this

    -- bounds on im part
    have him : |(polarization q (t • x) y).im| ≤ R / 2 := by
      have him_def : (polarization q (t • x) y).im = (q (t • x + Complex.I • y) - q (t • x - Complex.I • y)) / 4 := by
        simp [polarization]
      rw [him_def]
      let diff : ℝ := q (t • x + Complex.I • y) - q (t • x - Complex.I • y)
      have habs : |diff| ≤ |q (t • x + Complex.I • y)| + |q (t • x - Complex.I • y)| := by
        have := abs_sub_le (q (t • x + Complex.I • y)) 0 (q (t • x - Complex.I • y))
        simpa [diff] using this
      have habsR : |diff| ≤ R + R := le_trans habs (by linarith [hqc, hqd])
      have h4pos : (0 : ℝ) < 4 := by norm_num
      have hdiv : |diff| / 4 ≤ (R + R) / 4 := by
        nlinarith [habsR]
      have hdiv' : |diff / 4| ≤ (R + R) / 4 := by
        have : |diff / 4| = |diff| / 4 := by simp [abs_div, abs_of_pos h4pos]
        simpa [this] using hdiv
      have hRR : (R + R) / 4 = R / 2 := by ring
      have : |diff / 4| ≤ R / 2 := by simpa [hRR] using hdiv'
      simpa [diff] using this

    -- bound complex norm by triangle inequality on re/im decomposition
    have hz_norm : ‖polarization q (t • x) y‖ ≤ R := by
      set zc : ℂ := polarization q (t • x) y
      have zrep : zc = (zc.re : ℂ) + (zc.im : ℂ) * Complex.I := by
        simpa using (Complex.re_add_im zc).symm
      have hzrepr : ‖zc‖ = ‖(zc.re : ℂ) + (zc.im : ℂ) * Complex.I‖ := by
        simpa using congrArg (fun z : ℂ => ‖z‖) zrep
      have hz0 : ‖zc‖ ≤ |zc.re| + |zc.im| := by
        have hnr : ‖(zc.re : ℂ)‖ = |zc.re| := by simpa [Complex.norm_real]
        have hni : ‖(zc.im : ℂ) * Complex.I‖ = |zc.im| := by
          calc
            ‖(zc.im : ℂ) * Complex.I‖ = ‖(zc.im : ℂ)‖ * ‖(Complex.I : ℂ)‖ := by
              simpa using norm_mul (zc.im : ℂ) (Complex.I : ℂ)
            _ = |zc.im| := by simp [Complex.norm_real]
        calc
          ‖zc‖ = ‖(zc.re : ℂ) + (zc.im : ℂ) * Complex.I‖ := hzrepr
          _ ≤ ‖(zc.re : ℂ)‖ + ‖(zc.im : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = |zc.re| + |zc.im| := by simpa [hnr, hni]
      have hz1 : |zc.re| + |zc.im| ≤ R := by
        have hzre : |zc.re| ≤ R / 2 := by simpa [zc] using hre
        have hzim : |zc.im| ≤ R / 2 := by simpa [zc] using him
        linarith
      exact le_trans hz0 hz1

    simpa [Metric.mem_closedBall, dist_eq_norm] using hz_norm

  have hf_bounded : Bornology.IsBounded (Set.image (fun t : ℝ => f t) (Metric.ball (0 : ℝ) 1)) := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).2 ?_
    exact ⟨R, hsubset⟩

  have hf_cont : Continuous fun t : ℝ => f t := by
    refine AddMonoidHom.continuous_of_isBounded_nhds_zero f
      (Metric.ball_mem_nhds (0 : ℝ) (ε := (1 : ℝ)) (by norm_num)) ?_
    simpa using hf_bounded

  have hlin : f r = (r : ℝ) • f 1 := by
    have := map_real_smul f hf_cont r (1 : ℝ)
    simpa using this

  -- unfold f, and rewrite r • z as r * z in ℂ
  simpa [f, Algebra.smul_def] using hlin


/-- Polarization respects multiplication by `I` in the left argument. -/
lemma polarization_smul_left_I
    (q : H → ℝ) (hq : IsBoundedQuadraticForm q) (x y : H) :
    polarization q (Complex.I • x) y = Complex.I * polarization q x y := by
  classical
  -- q(I•u) = q(u)
  have hI : ∀ u : H, q (Complex.I • u) = q u := by
    intro u
    have h := hq.sq_hom Complex.I u
    simpa [Complex.norm_I] using h

  -- rewrite q-terms appearing in polarization(I•x, y)
  have q1 : q (Complex.I • x + y) = q (x - Complex.I • y) := by
    have hx' : Complex.I • (x - Complex.I • y) = Complex.I • x + y := by
      calc
        Complex.I • (x - Complex.I • y)
            = Complex.I • x - Complex.I • (Complex.I • y) := by
                simpa using (smul_sub Complex.I x (Complex.I • y))
        _ = Complex.I • x - (Complex.I * Complex.I) • y := by
                simp [smul_smul]
        _ = Complex.I • x - (-1 : ℂ) • y := by
                simp [Complex.I_mul_I]
        _ = Complex.I • x + y := by
                simp [sub_eq_add_neg]
    have hx : Complex.I • x + y = Complex.I • (x - Complex.I • y) := by
      simpa using hx'.symm
    calc
      q (Complex.I • x + y) = q (Complex.I • (x - Complex.I • y)) := by simpa [hx]
      _ = q (x - Complex.I • y) := hI _

  have q2 : q (Complex.I • x - y) = q (x + Complex.I • y) := by
    have hx' : Complex.I • (x + Complex.I • y) = Complex.I • x - y := by
      calc
        Complex.I • (x + Complex.I • y)
            = Complex.I • x + Complex.I • (Complex.I • y) := by
                simpa using (smul_add Complex.I x (Complex.I • y))
        _ = Complex.I • x + (Complex.I * Complex.I) • y := by
                simp [smul_smul]
        _ = Complex.I • x + (-1 : ℂ) • y := by
                simp [Complex.I_mul_I]
        _ = Complex.I • x - y := by
                simp [sub_eq_add_neg]
    have hx : Complex.I • x - y = Complex.I • (x + Complex.I • y) := by
      simpa using hx'.symm
    calc
      q (Complex.I • x - y) = q (Complex.I • (x + Complex.I • y)) := by simpa [hx]
      _ = q (x + Complex.I • y) := hI _

  have q3 : q (Complex.I • x + Complex.I • y) = q (x + y) := by
    have hx : Complex.I • x + Complex.I • y = Complex.I • (x + y) := by
      simpa using (smul_add Complex.I x y).symm
    calc
      q (Complex.I • x + Complex.I • y) = q (Complex.I • (x + y)) := by
        -- avoid simp recursion in `simpa [hx]`
        rw [hx]
      
      _ = q (x + y) := hI _

  have q4 : q (Complex.I • x - Complex.I • y) = q (x - y) := by
    have hx : Complex.I • x - Complex.I • y = Complex.I • (x - y) := by
      -- I•(x - y) = I•x - I•y
      simpa [sub_eq_add_neg, smul_add, smul_neg] using (smul_sub Complex.I x y)
    calc
      q (Complex.I • x - Complex.I • y) = q (Complex.I • (x - y)) := by simpa [hx]
      _ = q (x - y) := hI _

  apply Complex.ext
  · -- re: becomes - (polarization q x y).im
    have hreR : (Complex.I * polarization q x y).re = - (polarization q x y).im := by
      simp
    -- compute re of LHS using q1,q2, compute im of polarization q x y by definition
    -- and finish by ring
    first
      | (simp [hreR, polarization, q1, q2]; ring_nf)
      | simp [hreR, polarization, q1, q2]
  · -- im: becomes (polarization q x y).re
    have himR : (Complex.I * polarization q x y).im = (polarization q x y).re := by
      simp
    first
      | (simp [himR, polarization, q3, q4]; ring_nf)
      | simp [himR, polarization, q3, q4]


/-- Full complex scalar rule in the left argument. -/
lemma polarization_smul_left
    (q : H → ℝ) (hq : IsBoundedQuadraticForm q) (c : ℂ) (x y : H) :
    polarization q (c • x) y = c * polarization q x y := by
  classical
  have hc : c = (c.re : ℂ) + (c.im : ℂ) * Complex.I := by
    simpa using Complex.re_add_im c

  have hcx : c • x = (c.re : ℂ) • x + ((c.im : ℂ) * Complex.I) • x := by
    calc
      c • x = (((c.re : ℂ) + (c.im : ℂ) * Complex.I) : ℂ) • x := by
        -- avoid simp loops; use congrArg
        simpa using congrArg (fun z : ℂ => z • x) hc
      _ = (c.re : ℂ) • x + ((c.im : ℂ) * Complex.I) • x := by
        simpa using (add_smul (c.re : ℂ) ((c.im : ℂ) * Complex.I) x)

  have hreal : polarization q ((c.re : ℂ) • x) y = (c.re : ℝ) * polarization q x y := by
    have hx : ((c.re : ℂ) • x) = (c.re : ℝ) • x := by
      simp [Algebra.smul_def]
    simpa [hx] using (polarization_smul_left_real q hq (c.re : ℝ) x y)

  have himx : (((c.im : ℂ) * Complex.I) • x) = (c.im : ℝ) • (Complex.I • x) := by
    calc
      (((c.im : ℂ) * Complex.I) • x) = (c.im : ℂ) • (Complex.I • x) := by
        simpa [mul_smul]
      _ = (c.im : ℝ) • (Complex.I • x) := by
        simp [Algebra.smul_def]

  have him :
      polarization q (((c.im : ℂ) * Complex.I) • x) y =
        (c.im : ℝ) * (Complex.I * polarization q x y) := by
    calc
      polarization q (((c.im : ℂ) * Complex.I) • x) y
          = polarization q ((c.im : ℝ) • (Complex.I • x)) y := by
              simpa [himx]
      _ = (c.im : ℝ) * polarization q (Complex.I • x) y := by
              simpa using (polarization_smul_left_real q hq (c.im : ℝ) (Complex.I • x) y)
      _ = (c.im : ℝ) * (Complex.I * polarization q x y) := by
              simp [polarization_smul_left_I q hq]

  calc
    polarization q (c • x) y
        = polarization q ((c.re : ℂ) • x + ((c.im : ℂ) * Complex.I) • x) y := by
            simpa [hcx]
    _ = polarization q ((c.re : ℂ) • x) y + polarization q (((c.im : ℂ) * Complex.I) • x) y := by
            simpa using polarization_add_left q hq ((c.re : ℂ) • x) (((c.im : ℂ) * Complex.I) • x) y
    _ = (c.re : ℝ) * polarization q x y + (c.im : ℝ) * (Complex.I * polarization q x y) := by
            simpa [hreal, him]
    _ = ((c.re : ℂ) + (c.im : ℂ) * Complex.I) * polarization q x y := by
            -- convert the `ℝ` scalars to `ℂ` and factor
            ring
    _ = c * polarization q x y := by
            simpa [hc.symm]
