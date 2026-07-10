import Mathlib.Analysis.Complex.Trigonometric

noncomputable section

open Real Complex

def surfaceModeA (n : ℕ) (x y _z : ℝ) : ℝ :=
  (((x : ℂ) + Complex.I * y) ^ n).re

def surfaceModeB (n : ℕ) (x y z : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2 - 2 * (n - 1) * z ^ 2) * (((x : ℂ) + Complex.I * y) ^ (n - 2)).re

lemma surfaceModeA_equator (n : ℕ) (θ : ℝ) :
    surfaceModeA n (Real.cos θ) (Real.sin θ) 0 = Real.cos ((n : ℝ) * θ) := by
  unfold surfaceModeA
  have hpow :=
    Complex.cos_add_sin_mul_I_pow n (θ : ℂ)
  have hre := congrArg Complex.re hpow
  have hre' :
      (((Real.cos θ : ℂ) + Complex.I * Real.sin θ) ^ n).re =
        (Complex.cos ((n : ℂ) * (θ : ℂ))).re + -(Complex.sin ((n : ℂ) * (θ : ℂ))).im := by
    simpa [Complex.ofReal_cos, Complex.ofReal_sin, mul_comm, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im] using hre
  have harg : ((n : ℂ) * (θ : ℂ)) = ((((n : ℝ) * θ) : ℝ) : ℂ) := by
    simp [Complex.ofReal_mul]
  calc
    (((Real.cos θ : ℂ) + Complex.I * Real.sin θ) ^ n).re
        = (Complex.cos ((n : ℂ) * (θ : ℂ))).re + -(Complex.sin ((n : ℂ) * (θ : ℂ))).im := hre'
    _ = Real.cos ((n : ℝ) * θ) := by
          rw [harg, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
          ring

lemma surfaceModeB_equator {n : ℕ} (_hn : 2 ≤ n) (θ : ℝ) :
    surfaceModeB n (Real.cos θ) (Real.sin θ) 0 = Real.cos (((n - 2 : ℕ) : ℝ) * θ) := by
  unfold surfaceModeB
  have hpow :=
    Complex.cos_add_sin_mul_I_pow (n - 2) (θ : ℂ)
  have hre := congrArg Complex.re hpow
  have hcoeff : Real.cos θ ^ 2 + Real.sin θ ^ 2 - 2 * (n - 1) * (0 : ℝ) ^ 2 = 1 := by
    simp
  have hre' :
      ((((Real.cos θ : ℂ) + Complex.I * Real.sin θ) ^ (n - 2)).re) =
        Real.cos (((n - 2 : ℕ) : ℝ) * θ) := by
    have hre'' :
        (((Real.cos θ : ℂ) + Complex.I * Real.sin θ) ^ (n - 2)).re =
          (Complex.cos (((n - 2 : ℕ) : ℂ) * (θ : ℂ))).re +
            -(Complex.sin (((n - 2 : ℕ) : ℂ) * (θ : ℂ))).im := by
      simpa [Complex.ofReal_cos, Complex.ofReal_sin, mul_comm, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im] using hre
    have harg : (((n - 2 : ℕ) : ℂ) * (θ : ℂ)) =
        (((((n - 2 : ℕ) : ℝ) * θ) : ℝ) : ℂ) := by
      simp [Complex.ofReal_mul]
    calc
      (((Real.cos θ : ℂ) + Complex.I * Real.sin θ) ^ (n - 2)).re
          = (Complex.cos (((n - 2 : ℕ) : ℂ) * (θ : ℂ))).re +
              -(Complex.sin (((n - 2 : ℕ) : ℂ) * (θ : ℂ))).im := hre''
      _ = Real.cos (((n - 2 : ℕ) : ℝ) * θ) := by
            rw [harg, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
            ring
  rw [hcoeff, hre']
  ring
