import Gleason.Continuity.CircleFrame
import Gleason.Harmonic.Sectors.HarmonicB
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section

open Real Complex InnerProductSpace

def rotatedSurfaceModeAEquator (n : ℕ) (c : ℝ) (θ : ℝ) : ℝ :=
  ((((c : ℂ) * Complex.cos θ) + Complex.I * Complex.sin θ) ^ n).re

def rotatedSurfaceModeAQuarterSum (n : ℕ) (c : ℝ) (θ : ℝ) : ℝ :=
  rotatedSurfaceModeAEquator n c θ + rotatedSurfaceModeAEquator n c (θ + π / 2)

def rotatedSurfaceModeAPath (c : ℝ) (θ : ℝ) : ℂ :=
  (c : ℂ) * Complex.cos θ + Complex.I * Complex.sin θ

def rotatedSurfaceModeAQuarterPath (c : ℝ) (θ : ℝ) : ℂ :=
  -((c : ℂ) * Complex.sin θ) + Complex.I * Complex.cos θ

lemma rotatedSurfaceModeAPath_zero (c : ℝ) :
    rotatedSurfaceModeAPath c 0 = c := by
  simp [rotatedSurfaceModeAPath]

lemma rotatedSurfaceModeAQuarterPath_zero (c : ℝ) :
    rotatedSurfaceModeAQuarterPath c 0 = Complex.I := by
  simp [rotatedSurfaceModeAQuarterPath]

lemma rotatedSurfaceModeAPath_eq_add_shift (c : ℝ) (θ : ℝ) :
    rotatedSurfaceModeAPath c θ =
      (c : ℂ) + (((c : ℂ) * Complex.cos θ - c) + Complex.I * Complex.sin θ) := by
  simp [rotatedSurfaceModeAPath]
  ring

lemma rotatedSurfaceModeAQuarterPath_eq_shift (c : ℝ) (θ : ℝ) :
    rotatedSurfaceModeAPath c (θ + π / 2) = rotatedSurfaceModeAQuarterPath c θ := by
  simp [rotatedSurfaceModeAPath, rotatedSurfaceModeAQuarterPath, Complex.cos_add, Complex.sin_add]

lemma hasDerivAt_ofReal_cos (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.cos t) (-Complex.sin x) x := by
  simpa using (Complex.hasDerivAt_cos (x : ℂ)).comp_ofReal

lemma hasDerivAt_ofReal_sin (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.sin t) (Complex.cos x) x := by
  simpa using (Complex.hasDerivAt_sin (x : ℂ)).comp_ofReal

lemma deriv_rotatedSurfaceModeAPath (c : ℝ) :
    deriv (rotatedSurfaceModeAPath c) =
      fun θ => (-(c * Real.sin θ) : ℂ) + Complex.I * Real.cos θ := by
  funext θ
  have h1 : HasDerivAt (fun t : ℝ => (c : ℂ) * Complex.cos t) ((c : ℂ) * (-Complex.sin θ)) θ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_ofReal_cos θ).const_mul (c : ℂ)
  have h2 : HasDerivAt (fun t : ℝ => Complex.I * Complex.sin t) (Complex.I * Complex.cos θ) θ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_ofReal_sin θ).const_mul Complex.I
  simpa [rotatedSurfaceModeAPath] using (h1.add h2).deriv

lemma deriv_rotatedSurfaceModeAQuarterPath (c : ℝ) :
    deriv (rotatedSurfaceModeAQuarterPath c) =
      fun θ => (-(c * Real.cos θ) : ℂ) + Complex.I * (-(Real.sin θ)) := by
  funext θ
  have h1 : HasDerivAt (fun t : ℝ => (-(c : ℂ)) * Complex.sin t) ((-(c : ℂ)) * Complex.cos θ) θ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_ofReal_sin θ).const_mul (-(c : ℂ))
  have h2 : HasDerivAt (fun t : ℝ => Complex.I * Complex.cos t) (Complex.I * (-Complex.sin θ)) θ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_ofReal_cos θ).const_mul Complex.I
  have hsum :
      deriv (fun t : ℝ => (-(c : ℂ)) * Complex.sin t + Complex.I * Complex.cos t) θ =
        (-(c * Real.cos θ) : ℂ) + Complex.I * (-(Real.sin θ)) := by
    simpa using (h1.add h2).deriv
  simpa [rotatedSurfaceModeAQuarterPath] using hsum

lemma iteratedDeriv_two_rotatedSurfaceModeAPath (c : ℝ) :
    iteratedDeriv 2 (rotatedSurfaceModeAPath c) 0 = -(c : ℂ) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_rotatedSurfaceModeAPath]
  have h1 : HasDerivAt (fun θ : ℝ => (c : ℂ) * (-Complex.sin θ)) (-(c : ℂ)) 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_ofReal_sin 0).const_mul (-(c : ℂ)))
  have h2 : HasDerivAt (fun θ : ℝ => Complex.I * Complex.cos θ) 0 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_ofReal_cos 0).const_mul Complex.I
  simpa using (h1.add h2).deriv

lemma iteratedDeriv_two_rotatedSurfaceModeAQuarterPath (c : ℝ) :
    iteratedDeriv 2 (rotatedSurfaceModeAQuarterPath c) 0 = -Complex.I := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_rotatedSurfaceModeAQuarterPath]
  have h1 : HasDerivAt (fun θ : ℝ => (-(c : ℂ)) * Complex.cos θ) 0 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_ofReal_cos 0).const_mul (-(c : ℂ))
  have h2 : HasDerivAt (fun θ : ℝ => Complex.I * (-Complex.sin θ)) (-Complex.I) 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_ofReal_sin 0).const_mul (-1 : ℂ)).const_mul Complex.I
  simpa using (h1.add h2).deriv

lemma contDiffAt_rotatedSurfaceModeAPath (c : ℝ) :
    ContDiffAt ℝ 2 (rotatedSurfaceModeAPath c) 0 := by
  have hrew :
      rotatedSurfaceModeAPath c =
        fun θ : ℝ => (c : ℂ) * (Real.cos θ : ℂ) + Complex.I * (Real.sin θ : ℂ) := by
    funext θ
    simp [rotatedSurfaceModeAPath]
  have hcos : ContDiff ℝ 2 (fun θ : ℝ => (Real.cos θ : ℂ)) := by
    change ContDiff ℝ 2 (Complex.ofRealCLM ∘ Real.cos)
    simpa using
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos : ContDiff ℝ 2 Real.cos))
  have hsin : ContDiff ℝ 2 (fun θ : ℝ => (Real.sin θ : ℂ)) := by
    change ContDiff ℝ 2 (Complex.ofRealCLM ∘ Real.sin)
    simpa using
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin : ContDiff ℝ 2 Real.sin))
  rw [hrew]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (ContDiff.add (ContDiff.const_smul (c : ℂ) hcos) (ContDiff.const_smul Complex.I hsin)).contDiffAt

lemma contDiffAt_rotatedSurfaceModeAQuarterPath (c : ℝ) :
    ContDiffAt ℝ 2 (rotatedSurfaceModeAQuarterPath c) 0 := by
  have hrew :
      rotatedSurfaceModeAQuarterPath c =
        fun θ : ℝ => -((c : ℂ) * (Real.sin θ : ℂ)) + Complex.I * (Real.cos θ : ℂ) := by
    funext θ
    simp [rotatedSurfaceModeAQuarterPath]
  have hcos : ContDiff ℝ 2 (fun θ : ℝ => (Real.cos θ : ℂ)) := by
    change ContDiff ℝ 2 (Complex.ofRealCLM ∘ Real.cos)
    simpa using
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos : ContDiff ℝ 2 Real.cos))
  have hsin : ContDiff ℝ 2 (fun θ : ℝ => (Real.sin θ : ℂ)) := by
    change ContDiff ℝ 2 (Complex.ofRealCLM ∘ Real.sin)
    simpa using
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin : ContDiff ℝ 2 Real.sin))
  rw [hrew]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    (ContDiff.sub (ContDiff.const_smul Complex.I hcos) (ContDiff.const_smul (c : ℂ) hsin)).contDiffAt

lemma deriv_add_const_pow (n : ℕ) (c : ℝ) :
    deriv (fun s : ℝ => (c + s) ^ n) 0 = (n : ℝ) * c ^ (n - 1) := by
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => c + s) 0 :=
    (differentiableAt_const c).add differentiableAt_id
  have hadd : deriv (fun s : ℝ => c + s) 0 = 1 := by
    simpa [add_comm] using (hasDerivAt_id 0).const_add c |>.deriv
  simpa [hadd, zero_add, mul_comm, mul_left_comm, mul_assoc] using deriv_pow hdiff n

lemma iteratedDeriv_two_add_const_pow {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => (c + s) ^ n) 0 =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * c ^ (n - 2) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ => (c + s) ^ n) = fun s => (n : ℝ) * (c + s) ^ (n - 1) := by
    funext s
    have hdiff : DifferentiableAt ℝ (fun t : ℝ => c + t) s :=
      (differentiableAt_const c).add differentiableAt_id
    have hadd : deriv (fun t : ℝ => c + t) s = 1 := by
      simpa [add_comm] using (hasDerivAt_id s).const_add c |>.deriv
    simpa [hadd, mul_comm, mul_left_comm, mul_assoc] using deriv_pow hdiff n
  rw [hderiv]
  have hinner : deriv (fun s : ℝ => (c + s) ^ (n - 1)) 0 = ((n - 1 : ℕ) : ℝ) * c ^ (n - 2) := by
    have hdiff : DifferentiableAt ℝ (fun t : ℝ => c + t) 0 :=
      (differentiableAt_const c).add differentiableAt_id
    have hadd : deriv (fun t : ℝ => c + t) 0 = 1 := by
      simpa [add_comm] using (hasDerivAt_id 0).const_add c |>.deriv
    have hpow :
        deriv (fun s : ℝ => (c + s) ^ (n - 1)) 0 = c ^ (n - 1 - 1) * ((n - 1 : ℕ) : ℝ) := by
      simpa [hadd, zero_add, mul_comm, mul_left_comm, mul_assoc] using deriv_pow hdiff (n - 1)
    have hsub : n - 1 - 1 = n - 2 := by omega
    calc
      deriv (fun s : ℝ => (c + s) ^ (n - 1)) 0 = c ^ (n - 2) * ((n - 1 : ℕ) : ℝ) := by
        simpa [hsub] using hpow
      _ = ((n - 1 : ℕ) : ℝ) * c ^ (n - 2) := by ring
  simpa [hinner, mul_assoc] using deriv_const_mul (n : ℝ) (fun s : ℝ => (c + s) ^ (n - 1)) 0

lemma complex_I_pow_of_mod_four_eq_two {n : ℕ} (hmod : n % 4 = 2) :
    (Complex.I : ℂ) ^ n = -1 := by
  have hk : n = 4 * (n / 4) + 2 := by
    omega
  rw [hk, pow_add, pow_mul]
  norm_num

lemma complexRePow_second_sum_zero (n : ℕ) (z : ℂ) :
    (iteratedFDeriv ℝ 2 (fun w : ℂ => (w ^ n).re) z) ![1, 1] +
      (iteratedFDeriv ℝ 2 (fun w : ℂ => (w ^ n).re) z) ![Complex.I, Complex.I] = 0 := by
  have hΔ : Δ (fun w : ℂ => (w ^ n).re) z = 0 := by
    simpa using (((analyticAt_id.pow n).harmonicAt_re (x := z)).2.eq_of_nhds)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] at hΔ
  simpa using hΔ

lemma complexRePow_first_real_at_real (n : ℕ) (c : ℝ) :
    (fderiv ℝ (fun w : ℂ => (w ^ n).re) (c : ℂ)) 1 =
      (n : ℝ) * c ^ (n - 1) := by
  calc
    (fderiv ℝ (fun w : ℂ => (w ^ n).re) (c : ℂ)) 1
      = deriv (fun s : ℝ => ((((c : ℂ) + (s : ℂ)) ^ n).re)) 0 := by
          symm
          exact deriv_complexRePow_add_real n (c : ℂ)
    _ = deriv (fun s : ℝ => (c + s) ^ n) 0 := by
          congr with s
          simpa [Complex.ofReal_add, add_comm, add_left_comm, add_assoc] using
            (complex_ofReal_pow_re (c + s) n)
    _ = (n : ℝ) * c ^ (n - 1) := deriv_add_const_pow n c

lemma complexRePow_second_real_at_real {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    (iteratedFDeriv ℝ 2 (fun w : ℂ => (w ^ n).re) (c : ℂ)) ![1, 1] =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * c ^ (n - 2) := by
  calc
    (iteratedFDeriv ℝ 2 (fun w : ℂ => (w ^ n).re) (c : ℂ)) ![1, 1]
      = iteratedDeriv 2 (fun s : ℝ => ((((c : ℂ) + (s : ℂ)) ^ n).re)) 0 := by
          symm
          exact iteratedDeriv_two_complexRePow_add_real n (c : ℂ)
    _ = iteratedDeriv 2 (fun s : ℝ => (c + s) ^ n) 0 := by
          congr with s
          simpa [Complex.ofReal_add, add_comm, add_left_comm, add_assoc] using
            (complex_ofReal_pow_re (c + s) n)
    _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * c ^ (n - 2) :=
          iteratedDeriv_two_add_const_pow hn c

lemma complexRePow_second_I_at_real {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    (iteratedFDeriv ℝ 2 (fun w : ℂ => (w ^ n).re) (c : ℂ)) ![Complex.I, Complex.I] =
      -((n : ℝ) * ((n - 1 : ℕ) : ℝ) * c ^ (n - 2)) := by
  have hsum := complexRePow_second_sum_zero n (c : ℂ)
  have hreal := complexRePow_second_real_at_real hn c
  linarith

lemma complexRePow_add_I_mul_at_I_eq_neg_pow {n : ℕ} (hmod : n % 4 = 2) :
    (fun s : ℝ => (((Complex.I + (s : ℂ) * Complex.I) ^ n).re)) =
      fun s : ℝ => -((1 + s) ^ n) := by
  funext s
  have hI : (Complex.I : ℂ) ^ n = -1 := complex_I_pow_of_mod_four_eq_two hmod
  calc
    (((Complex.I + (s : ℂ) * Complex.I) ^ n).re)
      = ((((1 + s : ℂ) * Complex.I) ^ n).re) := by
          congr 1
          ring
    _ = ((((1 + s : ℂ)) ^ n * (Complex.I : ℂ) ^ n).re) := by
          rw [mul_pow]
    _ = (-(((1 + s : ℂ) ^ n)).re) := by
          rw [hI]
          simp
    _ = -((1 + s) ^ n) := by
          simpa [Complex.ofReal_add] using congrArg Neg.neg (complex_ofReal_pow_re (1 + s) n)

lemma complexRePow_first_I_at_I {n : ℕ} (hmod : n % 4 = 2) :
    (fderiv ℝ (fun w : ℂ => (w ^ n).re) Complex.I) Complex.I = -(n : ℝ) := by
  calc
    (fderiv ℝ (fun w : ℂ => (w ^ n).re) Complex.I) Complex.I
      = deriv (fun s : ℝ => (((Complex.I + (s : ℂ) * Complex.I) ^ n).re)) 0 := by
          symm
          exact deriv_complexRePow_add_I_mul n Complex.I
    _ = deriv (fun s : ℝ => -((1 + s) ^ n)) 0 := by
          rw [complexRePow_add_I_mul_at_I_eq_neg_pow hmod]
    _ = -(n : ℝ) := by
          simpa using (deriv_add_const_pow n 1 |> congrArg (fun t => -t))

lemma complexRePow_second_I_at_I {n : ℕ} (hn : 2 ≤ n) (hmod : n % 4 = 2) :
    (iteratedFDeriv ℝ 2 (fun w : ℂ => (w ^ n).re) Complex.I) ![Complex.I, Complex.I] =
      -((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
  calc
    (iteratedFDeriv ℝ 2 (fun w : ℂ => (w ^ n).re) Complex.I) ![Complex.I, Complex.I]
      = iteratedDeriv 2 (fun s : ℝ => (((Complex.I + (s : ℂ) * Complex.I) ^ n).re)) 0 := by
          symm
          exact iteratedDeriv_two_complexRePow_add_I_mul n Complex.I
    _ = iteratedDeriv 2 (fun s : ℝ => -((1 + s) ^ n)) 0 := by
          rw [complexRePow_add_I_mul_at_I_eq_neg_pow hmod]
    _ = -((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
          have hcont : ContDiffAt ℝ 2 (fun s : ℝ => (1 + s) ^ n) 0 := by
            simpa using (((contDiff_const.add contDiff_id).pow n).contDiffAt)
          rw [show (fun s : ℝ => -((1 + s) ^ n)) = fun s : ℝ => (-1 : ℝ) * (1 + s) ^ n by
            funext s
            ring]
          simpa [iteratedDeriv_two_add_const_pow hn 1] using
            (iteratedDeriv_const_mul hcont (-1 : ℝ))

lemma complexRePow_second_real_at_I {n : ℕ} (hn : 2 ≤ n) (hmod : n % 4 = 2) :
    (iteratedFDeriv ℝ 2 (fun w : ℂ => (w ^ n).re) Complex.I) ![1, 1] =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
  have hsum := complexRePow_second_sum_zero n Complex.I
  have hI := complexRePow_second_I_at_I hn hmod
  linarith

lemma rotatedSurfaceModeAEquator_secondDeriv_at_zero {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    iteratedDeriv 2 (fun θ : ℝ => rotatedSurfaceModeAEquator n c θ) 0 =
      -((n : ℝ) * ((n - 1 : ℕ) : ℝ) * c ^ (n - 2)) - (n : ℝ) * c ^ n := by
  let u : ℂ → ℝ := fun w => (w ^ n).re
  have hu : ContDiffAt ℝ 2 u (rotatedSurfaceModeAPath c 0) := by
    simpa [u, rotatedSurfaceModeAPath_zero] using
      (contDiff_iff_contDiffAt.mp (complexRePow_contDiff n)) (c : ℂ)
  have hcomp := iteratedDeriv_vcomp_two (g := u) (f := rotatedSurfaceModeAPath c) hu
    (contDiffAt_rotatedSurfaceModeAPath c)
  have hderiv : deriv (rotatedSurfaceModeAPath c) 0 = Complex.I := by
    rw [deriv_rotatedSurfaceModeAPath]
    simp
  have hsecond : iteratedDeriv 2 (rotatedSurfaceModeAPath c) 0 = -(c : ℂ) := by
    exact iteratedDeriv_two_rotatedSurfaceModeAPath c
  have hconst : (fun _ : Fin 2 => Complex.I) = ![Complex.I, Complex.I] := by
    funext i
    fin_cases i <;> rfl
  calc
    iteratedDeriv 2 (fun θ : ℝ => rotatedSurfaceModeAEquator n c θ) 0
      = iteratedDeriv 2 (u ∘ rotatedSurfaceModeAPath c) 0 := by rfl
    _ = ((iteratedFDeriv ℝ 2 u (rotatedSurfaceModeAPath c 0)) ![Complex.I, Complex.I]) +
          (fderiv ℝ u (rotatedSurfaceModeAPath c 0)) (-(c : ℂ)) := by
            simpa [hderiv, hsecond, hconst] using hcomp
    _ = ((iteratedFDeriv ℝ 2 u (c : ℂ)) ![Complex.I, Complex.I]) -
          c * (fderiv ℝ u (c : ℂ)) 1 := by
            rw [rotatedSurfaceModeAPath_zero]
            have happly :
                (fderiv ℝ u (c : ℂ)) (-(c : ℂ)) = -c * (fderiv ℝ u (c : ℂ)) 1 := by
              calc
                (fderiv ℝ u (c : ℂ)) (-(c : ℂ))
                  = (fderiv ℝ u (c : ℂ)) ((-c : ℝ) • (1 : ℂ)) := by simp
                _ = (-c : ℝ) * (fderiv ℝ u (c : ℂ)) 1 := by
                      rw [map_smul]
                      simp [smul_eq_mul]
                _ = -c * (fderiv ℝ u (c : ℂ)) 1 := by ring
            rw [happly]
            ring
    _ = -((n : ℝ) * ((n - 1 : ℕ) : ℝ) * c ^ (n - 2)) - (n : ℝ) * c ^ n := by
            rw [complexRePow_second_I_at_real hn c, complexRePow_first_real_at_real]
            have hpow : c * c ^ (n - 1) = c ^ n := by
              calc
                c * c ^ (n - 1) = c ^ (n - 1) * c := by rw [mul_comm]
                _ = c ^ ((n - 1) + 1) := by simpa using (pow_succ c (n - 1)).symm
                _ = c ^ n := by
                      have hs : n - 1 + 1 = n := by omega
                      simpa [hs]
            have hpow' : c * ((n : ℝ) * c ^ (n - 1)) = (n : ℝ) * c ^ n := by
              calc
                c * ((n : ℝ) * c ^ (n - 1)) = (n : ℝ) * (c * c ^ (n - 1)) := by ring
                _ = (n : ℝ) * c ^ n := by rw [hpow]
            rw [hpow']

lemma rotatedSurfaceModeAQuarterShift_secondDeriv_at_zero {n : ℕ}
    (hn : 2 ≤ n) (hmod : n % 4 = 2) (c : ℝ) :
    iteratedDeriv 2 (fun θ : ℝ => rotatedSurfaceModeAEquator n c (θ + π / 2)) 0 =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * c ^ 2 + (n : ℝ) := by
  let u : ℂ → ℝ := fun w => (w ^ n).re
  have hu : ContDiffAt ℝ 2 u (rotatedSurfaceModeAQuarterPath c 0) := by
    simpa [u, rotatedSurfaceModeAQuarterPath_zero] using
      (contDiff_iff_contDiffAt.mp (complexRePow_contDiff n)) Complex.I
  have hcomp := iteratedDeriv_vcomp_two (g := u) (f := rotatedSurfaceModeAQuarterPath c) hu
    (contDiffAt_rotatedSurfaceModeAQuarterPath c)
  have hderiv : deriv (rotatedSurfaceModeAQuarterPath c) 0 = -(c : ℂ) := by
    rw [deriv_rotatedSurfaceModeAQuarterPath]
    simp
  have hsecond : iteratedDeriv 2 (rotatedSurfaceModeAQuarterPath c) 0 = -Complex.I := by
    exact iteratedDeriv_two_rotatedSurfaceModeAQuarterPath c
  have hconst : (fun _ : Fin 2 => (-(c : ℂ))) = ![-(c : ℂ), -(c : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  have hone : (fun _ : Fin 2 => (1 : ℂ)) = ![1, 1] := by
    funext i
    fin_cases i <;> rfl
  have hnegconst :
      ![-(c : ℂ), -(c : ℂ)] = fun _ : Fin 2 => (-c : ℝ) • (1 : ℂ) := by
    ext i
    fin_cases i <;> simp
  calc
    iteratedDeriv 2 (fun θ : ℝ => rotatedSurfaceModeAEquator n c (θ + π / 2)) 0
      = iteratedDeriv 2 (u ∘ rotatedSurfaceModeAQuarterPath c) 0 := by
          congr with θ
          change ((rotatedSurfaceModeAPath c (θ + π / 2)) ^ n).re =
            ((rotatedSurfaceModeAQuarterPath c θ) ^ n).re
          rw [rotatedSurfaceModeAQuarterPath_eq_shift]
    _ = ((iteratedFDeriv ℝ 2 u (rotatedSurfaceModeAQuarterPath c 0)) ![-(c : ℂ), -(c : ℂ)]) +
          (fderiv ℝ u (rotatedSurfaceModeAQuarterPath c 0)) (-Complex.I) := by
            simpa [hderiv, hsecond, hconst] using hcomp
    _ = c ^ 2 * ((iteratedFDeriv ℝ 2 u Complex.I) ![1, 1]) -
          (fderiv ℝ u Complex.I) Complex.I := by
            rw [rotatedSurfaceModeAQuarterPath_zero]
            have hmult :
                (iteratedFDeriv ℝ 2 u Complex.I) ![-(c : ℂ), -(c : ℂ)] =
                  c ^ 2 * ((iteratedFDeriv ℝ 2 u Complex.I) ![1, 1]) := by
              calc
                (iteratedFDeriv ℝ 2 u Complex.I) ![-(c : ℂ), -(c : ℂ)]
                  = (iteratedFDeriv ℝ 2 u Complex.I) (fun _ : Fin 2 => (-c : ℝ) • (1 : ℂ)) := by
                      rw [hnegconst]
                _ = (∏ i : Fin 2, (-c : ℝ)) • (iteratedFDeriv ℝ 2 u Complex.I) (fun _ : Fin 2 => (1 : ℂ)) := by
                      rw [ContinuousMultilinearMap.map_smul_univ]
                _ = c ^ 2 * ((iteratedFDeriv ℝ 2 u Complex.I) ![1, 1]) := by
                      rw [hone]
                      simp [Fin.prod_univ_two, pow_two, smul_eq_mul]
            have hlin :
                (fderiv ℝ u Complex.I) (-Complex.I) = -(fderiv ℝ u Complex.I) Complex.I := by
              calc
                (fderiv ℝ u Complex.I) (-Complex.I)
                  = (fderiv ℝ u Complex.I) ((-1 : ℝ) • Complex.I) := by simp
                _ = (-1 : ℝ) * (fderiv ℝ u Complex.I) Complex.I := by
                      rw [map_smul]
                      simp [smul_eq_mul]
                _ = -(fderiv ℝ u Complex.I) Complex.I := by ring
            rw [hmult, hlin]
            ring
    _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * c ^ 2 + (n : ℝ) := by
            rw [complexRePow_second_real_at_I hn hmod, complexRePow_first_I_at_I hmod]
            ring

lemma rotatedSurfaceModeAQuarterSum_secondDeriv_at_zero {n : ℕ}
    (hn : 2 ≤ n) (hmod : n % 4 = 2) (c : ℝ) :
    iteratedDeriv 2 (rotatedSurfaceModeAQuarterSum n c) 0 =
      (n : ℝ) *
        (((n - 1 : ℕ) : ℝ) * c ^ 2 + 1 -
          ((n - 1 : ℕ) : ℝ) * c ^ (n - 2) - c ^ n) := by
  unfold rotatedSurfaceModeAQuarterSum
  have hleft : ContDiffAt ℝ 2 (fun θ : ℝ => rotatedSurfaceModeAEquator n c θ) 0 := by
    let u : ℂ → ℝ := fun w => (w ^ n).re
    have hu : ContDiffAt ℝ 2 u (rotatedSurfaceModeAPath c 0) := by
      simpa [u, rotatedSurfaceModeAPath_zero] using
        (contDiff_iff_contDiffAt.mp (complexRePow_contDiff n)) (c : ℂ)
    simpa [u, rotatedSurfaceModeAEquator, rotatedSurfaceModeAPath] using
      hu.comp 0 (contDiffAt_rotatedSurfaceModeAPath c)
  have hright : ContDiffAt ℝ 2 (fun θ : ℝ => rotatedSurfaceModeAEquator n c (θ + π / 2)) 0 := by
    let u : ℂ → ℝ := fun w => (w ^ n).re
    have hu : ContDiffAt ℝ 2 u (rotatedSurfaceModeAQuarterPath c 0) := by
      simpa [u, rotatedSurfaceModeAQuarterPath_zero] using
        (contDiff_iff_contDiffAt.mp (complexRePow_contDiff n)) Complex.I
    have hrew :
        (fun θ : ℝ => rotatedSurfaceModeAEquator n c (θ + π / 2)) = u ∘ rotatedSurfaceModeAQuarterPath c := by
      funext θ
      change ((rotatedSurfaceModeAPath c (θ + π / 2)) ^ n).re =
        ((rotatedSurfaceModeAQuarterPath c θ) ^ n).re
      rw [rotatedSurfaceModeAQuarterPath_eq_shift]
    rw [hrew]
    exact hu.comp 0 (contDiffAt_rotatedSurfaceModeAQuarterPath c)
  rw [show (fun θ : ℝ => rotatedSurfaceModeAEquator n c θ + rotatedSurfaceModeAEquator n c (θ + π / 2)) =
      ((fun θ : ℝ => rotatedSurfaceModeAEquator n c θ) + fun θ : ℝ => rotatedSurfaceModeAEquator n c (θ + π / 2)) by
      rfl]
  rw [iteratedDeriv_add hleft hright]
  rw [rotatedSurfaceModeAEquator_secondDeriv_at_zero hn c,
    rotatedSurfaceModeAQuarterShift_secondDeriv_at_zero hn hmod c]
  ring

lemma rotatedSurfaceModeAQuarterSum_secondDeriv_at_zero_pos {n : ℕ}
    (hn : 2 < n) (hmod : n % 4 = 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    0 < iteratedDeriv 2 (rotatedSurfaceModeAQuarterSum n c) 0 := by
  have hn2 : 2 ≤ n := le_of_lt hn
  rw [rotatedSurfaceModeAQuarterSum_secondDeriv_at_zero hn2 hmod c]
  have hpowlt : c ^ (n - 2) < c ^ 2 := by
    simpa using (pow_right_strictAnti₀ hc0 hc1 (show 2 < n - 2 by omega))
  have hpowlt1 : c ^ n < 1 := by
    exact pow_lt_one₀ (le_of_lt hc0) hc1 (show n ≠ 0 by omega)
  have hcoef : 0 < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hcoef' : 0 ≤ ((n - 1 : ℕ) : ℝ) := le_of_lt hcoef
  have hsub1 : 0 < c ^ 2 - c ^ (n - 2) := sub_pos.mpr hpowlt
  have hsub2 : 0 < 1 - c ^ n := sub_pos.mpr hpowlt1
  have hterm1 : 0 < ((n - 1 : ℕ) : ℝ) * (c ^ 2 - c ^ (n - 2)) := by
    nlinarith
  have hinner :
      0 < ((n - 1 : ℕ) : ℝ) * c ^ 2 + 1 - ((n - 1 : ℕ) : ℝ) * c ^ (n - 2) - c ^ n := by
    nlinarith
  have hnreal : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n by omega)
  nlinarith

theorem not_circleFrame_rotatedSurfaceModeAEquator_of_mod_four_eq_two {n : ℕ}
    (hn : 2 < n) (hmod : n % 4 = 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ circleFrameFunction (fun θ : ℝ => rotatedSurfaceModeAEquator n c θ) := by
  intro hframe
  rcases hframe with ⟨W, hW⟩
  have hconst : rotatedSurfaceModeAQuarterSum n c = fun _ : ℝ => W := by
    funext θ
    simpa [rotatedSurfaceModeAQuarterSum] using hW θ
  have hzero : iteratedDeriv 2 (rotatedSurfaceModeAQuarterSum n c) 0 = 0 := by
    rw [hconst]
    simpa using (iteratedDeriv_const (n := 2) (c := W) (x := 0))
  have hpos :=
    rotatedSurfaceModeAQuarterSum_secondDeriv_at_zero_pos hn hmod hc0 hc1
  linarith
