import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
noncomputable section

open Complex InnerProductSpace
open scoped Topology

lemma complexRePow_contDiff (m : ℕ) : ContDiff ℝ 2 (fun z : ℂ => (z ^ m).re) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  simpa using ((analyticAt_id.pow m).harmonicAt_re (x := z)).1

lemma complex_ofReal_pow_re (s : ℝ) : ∀ m : ℕ, (((s : ℂ) ^ m).re) = s ^ m
  | 0 => by simp
  | m + 1 => by
      simp [pow_succ, complex_ofReal_pow_re s m, mul_comm]

lemma complex_ofReal_pow_im (s : ℝ) : ∀ m : ℕ, (((s : ℂ) ^ m).im) = 0
  | 0 => by simp
  | m + 1 => by
      simp [pow_succ, complex_ofReal_pow_im s m, mul_comm]

lemma complexRePow_homogeneous (m : ℕ) (z : ℂ) (s : ℝ) :
    (fun w : ℂ => (w ^ m).re) ((s : ℂ) * z) = s ^ m * (fun w : ℂ => (w ^ m).re) z := by
  calc
    ((((s : ℂ) * z) ^ m).re) = ((((s : ℂ) ^ m) * (z ^ m)).re) := by
      simp [mul_pow]
    _ = (((s : ℂ) ^ m).re) * (z ^ m).re - (((s : ℂ) ^ m).im) * (z ^ m).im := by
      simp [Complex.mul_re]
    _ = s ^ m * (z ^ m).re := by
      rw [complex_ofReal_pow_re, complex_ofReal_pow_im]
      ring

lemma hasDerivAt_realMul_complex (z : ℂ) : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z 1 := by
  simpa using ((hasDerivAt_id (1 : ℂ)).mul_const z).comp_ofReal

lemma complexRePow_euler (m : ℕ) (z : ℂ) :
    (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) z = (m : ℝ) * (z ^ m).re := by
  have hcd : ContDiffAt ℝ 2 (fun w : ℂ => (w ^ m).re) z :=
    contDiff_iff_contDiffAt.mp (complexRePow_contDiff m) z
  have hg : HasFDerivAt (fun w : ℂ => (w ^ m).re) (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) z := by
    exact (hcd.differentiableAt (by norm_num)).hasFDerivAt
  have hs : HasDerivAt (fun s : ℝ => (s : ℂ) * z) z 1 :=
    hasDerivAt_realMul_complex z
  have hcomp :
      HasDerivAt ((fun w : ℂ => (w ^ m).re) ∘ fun s : ℝ => (s : ℂ) * z)
        ((fderiv ℝ (fun w : ℂ => (w ^ m).re) z) z) 1 := by
    simpa [Function.comp] using
      hg.comp_hasDerivAt_of_eq (x := 1) (y := z) hs (by simp)
  have hcomp' : HasDerivAt (fun s : ℝ => s ^ m * (z ^ m).re)
      ((fderiv ℝ (fun w : ℂ => (w ^ m).re) z) z) 1 := by
    convert hcomp using 1
    ext s
    simp [Function.comp, complexRePow_homogeneous]
  have hpow : HasDerivAt (fun s : ℝ => s ^ m * (z ^ m).re) ((m : ℝ) * (z ^ m).re) 1 := by
    simpa [one_pow, mul_comm, mul_left_comm, mul_assoc] using
      (HasDerivAt.mul_const ((hasDerivAt_id (1 : ℝ)).pow m) ((z ^ m).re))
  exact hcomp'.unique hpow

lemma bilinearIteratedFDerivTwo_apply_of_bilinear
    {g : (ℝ × ℝ) → ℝ} (h : IsBoundedBilinearMap ℝ g)
    (p v w : ℝ × ℝ) :
    ((bilinearIteratedFDerivTwo ℝ g p) v) w = g (v.1, w.2) + g (w.1, v.2) := by
  have hEq : fderiv ℝ g = h.deriv := by
    funext q
    exact h.fderiv (p := q)
  rw [bilinearIteratedFDerivTwo, hEq, h.isBoundedLinearMap_deriv.fderiv]
  rfl

lemma iteratedDeriv_prodMk_fst {a b : ℝ → ℝ} {x : ℝ}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) :
    (iteratedDeriv 2 (fun s => (a s, b s)) x).1 = iteratedDeriv 2 a x := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  have hcomp := L.iteratedFDeriv_comp_left (f := fun s : ℝ => (a s, b s)) (ha.prodMk hb)
    (show (2 : WithTop ℕ∞) ≤ 2 by norm_num)
  have happ := congrArg (fun M => M ![1, 1]) hcomp
  simpa [L, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Fin.prod_univ_two] using happ.symm

lemma iteratedDeriv_prodMk_snd {a b : ℝ → ℝ} {x : ℝ}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) :
    (iteratedDeriv 2 (fun s => (a s, b s)) x).2 = iteratedDeriv 2 b x := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hcomp := L.iteratedFDeriv_comp_left (f := fun s : ℝ => (a s, b s)) (ha.prodMk hb)
    (show (2 : WithTop ℕ∞) ≤ 2 by norm_num)
  have happ := congrArg (fun M => M ![1, 1]) hcomp
  simpa [L, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Fin.prod_univ_two] using happ.symm

lemma iteratedDeriv_mul_formula
    {a b : ℝ → ℝ} {x : ℝ}
    (ha : ContDiffAt ℝ 2 a x) (hb : ContDiffAt ℝ 2 b x) :
    iteratedDeriv 2 (fun s => a s * b s) x =
      iteratedDeriv 2 a x * b x + 2 * deriv a x * deriv b x + a x * iteratedDeriv 2 b x := by
  let g : ℝ × ℝ → ℝ := fun p => p.1 * p.2
  let f : ℝ → ℝ × ℝ := fun s => (a s, b s)
  have hg : ContDiffAt ℝ 2 g (f x) := by
    simpa [g] using (contDiff_mul.comp (contDiff_fst.prodMk contDiff_snd)).contDiffAt
  have hf : ContDiffAt ℝ 2 f x := by
    simpa [f] using ha.prodMk hb
  rw [show (fun s => a s * b s) = g ∘ f by rfl]
  rw [iteratedDeriv_vcomp_two hg hf]
  have hbil : IsBoundedBilinearMap ℝ g := by
    simpa [g] using (ContinuousLinearMap.mul ℝ ℝ).isBoundedBilinearMap
  have hderivf : deriv f x = (deriv a x, deriv b x) := by
    simpa [f] using
      ((ha.differentiableAt (by norm_num)).hasDerivAt.prodMk
        (hb.differentiableAt (by norm_num)).hasDerivAt).deriv
  rw [hderivf, hbil.fderiv]
  have h2 : ((iteratedFDeriv ℝ 2 g (f x)) fun _ : Fin 2 => (deriv a x, deriv b x))
      = 2 * deriv a x * deriv b x := by
    have hconst : (fun _ : Fin 2 => (deriv a x, deriv b x)) =
        ![(deriv a x, deriv b x), (deriv a x, deriv b x)] := by
      funext i
      fin_cases i <;> rfl
    rw [hconst, ← bilinearIteratedFDerivTwo_eq_iteratedFDeriv (f := g) (e := f x)
      (e₁ := (deriv a x, deriv b x)) (e₂ := (deriv a x, deriv b x))]
    have htmp := bilinearIteratedFDerivTwo_apply_of_bilinear hbil (f x)
      (deriv a x, deriv b x) (deriv a x, deriv b x)
    simp [g] at htmp
    ring_nf at htmp ⊢
    exact htmp
  rw [h2, hbil.deriv_apply]
  rw [iteratedDeriv_prodMk_fst ha hb, iteratedDeriv_prodMk_snd ha hb]
  simp [g, f, mul_comm, mul_left_comm]
  ring

lemma deriv_normSq_add_real (z : ℂ) :
    deriv (fun s : ℝ => Complex.normSq (z + s)) 0 = 2 * z.re := by
  have hfun : (fun s : ℝ => Complex.normSq (z + s)) =
      fun s : ℝ => (z.re + s) ^ 2 + z.im ^ 2 := by
    funext s
    simp [Complex.normSq, pow_two, add_comm]
  rw [hfun]
  have hsq : HasDerivAt (fun s : ℝ => (z.re + s) ^ 2) (2 * z.re) 0 := by
    simpa using (((hasDerivAt_const (0 : ℝ) z.re).add (hasDerivAt_id 0)).pow 2)
  exact (hsq.add_const (z.im ^ 2)).deriv

lemma iteratedDeriv_two_normSq_add_real (z : ℂ) :
    iteratedDeriv 2 (fun s : ℝ => Complex.normSq (z + s)) 0 = 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ => Complex.normSq (z + s)) = fun s => 2 * (z.re + s) := by
    funext s
    have hsq : HasDerivAt (fun t : ℝ => (z.re + t) ^ 2) (2 * (z.re + s)) s := by
      simpa using (((hasDerivAt_const s z.re).add (hasDerivAt_id s)).pow 2)
    have hfun : (fun t : ℝ => Complex.normSq (z + t)) =
        fun t : ℝ => (z.re + t) ^ 2 + z.im ^ 2 := by
      funext t
      simp [Complex.normSq, pow_two, add_comm]
    rw [hfun]
    exact (hsq.add_const (z.im ^ 2)).deriv
  rw [hderiv]
  have hlin : HasDerivAt (fun s : ℝ => 2 * (z.re + s)) 2 0 := by
    simpa [two_mul, mul_add, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_const (0 : ℝ) z.re).add (hasDerivAt_id 0)).const_mul 2
  exact hlin.deriv

lemma deriv_normSq_add_I_mul (z : ℂ) :
    deriv (fun s : ℝ => Complex.normSq (z + s * I)) 0 = 2 * z.im := by
  have hfun : (fun s : ℝ => Complex.normSq (z + s * I)) =
      fun s : ℝ => z.re ^ 2 + (z.im + s) ^ 2 := by
    funext s
    simp [Complex.normSq, pow_two, add_comm, mul_comm]
  rw [hfun]
  have hsq : HasDerivAt (fun s : ℝ => (z.im + s) ^ 2) (2 * z.im) 0 := by
    simpa using (((hasDerivAt_const (0 : ℝ) z.im).add (hasDerivAt_id 0)).pow 2)
  exact (hsq.const_add (z.re ^ 2)).deriv

lemma iteratedDeriv_two_normSq_add_I_mul (z : ℂ) :
    iteratedDeriv 2 (fun s : ℝ => Complex.normSq (z + s * I)) 0 = 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ => Complex.normSq (z + s * I)) = fun s => 2 * (z.im + s) := by
    funext s
    have hsq : HasDerivAt (fun t : ℝ => (z.im + t) ^ 2) (2 * (z.im + s)) s := by
      simpa using (((hasDerivAt_const s z.im).add (hasDerivAt_id s)).pow 2)
    have hfun : (fun t : ℝ => Complex.normSq (z + t * I)) =
        fun t : ℝ => z.re ^ 2 + (z.im + t) ^ 2 := by
      funext t
      simp [Complex.normSq, pow_two, add_comm, mul_comm]
    rw [hfun]
    exact (hsq.const_add (z.re ^ 2)).deriv
  rw [hderiv]
  have hlin : HasDerivAt (fun s : ℝ => 2 * (z.im + s)) 2 0 := by
    simpa [two_mul, mul_add, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_const (0 : ℝ) z.im).add (hasDerivAt_id 0)).const_mul 2
  exact hlin.deriv

lemma hasDerivAt_realMul_complex_at (z : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ) * z) z s := by
  simpa using ((hasDerivAt_id (s : ℂ)).mul_const z).comp_ofReal

lemma hasDerivAt_add_real_complex (z : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 s := by
  simpa [add_comm] using (hasDerivAt_realMul_complex_at 1 s).const_add z

lemma hasDerivAt_add_I_mul_complex (z : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => z + (t : ℂ) * I) I s := by
  simpa [add_comm, add_left_comm, add_assoc, mul_comm] using
    (hasDerivAt_realMul_complex_at I s).const_add z

lemma iteratedDeriv_two_add_real_complex (z : ℂ) :
    iteratedDeriv 2 (fun s : ℝ => z + (s : ℂ)) 0 = 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ => z + (s : ℂ)) = fun _ : ℝ => (1 : ℂ) := by
    funext s
    exact (hasDerivAt_add_real_complex z s).deriv
  rw [hderiv]
  simp

lemma iteratedDeriv_two_add_I_mul_complex (z : ℂ) :
    iteratedDeriv 2 (fun s : ℝ => z + (s : ℂ) * I) 0 = 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ => z + (s : ℂ) * I) = fun _ : ℝ => I := by
    funext s
    exact (hasDerivAt_add_I_mul_complex z s).deriv
  rw [hderiv]
  simp

lemma contDiff_add_real_path (z : ℂ) : ContDiff ℝ 2 (fun s : ℝ => z + (s : ℂ)) := by
  simpa using (contDiff_const.add Complex.ofRealCLM.contDiff)

lemma contDiff_add_I_mul_path (z : ℂ) : ContDiff ℝ 2 (fun s : ℝ => z + (s : ℂ) * I) := by
  simpa [smul_eq_mul, mul_comm] using
    (contDiff_const.add (ContDiff.const_smul I Complex.ofRealCLM.contDiff))

lemma contDiffAt_normSq_add_real (z : ℂ) :
    ContDiffAt ℝ 2 (fun s : ℝ => Complex.normSq (z + s)) 0 := by
  have hfun : (fun s : ℝ => Complex.normSq (z + s)) =
      fun s : ℝ => (z.re + s) ^ 2 + z.im ^ 2 := by
    funext s
    simp [Complex.normSq, pow_two, add_comm]
  rw [hfun]
  exact (((contDiff_const.add contDiff_id).pow 2).add contDiff_const).contDiffAt

lemma contDiffAt_normSq_add_I_mul (z : ℂ) :
    ContDiffAt ℝ 2 (fun s : ℝ => Complex.normSq (z + s * I)) 0 := by
  have hfun : (fun s : ℝ => Complex.normSq (z + s * I)) =
      fun s : ℝ => z.re ^ 2 + (z.im + s) ^ 2 := by
    funext s
    simp [Complex.normSq, pow_two, add_comm, mul_comm]
  rw [hfun]
  exact (contDiff_const.add ((contDiff_const.add contDiff_id).pow 2)).contDiffAt

lemma contDiffAt_repow_add_real (m : ℕ) (z : ℂ) :
    ContDiffAt ℝ 2 (fun s : ℝ => ((z + (s : ℂ)) ^ m).re) 0 := by
  simpa using
    (Complex.reCLM.contDiff.contDiffAt.comp 0 (((contDiff_add_real_path z).pow m).contDiffAt))

lemma contDiffAt_repow_add_I_mul (m : ℕ) (z : ℂ) :
    ContDiffAt ℝ 2 (fun s : ℝ => ((z + (s : ℂ) * I) ^ m).re) 0 := by
  simpa using
    (Complex.reCLM.contDiff.contDiffAt.comp 0 (((contDiff_add_I_mul_path z).pow m).contDiffAt))

lemma complex_normSq_contDiff : ContDiff ℝ 2 Complex.normSq := by
  simpa [Complex.normSq, pow_two, add_comm] using
    (Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)

lemma deriv_complexRePow_add_real (m : ℕ) (z : ℂ) :
    deriv (fun s : ℝ => ((z + (s : ℂ)) ^ m).re) 0 =
      (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) 1 := by
  have hcd : ContDiffAt ℝ 2 (fun w : ℂ => (w ^ m).re) z :=
    contDiff_iff_contDiffAt.mp (complexRePow_contDiff m) z
  have hg : HasFDerivAt (fun w : ℂ => (w ^ m).re) (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) z := by
    exact (hcd.differentiableAt (by norm_num)).hasFDerivAt
  exact (hg.comp_hasDerivAt_of_eq (x := 0) (y := z) (hasDerivAt_add_real_complex z 0) (by simp)).deriv

lemma deriv_complexRePow_add_I_mul (m : ℕ) (z : ℂ) :
    deriv (fun s : ℝ => ((z + (s : ℂ) * I) ^ m).re) 0 =
      (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) I := by
  have hcd : ContDiffAt ℝ 2 (fun w : ℂ => (w ^ m).re) z :=
    contDiff_iff_contDiffAt.mp (complexRePow_contDiff m) z
  have hg : HasFDerivAt (fun w : ℂ => (w ^ m).re) (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) z := by
    exact (hcd.differentiableAt (by norm_num)).hasFDerivAt
  exact (hg.comp_hasDerivAt_of_eq (x := 0) (y := z) (hasDerivAt_add_I_mul_complex z 0) (by simp)).deriv

lemma iteratedDeriv_two_complexRePow_add_real (m : ℕ) (z : ℂ) :
    iteratedDeriv 2 (fun s : ℝ => ((z + (s : ℂ)) ^ m).re) 0 =
      (iteratedFDeriv ℝ 2 (fun w : ℂ => (w ^ m).re) z) ![1, 1] := by
  let u : ℂ → ℝ := fun w => (w ^ m).re
  have hu : ContDiffAt ℝ 2 u z :=
    contDiff_iff_contDiffAt.mp (complexRePow_contDiff m) z
  have hpath : ContDiffAt ℝ 2 (fun s : ℝ => z + (s : ℂ)) 0 := (contDiff_add_real_path z).contDiffAt
  have hcomp := iteratedDeriv_vcomp_two
    (g := u) (f := fun s : ℝ => z + (s : ℂ)) (x := 0) (by simpa using hu) hpath
  have hderiv : deriv (fun s : ℝ => z + (s : ℂ)) 0 = 1 := (hasDerivAt_add_real_complex z 0).deriv
  have hsecond : iteratedDeriv 2 (fun s : ℝ => z + (s : ℂ)) 0 = 0 := iteratedDeriv_two_add_real_complex z
  have hconst : (fun _ : Fin 2 => (1 : ℂ)) = ![1, 1] := by
    funext i
    fin_cases i <;> rfl
  simpa [u, hderiv, hsecond, hconst] using hcomp

lemma iteratedDeriv_two_complexRePow_add_I_mul (m : ℕ) (z : ℂ) :
    iteratedDeriv 2 (fun s : ℝ => ((z + (s : ℂ) * I) ^ m).re) 0 =
      (iteratedFDeriv ℝ 2 (fun w : ℂ => (w ^ m).re) z) ![I, I] := by
  let u : ℂ → ℝ := fun w => (w ^ m).re
  have hu : ContDiffAt ℝ 2 u z :=
    contDiff_iff_contDiffAt.mp (complexRePow_contDiff m) z
  have hpath : ContDiffAt ℝ 2 (fun s : ℝ => z + (s : ℂ) * I) 0 := (contDiff_add_I_mul_path z).contDiffAt
  have hcomp := iteratedDeriv_vcomp_two
    (g := u) (f := fun s : ℝ => z + (s : ℂ) * I) (x := 0) (by simpa using hu) hpath
  have hderiv : deriv (fun s : ℝ => z + (s : ℂ) * I) 0 = I := (hasDerivAt_add_I_mul_complex z 0).deriv
  have hsecond : iteratedDeriv 2 (fun s : ℝ => z + (s : ℂ) * I) 0 = 0 := iteratedDeriv_two_add_I_mul_complex z
  have hconst : (fun _ : Fin 2 => I) = ![I, I] := by
    funext i
    fin_cases i <;> rfl
  simpa [u, hderiv, hsecond, hconst] using hcomp

lemma iteratedDeriv_two_comp_add_real {h : ℂ → ℝ} {z : ℂ}
    (hh : ContDiffAt ℝ 2 h z) :
    iteratedDeriv 2 (fun s : ℝ => h (z + (s : ℂ))) 0 = (iteratedFDeriv ℝ 2 h z) ![1, 1] := by
  have hpath : ContDiffAt ℝ 2 (fun s : ℝ => z + (s : ℂ)) 0 := (contDiff_add_real_path z).contDiffAt
  have hcomp := iteratedDeriv_vcomp_two
    (g := h) (f := fun s : ℝ => z + (s : ℂ)) (x := 0) (by simpa using hh) hpath
  have hderiv : deriv (fun s : ℝ => z + (s : ℂ)) 0 = 1 := (hasDerivAt_add_real_complex z 0).deriv
  have hsecond : iteratedDeriv 2 (fun s : ℝ => z + (s : ℂ)) 0 = 0 := iteratedDeriv_two_add_real_complex z
  have hconst : (fun _ : Fin 2 => (1 : ℂ)) = ![1, 1] := by
    funext i
    fin_cases i <;> rfl
  simpa [hderiv, hsecond, hconst] using hcomp

lemma iteratedDeriv_two_comp_add_I_mul {h : ℂ → ℝ} {z : ℂ}
    (hh : ContDiffAt ℝ 2 h z) :
    iteratedDeriv 2 (fun s : ℝ => h (z + (s : ℂ) * I)) 0 = (iteratedFDeriv ℝ 2 h z) ![I, I] := by
  have hpath : ContDiffAt ℝ 2 (fun s : ℝ => z + (s : ℂ) * I) 0 := (contDiff_add_I_mul_path z).contDiffAt
  have hcomp := iteratedDeriv_vcomp_two
    (g := h) (f := fun s : ℝ => z + (s : ℂ) * I) (x := 0) (by simpa using hh) hpath
  have hderiv : deriv (fun s : ℝ => z + (s : ℂ) * I) 0 = I := (hasDerivAt_add_I_mul_complex z 0).deriv
  have hsecond : iteratedDeriv 2 (fun s : ℝ => z + (s : ℂ) * I) 0 = 0 := iteratedDeriv_two_add_I_mul_complex z
  have hconst : (fun _ : Fin 2 => I) = ![I, I] := by
    funext i
    fin_cases i <;> rfl
  simpa [hderiv, hsecond, hconst] using hcomp

lemma complexRePow_fderiv_apply_self (m : ℕ) (z : ℂ) :
    (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) z =
      z.re * (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) 1 +
        z.im * (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) I := by
  have hz : (z.re : ℂ) + z.im * I = z := by
    simp [Complex.re_add_im]
  have h1 : ((z.re : ℂ)) = z.re • (1 : ℂ) := by simp
  have hI : z.im * I = z.im • I := by simp [mul_comm]
  calc
    (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) z
      = (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) ((z.re : ℂ) + z.im * I) := by rw [hz]
    _ = (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) (z.re : ℂ) +
          (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) (z.im * I) := by rw [map_add]
    _ = z.re * (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) 1 +
          z.im * (fderiv ℝ (fun w : ℂ => (w ^ m).re) z) I := by
            rw [h1, hI, map_smul, map_smul]
            simp [smul_eq_mul]

theorem complex_normSq_mul_rePow_laplacian (m : ℕ) (z : ℂ) :
    Δ (fun w : ℂ => Complex.normSq w * (w ^ m).re) z =
      4 * ((m + 1 : ℕ) : ℝ) * (z ^ m).re := by
  let u : ℂ → ℝ := fun w => (w ^ m).re
  let h : ℂ → ℝ := fun w => Complex.normSq w * (w ^ m).re
  have hh : ContDiffAt ℝ 2 h z := by
    simpa [h, u] using (complex_normSq_contDiff.contDiffAt.mul ((complexRePow_contDiff m).contDiffAt))
  have hdx :=
    iteratedDeriv_mul_formula
      (a := fun s : ℝ => Complex.normSq (z + s))
      (b := fun s : ℝ => ((z + (s : ℂ)) ^ m).re)
      (x := 0)
      (contDiffAt_normSq_add_real z)
      (contDiffAt_repow_add_real m z)
  have hdy :=
    iteratedDeriv_mul_formula
      (a := fun s : ℝ => Complex.normSq (z + s * I))
      (b := fun s : ℝ => ((z + (s : ℂ) * I) ^ m).re)
      (x := 0)
      (contDiffAt_normSq_add_I_mul z)
      (contDiffAt_repow_add_I_mul m z)
  have hx : (iteratedFDeriv ℝ 2 h z) ![1, 1] =
      iteratedDeriv 2 (fun s : ℝ => h (z + (s : ℂ))) 0 := by
    symm
    exact iteratedDeriv_two_comp_add_real hh
  have hy : (iteratedFDeriv ℝ 2 h z) ![I, I] =
      iteratedDeriv 2 (fun s : ℝ => h (z + (s : ℂ) * I)) 0 := by
    symm
    exact iteratedDeriv_two_comp_add_I_mul hh
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  change (iteratedFDeriv ℝ 2 h z) ![1, 1] + (iteratedFDeriv ℝ 2 h z) ![I, I] =
    4 * ((m + 1 : ℕ) : ℝ) * (z ^ m).re
  rw [hx, hy]
  have hu0 :
      (iteratedFDeriv ℝ 2 u z) ![1, 1] + (iteratedFDeriv ℝ 2 u z) ![I, I] = 0 := by
    have hΔu : Δ u z = 0 := by
      simpa [u] using (((analyticAt_id.pow m).harmonicAt_re (x := z)).2.eq_of_nhds)
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] at hΔu
    simpa [u] using hΔu
  have hself :
      (fderiv ℝ u z) z = z.re * (fderiv ℝ u z) 1 + z.im * (fderiv ℝ u z) I := by
    simpa [u] using complexRePow_fderiv_apply_self m z
  have heuler : (fderiv ℝ u z) z = (m : ℝ) * (z ^ m).re := by
    simpa [u] using complexRePow_euler m z
  calc
    iteratedDeriv 2 (fun s : ℝ => h (z + (s : ℂ))) 0 +
        iteratedDeriv 2 (fun s : ℝ => h (z + (s : ℂ) * I)) 0
      = (2 * (z ^ m).re + 2 * (2 * z.re) * (fderiv ℝ u z) 1 + Complex.normSq z * (iteratedFDeriv ℝ 2 u z) ![1, 1]) +
          (2 * (z ^ m).re + 2 * (2 * z.im) * (fderiv ℝ u z) I + Complex.normSq z * (iteratedFDeriv ℝ 2 u z) ![I, I]) := by
            rw [hdx, hdy]
            rw [iteratedDeriv_two_complexRePow_add_real, deriv_complexRePow_add_real,
              iteratedDeriv_two_normSq_add_real, deriv_normSq_add_real]
            rw [iteratedDeriv_two_complexRePow_add_I_mul, deriv_complexRePow_add_I_mul,
              iteratedDeriv_two_normSq_add_I_mul, deriv_normSq_add_I_mul]
            simp [u]
    _ = 4 * (z ^ m).re + 4 * ((fderiv ℝ u z) z) + Complex.normSq z *
          (((iteratedFDeriv ℝ 2 u z) ![1, 1]) + ((iteratedFDeriv ℝ 2 u z) ![I, I])) := by
            rw [hself]
            ring
    _ = 4 * (z ^ m).re + 4 * ((fderiv ℝ u z) z) := by
          rw [hu0]
          ring
    _ = 4 * (z ^ m).re + 4 * ((m : ℝ) * (z ^ m).re) := by rw [heuler]
    _ = 4 * (((m : ℝ) + 1) * (z ^ m).re) := by
          ring
    _ = 4 * ((m + 1 : ℕ) : ℝ) * (z ^ m).re := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
