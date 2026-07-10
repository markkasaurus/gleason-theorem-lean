import Gleason.Harmonic.Sectors.HarmonicB
import Gleason.Harmonic.Auxiliary.TestFunctions

noncomputable section

open Complex InnerProductSpace
open scoped Topology

abbrev complexBasis : OrthonormalBasis (Fin 2) ℝ ℂ :=
  Complex.orthonormalBasisOneI

abbrev realBasis : OrthonormalBasis (Fin 1) ℝ ℝ :=
  OrthonormalBasis.singleton (Fin 1) ℝ

abbrev complexRealBasis : OrthonormalBasis (Fin 2 ⊕ Fin 1) ℝ (WithLp 2 (ℂ × ℝ)) :=
  complexBasis.prod realBasis

abbrev complexProjL : WithLp 2 (ℂ × ℝ) →L[ℝ] ℂ :=
  WithLp.fstL 2 ℝ ℂ ℝ

abbrev realProjL : WithLp 2 (ℂ × ℝ) →L[ℝ] ℝ :=
  WithLp.sndL 2 ℝ ℂ ℝ

abbrev complexOneVec : WithLp 2 (ℂ × ℝ) :=
  WithLp.toLp 2 ((1 : ℂ), (0 : ℝ))

abbrev complexIVec : WithLp 2 (ℂ × ℝ) :=
  WithLp.toLp 2 (I, (0 : ℝ))

abbrev realUnitVec : WithLp 2 (ℂ × ℝ) :=
  WithLp.toLp 2 ((0 : ℂ), (1 : ℝ))

lemma hasDerivAt_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x v : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => x + t • v) v s := by
  simpa [one_smul, add_comm, add_left_comm, add_assoc] using
    ((hasDerivAt_id s).smul_const v).const_add x

lemma iteratedDeriv_two_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x v : E) :
    iteratedDeriv 2 (fun t : ℝ => x + t • v) 0 = 0 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun t : ℝ => x + t • v) = fun _ : ℝ => v := by
    funext s
    exact (hasDerivAt_add_smul x v s).deriv
  rw [hderiv]
  simp

lemma contDiff_add_smul_path {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x v : E) :
    ContDiff ℝ 2 (fun t : ℝ => x + t • v) := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  simpa [one_smul, add_comm, add_left_comm, add_assoc] using
    (contDiff_const.add L.contDiff)

lemma iteratedDeriv_two_comp_add_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} {x v : E} (hh : ContDiffAt ℝ 2 h x) :
    iteratedDeriv 2 (fun t : ℝ => h (x + t • v)) 0 = (iteratedFDeriv ℝ 2 h x) ![v, v] := by
  have hpath : ContDiffAt ℝ 2 (fun t : ℝ => x + t • v) 0 := (contDiff_add_smul_path x v).contDiffAt
  have hcomp := iteratedDeriv_vcomp_two
    (g := h) (f := fun t : ℝ => x + t • v) (x := 0) (by simpa using hh) hpath
  have hderiv : deriv (fun t : ℝ => x + t • v) 0 = v := (hasDerivAt_add_smul x v 0).deriv
  have hsecond : iteratedDeriv 2 (fun t : ℝ => x + t • v) 0 = 0 := iteratedDeriv_two_add_smul x v
  have hconst : (fun _ : Fin 2 => v) = ![v, v] := by
    funext i
    fin_cases i <;> rfl
  simpa [hderiv, hsecond, hconst] using hcomp

/-- The explicit degree-`n` `A`-mode viewed on the `L²` model `ℂ × ℝ ≃ ℝ³`. -/
def surfaceModeAL2 (n : ℕ) : WithLp 2 (ℂ × ℝ) → ℝ :=
  fun p => (p.fst ^ n).re

lemma surfaceModeAL2_eq_comp (n : ℕ) :
    surfaceModeAL2 n = (fun z : ℂ => (z ^ n).re) ∘ complexProjL := by
  rfl

lemma surfaceModeAL2_contDiff (n : ℕ) : ContDiff ℝ 2 (surfaceModeAL2 n) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  simpa [surfaceModeAL2] using
    (Complex.reCLM.contDiff.contDiffAt.comp p <|
      (contDiffAt_id.pow n).comp p complexProjL.contDiff.contDiffAt)

theorem surfaceModeAL2_laplacian_eq_zero (n : ℕ) :
    Δ (surfaceModeAL2 n) = 0 := by
  ext p
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f := surfaceModeAL2 n) complexRealBasis]
  simp only
  have hcomp : iteratedFDeriv ℝ 2 (surfaceModeAL2 n) p =
      ContinuousMultilinearMap.compContinuousLinearMap
        (iteratedFDeriv ℝ 2 (fun z : ℂ => (z ^ n).re) (complexProjL p))
        (fun _ => complexProjL) := by
    simpa [surfaceModeAL2_eq_comp] using
      (complexProjL.iteratedFDeriv_comp_right
        (f := fun z : ℂ => (z ^ n).re)
        (complexRePow_contDiff n)
        p
        (show (2 : WithTop ℕ∞) ≤ 2 by norm_num))
  rw [hcomp]
  simp [complexRealBasis, complexBasis, realBasis, OrthonormalBasis.prod_apply, Fin.sum_univ_two]
  let M := iteratedFDeriv ℝ 2 (fun z : ℂ => (z ^ n).re) (complexProjL p)
  change ((M (fun i =>
      (![WithLp.toLp 2 ((1 : ℂ), (0 : ℝ)), WithLp.toLp 2 ((1 : ℂ), (0 : ℝ))] i).fst) +
      M (fun i =>
      (![WithLp.toLp 2 (I, (0 : ℝ)), WithLp.toLp 2 (I, (0 : ℝ))] i).fst)) +
      M (fun i =>
      (![WithLp.toLp 2 ((0 : ℂ), (1 : ℝ)), WithLp.toLp 2 ((0 : ℂ), (1 : ℝ))] i).fst)) = 0
  have hvec1 :
      (fun i =>
        (![WithLp.toLp 2 ((1 : ℂ), (0 : ℝ)), WithLp.toLp 2 ((1 : ℂ), (0 : ℝ))] i).fst) =
        ![1, 1] := by
    ext i
    fin_cases i <;> simp
  have hvecI :
      (fun i =>
        (![WithLp.toLp 2 (I, (0 : ℝ)), WithLp.toLp 2 (I, (0 : ℝ))] i).fst) =
        ![I, I] := by
    ext i
    fin_cases i <;> simp
  have hvec0 :
      (fun i =>
        (![WithLp.toLp 2 ((0 : ℂ), (1 : ℝ)), WithLp.toLp 2 ((0 : ℂ), (1 : ℝ))] i).fst) =
        ![0, 0] := by
    ext i
    fin_cases i <;> simp
  rw [hvec1, hvecI, hvec0]
  have hΔ : M ![1, 1] + M ![I, I] = 0 := by
    have hΔ' : Δ (fun z : ℂ => (z ^ n).re) (complexProjL p) = 0 :=
      ((analyticAt_id.pow n).harmonicAt_re (x := complexProjL p)).2.eq_of_nhds
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] at hΔ'
    simpa [M] using hΔ'
  have h0 : M ![0, 0] = 0 := by
    exact M.map_coord_zero 0 rfl
  rw [h0]
  simpa [add_assoc] using hΔ

theorem surfaceModeAL2_harmonicAt (n : ℕ) (p : WithLp 2 (ℂ × ℝ)) :
    HarmonicAt (surfaceModeAL2 n) p := by
  refine ⟨(surfaceModeAL2_contDiff n).contDiffAt, ?_⟩
  simp [surfaceModeAL2_laplacian_eq_zero n]

lemma surfaceModeAL2_toLp_eq_surfaceModeA (n : ℕ) (x y z : ℝ) :
    surfaceModeAL2 n (WithLp.toLp 2 (((x : ℂ) + Complex.I * y), z)) = surfaceModeA n x y z := by
  simp [surfaceModeAL2, surfaceModeA]

/-- The horizontal degree-`m+2` witness `(x²+y²) Re((x+iy)^m)` on the `ℂ × ℝ` model. -/
def complexNormSqMulRePowLift (m : ℕ) : WithLp 2 (ℂ × ℝ) → ℝ :=
  fun p => Complex.normSq (complexProjL p) * ((complexProjL p) ^ m).re

lemma complexNormSqMulRePowLift_eq_comp (m : ℕ) :
    complexNormSqMulRePowLift m =
      (fun z : ℂ => Complex.normSq z * (z ^ m).re) ∘ complexProjL := by
  rfl

lemma complexNormSqMulRePowLift_contDiff (m : ℕ) :
    ContDiff ℝ 2 (complexNormSqMulRePowLift m) := by
  have hnorm : ContDiff ℝ 2 (fun p : WithLp 2 (ℂ × ℝ) => Complex.normSq (complexProjL p)) := by
    simpa using complex_normSq_contDiff.comp complexProjL.contDiff
  have hre : ContDiff ℝ 2 (fun p : WithLp 2 (ℂ × ℝ) => ((complexProjL p) ^ m).re) := by
    simpa using (Complex.reCLM.contDiff.comp ((complexProjL.contDiff).pow m))
  simpa [complexNormSqMulRePowLift] using hnorm.mul hre

theorem complexNormSqMulRePowLift_laplacian (m : ℕ) (p : WithLp 2 (ℂ × ℝ)) :
    Δ (complexNormSqMulRePowLift m) p =
      4 * ((m + 1 : ℕ) : ℝ) * ((complexProjL p) ^ m).re := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f := complexNormSqMulRePowLift m) complexRealBasis]
  simp only
  have hcomp : iteratedFDeriv ℝ 2 (complexNormSqMulRePowLift m) p =
      ContinuousMultilinearMap.compContinuousLinearMap
        (iteratedFDeriv ℝ 2 (fun z : ℂ => Complex.normSq z * (z ^ m).re) (complexProjL p))
        (fun _ => complexProjL) := by
    simpa [complexNormSqMulRePowLift_eq_comp] using
      (complexProjL.iteratedFDeriv_comp_right
        (f := fun z : ℂ => Complex.normSq z * (z ^ m).re)
        (complex_normSq_contDiff.mul (complexRePow_contDiff m))
        p
        (show (2 : WithTop ℕ∞) ≤ 2 by norm_num))
  rw [hcomp]
  simp [complexRealBasis, complexBasis, realBasis, OrthonormalBasis.prod_apply,
    Fin.sum_univ_two]
  let M := iteratedFDeriv ℝ 2 (fun z : ℂ => Complex.normSq z * (z ^ m).re) (complexProjL p)
  change ((M (fun i =>
      (![WithLp.toLp 2 ((1 : ℂ), (0 : ℝ)), WithLp.toLp 2 ((1 : ℂ), (0 : ℝ))] i).fst) +
      M (fun i =>
      (![WithLp.toLp 2 (I, (0 : ℝ)), WithLp.toLp 2 (I, (0 : ℝ))] i).fst)) +
      M (fun i =>
      (![WithLp.toLp 2 ((0 : ℂ), (1 : ℝ)), WithLp.toLp 2 ((0 : ℂ), (1 : ℝ))] i).fst)) =
      4 * ((m : ℝ) + 1) * (p.fst ^ m).re
  have hvec1 :
      (fun i =>
        (![WithLp.toLp 2 ((1 : ℂ), (0 : ℝ)), WithLp.toLp 2 ((1 : ℂ), (0 : ℝ))] i).fst) =
        ![1, 1] := by
    ext i
    fin_cases i <;> simp
  have hvecI :
      (fun i =>
        (![WithLp.toLp 2 (I, (0 : ℝ)), WithLp.toLp 2 (I, (0 : ℝ))] i).fst) =
        ![I, I] := by
    ext i
    fin_cases i <;> simp
  have hvec0 :
      (fun i =>
        (![WithLp.toLp 2 ((0 : ℂ), (1 : ℝ)), WithLp.toLp 2 ((0 : ℂ), (1 : ℝ))] i).fst) =
        ![0, 0] := by
    ext i
    fin_cases i <;> simp
  rw [hvec1, hvecI, hvec0]
  have hΔ : M ![1, 1] + M ![I, I] =
      4 * ((m : ℝ) + 1) * (p.fst ^ m).re := by
    have hΔ' : Δ (fun z : ℂ => Complex.normSq z * (z ^ m).re) (complexProjL p) =
        4 * ((m : ℝ) + 1) * (p.fst ^ m).re := by
      simpa [Nat.cast_add, Nat.cast_one, complexProjL] using
        complex_normSq_mul_rePow_laplacian m (complexProjL p)
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] at hΔ'
    simpa [M] using hΔ'
  have h0 : M ![0, 0] = 0 := by
    exact M.map_coord_zero 0 rfl
  rw [h0]
  simpa [add_assoc] using hΔ

/-- The vertical correction mode `z² Re((x+iy)^m)` on the `ℂ × ℝ` model. -/
def realSqMulRePowLift (m : ℕ) : WithLp 2 (ℂ × ℝ) → ℝ :=
  fun p => (realProjL p) ^ 2 * ((complexProjL p) ^ m).re

lemma realSqMulRePowLift_contDiff (m : ℕ) :
    ContDiff ℝ 2 (realSqMulRePowLift m) := by
  have hsq : ContDiff ℝ 2 (fun p : WithLp 2 (ℂ × ℝ) => (realProjL p) ^ 2) := by
    simpa using (realProjL.contDiff.pow 2)
  have hre : ContDiff ℝ 2 (fun p : WithLp 2 (ℂ × ℝ) => ((complexProjL p) ^ m).re) := by
    simpa using (Complex.reCLM.contDiff.comp ((complexProjL.contDiff).pow m))
  simpa [realSqMulRePowLift] using hsq.mul hre

lemma iteratedDeriv_two_realShift_sq (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => (t + s) ^ 2) 0 = 2 := by
  have hfun : (fun s : ℝ => Complex.normSq ((t : ℂ) + s)) = fun s : ℝ => (t + s) ^ 2 := by
    funext s
    simp [Complex.normSq, pow_two]
  rw [← hfun]
  simpa using iteratedDeriv_two_normSq_add_real (t : ℂ)

theorem realSqMulRePowLift_laplacian (m : ℕ) (p : WithLp 2 (ℂ × ℝ)) :
    Δ (realSqMulRePowLift m) p = 2 * ((complexProjL p) ^ m).re := by
  let g : WithLp 2 (ℂ × ℝ) → ℝ := realSqMulRePowLift m
  let u : ℂ → ℝ := fun z => (z ^ m).re
  let M := iteratedFDeriv ℝ 2 g p
  have hg : ContDiffAt ℝ 2 g p := (realSqMulRePowLift_contDiff m).contDiffAt
  have hvec1 :
      (fun i => (![complexOneVec, complexOneVec] i)) =
        ![complexOneVec, complexOneVec] := by
    rfl
  have hvecI :
      (fun i => (![complexIVec, complexIVec] i)) =
        ![complexIVec, complexIVec] := by
    rfl
  have hvecR :
      (fun i => (![realUnitVec, realUnitVec] i)) =
        ![realUnitVec, realUnitVec] := by
    rfl
  have hx :
      M ![complexOneVec, complexOneVec] =
        iteratedDeriv 2 (fun s : ℝ => g (p + s • complexOneVec)) 0 := by
    symm
    simpa [M, g] using (iteratedDeriv_two_comp_add_smul (x := p) (v := complexOneVec) hg)
  have hy :
      M ![complexIVec, complexIVec] =
        iteratedDeriv 2 (fun s : ℝ => g (p + s • complexIVec)) 0 := by
    symm
    simpa [M, g] using (iteratedDeriv_two_comp_add_smul (x := p) (v := complexIVec) hg)
  have hz :
      M ![realUnitVec, realUnitVec] =
        iteratedDeriv 2 (fun s : ℝ => g (p + s • realUnitVec)) 0 := by
    symm
    simpa [M, g] using (iteratedDeriv_two_comp_add_smul (x := p) (v := realUnitVec) hg)
  have hpathx :
      (fun s : ℝ => g (p + s • complexOneVec)) =
        fun s : ℝ => (p.snd ^ 2) * ((p.fst + (s : ℂ)) ^ m).re := by
    funext s
    simp [g, realSqMulRePowLift, complexOneVec, complexProjL, realProjL, pow_two, add_comm,
      mul_comm]
  have hpathy :
      (fun s : ℝ => g (p + s • complexIVec)) =
        fun s : ℝ => (p.snd ^ 2) * ((p.fst + (s : ℂ) * I) ^ m).re := by
    funext s
    simp [g, realSqMulRePowLift, complexIVec, complexProjL, realProjL, pow_two, add_comm,
      mul_comm]
  have hpathz :
      (fun s : ℝ => g (p + s • realUnitVec)) =
        fun s : ℝ => ((p.fst ^ m).re) * (p.snd + s) ^ 2 := by
    funext s
    simp [g, realSqMulRePowLift, realUnitVec, complexProjL, realProjL, pow_two, add_comm,
      mul_comm]
  have hu0 :
      (iteratedFDeriv ℝ 2 u (complexProjL p)) ![1, 1] +
        (iteratedFDeriv ℝ 2 u (complexProjL p)) ![I, I] = 0 := by
    have hΔu : Δ u (complexProjL p) = 0 := by
      simpa [u] using (((analyticAt_id.pow m).harmonicAt_re (x := complexProjL p)).2.eq_of_nhds)
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane] at hΔu
    simpa [u] using hΔu
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := g) complexRealBasis]
  simp [complexRealBasis, complexBasis, realBasis, OrthonormalBasis.prod_apply, Fin.sum_univ_two,
    hvec1, hvecI, hvecR]
  calc
    M ![complexOneVec, complexOneVec] + M ![complexIVec, complexIVec] +
        M ![realUnitVec, realUnitVec]
      = iteratedDeriv 2 (fun s : ℝ => g (p + s • complexOneVec)) 0 +
          iteratedDeriv 2 (fun s : ℝ => g (p + s • complexIVec)) 0 +
          iteratedDeriv 2 (fun s : ℝ => g (p + s • realUnitVec)) 0 := by
            rw [hx, hy, hz]
    _ =
        iteratedDeriv 2 (fun s : ℝ => g (p + s • complexOneVec)) 0 +
        iteratedDeriv 2 (fun s : ℝ => g (p + s • complexIVec)) 0 +
        iteratedDeriv 2 (fun s : ℝ => g (p + s • realUnitVec)) 0
          := by rfl
    _ = p.snd ^ 2 * (iteratedFDeriv ℝ 2 u (complexProjL p)) ![1, 1] +
          p.snd ^ 2 * (iteratedFDeriv ℝ 2 u (complexProjL p)) ![I, I] +
          2 * ((complexProjL p) ^ m).re := by
            rw [hpathx, hpathy, hpathz]
            have hx' :
                iteratedDeriv 2 (fun s : ℝ => p.snd ^ 2 * ((p.fst + (s : ℂ)) ^ m).re) 0 =
                  p.snd ^ 2 * (iteratedFDeriv ℝ 2 u (complexProjL p)) ![1, 1] := by
              calc
                iteratedDeriv 2 (fun s : ℝ => p.snd ^ 2 * ((p.fst + (s : ℂ)) ^ m).re) 0
                  = p.snd ^ 2 * iteratedDeriv 2 (fun s : ℝ => ((p.fst + (s : ℂ)) ^ m).re) 0 := by
                      simpa using
                        iteratedDeriv_const_mul (contDiffAt_repow_add_real m p.fst) (p.snd ^ 2)
                _ = p.snd ^ 2 * (iteratedFDeriv ℝ 2 u (complexProjL p)) ![1, 1] := by
                      rw [iteratedDeriv_two_complexRePow_add_real]
                      rfl
            have hy' :
                iteratedDeriv 2 (fun s : ℝ => p.snd ^ 2 * ((p.fst + (s : ℂ) * I) ^ m).re) 0 =
                  p.snd ^ 2 * (iteratedFDeriv ℝ 2 u (complexProjL p)) ![I, I] := by
              calc
                iteratedDeriv 2 (fun s : ℝ => p.snd ^ 2 * ((p.fst + (s : ℂ) * I) ^ m).re) 0
                  = p.snd ^ 2 * iteratedDeriv 2 (fun s : ℝ => ((p.fst + (s : ℂ) * I) ^ m).re) 0 := by
                      simpa using
                        iteratedDeriv_const_mul (contDiffAt_repow_add_I_mul m p.fst) (p.snd ^ 2)
                _ = p.snd ^ 2 * (iteratedFDeriv ℝ 2 u (complexProjL p)) ![I, I] := by
                      rw [iteratedDeriv_two_complexRePow_add_I_mul]
                      rfl
            have hz' :
                iteratedDeriv 2 (fun s : ℝ => (p.fst ^ m).re * (p.snd + s) ^ 2) 0 =
                  2 * ((complexProjL p) ^ m).re := by
              calc
                iteratedDeriv 2 (fun s : ℝ => (p.fst ^ m).re * (p.snd + s) ^ 2) 0
                  = (p.fst ^ m).re * iteratedDeriv 2 (fun s : ℝ => (p.snd + s) ^ 2) 0 := by
                      simpa using
                        iteratedDeriv_const_mul ((((contDiff_const.add contDiff_id).pow 2).contDiffAt))
                          ((p.fst ^ m).re)
                _ = (p.fst ^ m).re * 2 := by rw [iteratedDeriv_two_realShift_sq]
                _ = 2 * ((complexProjL p) ^ m).re := by
                      simp [complexProjL, mul_comm]
            rw [hx', hy', hz']
    _ = p.snd ^ 2 *
          ((iteratedFDeriv ℝ 2 u (complexProjL p)) ![1, 1] +
            (iteratedFDeriv ℝ 2 u (complexProjL p)) ![I, I]) +
          2 * ((complexProjL p) ^ m).re := by
            ring
    _ = 2 * ((complexProjL p) ^ m).re := by
          rw [hu0]
          ring

/-- The explicit degree-`n` `B`-mode on the `ℂ × ℝ` model. -/
def surfaceModeBL2 (n : ℕ) : WithLp 2 (ℂ × ℝ) → ℝ :=
  fun p =>
    (Complex.normSq (complexProjL p) - 2 * (n - 1) * (realProjL p) ^ 2) *
      ((complexProjL p) ^ (n - 2)).re

lemma surfaceModeBL2_eq_split {n : ℕ} (hn : 2 ≤ n) :
    surfaceModeBL2 n =
      complexNormSqMulRePowLift (n - 2) +
        (-2 * (n - 1 : ℕ) : ℝ) • realSqMulRePowLift (n - 2) := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  funext p
  simp [surfaceModeBL2, complexNormSqMulRePowLift, realSqMulRePowLift, smul_eq_mul]
  ring

lemma surfaceModeBL2_contDiff (n : ℕ) :
    ContDiff ℝ 2 (surfaceModeBL2 n) := by
  have hcoeff : ContDiff ℝ 2
      (fun p : WithLp 2 (ℂ × ℝ) =>
        Complex.normSq (complexProjL p) - 2 * ((n : ℝ) - 1) * (realProjL p) ^ 2) := by
    have hnorm : ContDiff ℝ 2 (fun p : WithLp 2 (ℂ × ℝ) => Complex.normSq (complexProjL p)) := by
      simpa using complex_normSq_contDiff.comp complexProjL.contDiff
    have hzsq : ContDiff ℝ 2 (fun p : WithLp 2 (ℂ × ℝ) => (realProjL p) ^ 2) := by
      simpa using (realProjL.contDiff.pow 2)
    exact hnorm.sub ((hzsq.const_smul (2 * ((n : ℝ) - 1))))
  have hre : ContDiff ℝ 2 (fun p : WithLp 2 (ℂ × ℝ) => ((complexProjL p) ^ (n - 2)).re) := by
    simpa using (Complex.reCLM.contDiff.comp ((complexProjL.contDiff).pow (n - 2)))
  simpa [surfaceModeBL2] using hcoeff.mul hre

theorem surfaceModeBL2_laplacian_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    Δ (surfaceModeBL2 n) = 0 := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  ext p
  have hsplit :
      surfaceModeBL2 (k + 2) =
        complexNormSqMulRePowLift k + (-2 * ((k + 1 : ℕ) : ℝ)) • realSqMulRePowLift k := by
    simpa [Nat.add_comm] using surfaceModeBL2_eq_split
      (show 2 ≤ 2 + k by exact Nat.le_add_right 2 k)
  have hsplit' :
      surfaceModeBL2 (2 + k) =
        complexNormSqMulRePowLift k + (-2 * ((k + 1 : ℕ) : ℝ)) • realSqMulRePowLift k := by
    simpa [Nat.add_comm] using hsplit
  have hA : ContDiffAt ℝ 2 (complexNormSqMulRePowLift k) p :=
    (complexNormSqMulRePowLift_contDiff k).contDiffAt
  have hB : ContDiffAt ℝ 2 (realSqMulRePowLift k) p :=
    (realSqMulRePowLift_contDiff k).contDiffAt
  rw [hsplit']
  calc
    Δ (complexNormSqMulRePowLift k + (-2 * ((k + 1 : ℕ) : ℝ)) • realSqMulRePowLift k) p
      = Δ (complexNormSqMulRePowLift k) p +
          Δ ((-2 * ((k + 1 : ℕ) : ℝ)) • realSqMulRePowLift k) p := by
            exact hA.laplacian_add (hB.const_smul (-2 * ((k + 1 : ℕ) : ℝ)))
    _ = Δ (complexNormSqMulRePowLift k) p +
          (-2 * ((k + 1 : ℕ) : ℝ)) * Δ (realSqMulRePowLift k) p := by
          rw [laplacian_smul (-2 * ((k + 1 : ℕ) : ℝ)) hB]
          simp [smul_eq_mul]
    _ = 4 * ((k + 1 : ℕ) : ℝ) * ((complexProjL p) ^ k).re +
          (-2 * ((k + 1 : ℕ) : ℝ)) * (2 * ((complexProjL p) ^ k).re) := by
            rw [complexNormSqMulRePowLift_laplacian, realSqMulRePowLift_laplacian]
    _ = 0 := by
          simp
          ring

theorem surfaceModeBL2_harmonicAt {n : ℕ} (hn : 2 ≤ n) (p : WithLp 2 (ℂ × ℝ)) :
    HarmonicAt (surfaceModeBL2 n) p := by
  refine ⟨(surfaceModeBL2_contDiff n).contDiffAt, ?_⟩
  simp [surfaceModeBL2_laplacian_eq_zero hn]

lemma surfaceModeBL2_toLp_eq_surfaceModeB (n : ℕ) (x y z : ℝ) :
    surfaceModeBL2 n (WithLp.toLp 2 (((x : ℂ) + Complex.I * y), z)) = surfaceModeB n x y z := by
  simp [surfaceModeBL2, surfaceModeB, Complex.normSq, pow_two, mul_assoc, mul_comm]

lemma surfaceModeAL2_equator (n : ℕ) (θ : ℝ) :
    surfaceModeAL2 n (WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), 0)) =
      Real.cos ((n : ℝ) * θ) := by
  calc
    surfaceModeAL2 n (WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), 0))
      = surfaceModeA n (Real.cos θ) (Real.sin θ) 0 := by
          simpa using surfaceModeAL2_toLp_eq_surfaceModeA n (Real.cos θ) (Real.sin θ) 0
    _ = Real.cos ((n : ℝ) * θ) := surfaceModeA_equator n θ

lemma surfaceModeBL2_equator {n : ℕ} (hn : 2 ≤ n) (θ : ℝ) :
    surfaceModeBL2 n (WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), 0)) =
      Real.cos (((n - 2 : ℕ) : ℝ) * θ) := by
  calc
    surfaceModeBL2 n (WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), 0))
      = surfaceModeB n (Real.cos θ) (Real.sin θ) 0 := by
          simpa using surfaceModeBL2_toLp_eq_surfaceModeB n (Real.cos θ) (Real.sin θ) 0
    _ = Real.cos (((n - 2 : ℕ) : ℝ) * θ) := surfaceModeB_equator hn θ
