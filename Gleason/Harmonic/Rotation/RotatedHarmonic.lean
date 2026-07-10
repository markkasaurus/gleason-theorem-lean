import Gleason.Harmonic.Sectors.HarmonicBWitness
import Gleason.Harmonic.Rotation.RotatedSector

noncomputable section

open Complex InnerProductSpace Real
open scoped Topology

def rotatedComplexProjL (c s : ℝ) : WithLp 2 (ℂ × ℝ) →L[ℝ] ℂ :=
  (Complex.ofRealCLM.comp (((c : ℝ) • (Complex.reCLM.comp complexProjL)) + (s • realProjL))) +
    (Complex.I • (Complex.ofRealCLM.comp (Complex.imCLM.comp complexProjL)))

lemma rotatedComplexProjL_apply (c s : ℝ) (p : WithLp 2 (ℂ × ℝ)) :
    rotatedComplexProjL c s p =
      (((c * (complexProjL p).re + s * realProjL p : ℝ) : ℂ) +
        Complex.I * (complexProjL p).im) := by
  simp [rotatedComplexProjL]

def rotatedSurfaceModeAL2 (n : ℕ) (c s : ℝ) : WithLp 2 (ℂ × ℝ) → ℝ :=
  fun p => ((rotatedComplexProjL c s p) ^ n).re

lemma rotatedSurfaceModeAL2_eq_comp (n : ℕ) (c s : ℝ) :
    rotatedSurfaceModeAL2 n c s = (fun z : ℂ => (z ^ n).re) ∘ rotatedComplexProjL c s := by
  rfl

lemma rotatedSurfaceModeAL2_contDiff (n : ℕ) (c s : ℝ) :
    ContDiff ℝ 2 (rotatedSurfaceModeAL2 n c s) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  simpa [rotatedSurfaceModeAL2] using
    (Complex.reCLM.contDiff.contDiffAt.comp p <|
      (contDiffAt_id.pow n).comp p (rotatedComplexProjL c s).contDiff.contDiffAt)

lemma iteratedFDeriv_pair_real_apply
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => ℂ) ℝ) (a : ℝ) :
    M ![(a : ℂ), (a : ℂ)] = a ^ 2 * M ![1, 1] := by
  have hone : (fun _ : Fin 2 => (1 : ℂ)) = ![1, 1] := by
    funext i
    fin_cases i <;> rfl
  have hconst :
      ![(a : ℂ), (a : ℂ)] = fun _ : Fin 2 => (a : ℝ) • (1 : ℂ) := by
    ext i
    fin_cases i <;> simp
  calc
    M ![(a : ℂ), (a : ℂ)] = M (fun _ : Fin 2 => (a : ℝ) • (1 : ℂ)) := by
      rw [hconst]
    _ = (∏ i : Fin 2, (a : ℝ)) • M (fun _ : Fin 2 => (1 : ℂ)) := by
      rw [ContinuousMultilinearMap.map_smul_univ]
    _ = a ^ 2 * M ![1, 1] := by
      rw [hone]
      simp [pow_two, smul_eq_mul]

theorem rotatedSurfaceModeAL2_laplacian_eq_zero (n : ℕ) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) :
    Δ (rotatedSurfaceModeAL2 n c s) = 0 := by
  ext p
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (f := rotatedSurfaceModeAL2 n c s) complexRealBasis]
  simp only
  have hcomp : iteratedFDeriv ℝ 2 (rotatedSurfaceModeAL2 n c s) p =
      ContinuousMultilinearMap.compContinuousLinearMap
        (iteratedFDeriv ℝ 2 (fun z : ℂ => (z ^ n).re) (rotatedComplexProjL c s p))
        (fun _ => rotatedComplexProjL c s) := by
    simpa [rotatedSurfaceModeAL2_eq_comp] using
      ((rotatedComplexProjL c s).iteratedFDeriv_comp_right
        (f := fun z : ℂ => (z ^ n).re)
        (complexRePow_contDiff n)
        p
        (show (2 : WithTop ℕ∞) ≤ 2 by norm_num))
  rw [hcomp]
  simp [complexRealBasis, complexBasis, realBasis, OrthonormalBasis.prod_apply, Fin.sum_univ_two]
  let M := iteratedFDeriv ℝ 2 (fun z : ℂ => (z ^ n).re) (rotatedComplexProjL c s p)
  change ((M (fun i =>
      rotatedComplexProjL c s (![WithLp.toLp 2 ((1 : ℂ), (0 : ℝ)),
        WithLp.toLp 2 ((1 : ℂ), (0 : ℝ))] i)) +
      M (fun i =>
      rotatedComplexProjL c s (![WithLp.toLp 2 (I, (0 : ℝ)),
        WithLp.toLp 2 (I, (0 : ℝ))] i))) +
      M (fun i =>
      rotatedComplexProjL c s (![WithLp.toLp 2 ((0 : ℂ), (1 : ℝ)),
        WithLp.toLp 2 ((0 : ℂ), (1 : ℝ))] i))) = 0
  have hvecc :
      (fun i =>
        rotatedComplexProjL c s (![WithLp.toLp 2 ((1 : ℂ), (0 : ℝ)),
          WithLp.toLp 2 ((1 : ℂ), (0 : ℝ))] i)) =
        ![(c : ℂ), (c : ℂ)] := by
    ext i
    fin_cases i <;> simp [rotatedComplexProjL_apply, complexProjL, realProjL]
  have hvecI :
      (fun i =>
        rotatedComplexProjL c s (![WithLp.toLp 2 (I, (0 : ℝ)),
          WithLp.toLp 2 (I, (0 : ℝ))] i)) =
        ![I, I] := by
    ext i
    fin_cases i <;> simp [rotatedComplexProjL_apply, complexProjL, realProjL]
  have hvecs :
      (fun i =>
        rotatedComplexProjL c s (![WithLp.toLp 2 ((0 : ℂ), (1 : ℝ)),
          WithLp.toLp 2 ((0 : ℂ), (1 : ℝ))] i)) =
        ![(s : ℂ), (s : ℂ)] := by
    ext i
    fin_cases i <;> simp [rotatedComplexProjL_apply, complexProjL, realProjL]
  rw [hvecc, hvecI, hvecs]
  have hΔ : M ![1, 1] + M ![I, I] = 0 := by
    simpa [M] using complexRePow_second_sum_zero n (rotatedComplexProjL c s p)
  rw [iteratedFDeriv_pair_real_apply M c, iteratedFDeriv_pair_real_apply M s]
  calc
    c ^ 2 * M ![1, 1] + M ![I, I] + s ^ 2 * M ![1, 1]
      = (c ^ 2 + s ^ 2) * M ![1, 1] + M ![I, I] := by ring
    _ = M ![1, 1] + M ![I, I] := by rw [hcs, one_mul]
    _ = 0 := hΔ

theorem rotatedSurfaceModeAL2_harmonicAt (n : ℕ) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (p : WithLp 2 (ℂ × ℝ)) :
    HarmonicAt (rotatedSurfaceModeAL2 n c s) p := by
  refine ⟨(rotatedSurfaceModeAL2_contDiff n c s).contDiffAt, ?_⟩
  simp [rotatedSurfaceModeAL2_laplacian_eq_zero n hcs]

lemma rotatedSurfaceModeAL2_equator (n : ℕ) (c s θ : ℝ) :
    rotatedSurfaceModeAL2 n c s
      (WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), 0)) =
        rotatedSurfaceModeAEquator n c θ := by
  simp [rotatedSurfaceModeAL2, rotatedSurfaceModeAEquator, rotatedComplexProjL_apply,
    complexProjL, realProjL, Complex.add_re, Complex.mul_re, Complex.mul_im]

theorem rotated_harmonic_surface_mode_not_circleFrame_of_mod_four_eq_two {n : ℕ}
    (hn : 2 < n) (hmod : n % 4 = 2) {c s : ℝ} (_hcs : c ^ 2 + s ^ 2 = 1)
    (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ circleFrameFunction
      (fun θ =>
        rotatedSurfaceModeAL2 n c s
          (WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), 0))) := by
  intro hframe
  have hrot : circleFrameFunction (fun θ : ℝ => rotatedSurfaceModeAEquator n c θ) := by
    convert hframe using 1
    funext θ
    symm
    exact rotatedSurfaceModeAL2_equator n c s θ
  exact not_circleFrame_rotatedSurfaceModeAEquator_of_mod_four_eq_two hn hmod hc0 hc1 hrot
