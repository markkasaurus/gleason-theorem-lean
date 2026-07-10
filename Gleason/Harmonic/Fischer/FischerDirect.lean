import Gleason.Harmonic.Fischer.FischerExact
import Gleason.Harmonic.Fischer.FischerEndomorphism
import Gleason.Harmonic.Fischer.FischerAmbient
import Gleason.Harmonic.Fischer.FischerNorthRotation

noncomputable section

open Complex InnerProductSpace

private lemma norm_inv_smul_mem_spherePoint3 {x : WithLp 2 (ℂ × ℝ)} (hx : x ≠ 0) :
    ‖‖x‖⁻¹ • x‖ = 1 := by
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
  field_simp [hnx]

private lemma smul_norm_inv_smul {x : WithLp 2 (ℂ × ℝ)} (hx : x ≠ 0) :
    ‖x‖ • ((⟨‖x‖⁻¹ • x, norm_inv_smul_mem_spherePoint3 hx⟩ : spherePoint3).1) = x := by
  change ‖x‖ • (‖x‖⁻¹ • x) = x
  rw [smul_smul]
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hnx]
  simp

theorem eq_zero_of_sphereCoordMvEval_eq_zero_of_mem_homogeneousSubmodule
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (hres : sphereCoordMvEval p = 0) :
    p = 0 := by
  apply MvPolynomial.funext
  intro r
  let x : WithLp 2 (ℂ × ℝ) := ambientPointOfCoords r
  have hEval : MvPolynomial.eval r p = ambientCoordMvEval p x := by
    rw [ambientCoordMvEval_apply]
    congr
    ext i
    symm
    exact ambientCoordFun_ambientPointOfCoords r i
  by_cases hx : x = 0
  · have hy : sphereCoordMvEval p sphereE1 = 0 := by
      simpa using congrArg (fun f : C(spherePoint3, ℝ) => f sphereE1) hres
    have hzero0 : ambientCoordMvEval p 0 = 0 := by
      calc
        ambientCoordMvEval p 0 = ambientCoordMvEval p (0 • sphereE1.1) := by simp
        _ = 0 ^ n * ambientCoordMvEval p sphereE1.1 := by
              simpa using ambientCoordMvEval_smul_of_homogeneous hp 0 sphereE1.1
        _ = 0 := by
              by_cases h0 : n = 0
              · subst h0
                rw [pow_zero]
                have hy' :
                    MvPolynomial.eval (fun i => ambientCoordFun i sphereE1.1) p = 0 := by
                  have hcoords :
                      (fun i => ambientCoordFun i sphereE1.1) =
                        fun i => sphereCoordVec i sphereE1 := by
                    funext i
                    fin_cases i <;> rfl
                  rw [hcoords, ← sphereCoordMvEval_apply]
                  exact hy
                simpa using hy'
              · have hpos : 0 < n := Nat.pos_of_ne_zero h0
                rw [zero_pow (Nat.ne_of_gt hpos)]
                simp
    calc
      MvPolynomial.eval r p = ambientCoordMvEval p x := hEval
      _ = ambientCoordMvEval p 0 := by simpa [hx]
      _ = 0 := hzero0
  · let y : spherePoint3 := ⟨‖x‖⁻¹ • x, norm_inv_smul_mem_spherePoint3 hx⟩
    have hy0 : sphereCoordMvEval p y = 0 := by
      simpa using congrArg (fun f : C(spherePoint3, ℝ) => f y) hres
    have hxy :
        ambientCoordMvEval p x =
          ‖x‖ ^ n * sphereCoordMvEval p y := by
      calc
        ambientCoordMvEval p x
            = ambientCoordMvEval p (‖x‖ • y.1) := by rw [smul_norm_inv_smul hx]
        _ = ‖x‖ ^ n * ambientCoordMvEval p y.1 := by
              simpa using ambientCoordMvEval_smul_of_homogeneous hp ‖x‖ y.1
        _ = ‖x‖ ^ n * sphereCoordMvEval p y := by
              rw [← sphereRestrictionLinear_ambientCoordMvEval]
              rfl
    have hzero : ambientCoordMvEval p x = 0 := by
      rw [hxy, hy0]
      simp
    calc
      MvPolynomial.eval r p = ambientCoordMvEval p x := hEval
      _ = 0 := hzero

theorem eq_of_sphereCoordMvEval_eq_of_mem_homogeneousSubmodule
    {n : ℕ} {p q : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (hq : q ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (hres : sphereCoordMvEval p = sphereCoordMvEval q) :
    p = q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_sphereCoordMvEval_eq_zero_of_mem_homogeneousSubmodule
  · exact sub_mem hp hq
  · change sphereCoordMvEval.toLinearMap (p - q) = 0
    rw [LinearMap.map_sub]
    exact sub_eq_zero.mpr hres

theorem harmonicPolyHomogeneousImageSubmodule_disjoint_prev_homogeneousImage
    {n : ℕ} (hn : 2 ≤ n) :
    Disjoint
      (harmonicPolyHomogeneousImageSubmodule n)
      ((MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2)).map sphereCoordMvEval.toLinearMap) := by
  rw [Submodule.disjoint_def]
  intro f hfH hfPrev
  rcases hfH with ⟨p, hp, rfl⟩
  rcases hfPrev with ⟨q, hq, hqres⟩
  have hpq :
      sphereCoordMvEval p = sphereCoordMvEval (rhoPoly * q) := by
    rw [sphereCoordMvEval_rhoPoly_mul]
    exact hqres.symm
  have hpeq : p = rhoPoly * q := by
    apply eq_of_sphereCoordMvEval_eq_of_mem_homogeneousSubmodule hp.1
    · simpa [Nat.sub_add_cancel hn, add_comm, add_left_comm, add_assoc] using
        smul_rhoPoly_mem_homogeneousSubmodule_succ_two hq (1 : ℝ)
    · exact hpq
  have hΔzero : polyLaplacian (rhoPoly * q) = 0 := by
    rw [← hpeq]
    simpa [harmonicPolyHomogeneousSubmodule, LinearMap.mem_ker] using hp.2
  have hqzero :
      q = 0 := eq_zero_of_polyLaplacian_rhoPoly_mul_eq_zero_of_homogeneous hq hΔzero
  subst hqzero
  simpa using hqres.symm

theorem homogeneousImage_disjoint_harmonicPolyImage_sup_prev
    {n : ℕ} (hn : 2 ≤ n) :
    Disjoint
      (harmonicPolyHomogeneousImageSubmodule n)
      ((MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2)).map sphereCoordMvEval.toLinearMap) ∧
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n).map sphereCoordMvEval.toLinearMap =
      harmonicPolyHomogeneousImageSubmodule n ⊔
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ (n - 2)).map sphereCoordMvEval.toLinearMap := by
  exact ⟨harmonicPolyHomogeneousImageSubmodule_disjoint_prev_homogeneousImage hn,
    homogeneousImage_eq_harmonicPolyImage_sup_prev (n := n) hn⟩
