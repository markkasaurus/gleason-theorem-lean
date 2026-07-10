import Gleason.Harmonic.Zonal.NorthZonalProfilePoly
import Gleason.Harmonic.Zonal.NorthZonalEven
import Gleason.Continuity.Auxiliary.ClosedQuadratic

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

lemma northSection_eq_combo_sphereE1_sphereE3 (z : Set.Icc (-1 : ℝ) 1) :
    (northSection z).1 =
      Real.sqrt (1 - z.1 ^ 2) • sphereE1.1 + z.1 • sphereE3.1 := by
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  simp [northSection, sphereE1, sphereE3]

lemma centeredNorthZonalProfile_eq_quadratic_combo_of_bilin
    {f : C(spherePoint3, ℝ)}
    {B : LinearMap.BilinMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ}
    (hB : ∀ x : spherePoint3, f x = B x.1 x.1)
    (z : Set.Icc (-1 : ℝ) 1) :
    centeredNorthZonalProfile f z =
      ((B sphereE3.1 sphereE3.1) - (B sphereE1.1 sphereE1.1)) * z.1 ^ 2 +
        (B sphereE1.1 sphereE3.1 + B sphereE3.1 sphereE1.1) *
          (Real.sqrt (1 - z.1 ^ 2) * z.1) := by
  have hzsec := hB (northSection z)
  rw [centeredNorthZonalProfile]
  rw [northZonalProfile_apply, northZonalProfile_apply]
  rw [hzsec]
  have hzero : f (northSection zeroIcc) = B sphereE1.1 sphereE1.1 := by
    simpa [northSection, zeroIcc, sphereE1] using hB (northSection zeroIcc)
  have hsqrt_sq : Real.sqrt (1 - z.1 ^ 2) ^ 2 = 1 - z.1 ^ 2 := by
    apply Real.sq_sqrt
    nlinarith [z.2.1, z.2.2]
  have hsqrt_mul :
      Real.sqrt (1 + -(z.1 * z.1)) * Real.sqrt (1 + -(z.1 * z.1)) = 1 + -(z.1 * z.1) := by
    simpa [pow_two, sub_eq_add_neg] using hsqrt_sq
  have hsqrt_mul_e1 :
      Real.sqrt (1 + -(z.1 * z.1)) *
          (Real.sqrt (1 + -(z.1 * z.1)) * (B sphereE1.1 sphereE1.1)) =
        (1 + -(z.1 * z.1)) * (B sphereE1.1 sphereE1.1) := by
    rw [← mul_assoc, hsqrt_mul]
  rw [hzero, northSection_eq_combo_sphereE1_sphereE3]
  simp [pow_two, mul_add, add_mul, sub_eq_add_neg]
  rw [hsqrt_mul_e1]
  ring

theorem exists_const_add_sq_of_isNorthZonal_mem_quadratic_pointConstraint
    {f : C(spherePoint3, ℝ)}
    (hfq : f ∈ continuousSphereQuadraticSubmodule)
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f) :
    ∃ a b : ℝ, ∀ x : spherePoint3, f x = a + b * sphereCoordZ x ^ 2 := by
  rcases hfq with ⟨Q, hQ⟩
  rcases LinearMap.BilinMap.toQuadraticMap_surjective
      (R := ℝ) (M := WithLp 2 (ℂ × ℝ)) (N := ℝ) Q with ⟨B, rfl⟩
  let c : ℝ := B sphereE3.1 sphereE3.1 - B sphereE1.1 sphereE1.1
  let zhalf : Set.Icc (-1 : ℝ) 1 := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  have hhalf :
      centeredNorthZonalProfile f zhalf =
        c * zhalf.1 ^ 2 +
          (B sphereE1.1 sphereE3.1 + B sphereE3.1 sphereE1.1) *
            (Real.sqrt (1 - zhalf.1 ^ 2) * zhalf.1) := by
    dsimp [c]
    apply centeredNorthZonalProfile_eq_quadratic_combo_of_bilin
    intro x
    simpa [LinearMap.BilinMap.toQuadraticMap_apply] using hQ x
  have hhalfNeg :
      centeredNorthZonalProfile f (negIcc zhalf) =
        c * (negIcc zhalf).1 ^ 2 +
          (B sphereE1.1 sphereE3.1 + B sphereE3.1 sphereE1.1) *
            (Real.sqrt (1 - (negIcc zhalf).1 ^ 2) * (negIcc zhalf).1) := by
    dsimp [c]
    apply centeredNorthZonalProfile_eq_quadratic_combo_of_bilin
    intro x
    simpa [LinearMap.BilinMap.toQuadraticMap_apply] using hQ x
  have hevenHalf :
      centeredNorthZonalProfile f (negIcc zhalf) = centeredNorthZonalProfile f zhalf :=
    centeredNorthZonalProfile_even_of_mem_pointConstraint hfmem hfz zhalf
  have hcrossZero :
      B sphereE1.1 sphereE3.1 + B sphereE3.1 sphereE1.1 = 0 := by
    rw [hhalf, hhalfNeg] at hevenHalf
    have hsqrt : Real.sqrt (1 - zhalf.1 ^ 2) = Real.sqrt (3 / 4 : ℝ) := by
      norm_num [zhalf]
    have hterm :
        Real.sqrt (1 - zhalf.1 ^ 2) * zhalf.1 = Real.sqrt (3 / 4 : ℝ) / 2 := by
      rw [hsqrt]
      ring
    have htermNeg :
        Real.sqrt (1 - (negIcc zhalf).1 ^ 2) * (negIcc zhalf).1 =
          -(Real.sqrt (3 / 4 : ℝ) / 2) := by
      have hsqrtNeg : Real.sqrt (1 - (negIcc zhalf).1 ^ 2) = Real.sqrt (3 / 4 : ℝ) := by
        rw [negIcc_val]
        norm_num [zhalf]
      rw [hsqrtNeg, negIcc_val]
      norm_num [zhalf]
      ring
    have hzsq : (negIcc zhalf).1 ^ 2 = zhalf.1 ^ 2 := by
      rw [negIcc_val]
      ring
    rw [hterm, htermNeg] at hevenHalf
    rw [hzsq] at hevenHalf
    have hspos : 0 < Real.sqrt (3 / 4 : ℝ) / 2 := by
      positivity
    nlinarith
  let p : ℝ[X] := C c * X ^ 2
  have hpoly :
      ∀ z : Set.Icc (-1 : ℝ) 1, centeredNorthZonalProfile f z = p.eval z.1 := by
    intro z
    rw [centeredNorthZonalProfile_eq_quadratic_combo_of_bilin
      (f := f) (B := B)
      (hB := by intro x; simpa [LinearMap.BilinMap.toQuadraticMap_apply] using hQ x) z]
    simp [p, c, hcrossZero]
  refine ⟨f sphereE2, p.coeff 2, ?_⟩
  exact isNorthZonal_eq_const_add_sq_of_polynomial hfmem hfz p hpoly
