import Gleason.Harmonic.Zonal.NorthZonalSquaredProfile
import Gleason.Harmonic.Zonal.NorthZonalProfileQuadratic

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

lemma sq_mem_Icc (z : Set.Icc (-1 : ℝ) 1) :
    z.1 ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact sq_nonneg z.1
  · nlinarith [z.2.1, z.2.2]

def absIcc (z : Set.Icc (-1 : ℝ) 1) : Set.Icc (-1 : ℝ) 1 :=
  ⟨|z.1|, by
    constructor
    · nlinarith [abs_nonneg z.1]
    · rw [abs_le]
      constructor <;> nlinarith [z.2.1, z.2.2]⟩

lemma sqCenteredNorthZonalProfile_eq_absProfile
    (f : C(spherePoint3, ℝ)) (z : Set.Icc (-1 : ℝ) 1) :
    sqCenteredNorthZonalProfile f ⟨z.1 ^ 2, sq_mem_Icc z⟩ =
      centeredNorthZonalProfile f (absIcc z) := by
  rw [sqCenteredNorthZonalProfile_apply]
  have hz :
      (⟨Real.sqrt (z.1 ^ 2), by
        constructor
        · have : 0 ≤ Real.sqrt (z.1 ^ 2) := Real.sqrt_nonneg (z.1 ^ 2)
          nlinarith
        · have hsq : (Real.sqrt (z.1 ^ 2)) ^ 2 = z.1 ^ 2 := by
            exact Real.sq_sqrt (sq_nonneg z.1)
          have hle : Real.sqrt (z.1 ^ 2) ≤ 1 := by
            nlinarith [sq_mem_Icc z |>.2, Real.sqrt_nonneg (z.1 ^ 2), hsq]
          simpa using hle⟩ : Set.Icc (-1 : ℝ) 1) =
      absIcc z := by
    apply Subtype.ext
    simp [absIcc, Real.sqrt_sq_eq_abs]
  rw [hz]

theorem centeredNorthZonalProfile_eq_sqCenteredNorthZonalProfile_sq
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (z : Set.Icc (-1 : ℝ) 1) :
    centeredNorthZonalProfile f z =
      sqCenteredNorthZonalProfile f ⟨z.1 ^ 2, sq_mem_Icc z⟩ := by
  rw [sqCenteredNorthZonalProfile_eq_absProfile]
  by_cases hz : 0 ≤ z.1
  · have habs : absIcc z = z := by
      apply Subtype.ext
      simp [absIcc, abs_of_nonneg hz]
    rw [habs]
  · have habs : absIcc z = negIcc z := by
      apply Subtype.ext
      simp [absIcc, negIcc, abs_of_neg (lt_of_not_ge hz)]
    rw [habs]
    symm
    exact centeredNorthZonalProfile_even_of_mem_pointConstraint hfmem hfz z

theorem exists_quadraticMap_of_isNorthZonal_pointConstraint_sqPolynomial
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (q : ℝ[X])
    (hsqpoly : ∀ u : Set.Icc (0 : ℝ) 1,
      sqCenteredNorthZonalProfile f u = q.eval u.1) :
    ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ,
      ∀ x : spherePoint3, f x = Q x.1 := by
  let p : ℝ[X] := q.comp (X ^ 2)
  have hpoly : ∀ z : Set.Icc (-1 : ℝ) 1,
      centeredNorthZonalProfile f z = p.eval z.1 := by
    intro z
    rw [centeredNorthZonalProfile_eq_sqCenteredNorthZonalProfile_sq hfmem hfz z,
      hsqpoly ⟨z.1 ^ 2, sq_mem_Icc z⟩]
    simp [p, pow_two]
  exact exists_quadraticMap_of_isNorthZonal_pointConstraint_polynomial hfmem hfz p hpoly

theorem mem_continuousSphereQuadraticSubmodule_of_isNorthZonal_pointConstraint_sqPolynomial
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (q : ℝ[X])
    (hsqpoly : ∀ u : Set.Icc (0 : ℝ) 1,
      sqCenteredNorthZonalProfile f u = q.eval u.1) :
    f ∈ continuousSphereQuadraticSubmodule := by
  rcases exists_quadraticMap_of_isNorthZonal_pointConstraint_sqPolynomial
      hfmem hfz q hsqpoly with ⟨Q, hQ⟩
  exact ⟨Q, hQ⟩
