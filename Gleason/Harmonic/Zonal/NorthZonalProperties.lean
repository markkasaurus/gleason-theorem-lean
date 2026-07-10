import Gleason.Harmonic.Zonal.NorthZonalClosed

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

lemma northEquatorAverageLinear_eq_of_isNorthZonal
    {f : C(spherePoint3, ℝ)} (hf : IsNorthZonal f) :
    northEquatorAverageLinear f = f sphereE1 := by
  rw [northEquatorAverageLinear_apply]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hconst :
      (∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ)) =
        (2 * Real.pi) * f sphereE1 := by
    have hEq : ∀ θ : ℝ, f (equatorSpherePoint θ) = f sphereE1 := by
      intro θ
      have hθ := congrArg (fun g : C(spherePoint3, ℝ) => g sphereE1) (hf θ)
      have hmap : sphereMap (northRotation θ) sphereE1 = equatorSpherePoint θ := by
        apply Subtype.ext
        simp [sphereMap, sphereE1, equatorSpherePoint, northRotation_apply]
        rw [Complex.exp_mul_I]
        ring
      simpa [spherePrecomp_apply, hmap] using hθ
    simp [hEq]
  rw [hconst]
  field_simp [hpi.ne']

lemma northOrbitAverage_eq_self_of_isNorthZonal
    {f : C(spherePoint3, ℝ)} (hf : IsNorthZonal f) :
    northOrbitAverage f = f := by
  ext x
  rw [northOrbitAverage_apply]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hconst :
      (∫ t in 0..2 * Real.pi, f (sphereMap (northRotation t) x)) =
        (2 * Real.pi) * f x := by
    have hEq : ∀ t : ℝ, f (sphereMap (northRotation t) x) = f x := by
      intro t
      exact congrArg (fun g : C(spherePoint3, ℝ) => g x) (hf t)
    simp [hEq]
  rw [hconst]
  field_simp [hpi.ne']

lemma northOrbitAverage_idempotent (f : C(spherePoint3, ℝ)) :
    northOrbitAverage (northOrbitAverage f) = northOrbitAverage f := by
  exact northOrbitAverage_eq_self_of_isNorthZonal (northOrbitAverage_isNorthZonal f)
