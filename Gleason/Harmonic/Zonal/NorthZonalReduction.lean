import Gleason.Harmonic.Zonal.NorthOrbitAverage
import Mathlib.Analysis.InnerProductSpace.Orthonormal

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

def IsNorthZonal (f : C(spherePoint3, ℝ)) : Prop :=
  ∀ t : ℝ, spherePrecomp (northRotation t) f = f

@[simp] lemma northRotation_add (s t : ℝ) :
    northRotation (s + t) = (northRotation s).trans (northRotation t) := by
  ext x
  simp [northRotation_apply, Circle.exp_add, mul_assoc, mul_left_comm, mul_comm]

@[simp] lemma northRotation_two_pi :
    northRotation (2 * Real.pi) = LinearIsometryEquiv.refl ℝ (WithLp 2 (ℂ × ℝ)) := by
  ext x
  cases x
  simp [northRotation_apply]

@[simp] lemma northRotation_add_two_pi (t : ℝ) :
    northRotation (t + 2 * Real.pi) = northRotation t := by
  calc
    northRotation (t + 2 * Real.pi)
        = (northRotation t).trans (northRotation (2 * Real.pi)) := by
            simpa [add_comm, add_left_comm, add_assoc] using northRotation_add t (2 * Real.pi)
    _ = northRotation t := by simp [northRotation_two_pi]

@[simp] lemma sphereMap_northRotation_add (s t : ℝ) (x : spherePoint3) :
    sphereMap (northRotation (s + t)) x =
      sphereMap (northRotation t) (sphereMap (northRotation s) x) := by
  simp [sphereMap, northRotation_add, LinearIsometryEquiv.trans_apply]

@[simp] lemma sphereMap_northRotation_add_two_pi (t : ℝ) (x : spherePoint3) :
    sphereMap (northRotation (t + 2 * Real.pi)) x =
      sphereMap (northRotation t) x := by
  simp [northRotation_add_two_pi]

lemma northOrbitAverage_eq_of_spherePrecomp_northRotation
    (f : C(spherePoint3, ℝ)) (s : ℝ) :
    northOrbitAverage (spherePrecomp (northRotation s) f) = northOrbitAverage f := by
  ext x
  rw [northOrbitAverage_apply, northOrbitAverage_apply]
  let F : ℝ → ℝ := fun t => f (sphereMap (northRotation t) x)
  have hshift :
      (∫ t in 0..2 * Real.pi, F (t + s)) = ∫ u in s..2 * Real.pi + s, F u := by
    simpa [F] using
      (intervalIntegral.integral_comp_add_right (f := F) (a := 0) (b := 2 * Real.pi) s)
  have hperiodic :
      Function.Periodic F (2 * Real.pi) := by
    intro t
    simp [F, sphereMap_northRotation_add_two_pi, add_assoc, add_left_comm, add_comm]
  have hperiod :
      ∫ u in s..2 * Real.pi + s, F u = ∫ u in 0..2 * Real.pi, F u := by
    simpa [add_comm, add_left_comm, add_assoc] using hperiodic.intervalIntegral_add_eq s 0
  have hEq1 :
      (fun t : ℝ =>
        ((spherePrecomp (northRotation s)) f) (sphereMap (northRotation t) x)) =
      fun t : ℝ => F (t + s) := by
    funext t
    simp [F, spherePrecomp_apply]
    rw [← sphereMap_northRotation_add t s x]
    simp [northRotation_add]
  calc
    ((2 * Real.pi)⁻¹ : ℝ) *
        ∫ t in 0..2 * Real.pi, ((spherePrecomp (northRotation s)) f) (sphereMap (northRotation t) x)
        = ((2 * Real.pi)⁻¹ : ℝ) * ∫ t in 0..2 * Real.pi, F (t + s) := by rw [hEq1]
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ u in s..2 * Real.pi + s, F u := by rw [hshift]
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ u in 0..2 * Real.pi, F u := by rw [hperiod]
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ t in 0..2 * Real.pi, f (sphereMap (northRotation t) x) := by
          simp [F]

lemma northOrbitAverage_isNorthZonal (f : C(spherePoint3, ℝ)) :
    IsNorthZonal (northOrbitAverage f) := by
  intro t
  ext x
  rw [spherePrecomp_apply, northOrbitAverage_apply, northOrbitAverage_apply]
  let F : ℝ → ℝ := fun s => f (sphereMap (northRotation s) x)
  have hshift :
      (∫ s in 0..2 * Real.pi, F (t + s)) = ∫ u in t..t + 2 * Real.pi, F u := by
    simpa [F] using
      (intervalIntegral.integral_comp_add_left (f := F) (a := 0) (b := 2 * Real.pi) t)
  have hperiodic :
      Function.Periodic F (2 * Real.pi) := by
    intro s
    simp [F, sphereMap_northRotation_add_two_pi, add_assoc, add_left_comm, add_comm]
  have hperiod :
      ∫ u in t..t + 2 * Real.pi, F u = ∫ u in 0..2 * Real.pi, F u := by
    simpa [add_comm, add_left_comm, add_assoc] using hperiodic.intervalIntegral_add_eq t 0
  have hEq1 :
      (fun t_1 : ℝ =>
        f (sphereMap (northRotation t_1) (sphereMap (northRotation t) x))) =
      fun s : ℝ => F (t + s) := by
    funext s
    simp [F]
    rw [← sphereMap_northRotation_add t s x]
    simp [northRotation_add]
  calc
    ((2 * Real.pi)⁻¹ : ℝ) * ∫ t_1 in 0..2 * Real.pi, f (sphereMap (northRotation t_1) (sphereMap (northRotation t) x))
        = ((2 * Real.pi)⁻¹ : ℝ) * ∫ s in 0..2 * Real.pi, F (t + s) := by rw [hEq1]
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ u in t..t + 2 * Real.pi, F u := by rw [hshift]
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ u in 0..2 * Real.pi, F u := by rw [hperiod]
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ t_1 in 0..2 * Real.pi, f (sphereMap (northRotation t_1) x) := by
          simp [F]

lemma exists_orthonormal_completion_of_spherePoint
    (z : spherePoint3) :
    ∃ x y : spherePoint3,
      inner (𝕜 := ℝ) x.1 y.1 = 0 ∧
      inner (𝕜 := ℝ) x.1 z.1 = 0 ∧
      inner (𝕜 := ℝ) y.1 z.1 = 0 := by
  let seed : Fin 3 → WithLp 2 (ℂ × ℝ) := fun i => if i = 0 then z.1 else 0
  let s : Set (Fin 3) := {0}
  have hseed_orth : Orthonormal ℝ (s.restrict seed) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    have hi' : i = 0 := by simpa [s, Set.mem_singleton_iff] using hi
    have hj' : j = 0 := by simpa [s, Set.mem_singleton_iff] using hj
    subst hi'; subst hj'
    simp [seed, z.2]
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℝ) (E := WithLp 2 (ℂ × ℝ)) (ι := Fin 3)
      (by rw [finrank_real_withLp_complex_prod_real]; simp) (v := seed) (s := s) hseed_orth
  have hb0 : b 0 = z.1 := hb 0 (by simp [s])
  have hortho := orthonormal_iff_ite.mp b.orthonormal
  have hxnorm : ‖b 1‖ = 1 := by
    have hnorm : inner (𝕜 := ℝ) (b 1) (b 1) = (1 : ℝ) := by simpa using hortho 1 1
    simpa [inner_self_eq_norm_sq_to_K] using hnorm
  have hynorm : ‖b 2‖ = 1 := by
    have hnorm : inner (𝕜 := ℝ) (b 2) (b 2) = (1 : ℝ) := by simpa using hortho 2 2
    simpa [inner_self_eq_norm_sq_to_K] using hnorm
  let x : spherePoint3 := ⟨b 1, hxnorm⟩
  let y : spherePoint3 := ⟨b 2, hynorm⟩
  have hxy : inner (𝕜 := ℝ) x.1 y.1 = 0 := by
    change inner (𝕜 := ℝ) (b 1) (b 2) = 0
    simpa using hortho 1 2
  have hxz : inner (𝕜 := ℝ) x.1 z.1 = 0 := by
    change inner (𝕜 := ℝ) (b 1) z.1 = 0
    simpa [hb0] using hortho 1 0
  have hyz : inner (𝕜 := ℝ) y.1 z.1 = 0 := by
    change inner (𝕜 := ℝ) (b 2) z.1 = 0
    simpa [hb0] using hortho 2 0
  exact ⟨x, y, hxy, hxz, hyz⟩

lemma exists_point_ne_zero_of_ne_zero
    {f : C(spherePoint3, ℝ)} (hf : f ≠ 0) :
    ∃ z : spherePoint3, f z ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hf
  ext z
  exact h z

theorem exists_nonzero_northZonal_mem_continuousSphereGreatCirclePointConstraintSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf_mem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hf_ne : f ≠ 0) :
    ∃ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
      northOrbitAverage (spherePrecomp e f) ∈ continuousSphereGreatCirclePointConstraintSubmodule ∧
      northOrbitAverage (spherePrecomp e f) ≠ 0 ∧
      IsNorthZonal (northOrbitAverage (spherePrecomp e f)) := by
  rcases exists_point_ne_zero_of_ne_zero hf_ne with ⟨z, hz⟩
  rcases exists_orthonormal_completion_of_spherePoint z with ⟨x, y, hxy, hxz, hyz⟩
  let e := sphereTripleIsometryEquiv x y z hxy hxz hyz
  have hmem :
      spherePrecomp e f ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
    exact continuousSphereGreatCirclePointConstraintSubmodule_invariant_under_spherePrecomp e hf_mem
  have hnorth :
      spherePrecomp e f sphereE3 ≠ 0 := by
    simpa [spherePrecomp_apply, e, sphereMap_sphereTripleIsometryEquiv_sphereE3]
      using hz
  refine ⟨e, ?_, ?_, northOrbitAverage_isNorthZonal (spherePrecomp e f)⟩
  · exact northOrbitAverage_mem_continuousSphereGreatCirclePointConstraintSubmodule hmem
  · exact northOrbitAverage_ne_zero_of_sphereE3_ne_zero hnorth
