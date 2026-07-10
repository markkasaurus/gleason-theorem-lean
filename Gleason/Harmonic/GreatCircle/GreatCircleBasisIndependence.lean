import Gleason.Harmonic.GreatCircle.GreatCirclePointStandard
import Gleason.Harmonic.Zonal.NorthZonalFactor

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

def equatorConjLinearEquiv :
    WithLp 2 (ℂ × ℝ) ≃ₗ[ℝ] WithLp 2 (ℂ × ℝ) :=
  (WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).trans
      ((conjLIE.toLinearEquiv).prodCongr (LinearEquiv.refl ℝ ℝ))
    |>.trans (WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).symm

@[simp] lemma equatorConjLinearEquiv_apply
    (x : WithLp 2 (ℂ × ℝ)) :
    equatorConjLinearEquiv x = WithLp.toLp 2 ((starRingEnd ℂ) x.fst, x.snd) := by
  simp [equatorConjLinearEquiv]

def equatorConj : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ) :=
  ⟨equatorConjLinearEquiv, by
    intro x
    rw [equatorConjLinearEquiv_apply, WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
    simp⟩

@[simp] lemma equatorConj_apply
    (x : WithLp 2 (ℂ × ℝ)) :
    equatorConj x = WithLp.toLp 2 ((starRingEnd ℂ) x.fst, x.snd) := by
  simp [equatorConj]

@[simp] lemma sphereMap_equatorConj_sphereE1 :
    sphereMap equatorConj sphereE1 = sphereE1 := by
  apply Subtype.ext
  simp [sphereMap, sphereE1, equatorConj_apply]

@[simp] lemma sphereMap_equatorConj_sphereE3 :
    sphereMap equatorConj sphereE3 = sphereE3 := by
  apply Subtype.ext
  simp [sphereMap, sphereE3, equatorConj_apply]

@[simp] lemma sphereMap_equatorConj_equatorSpherePoint
    (θ : ℝ) :
    sphereMap equatorConj (equatorSpherePoint θ) = equatorSpherePoint (-θ) := by
  have hreal : ∀ r : ℝ, (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := by
    intro r
    simpa using Complex.conj_ofReal r
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  refine Prod.ext ?_ ?_
  · simpa [hreal (Real.cos θ), hreal (Real.sin θ), sphereMap, equatorSpherePoint, equatorConj_apply,
      Real.sin_neg, Real.cos_neg, sub_eq_add_neg] using
        congrArg₂ (fun a b : ℂ => a + -(Complex.I * b))
          (hreal (Real.cos θ)) (hreal (Real.sin θ))
  · simp [sphereMap, equatorSpherePoint, equatorConj_apply]

@[simp] lemma sphereMap_equatorConj_sphereE2 :
    sphereMap equatorConj sphereE2 = equatorSpherePoint (-Real.pi / 2) := by
  have hSphereE2 : sphereE2 = equatorSpherePoint (Real.pi / 2) := by
    apply Subtype.ext
    simp [sphereE2, equatorSpherePoint]
  rw [hSphereE2]
  have h := sphereMap_equatorConj_equatorSpherePoint (Real.pi / 2)
  convert h using 1 <;> ring_nf

theorem northEquatorAverage_reflect
    (f : C(spherePoint3, ℝ)) :
    ∫ θ in 0..2 * Real.pi, f (equatorSpherePoint (-θ)) =
      ∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ) := by
  let F : ℝ → ℝ := fun θ => f (equatorSpherePoint θ)
  have hneg :
      (∫ θ in 0..2 * Real.pi, F (-θ)) =
        ∫ θ in -(2 * Real.pi)..0, F θ := by
    simpa [F] using
      (intervalIntegral.integral_comp_neg (f := F) (a := 0) (b := 2 * Real.pi))
  have hperiodic :
      Function.Periodic F (2 * Real.pi) :=
    equatorRestrictionFromSphere_periodic (f := (f : spherePoint3 → ℝ))
  have hperiod :
      ∫ θ in -(2 * Real.pi)..0, F θ =
        ∫ θ in 0..2 * Real.pi, F θ := by
    simpa [zero_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hperiodic.intervalIntegral_add_eq (-(2 * Real.pi)) 0
  exact hneg.trans hperiod

theorem northEquatorAverageLinear_spherePrecomp_equatorConj
    (f : C(spherePoint3, ℝ)) :
    northEquatorAverageLinear (spherePrecomp equatorConj f) =
      northEquatorAverageLinear f := by
  rw [northEquatorAverageLinear_apply, northEquatorAverageLinear_apply]
  have hreflect := northEquatorAverage_reflect f
  simpa [spherePrecomp_apply, sphereMap_equatorConj_equatorSpherePoint] using
    congrArg (fun s : ℝ => (2 * Real.pi)⁻¹ * s) hreflect

lemma greatCircleAverageLinear_northRotation
    (f : C(spherePoint3, ℝ)) (t : ℝ) :
    greatCircleAverageLinear
        (equatorSpherePoint t)
        (equatorSpherePoint (t + Real.pi / 2))
        sphereE3
        (equatorSpherePoint_inner_quarter_turn t)
        (equatorSpherePoint_inner_sphereE3 t)
        (equatorSpherePoint_inner_sphereE3 (t + Real.pi / 2))
        f =
      northEquatorAverageLinear f := by
  have h :=
    greatCircleAverageLinear_spherePrecomp (northRotation t) f
      sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  rw [greatCircleAverageLinear_std] at h
  have hSphereE1 : sphereE1 = equatorSpherePoint 0 := by
    apply Subtype.ext
    simp [sphereE1, equatorSpherePoint]
  have hSphereE2 : sphereE2 = equatorSpherePoint (Real.pi / 2) := by
    apply Subtype.ext
    simp [sphereE2, equatorSpherePoint]
  have hE1 : sphereMap (northRotation t) sphereE1 = equatorSpherePoint t := by
    rw [hSphereE1]
    simpa using sphereMap_northRotation_equatorSpherePoint t 0
  have hE2 : sphereMap (northRotation t) sphereE2 = equatorSpherePoint (t + Real.pi / 2) := by
    rw [hSphereE2]
    have hEq := sphereMap_northRotation_equatorSpherePoint t (Real.pi / 2)
    convert hEq using 1
    ring_nf
  have h' :
      northEquatorAverageLinear (spherePrecomp (northRotation t) f) =
        greatCircleAverageLinear
          (equatorSpherePoint t)
          (equatorSpherePoint (t + Real.pi / 2))
          sphereE3
          (equatorSpherePoint_inner_quarter_turn t)
          (equatorSpherePoint_inner_sphereE3 t)
          (equatorSpherePoint_inner_sphereE3 (t + Real.pi / 2))
          f := by
    simpa [hE1, hE2, sphereMap_northRotation_sphereE3] using h
  calc
    greatCircleAverageLinear
        (equatorSpherePoint t)
        (equatorSpherePoint (t + Real.pi / 2))
        sphereE3
        (equatorSpherePoint_inner_quarter_turn t)
        (equatorSpherePoint_inner_sphereE3 t)
        (equatorSpherePoint_inner_sphereE3 (t + Real.pi / 2))
        f
      = northEquatorAverageLinear (spherePrecomp (northRotation t) f) := by
          exact h'.symm
    _ = northEquatorAverageLinear f := northEquatorAverageLinear_spherePrecomp_northRotation f t

lemma greatCircleAverageLinear_northRotation_reflect
    (f : C(spherePoint3, ℝ)) (t : ℝ) :
    greatCircleAverageLinear
        (equatorSpherePoint t)
        (equatorSpherePoint (t - Real.pi / 2))
        sphereE3
        (by
          rw [real_inner_comm]
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
            equatorSpherePoint_inner_quarter_turn (t - Real.pi / 2))
        (equatorSpherePoint_inner_sphereE3 t)
        (by simpa [sub_eq_add_neg] using equatorSpherePoint_inner_sphereE3 (t - Real.pi / 2))
        f =
      northEquatorAverageLinear f := by
  have h :=
    greatCircleAverageLinear_spherePrecomp (equatorConj.trans (northRotation t)) f
      sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  rw [greatCircleAverageLinear_std] at h
  have hE1 :
      sphereMap (equatorConj.trans (northRotation t)) sphereE1 = equatorSpherePoint t := by
    apply Subtype.ext
    simp [sphereMap, sphereE1, equatorSpherePoint, equatorConj_apply, northRotation_apply]
    rw [Complex.exp_mul_I]
    ring_nf
  have hE2 :
      sphereMap (equatorConj.trans (northRotation t)) sphereE2 = equatorSpherePoint (t - Real.pi / 2) := by
    calc
      sphereMap (equatorConj.trans (northRotation t)) sphereE2
          = sphereMap (northRotation t) (sphereMap equatorConj sphereE2) := by
              rfl
      _ = sphereMap (northRotation t) (equatorSpherePoint (-Real.pi / 2)) := by
            rw [sphereMap_equatorConj_sphereE2]
      _ = equatorSpherePoint ((-Real.pi / 2) + t) := by
            simpa using sphereMap_northRotation_equatorSpherePoint t (-Real.pi / 2)
      _ = equatorSpherePoint (t - Real.pi / 2) := by ring_nf
  have hE3 :
      sphereMap (equatorConj.trans (northRotation t)) sphereE3 = sphereE3 := by
    calc
      sphereMap (equatorConj.trans (northRotation t)) sphereE3
          = sphereMap (northRotation t) (sphereMap equatorConj sphereE3) := by
              rfl
      _ = sphereMap (northRotation t) sphereE3 := by rw [sphereMap_equatorConj_sphereE3]
      _ = sphereE3 := sphereMap_northRotation_sphereE3 t
  have havg :
      northEquatorAverageLinear (spherePrecomp (equatorConj.trans (northRotation t)) f) =
        northEquatorAverageLinear f := by
    calc
      northEquatorAverageLinear (spherePrecomp (equatorConj.trans (northRotation t)) f)
          = northEquatorAverageLinear (spherePrecomp equatorConj (spherePrecomp (northRotation t) f)) := by
              simp [spherePrecomp_apply]
      _ = northEquatorAverageLinear (spherePrecomp (northRotation t) f) := by
            rw [northEquatorAverageLinear_spherePrecomp_equatorConj]
      _ = northEquatorAverageLinear f := northEquatorAverageLinear_spherePrecomp_northRotation f t
  calc
    greatCircleAverageLinear
        (equatorSpherePoint t)
        (equatorSpherePoint (t - Real.pi / 2))
        sphereE3
        (by
          rw [real_inner_comm]
          simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
            equatorSpherePoint_inner_quarter_turn (t - Real.pi / 2))
        (equatorSpherePoint_inner_sphereE3 t)
        (by simpa [sub_eq_add_neg] using equatorSpherePoint_inner_sphereE3 (t - Real.pi / 2))
        f
      = northEquatorAverageLinear (spherePrecomp (equatorConj.trans (northRotation t)) f) := by
          simpa [hE1, hE2, hE3] using h.symm
    _ = northEquatorAverageLinear f := havg
