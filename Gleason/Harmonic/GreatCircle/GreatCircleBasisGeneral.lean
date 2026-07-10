import Gleason.Harmonic.GreatCircle.GreatCircleBasisIndependence

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

lemma exists_equator_angle_of_orthogonal_to_sphereE3
    (x : spherePoint3)
    (hxz : inner (𝕜 := ℝ) x.1 sphereE3.1 = 0) :
    ∃ t : ℝ, x = equatorSpherePoint t := by
  have hsnd : x.1.snd = 0 := by
    simpa [sphereE3] using hxz
  have hsq := fst_norm_sq_add_snd_sq x
  rw [hsnd] at hsq
  have hnorm : ‖x.1.fst‖ = 1 := by
    nlinarith [hsq, norm_nonneg x.1.fst]
  refine ⟨Complex.arg x.1.fst, ?_⟩
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  refine Prod.ext ?_ ?_
  · symm
    change ((Real.cos (Complex.arg x.1.fst) : ℂ) + Complex.I * Real.sin (Complex.arg x.1.fst)) = x.1.fst
    calc
      ((Real.cos (Complex.arg x.1.fst) : ℂ) + Complex.I * Real.sin (Complex.arg x.1.fst))
          = Complex.exp (Complex.arg x.1.fst * Complex.I) := by
              simpa [mul_comm, add_comm, add_left_comm, add_assoc] using
                (Complex.exp_mul_I (Complex.arg x.1.fst)).symm
      _ = (‖x.1.fst‖ : ℂ) * Complex.exp (Complex.arg x.1.fst * Complex.I) := by
            simp [hnorm]
      _ = x.1.fst := by
            simpa [mul_comm] using Complex.norm_mul_exp_arg_mul_I x.1.fst
  · simp [equatorSpherePoint, hsnd]

lemma eq_sphereE2_or_reflect_sphereE2_of_equator_orthogonal
    (y : spherePoint3)
    (hyz : inner (𝕜 := ℝ) y.1 sphereE3.1 = 0)
    (h1y : inner (𝕜 := ℝ) sphereE1.1 y.1 = 0) :
    y = sphereE2 ∨ y = sphereMap equatorConj sphereE2 := by
  rcases exists_equator_angle_of_orthogonal_to_sphereE3 y hyz with ⟨s, rfl⟩
  have hcos : Real.cos s = 0 := by
    simpa [sphereE1, equatorSpherePoint] using h1y
  have hsin : Real.sin s = 1 ∨ Real.sin s = -1 := by
    exact (Real.cos_eq_zero_iff_sin_eq).1 hcos
  rcases hsin with hs | hs
  · left
    apply Subtype.ext
    simp [sphereE2, equatorSpherePoint, hcos, hs]
  · right
    apply Subtype.ext
    simp [sphereMap, sphereE2, equatorConj_apply, equatorSpherePoint, hcos, hs]

theorem greatCircleAverageLinear_eq_northEquatorAverage_of_equator_orthonormal
    (x y : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 sphereE3.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 sphereE3.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    greatCircleAverageLinear x y sphereE3 hxy hxz hyz f =
      northEquatorAverageLinear f := by
  rcases exists_equator_angle_of_orthogonal_to_sphereE3 x hxz with ⟨t, rfl⟩
  have hSphereE1 : sphereE1 = equatorSpherePoint 0 := by
    apply Subtype.ext
    simp [sphereE1, equatorSpherePoint]
  have hy' :
      inner (𝕜 := ℝ)
        (sphereMap (northRotation (-t)) y).1 sphereE3.1 = 0 := by
    have hy0 :
        inner (𝕜 := ℝ)
          (sphereMap (northRotation (-t)) y).1
          (sphereMap (northRotation (-t)) sphereE3).1 = 0 := by
      rw [sphereMap_inner]
      exact hyz
    simpa using hy0
  have h1y' :
      inner (𝕜 := ℝ) sphereE1.1 (sphereMap (northRotation (-t)) y).1 = 0 := by
    have hxy0 :
        inner (𝕜 := ℝ)
          (sphereMap (northRotation (-t)) (equatorSpherePoint t)).1
          (sphereMap (northRotation (-t)) y).1 = 0 := by
      rw [sphereMap_inner]
      exact hxy
    have hx0 :
        sphereMap (northRotation (-t)) (equatorSpherePoint t) = equatorSpherePoint 0 := by
      simpa [sub_eq_add_neg] using sphereMap_northRotation_equatorSpherePoint (-t) t
    rw [hx0, ← hSphereE1] at hxy0
    exact hxy0
  have hrot_inj : Function.Injective (sphereMap (northRotation (-t))) := by
    intro a b hab
    apply Subtype.ext
    exact (northRotation (-t)).injective (by simpa [sphereMap] using congrArg Subtype.val hab)
  rcases eq_sphereE2_or_reflect_sphereE2_of_equator_orthogonal
      (sphereMap (northRotation (-t)) y) hy' h1y' with hy'' | hy''
  · have hsphere :
        y = equatorSpherePoint (t + Real.pi / 2) := by
      have hrot :
          sphereMap (northRotation (-t)) (equatorSpherePoint (t + Real.pi / 2)) = sphereE2 := by
        simpa [sphereE2, equatorSpherePoint, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using sphereMap_northRotation_equatorSpherePoint (-t) (t + Real.pi / 2)
      apply hrot_inj
      calc
        sphereMap (northRotation (-t)) y = sphereE2 := hy''
        _ = sphereMap (northRotation (-t)) (equatorSpherePoint (t + Real.pi / 2)) := hrot.symm
    subst hsphere
    exact greatCircleAverageLinear_northRotation f t
  · have hsphere :
        y = equatorSpherePoint (t - Real.pi / 2) := by
      have hrot :
          sphereMap (northRotation (-t)) (equatorSpherePoint (t - Real.pi / 2)) =
            sphereMap equatorConj sphereE2 := by
        have hrot0 :
            sphereMap (northRotation (-t)) (equatorSpherePoint (t - Real.pi / 2)) =
              equatorSpherePoint (-Real.pi / 2) := by
          have hrot1 :=
            sphereMap_northRotation_equatorSpherePoint (-t) (t - Real.pi / 2)
          rw [show (t - Real.pi / 2) + -t = -Real.pi / 2 by ring] at hrot1
          exact hrot1
        calc
          sphereMap (northRotation (-t)) (equatorSpherePoint (t - Real.pi / 2))
              = equatorSpherePoint (-Real.pi / 2) := hrot0
          _ = sphereMap equatorConj sphereE2 := by
                rw [sphereMap_equatorConj_sphereE2]
      apply hrot_inj
      calc
        sphereMap (northRotation (-t)) y = sphereMap equatorConj sphereE2 := hy''
        _ = sphereMap (northRotation (-t)) (equatorSpherePoint (t - Real.pi / 2)) := hrot.symm
    subst hsphere
    exact greatCircleAverageLinear_northRotation_reflect f t

theorem greatCircleAverageLinear_eq_of_same_pole
    (x y x' y' z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (hxy' : inner (𝕜 := ℝ) x'.1 y'.1 = 0)
    (hxz' : inner (𝕜 := ℝ) x'.1 z.1 = 0)
    (hyz' : inner (𝕜 := ℝ) y'.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    greatCircleAverageLinear x y z hxy hxz hyz f =
      greatCircleAverageLinear x' y' z hxy' hxz' hyz' f := by
  let e := sphereTripleIsometryEquiv x y z hxy hxz hyz
  have hmain :
      greatCircleAverageLinear x y z hxy hxz hyz f =
        northEquatorAverageLinear (spherePrecomp e f) := by
    have h :=
      greatCircleAverageLinear_spherePrecomp e f
        sphereE1 sphereE2 sphereE3
        sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
    simpa [e, greatCircleAverageLinear_std] using h.symm
  have hz :
      sphereMap e sphereE3 = z := by
    simpa [e] using sphereMap_sphereTripleIsometryEquiv_sphereE3 x y z hxy hxz hyz
  have hz0 : sphereMap e.symm z = sphereE3 := by
    have hz' := congrArg (sphereMap e.symm) hz
    simpa [sphereMap] using hz'.symm
  have hx0 :
      inner (𝕜 := ℝ) (sphereMap e.symm x').1 sphereE3.1 = 0 := by
    have hx0' :
        inner (𝕜 := ℝ)
          (sphereMap e.symm x').1
          (sphereMap e.symm z).1 = 0 := by
      simpa [sphereMap_inner] using hxz'
    simpa [hz0] using hx0'
  have hy0 :
      inner (𝕜 := ℝ) (sphereMap e.symm y').1 sphereE3.1 = 0 := by
    have hy0' :
        inner (𝕜 := ℝ)
          (sphereMap e.symm y').1
          (sphereMap e.symm z).1 = 0 := by
      simpa [sphereMap_inner] using hyz'
    simpa [hz0] using hy0'
  have hxy0 :
      inner (𝕜 := ℝ) (sphereMap e.symm x').1 (sphereMap e.symm y').1 = 0 := by
    simpa [sphereMap_inner] using hxy'
  have hpre : spherePrecomp e.symm (spherePrecomp e f) = f := by
    ext u
    simp [spherePrecomp_apply, sphereMap]
  have hmain' :
      greatCircleAverageLinear x' y' z hxy' hxz' hyz' f =
        northEquatorAverageLinear (spherePrecomp e f) := by
    have h :=
      greatCircleAverageLinear_spherePrecomp e.symm (spherePrecomp e f)
        x' y' z hxy' hxz' hyz'
    calc
      greatCircleAverageLinear x' y' z hxy' hxz' hyz' f
          = greatCircleAverageLinear (sphereMap e.symm x') (sphereMap e.symm y') sphereE3
              hxy0 hx0 hy0 (spherePrecomp e f) := by
                simpa [hpre, hz0] using h
      _ = northEquatorAverageLinear (spherePrecomp e f) := by
            exact
              greatCircleAverageLinear_eq_northEquatorAverage_of_equator_orthonormal
                (sphereMap e.symm x') (sphereMap e.symm y') hxy0 hx0 hy0 (spherePrecomp e f)
  exact hmain.trans hmain'.symm
