import Gleason.Harmonic.Zonal.NorthZonalProfilePoly
import Gleason.Harmonic.Sphere.SphereQuadraticEndpoint
import Gleason.Continuity.Auxiliary.ContinuousEndpoint

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral Real Polynomial

def sndSphereBilin (c : ℝ) :
    LinearMap.BilinMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ :=
  LinearMap.mk₂' ℝ ℝ
    (fun x y : WithLp 2 (ℂ × ℝ) => c * x.snd * y.snd)
    (by
      intro x1 x2 y
      simp [mul_add, add_mul, mul_assoc])
    (by
      intro a x y
      simp [mul_assoc, mul_left_comm])
    (by
      intro x y1 y2
      simp [mul_add, mul_assoc])
    (by
      intro a x y
      simp [mul_assoc, mul_left_comm])

def sndSphereQuadraticMap (c : ℝ) : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ :=
  LinearMap.BilinMap.toQuadraticMap (sndSphereBilin c)

@[simp] lemma sndSphereQuadraticMap_apply (c : ℝ) (x : WithLp 2 (ℂ × ℝ)) :
    sndSphereQuadraticMap c x = c * x.snd ^ 2 := by
  change (sndSphereBilin c x) x = c * x.snd ^ 2
  simp [sndSphereBilin, pow_two]
  ring

theorem exists_quadraticMap_of_isNorthZonal_pointConstraint_polynomial
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (p : ℝ[X])
    (hpoly : ∀ z : Set.Icc (-1 : ℝ) 1,
      centeredNorthZonalProfile f z = p.eval z.1) :
    ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ,
      ∀ x : spherePoint3, f x = Q x.1 := by
  let Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ :=
    constantSphereQuadraticMap (f sphereE2) + sndSphereQuadraticMap (p.coeff 2)
  refine ⟨Q, ?_⟩
  intro x
  have hx :
      f x = f sphereE2 + p.coeff 2 * sphereCoordZ x ^ 2 :=
    isNorthZonal_eq_const_add_sq_of_polynomial hfmem hfz p hpoly x
  have hQconst : constantSphereQuadraticMap (f sphereE2) x.1 = f sphereE2 := by
    exact constantSphereQuadraticMap_apply_unit (f sphereE2) x
  calc
    f x = f sphereE2 + p.coeff 2 * sphereCoordZ x ^ 2 := hx
    _ = constantSphereQuadraticMap (f sphereE2) x.1 +
          sndSphereQuadraticMap (p.coeff 2) x.1 := by
            rw [hQconst, sndSphereQuadraticMap_apply]
            simp [sphereCoordZ]
    _ = Q x.1 := by
          simp [Q]

theorem mem_continuousSphereQuadraticSubmodule_of_isNorthZonal_pointConstraint_polynomial
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (p : ℝ[X])
    (hpoly : ∀ z : Set.Icc (-1 : ℝ) 1,
      centeredNorthZonalProfile f z = p.eval z.1) :
    f ∈ continuousSphereQuadraticSubmodule := by
  rcases exists_quadraticMap_of_isNorthZonal_pointConstraint_polynomial hfmem hfz p hpoly with
    ⟨Q, hQ⟩
  exact ⟨Q, hQ⟩
