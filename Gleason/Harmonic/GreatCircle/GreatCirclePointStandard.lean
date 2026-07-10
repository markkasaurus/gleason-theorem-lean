import Gleason.Harmonic.GreatCircle.GreatCirclePointRotation
import Gleason.Harmonic.GreatCircle.GreatCircleExclusionA

noncomputable section

open Complex InnerProductSpace

def stdGreatCirclePointConstraintLinear :
    C(spherePoint3, ℝ) →ₗ[ℝ] ℝ :=
  greatCirclePointConstraintLinear sphereE1 sphereE2 sphereE3
    sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3

@[simp] theorem stdGreatCirclePointConstraintLinear_apply
    (f : C(spherePoint3, ℝ)) :
    stdGreatCirclePointConstraintLinear f =
      2 * northEquatorAverageLinear f - f sphereE1 - f sphereE2 := by
  rw [show stdGreatCirclePointConstraintLinear f =
      greatCirclePointConstraintLinear sphereE1 sphereE2 sphereE3
        sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3 f by rfl]
  rw [greatCirclePointConstraintLinear_apply, greatCircleAverageLinear_std]

theorem greatCirclePointConstraintLinear_eq_std_on_spherePrecomp
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    greatCirclePointConstraintLinear x y z hxy hxz hyz f =
      stdGreatCirclePointConstraintLinear
        (spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) f) := by
  rw [stdGreatCirclePointConstraintLinear_apply, greatCirclePointConstraintLinear_apply,
    greatCircleAverageLinear_apply]
  simp [spherePrecomp_apply]

theorem mem_continuousSphereGreatCirclePointConstraintSubmodule_iff_std
    (f : C(spherePoint3, ℝ)) :
    f ∈ continuousSphereGreatCirclePointConstraintSubmodule ↔
      ∀ x y z : spherePoint3,
        ∀ hxy : inner (𝕜 := ℝ) x.1 y.1 = 0,
        ∀ hxz : inner (𝕜 := ℝ) x.1 z.1 = 0,
        ∀ hyz : inner (𝕜 := ℝ) y.1 z.1 = 0,
        stdGreatCirclePointConstraintLinear
          (spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) f) = 0 := by
  constructor
  · intro hf x y z hxy hxz hyz
    rw [← greatCirclePointConstraintLinear_eq_std_on_spherePrecomp]
    exact hf x y z hxy hxz hyz
  · intro hf x y z hxy hxz hyz
    rw [greatCirclePointConstraintLinear_eq_std_on_spherePrecomp]
    exact hf x y z hxy hxz hyz

theorem mem_continuousSphereGreatCirclePointConstraintSubmodule_of_forall_spherePrecomp
    {f : C(spherePoint3, ℝ)}
    (hf :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        stdGreatCirclePointConstraintLinear (spherePrecomp e f) = 0) :
    f ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
  rw [mem_continuousSphereGreatCirclePointConstraintSubmodule_iff_std]
  intro x y z hxy hxz hyz
  exact hf (sphereTripleIsometryEquiv x y z hxy hxz hyz)
