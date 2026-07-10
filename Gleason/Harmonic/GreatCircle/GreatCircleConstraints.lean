import Gleason.Harmonic.GreatCircle.GreatCircleAverage

noncomputable section

open Complex InnerProductSpace

def sphereFrameCenterLinear : C(spherePoint3, ℝ) →ₗ[ℝ] ℝ where
  toFun := sphereFrameCenter
  map_add' := by
    intro f g
    simp [sphereFrameCenter]
    ring
  map_smul' := by
    intro c f
    simp [sphereFrameCenter]
    ring

@[simp] theorem sphereFrameCenterLinear_apply (f : C(spherePoint3, ℝ)) :
    sphereFrameCenterLinear f = sphereFrameCenter f := by
  rfl

def sphereFrameCenteredLinear : C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ) where
  toFun := sphereFrameCentered
  map_add' := by
    intro f g
    ext x
    simp [sphereFrameCentered, sphereFrameCenterLinear, sphereFrameCenter]
    ring
  map_smul' := by
    intro c f
    ext x
    simp [sphereFrameCentered, sphereFrameCenterLinear, sphereFrameCenter]
    ring

@[simp] theorem sphereFrameCenteredLinear_apply
    (f : C(spherePoint3, ℝ)) :
    sphereFrameCenteredLinear f = sphereFrameCentered f := by
  rfl

def greatCircleCenteredConstraintLinear
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    C(spherePoint3, ℝ) →ₗ[ℝ] ℝ :=
  (greatCircleAverageLinear x y z hxy hxz hyz).comp sphereFrameCenteredLinear +
    ((2 : ℝ)⁻¹ : ℝ) •
      ((ContinuousMap.evalCLM ℝ z).toLinearMap.comp sphereFrameCenteredLinear)

@[simp] theorem greatCircleCenteredConstraintLinear_apply
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    greatCircleCenteredConstraintLinear x y z hxy hxz hyz f =
      greatCircleAverageLinear x y z hxy hxz hyz (sphereFrameCentered f) +
        ((sphereFrameCentered f) z) / 2 := by
  simp [greatCircleCenteredConstraintLinear, sphereFrameCenteredLinear_apply, div_eq_mul_inv,
    add_comm]
  ring

def continuousSphereGreatCircleConstraintSubmodule : Submodule ℝ C(spherePoint3, ℝ) where
  carrier := {f | ∀ x y z : spherePoint3,
    ∀ hxy : inner (𝕜 := ℝ) x.1 y.1 = 0,
    ∀ hxz : inner (𝕜 := ℝ) x.1 z.1 = 0,
    ∀ hyz : inner (𝕜 := ℝ) y.1 z.1 = 0,
    greatCircleCenteredConstraintLinear x y z hxy hxz hyz f = 0}
  zero_mem' := by
    intro x y z hxy hxz hyz
    simp [greatCircleCenteredConstraintLinear_apply, sphereFrameCentered, sphereFrameCenter]
  add_mem' := by
    intro f g hf hg x y z hxy hxz hyz
    have hf' := hf x y z hxy hxz hyz
    have hg' := hg x y z hxy hxz hyz
    rw [LinearMap.map_add, hf', hg']
    simp
  smul_mem' := by
    intro c f hf x y z hxy hxz hyz
    have hf' := hf x y z hxy hxz hyz
    rw [LinearMap.map_smul, hf']
    simp

theorem mem_continuousSphereGreatCircleConstraintSubmodule_iff
    (f : C(spherePoint3, ℝ)) :
    f ∈ continuousSphereGreatCircleConstraintSubmodule ↔
      ∀ x y z : spherePoint3,
        ∀ hxy : inner (𝕜 := ℝ) x.1 y.1 = 0,
        ∀ hxz : inner (𝕜 := ℝ) x.1 z.1 = 0,
        ∀ hyz : inner (𝕜 := ℝ) y.1 z.1 = 0,
        greatCircleAverageLinear x y z hxy hxz hyz (sphereFrameCentered f) =
          -((sphereFrameCentered f) z) / 2 := by
  constructor
  · intro hf x y z hxy hxz hyz
    have hzero := hf x y z hxy hxz hyz
    rw [greatCircleCenteredConstraintLinear_apply] at hzero
    linarith [hzero]
  · intro hf x y z hxy hxz hyz
    have hEq := hf x y z hxy hxz hyz
    rw [greatCircleCenteredConstraintLinear_apply]
    linarith [hEq]

theorem continuousSphereFrameSubmodule_le_continuousSphereGreatCircleConstraintSubmodule :
    continuousSphereFrameSubmodule ≤ continuousSphereGreatCircleConstraintSubmodule := by
  intro f hf
  rw [mem_continuousSphereGreatCircleConstraintSubmodule_iff]
  intro x y z hxy hxz hyz
  exact greatCircleAverageCentered_of_mem_continuousSphereFrameSubmodule hf x y z hxy hxz hyz
