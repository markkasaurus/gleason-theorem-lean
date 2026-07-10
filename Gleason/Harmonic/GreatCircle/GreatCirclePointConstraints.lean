import Gleason.Continuity.Auxiliary.ClosedGreatCircle
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

noncomputable section

open Complex InnerProductSpace

def greatCirclePointConstraintLinear
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    C(spherePoint3, ℝ) →ₗ[ℝ] ℝ :=
  (2 : ℝ) • greatCircleAverageLinear x y z hxy hxz hyz -
    (ContinuousMap.evalCLM ℝ x).toLinearMap -
    (ContinuousMap.evalCLM ℝ y).toLinearMap

@[simp] theorem greatCirclePointConstraintLinear_apply
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    greatCirclePointConstraintLinear x y z hxy hxz hyz f =
      2 * greatCircleAverageLinear x y z hxy hxz hyz f - f x - f y := by
  simp [greatCirclePointConstraintLinear]

def continuousSphereGreatCirclePointConstraintSubmodule : Submodule ℝ C(spherePoint3, ℝ) where
  carrier := {f | ∀ x y z : spherePoint3,
    ∀ hxy : inner (𝕜 := ℝ) x.1 y.1 = 0,
    ∀ hxz : inner (𝕜 := ℝ) x.1 z.1 = 0,
    ∀ hyz : inner (𝕜 := ℝ) y.1 z.1 = 0,
    greatCirclePointConstraintLinear x y z hxy hxz hyz f = 0}
  zero_mem' := by
    intro x y z hxy hxz hyz
    simp [greatCirclePointConstraintLinear_apply]
  add_mem' := by
    intro f g hf hg x y z hxy hxz hyz
    have hf' := hf x y z hxy hxz hyz
    have hg' := hg x y z hxy hxz hyz
    rw [LinearMap.map_add, hf', hg']
    simp
  smul_mem' := by
    intro c f hf x y z hxy hxz hyz
    rw [LinearMap.map_smul, hf _ _ _ _ _ _]
    simp

theorem mem_continuousSphereGreatCirclePointConstraintSubmodule_iff
    (f : C(spherePoint3, ℝ)) :
    f ∈ continuousSphereGreatCirclePointConstraintSubmodule ↔
      ∀ x y z : spherePoint3,
        ∀ hxy : inner (𝕜 := ℝ) x.1 y.1 = 0,
        ∀ hxz : inner (𝕜 := ℝ) x.1 z.1 = 0,
        ∀ hyz : inner (𝕜 := ℝ) y.1 z.1 = 0,
        2 * greatCircleAverageLinear x y z hxy hxz hyz f = f x + f y := by
  constructor
  · intro hf x y z hxy hxz hyz
    have hzero := hf x y z hxy hxz hyz
    rw [greatCirclePointConstraintLinear_apply] at hzero
    linarith
  · intro hf x y z hxy hxz hyz
    have hEq := hf x y z hxy hxz hyz
    rw [greatCirclePointConstraintLinear_apply]
    linarith

theorem continuousSphereFrameSubmodule_le_continuousSphereGreatCirclePointConstraintSubmodule :
    continuousSphereFrameSubmodule ≤ continuousSphereGreatCirclePointConstraintSubmodule := by
  intro f hf
  rw [mem_continuousSphereGreatCirclePointConstraintSubmodule_iff]
  intro x y z hxy hxz hyz
  exact two_mul_greatCircleAverageLinear_apply_of_mem_continuousSphereFrameSubmodule
    hf x y z hxy hxz hyz

def greatCirclePointConstraintCLM
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    C(spherePoint3, ℝ) →L[ℝ] ℝ :=
  (2 : ℝ) • greatCircleAverageCLM x y z hxy hxz hyz -
    ContinuousMap.evalCLM ℝ x -
    ContinuousMap.evalCLM ℝ y

@[simp] theorem greatCirclePointConstraintCLM_apply
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    greatCirclePointConstraintCLM x y z hxy hxz hyz f =
      greatCirclePointConstraintLinear x y z hxy hxz hyz f := by
  simp [greatCirclePointConstraintCLM, greatCirclePointConstraintLinear,
    greatCircleAverageCLM_apply]

lemma isClosed_setOf_greatCirclePointConstraint
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    IsClosed {f : C(spherePoint3, ℝ) |
      greatCirclePointConstraintLinear x y z hxy hxz hyz f = 0} := by
  have hEq :
      {f : C(spherePoint3, ℝ) |
        greatCirclePointConstraintLinear x y z hxy hxz hyz f = 0} =
      (greatCirclePointConstraintCLM x y z hxy hxz hyz) ⁻¹' ({0} : Set ℝ) := by
    ext f
    simp [greatCirclePointConstraintCLM_apply]
  rw [hEq]
  simpa using isClosed_singleton.preimage
    (greatCirclePointConstraintCLM x y z hxy hxz hyz).continuous

theorem isClosed_continuousSphereGreatCirclePointConstraintSubmodule :
    IsClosed (continuousSphereGreatCirclePointConstraintSubmodule : Set C(spherePoint3, ℝ)) := by
  have hEq :
      (continuousSphereGreatCirclePointConstraintSubmodule : Set C(spherePoint3, ℝ)) =
        ⋂ x : spherePoint3, ⋂ y : spherePoint3, ⋂ z : spherePoint3,
          ⋂ hxy : inner (𝕜 := ℝ) x.1 y.1 = 0,
            ⋂ hxz : inner (𝕜 := ℝ) x.1 z.1 = 0,
              ⋂ hyz : inner (𝕜 := ℝ) y.1 z.1 = 0,
                {f : C(spherePoint3, ℝ) |
                  greatCirclePointConstraintLinear x y z hxy hxz hyz f = 0} := by
    ext f
    simp [continuousSphereGreatCirclePointConstraintSubmodule]
  rw [hEq]
  exact isClosed_iInter fun x =>
    isClosed_iInter fun y =>
      isClosed_iInter fun z =>
        isClosed_iInter fun hxy =>
          isClosed_iInter fun hxz =>
            isClosed_iInter fun hyz =>
              isClosed_setOf_greatCirclePointConstraint x y z hxy hxz hyz

def continuousSphereGreatCirclePointConstraintClosedSubmodule :
    ClosedSubmodule ℝ C(spherePoint3, ℝ) :=
  ⟨continuousSphereGreatCirclePointConstraintSubmodule,
    isClosed_continuousSphereGreatCirclePointConstraintSubmodule⟩
