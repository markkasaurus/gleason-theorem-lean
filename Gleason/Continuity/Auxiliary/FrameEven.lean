import Gleason.Harmonic.Auxiliary.PointConstraintFrame

noncomputable section

open Complex InnerProductSpace

def sphereAntipode : spherePoint3 → spherePoint3 :=
  sphereMap (LinearIsometryEquiv.neg ℝ)

@[simp] theorem sphereAntipode_apply_val (x : spherePoint3) :
    (sphereAntipode x).1 = -x.1 := by
  rfl

theorem IsSphereFrameFunction_even
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f) (x : spherePoint3) :
    f (sphereAntipode x) = f x := by
  rcases exists_common_orthogonal_spherePoint x sphereE3 with ⟨y, hxy, hy3⟩
  rcases exists_common_orthogonal_spherePoint x y with ⟨z, hxz, hyz⟩
  have hpos := hf x y z hxy hxz hyz
  have hxyNeg : inner (𝕜 := ℝ) (sphereAntipode x).1 y.1 = 0 := by
    calc
      inner (𝕜 := ℝ) (sphereAntipode x).1 y.1 = -inner (𝕜 := ℝ) x.1 y.1 := by
        simp [sphereAntipode, sphereMap, LinearIsometryEquiv.coe_neg]
      _ = 0 := by rw [hxy, neg_zero]
  have hxzNeg : inner (𝕜 := ℝ) (sphereAntipode x).1 z.1 = 0 := by
    calc
      inner (𝕜 := ℝ) (sphereAntipode x).1 z.1 = -inner (𝕜 := ℝ) x.1 z.1 := by
        simp [sphereAntipode, sphereMap, LinearIsometryEquiv.coe_neg]
      _ = 0 := by rw [hxz, neg_zero]
  have hneg :=
    hf (sphereAntipode x) y z
      hxyNeg hxzNeg
      hyz
  linarith

theorem mem_continuousSphereFrameSubmodule_even
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule) (x : spherePoint3) :
    f (sphereAntipode x) = f x := by
  exact IsSphereFrameFunction_even (show IsSphereFrameFunction (f : spherePoint3 → ℝ) from hf) x

def sphereEvenConstraintCLM (x : spherePoint3) :
    C(spherePoint3, ℝ) →L[ℝ] ℝ :=
  ContinuousMap.evalCLM ℝ x - ContinuousMap.evalCLM ℝ (sphereAntipode x)

@[simp] theorem sphereEvenConstraintCLM_apply
    (x : spherePoint3) (f : C(spherePoint3, ℝ)) :
    sphereEvenConstraintCLM x f = f x - f (sphereAntipode x) := by
  simp [sphereEvenConstraintCLM]

def continuousSphereEvenSubmodule : Submodule ℝ C(spherePoint3, ℝ) where
  carrier := {f | ∀ x : spherePoint3, f (sphereAntipode x) = f x}
  zero_mem' := by
    intro x
    simp
  add_mem' := by
    intro f g hf hg x
    simp [hf x, hg x]
  smul_mem' := by
    intro c f hf x
    simp [hf x]

theorem mem_continuousSphereEvenSubmodule_iff
    (f : C(spherePoint3, ℝ)) :
    f ∈ continuousSphereEvenSubmodule ↔ ∀ x : spherePoint3, sphereEvenConstraintCLM x f = 0 := by
  constructor
  · intro hf x
    rw [sphereEvenConstraintCLM_apply, hf x, sub_self]
  · intro hf x
    have hx := hf x
    rw [sphereEvenConstraintCLM_apply] at hx
    linarith

theorem continuousSphereFrameSubmodule_le_continuousSphereEvenSubmodule :
    continuousSphereFrameSubmodule ≤ continuousSphereEvenSubmodule := by
  intro f hf
  exact mem_continuousSphereFrameSubmodule_even hf

theorem isClosed_continuousSphereEvenSubmodule :
    IsClosed (continuousSphereEvenSubmodule : Set C(spherePoint3, ℝ)) := by
  have hEq :
      (continuousSphereEvenSubmodule : Set C(spherePoint3, ℝ)) =
        ⋂ x : spherePoint3, {f : C(spherePoint3, ℝ) | sphereEvenConstraintCLM x f = 0} := by
    ext f
    simp [mem_continuousSphereEvenSubmodule_iff]
  rw [hEq]
  refine isClosed_iInter ?_
  intro x
  change IsClosed ((sphereEvenConstraintCLM x) ⁻¹' ({0} : Set ℝ))
  simpa using isClosed_singleton.preimage (sphereEvenConstraintCLM x).continuous

def continuousSphereEvenClosedSubmodule : ClosedSubmodule ℝ C(spherePoint3, ℝ) :=
  ⟨continuousSphereEvenSubmodule, isClosed_continuousSphereEvenSubmodule⟩
