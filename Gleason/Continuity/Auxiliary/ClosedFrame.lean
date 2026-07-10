import Gleason.Harmonic.Sphere.SphereFrame
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

noncomputable section

open Complex InnerProductSpace

def sphereFrameConstraintCLM (x y z : spherePoint3) :
    C(spherePoint3, ℝ) →L[ℝ] ℝ :=
  ContinuousMap.evalCLM ℝ x +
    ContinuousMap.evalCLM ℝ y +
    ContinuousMap.evalCLM ℝ z -
    ContinuousMap.evalCLM ℝ sphereE1 -
    ContinuousMap.evalCLM ℝ sphereE2 -
    ContinuousMap.evalCLM ℝ sphereE3

@[simp] theorem sphereFrameConstraintCLM_apply
    (x y z : spherePoint3) (f : C(spherePoint3, ℝ)) :
    sphereFrameConstraintCLM x y z f =
      f x + f y + f z - (f sphereE1 + f sphereE2 + f sphereE3) := by
  simp [sphereFrameConstraintCLM]
  ring

theorem mem_continuousSphereFrameSubmodule_iff
    (f : C(spherePoint3, ℝ)) :
    f ∈ continuousSphereFrameSubmodule ↔
      ∀ x y z : spherePoint3,
        inner (𝕜 := ℝ) x.1 y.1 = 0 →
        inner (𝕜 := ℝ) x.1 z.1 = 0 →
        inner (𝕜 := ℝ) y.1 z.1 = 0 →
        sphereFrameConstraintCLM x y z f = 0 := by
  constructor
  · intro hf x y z hxy hxz hyz
    have hf' : IsSphereFrameFunction (f : spherePoint3 → ℝ) := hf
    have hsum := hf' x y z hxy hxz hyz
    simpa [sphereFrameConstraintCLM_apply] using sub_eq_zero.mpr hsum
  · intro hf
    show IsSphereFrameFunction (f : spherePoint3 → ℝ)
    intro x y z hxy hxz hyz
    have hzero := hf x y z hxy hxz hyz
    exact sub_eq_zero.mp (by simpa [sphereFrameConstraintCLM_apply] using hzero)

lemma isClosed_setOf_sphereFrameConstraint
    (x y z : spherePoint3) :
    IsClosed {f : C(spherePoint3, ℝ) |
      inner (𝕜 := ℝ) x.1 y.1 = 0 →
      inner (𝕜 := ℝ) x.1 z.1 = 0 →
      inner (𝕜 := ℝ) y.1 z.1 = 0 →
      sphereFrameConstraintCLM x y z f = 0} := by
  by_cases hxy : inner (𝕜 := ℝ) x.1 y.1 = 0
  · by_cases hxz : inner (𝕜 := ℝ) x.1 z.1 = 0
    · by_cases hyz : inner (𝕜 := ℝ) y.1 z.1 = 0
      · have hSet :
            {f : C(spherePoint3, ℝ) |
              inner (𝕜 := ℝ) x.1 y.1 = 0 →
              inner (𝕜 := ℝ) x.1 z.1 = 0 →
              inner (𝕜 := ℝ) y.1 z.1 = 0 →
              sphereFrameConstraintCLM x y z f = 0} =
            {f : C(spherePoint3, ℝ) | sphereFrameConstraintCLM x y z f = 0} := by
          ext f
          constructor
          · intro hf
            exact hf hxy hxz hyz
          · intro hf _ _ _
            exact hf
        rw [hSet]
        change IsClosed ((sphereFrameConstraintCLM x y z) ⁻¹' ({0} : Set ℝ))
        simpa using isClosed_singleton.preimage (sphereFrameConstraintCLM x y z).continuous
      · have hSet :
            {f : C(spherePoint3, ℝ) |
              inner (𝕜 := ℝ) x.1 y.1 = 0 →
              inner (𝕜 := ℝ) x.1 z.1 = 0 →
              inner (𝕜 := ℝ) y.1 z.1 = 0 →
              sphereFrameConstraintCLM x y z f = 0} = Set.univ := by
          ext f
          constructor
          · intro _
            trivial
          · intro _ _ _ hyz0
            exact False.elim (hyz hyz0)
        rw [hSet]
        simpa using isClosed_univ
    · have hSet :
          {f : C(spherePoint3, ℝ) |
            inner (𝕜 := ℝ) x.1 y.1 = 0 →
            inner (𝕜 := ℝ) x.1 z.1 = 0 →
            inner (𝕜 := ℝ) y.1 z.1 = 0 →
            sphereFrameConstraintCLM x y z f = 0} = Set.univ := by
        ext f
        constructor
        · intro _
          trivial
        · intro _ _ hxz0 _
          exact False.elim (hxz hxz0)
      rw [hSet]
      simpa using isClosed_univ
  · have hSet :
        {f : C(spherePoint3, ℝ) |
          inner (𝕜 := ℝ) x.1 y.1 = 0 →
          inner (𝕜 := ℝ) x.1 z.1 = 0 →
          inner (𝕜 := ℝ) y.1 z.1 = 0 →
          sphereFrameConstraintCLM x y z f = 0} = Set.univ := by
      ext f
      constructor
      · intro _
        trivial
      · intro _ hxy0 _ _
        exact False.elim (hxy hxy0)
    rw [hSet]
    simpa using isClosed_univ

theorem isClosed_continuousSphereFrameSubmodule :
    IsClosed (continuousSphereFrameSubmodule : Set C(spherePoint3, ℝ)) := by
  have hEq :
      (continuousSphereFrameSubmodule : Set C(spherePoint3, ℝ)) =
        ⋂ x : spherePoint3, ⋂ y : spherePoint3, ⋂ z : spherePoint3,
          {f : C(spherePoint3, ℝ) |
            inner (𝕜 := ℝ) x.1 y.1 = 0 →
            inner (𝕜 := ℝ) x.1 z.1 = 0 →
            inner (𝕜 := ℝ) y.1 z.1 = 0 →
            sphereFrameConstraintCLM x y z f = 0} := by
    ext f
    simp [mem_continuousSphereFrameSubmodule_iff]
  rw [hEq]
  exact isClosed_iInter fun x =>
    isClosed_iInter fun y =>
      isClosed_iInter fun z =>
        isClosed_setOf_sphereFrameConstraint x y z

def continuousSphereFrameClosedSubmodule : ClosedSubmodule ℝ C(spherePoint3, ℝ) :=
  ⟨continuousSphereFrameSubmodule, isClosed_continuousSphereFrameSubmodule⟩
