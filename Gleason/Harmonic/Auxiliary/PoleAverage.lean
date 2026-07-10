import Gleason.Harmonic.Zonal.NorthZonalReduction
import Gleason.Harmonic.GreatCircle.GreatCircleAverage
import Gleason.Harmonic.GreatCircle.GreatCircleConstraints
import Gleason.Harmonic.GreatCircle.GreatCircleBasisGeneral
import Gleason.Harmonic.Auxiliary.PointConstraintFrame

noncomputable section

open Complex InnerProductSpace

noncomputable def poleChoiceX (z : spherePoint3) : spherePoint3 :=
  Classical.choose (exists_orthonormal_completion_of_spherePoint z)

noncomputable def poleChoiceY (z : spherePoint3) : spherePoint3 :=
  Classical.choose (Classical.choose_spec (exists_orthonormal_completion_of_spherePoint z))

lemma poleChoice_spec (z : spherePoint3) :
    inner (𝕜 := ℝ) (poleChoiceX z).1 (poleChoiceY z).1 = 0 ∧
      inner (𝕜 := ℝ) (poleChoiceX z).1 z.1 = 0 ∧
      inner (𝕜 := ℝ) (poleChoiceY z).1 z.1 = 0 := by
  exact
    Classical.choose_spec
      (Classical.choose_spec (exists_orthonormal_completion_of_spherePoint z))

def poleAverageLinear : C(spherePoint3, ℝ) →ₗ[ℝ] (spherePoint3 → ℝ) where
  toFun f := fun z =>
    greatCircleAverageLinear
      (poleChoiceX z) (poleChoiceY z) z
      (poleChoice_spec z).1 (poleChoice_spec z).2.1 (poleChoice_spec z).2.2 f
  map_add' := by
    intro f g
    ext z
    simp [map_add]
  map_smul' := by
    intro c f
    ext z
    simp

@[simp] theorem poleAverageLinear_apply
    (f : C(spherePoint3, ℝ)) (z : spherePoint3) :
    poleAverageLinear f z =
      greatCircleAverageLinear
        (poleChoiceX z) (poleChoiceY z) z
        (poleChoice_spec z).1 (poleChoice_spec z).2.1 (poleChoice_spec z).2.2 f := by
  rfl

theorem poleAverageLinear_eq_greatCircleAverageLinear
    (f : C(spherePoint3, ℝ))
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    poleAverageLinear f z = greatCircleAverageLinear x y z hxy hxz hyz f := by
  exact
    greatCircleAverageLinear_eq_of_same_pole
      (poleChoiceX z) (poleChoiceY z) x y z
      (poleChoice_spec z).1 (poleChoice_spec z).2.1 (poleChoice_spec z).2.2
      hxy hxz hyz f

@[simp] theorem poleAverageLinear_sphereE3
    (f : C(spherePoint3, ℝ)) :
    poleAverageLinear f sphereE3 = northEquatorAverageLinear f := by
  rw [poleAverageLinear_eq_greatCircleAverageLinear
      f sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3]
  exact greatCircleAverageLinear_std f

theorem poleAverageLinear_centered_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (z : spherePoint3) :
    poleAverageLinear (sphereFrameCentered f) z =
      -((sphereFrameCentered f) z) / 2 := by
  rw [poleAverageLinear_eq_greatCircleAverageLinear
      (sphereFrameCentered f) (poleChoiceX z) (poleChoiceY z) z
      (poleChoice_spec z).1 (poleChoice_spec z).2.1 (poleChoice_spec z).2.2]
  exact
    greatCircleAverageCentered_of_mem_continuousSphereFrameSubmodule
      hf (poleChoiceX z) (poleChoiceY z) z
      (poleChoice_spec z).1 (poleChoice_spec z).2.1 (poleChoice_spec z).2.2

theorem two_mul_poleAverageLinear_centered_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (z : spherePoint3) :
    2 * poleAverageLinear (sphereFrameCentered f) z =
      -((sphereFrameCentered f) z) := by
  have h :=
    poleAverageLinear_centered_of_mem_continuousSphereFrameSubmodule hf z
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  linarith

theorem mem_continuousSphereGreatCircleConstraintSubmodule_iff_poleAverage_centered
    (f : C(spherePoint3, ℝ)) :
    f ∈ continuousSphereGreatCircleConstraintSubmodule ↔
      ∀ z : spherePoint3,
        poleAverageLinear (sphereFrameCentered f) z =
          -((sphereFrameCentered f) z) / 2 := by
  constructor
  · intro hf z
    have hgc := (mem_continuousSphereGreatCircleConstraintSubmodule_iff f).1 hf
    rw [poleAverageLinear_apply]
    exact hgc
      (poleChoiceX z) (poleChoiceY z) z
      (poleChoice_spec z).1 (poleChoice_spec z).2.1 (poleChoice_spec z).2.2
  · intro hf
    rw [mem_continuousSphereGreatCircleConstraintSubmodule_iff]
    intro x y z hxy hxz hyz
    rw [← poleAverageLinear_eq_greatCircleAverageLinear
      (sphereFrameCentered f) x y z hxy hxz hyz]
    exact hf z

theorem mem_continuousSphereFrameSubmodule_imp_poleAverage_centered
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule) :
    ∀ z : spherePoint3,
      poleAverageLinear (sphereFrameCentered f) z =
        -((sphereFrameCentered f) z) / 2 := by
  have hgc :
      f ∈ continuousSphereGreatCircleConstraintSubmodule :=
    continuousSphereFrameSubmodule_le_continuousSphereGreatCircleConstraintSubmodule hf
  exact (mem_continuousSphereGreatCircleConstraintSubmodule_iff_poleAverage_centered f).1 hgc

theorem poleAverageLinear_spherePrecomp
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (f : C(spherePoint3, ℝ))
    (z : spherePoint3) :
    poleAverageLinear (spherePrecomp e f) z =
      poleAverageLinear f (sphereMap e z) := by
  rw [poleAverageLinear_apply, poleAverageLinear_apply]
  rw [greatCircleAverageLinear_spherePrecomp]
  exact (poleAverageLinear_eq_greatCircleAverageLinear f
    (sphereMap e (poleChoiceX z)) (sphereMap e (poleChoiceY z)) (sphereMap e z)
    (by simpa [sphereMap_inner] using (poleChoice_spec z).1)
    (by simpa [sphereMap_inner] using (poleChoice_spec z).2.1)
    (by simpa [sphereMap_inner] using (poleChoice_spec z).2.2)).symm

def poleAverageCenteredConstraintLinear :
    C(spherePoint3, ℝ) →ₗ[ℝ] (spherePoint3 → ℝ) :=
  poleAverageLinear.comp sphereFrameCenteredLinear +
    ((2 : ℝ)⁻¹ : ℝ) •
      ((ContinuousMap.coeFnLinearMap ℝ).comp sphereFrameCenteredLinear)

@[simp] theorem poleAverageCenteredConstraintLinear_apply
    (f : C(spherePoint3, ℝ)) (z : spherePoint3) :
    poleAverageCenteredConstraintLinear f z =
      poleAverageLinear (sphereFrameCentered f) z +
        ((sphereFrameCentered f) z) / 2 := by
  simp [poleAverageCenteredConstraintLinear, div_eq_mul_inv, add_comm]
  ring_nf

theorem mem_continuousSphereGreatCircleConstraintSubmodule_iff_poleAverageCenteredConstraint
    (f : C(spherePoint3, ℝ)) :
    f ∈ continuousSphereGreatCircleConstraintSubmodule ↔
      poleAverageCenteredConstraintLinear f = 0 := by
  constructor
  · intro hf
    ext z
    rw [poleAverageCenteredConstraintLinear_apply]
    have hz :=
      (mem_continuousSphereGreatCircleConstraintSubmodule_iff_poleAverage_centered f).1 hf z
    rw [hz]
    ring_nf
    simp
  · intro hf
    rw [mem_continuousSphereGreatCircleConstraintSubmodule_iff_poleAverage_centered]
    intro z
    have hz0 : poleAverageCenteredConstraintLinear f z = 0 := by
      simpa using congrArg (fun g : spherePoint3 → ℝ => g z) hf
    rw [poleAverageCenteredConstraintLinear_apply] at hz0
    linarith

theorem continuousSphereGreatCircleConstraintSubmodule_eq_ker_poleAverageCenteredConstraintLinear :
    continuousSphereGreatCircleConstraintSubmodule =
      LinearMap.ker poleAverageCenteredConstraintLinear := by
  ext f
  exact mem_continuousSphereGreatCircleConstraintSubmodule_iff_poleAverageCenteredConstraint f
