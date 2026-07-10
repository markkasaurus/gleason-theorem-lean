import Gleason.Harmonic.Auxiliary.EquatorAverage
import Gleason.Harmonic.Rotation.RotationEquiv
import Mathlib.Analysis.Complex.Isometry

noncomputable section

open Complex InnerProductSpace

def northRotationLinearEquiv (a : Circle) :
    WithLp 2 (ℂ × ℝ) ≃ₗ[ℝ] WithLp 2 (ℂ × ℝ) :=
  (WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).trans
      (((rotation a).toLinearEquiv).prodCongr (LinearEquiv.refl ℝ ℝ))
    |>.trans (WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).symm

@[simp] lemma northRotationLinearEquiv_apply
    (a : Circle) (x : WithLp 2 (ℂ × ℝ)) :
    northRotationLinearEquiv a x = WithLp.toLp 2 (a * x.fst, x.snd) := by
  simp [northRotationLinearEquiv]

def northRotation (t : ℝ) : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ) :=
  ⟨northRotationLinearEquiv (Circle.exp t), by
    intro x
    rw [northRotationLinearEquiv_apply, WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
    simp⟩

@[simp] lemma northRotation_apply
    (t : ℝ) (x : WithLp 2 (ℂ × ℝ)) :
    northRotation t x = WithLp.toLp 2 (((Circle.exp t : Circle) : ℂ) * x.fst, x.snd) := by
  simp [northRotation]

@[simp] lemma sphereMap_northRotation_sphereE3
    (t : ℝ) :
    sphereMap (northRotation t) sphereE3 = sphereE3 := by
  apply Subtype.ext
  simp [sphereMap, sphereE3, northRotation_apply]

@[simp] lemma sphereMap_northRotation_equatorSpherePoint
    (t θ : ℝ) :
    sphereMap (northRotation t) (equatorSpherePoint θ) =
      equatorSpherePoint (θ + t) := by
  apply Subtype.ext
  simp [sphereMap, equatorSpherePoint, northRotation_apply]
  calc
    Complex.exp (t * Complex.I) * (Complex.cos θ + Complex.I * Complex.sin θ)
        = Complex.exp (t * Complex.I) * Complex.exp (θ * Complex.I) := by
            congr 1
            rw [Complex.exp_mul_I]
            ring
    _ = Complex.exp ((t + θ) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          ring
    _ = (Complex.cos (θ + t) + Complex.I * Complex.sin (θ + t)) := by
          rw [Complex.exp_mul_I]
          ring_nf

theorem northEquatorAverage_shift
    (f : C(spherePoint3, ℝ)) (t : ℝ) :
    ∫ θ in 0..2 * Real.pi, f (equatorSpherePoint (θ + t)) =
      ∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ) := by
  rw [intervalIntegral.integral_comp_add_right
      (fun θ ↦ f (equatorSpherePoint θ)) t]
  simpa [zero_add, add_assoc, add_left_comm, add_comm] using
    (equatorRestrictionFromSphere_periodic (f := (f : spherePoint3 → ℝ))).intervalIntegral_add_eq
      t 0

theorem northEquatorAverageLinear_spherePrecomp_northRotation
    (f : C(spherePoint3, ℝ)) (t : ℝ) :
    northEquatorAverageLinear (spherePrecomp (northRotation t) f) =
      northEquatorAverageLinear f := by
  rw [northEquatorAverageLinear_apply, northEquatorAverageLinear_apply]
  have hshift := northEquatorAverage_shift f t
  simpa [spherePrecomp_apply, sphereMap_northRotation_equatorSpherePoint] using
    congrArg (fun s : ℝ => (2 * Real.pi)⁻¹ * s) hshift

theorem sphereFrameCenter_spherePrecomp_northRotation_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (t : ℝ) :
    sphereFrameCenter (spherePrecomp (northRotation t) f) = sphereFrameCenter f := by
  have hframe : IsSphereFrameFunction (f : spherePoint3 → ℝ) := hf
  have h12 :
      inner (𝕜 := ℝ) (sphereMap (northRotation t) sphereE1).1
          (sphereMap (northRotation t) sphereE2).1 = 0 := by
    simpa [sphereMap_inner] using
      (sphereMap_inner (northRotation t) sphereE1 sphereE2).trans sphereE1_inner_sphereE2
  have h13 :
      inner (𝕜 := ℝ) (sphereMap (northRotation t) sphereE1).1
          (sphereMap (northRotation t) sphereE3).1 = 0 := by
    simpa [sphereMap_inner] using
      (sphereMap_inner (northRotation t) sphereE1 sphereE3).trans sphereE1_inner_sphereE3
  have h23 :
      inner (𝕜 := ℝ) (sphereMap (northRotation t) sphereE2).1
          (sphereMap (northRotation t) sphereE3).1 = 0 := by
    simpa [sphereMap_inner] using
      (sphereMap_inner (northRotation t) sphereE2 sphereE3).trans sphereE2_inner_sphereE3
  have hsum :=
    hframe (sphereMap (northRotation t) sphereE1)
      (sphereMap (northRotation t) sphereE2)
      (sphereMap (northRotation t) sphereE3) h12 h13 h23
  unfold sphereFrameCenter
  simp [spherePrecomp_apply, sphereMap_northRotation_sphereE3] at hsum ⊢
  linarith

theorem northEquatorAverageCLM_centered_spherePrecomp_northRotation_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (t : ℝ) :
    northEquatorAverageLinear (sphereFrameCentered (spherePrecomp (northRotation t) f)) =
      northEquatorAverageLinear (sphereFrameCentered f) := by
  have hmem :
      spherePrecomp (northRotation t) f ∈ continuousSphereFrameSubmodule := by
    exact continuousSphereFrameSubmodule_invariant_under_spherePrecomp (northRotation t) hf
  rw [northEquatorAverageCLM_centered_of_mem_continuousSphereFrameSubmodule hmem,
    northEquatorAverageCLM_centered_of_mem_continuousSphereFrameSubmodule hf]
  rw [sphereFrameCentered_apply, sphereFrameCentered_apply]
  simp [sphereMap_northRotation_sphereE3, spherePrecomp_apply,
    sphereFrameCenter_spherePrecomp_northRotation_of_mem_continuousSphereFrameSubmodule hf]
