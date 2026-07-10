import Gleason.Harmonic.GreatCircle.GreatCircleConstraints
import Gleason.Harmonic.Sphere.SphereCoordsAlgebra
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

noncomputable section

open Complex InnerProductSpace Real

lemma sphereFrameCenter_norm_le (f : C(spherePoint3, ℝ)) :
    ‖sphereFrameCenter f‖ ≤ ‖f‖ := by
  rw [sphereFrameCenter]
  have h1 : ‖f sphereE1‖ ≤ ‖f‖ := f.norm_coe_le_norm sphereE1
  have h2 : ‖f sphereE2‖ ≤ ‖f‖ := f.norm_coe_le_norm sphereE2
  have h3 : ‖f sphereE3‖ ≤ ‖f‖ := f.norm_coe_le_norm sphereE3
  have hsum : ‖f sphereE1 + f sphereE2 + f sphereE3‖ ≤ 3 * ‖f‖ := by
    calc
      ‖f sphereE1 + f sphereE2 + f sphereE3‖
        ≤ ‖f sphereE1 + f sphereE2‖ + ‖f sphereE3‖ := by
            simpa [add_assoc] using norm_add_le (f sphereE1 + f sphereE2) (f sphereE3)
      _ ≤ (‖f sphereE1‖ + ‖f sphereE2‖) + ‖f sphereE3‖ := by
            gcongr
            exact norm_add_le (f sphereE1) (f sphereE2)
      _ ≤ (‖f‖ + ‖f‖) + ‖f‖ := by gcongr
      _ = 3 * ‖f‖ := by ring
  have hthree : (0 : ℝ) < 3 := by norm_num
  have hnormInv : ‖(3 : ℝ)⁻¹‖ = (3 : ℝ)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hthree)]
  calc
    ‖(f sphereE1 + f sphereE2 + f sphereE3) / 3‖
      = ‖f sphereE1 + f sphereE2 + f sphereE3‖ * (3 : ℝ)⁻¹ := by
          rw [div_eq_mul_inv, norm_mul, hnormInv]
    _ ≤ (3 * ‖f‖) * (3 : ℝ)⁻¹ := by gcongr
    _ = ‖f‖ := by
          ring

def sphereFrameCenterCLM : C(spherePoint3, ℝ) →L[ℝ] ℝ :=
  sphereFrameCenterLinear.mkContinuous 1 <| by
    intro f
    simpa [one_mul, sphereFrameCenterLinear_apply] using sphereFrameCenter_norm_le f

@[simp] theorem sphereFrameCenterCLM_apply (f : C(spherePoint3, ℝ)) :
    sphereFrameCenterCLM f = sphereFrameCenter f := by
  simp [sphereFrameCenterCLM, LinearMap.mkContinuous_apply]

def sphereFrameCenteredCLM : C(spherePoint3, ℝ) →L[ℝ] C(spherePoint3, ℝ) :=
  sphereFrameCenteredLinear.mkContinuous 2 <| by
    intro f
    haveI : Nonempty spherePoint3 := ⟨sphereE1⟩
    change ‖sphereFrameCentered f‖ ≤ 2 * ‖f‖
    refine (ContinuousMap.norm_le_of_nonempty (f := sphereFrameCentered f) (M := 2 * ‖f‖)).2 ?_
    intro x
    rw [sphereFrameCentered_apply]
    have hcenter : ‖sphereFrameCenter f‖ ≤ ‖f‖ := sphereFrameCenter_norm_le f
    calc
      ‖f x - sphereFrameCenter f‖ ≤ ‖f x‖ + ‖sphereFrameCenter f‖ := norm_sub_le _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm x) hcenter
      _ = 2 * ‖f‖ := by ring

@[simp] theorem sphereFrameCenteredCLM_apply (f : C(spherePoint3, ℝ)) :
    sphereFrameCenteredCLM f = sphereFrameCentered f := by
  simp [sphereFrameCenteredCLM, LinearMap.mkContinuous_apply]

def northEquatorAverageCLM : C(spherePoint3, ℝ) →L[ℝ] ℝ :=
  northEquatorAverageLinear.mkContinuous 1 <| by
    intro f
    rw [one_mul, northEquatorAverageLinear_apply]
    have hpi : 0 < 2 * Real.pi := by positivity
    have hInt :
        ‖∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ)‖ ≤ ‖f‖ * |2 * Real.pi - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro θ hθ
      exact f.norm_coe_le_norm (equatorSpherePoint θ)
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpi)]
    calc
      (2 * Real.pi)⁻¹ * ‖∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ)‖
        ≤ (2 * Real.pi)⁻¹ * (‖f‖ * |2 * Real.pi - 0|) := by
            gcongr
      _ = ‖f‖ := by
            rw [sub_zero, abs_of_pos hpi]
            field_simp [hpi.ne']

@[simp] theorem northEquatorAverageCLM_apply (f : C(spherePoint3, ℝ)) :
    northEquatorAverageCLM f = northEquatorAverageLinear f := by
  simp [northEquatorAverageCLM, LinearMap.mkContinuous_apply]

def spherePrecompCLM
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    C(spherePoint3, ℝ) →L[ℝ] C(spherePoint3, ℝ) :=
  (spherePrecomp e).mkContinuous 1 <| by
    intro f
    haveI : Nonempty spherePoint3 := ⟨sphereE1⟩
    rw [one_mul]
    refine (ContinuousMap.norm_le_of_nonempty (f := spherePrecomp e f) (M := ‖f‖)).2 ?_
    intro x
    simpa [spherePrecomp_apply] using f.norm_coe_le_norm (sphereMap e x)

@[simp] theorem spherePrecompCLM_apply
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (f : C(spherePoint3, ℝ)) :
    spherePrecompCLM e f = spherePrecomp e f := by
  simp [spherePrecompCLM, LinearMap.mkContinuous_apply]

def greatCircleAverageCLM
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    C(spherePoint3, ℝ) →L[ℝ] ℝ :=
  northEquatorAverageCLM.comp
    (spherePrecompCLM (sphereTripleIsometryEquiv x y z hxy hxz hyz))

@[simp] theorem greatCircleAverageCLM_apply
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    greatCircleAverageCLM x y z hxy hxz hyz f =
      greatCircleAverageLinear x y z hxy hxz hyz f := by
  simp [greatCircleAverageCLM, greatCircleAverageLinear_apply]

def greatCircleCenteredConstraintCLM
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    C(spherePoint3, ℝ) →L[ℝ] ℝ :=
  (greatCircleAverageCLM x y z hxy hxz hyz).comp sphereFrameCenteredCLM +
    ((2 : ℝ)⁻¹ : ℝ) •
      ((ContinuousMap.evalCLM ℝ z).comp sphereFrameCenteredCLM)

@[simp] theorem greatCircleCenteredConstraintCLM_apply
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    greatCircleCenteredConstraintCLM x y z hxy hxz hyz f =
      greatCircleCenteredConstraintLinear x y z hxy hxz hyz f := by
  simp [greatCircleCenteredConstraintCLM, greatCircleCenteredConstraintLinear,
    greatCircleAverageCLM_apply, sphereFrameCenteredCLM_apply, add_comm]

lemma isClosed_setOf_greatCircleCenteredConstraint
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    IsClosed {f : C(spherePoint3, ℝ) |
      greatCircleCenteredConstraintLinear x y z hxy hxz hyz f = 0} := by
  have hEq :
      {f : C(spherePoint3, ℝ) |
        greatCircleCenteredConstraintLinear x y z hxy hxz hyz f = 0} =
      (greatCircleCenteredConstraintCLM x y z hxy hxz hyz) ⁻¹' ({0} : Set ℝ) := by
    ext f
    simp [greatCircleCenteredConstraintCLM_apply]
  rw [hEq]
  simpa using isClosed_singleton.preimage (greatCircleCenteredConstraintCLM x y z hxy hxz hyz).continuous

theorem isClosed_continuousSphereGreatCircleConstraintSubmodule :
    IsClosed (continuousSphereGreatCircleConstraintSubmodule : Set C(spherePoint3, ℝ)) := by
  have hEq :
      (continuousSphereGreatCircleConstraintSubmodule : Set C(spherePoint3, ℝ)) =
        ⋂ x : spherePoint3, ⋂ y : spherePoint3, ⋂ z : spherePoint3,
          ⋂ hxy : inner (𝕜 := ℝ) x.1 y.1 = 0,
            ⋂ hxz : inner (𝕜 := ℝ) x.1 z.1 = 0,
              ⋂ hyz : inner (𝕜 := ℝ) y.1 z.1 = 0,
                {f : C(spherePoint3, ℝ) |
                  greatCircleCenteredConstraintLinear x y z hxy hxz hyz f = 0} := by
    ext f
    simp [continuousSphereGreatCircleConstraintSubmodule]
  rw [hEq]
  exact isClosed_iInter fun x =>
    isClosed_iInter fun y =>
      isClosed_iInter fun z =>
        isClosed_iInter fun hxy =>
          isClosed_iInter fun hxz =>
            isClosed_iInter fun hyz =>
              isClosed_setOf_greatCircleCenteredConstraint x y z hxy hxz hyz

def continuousSphereGreatCircleConstraintClosedSubmodule :
    ClosedSubmodule ℝ C(spherePoint3, ℝ) :=
  ⟨continuousSphereGreatCircleConstraintSubmodule,
    isClosed_continuousSphereGreatCircleConstraintSubmodule⟩
