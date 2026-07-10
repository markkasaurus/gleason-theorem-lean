import Gleason.Continuity.Auxiliary.ClosedFrame
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section

open Complex InnerProductSpace

lemma continuous_equatorSpherePoint : Continuous equatorSpherePoint := by
  let base : ℝ → WithLp 2 (ℂ × ℝ) :=
    fun θ => WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), (0 : ℝ))
  have hbase : Continuous base := by
    change Continuous (fun θ : ℝ =>
      WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), (0 : ℝ)))
    continuity
  have hnorm : ∀ θ, ‖base θ‖ = 1 := by
    intro θ
    simpa [base, equatorSpherePoint] using (equatorSpherePoint θ).2
  let lift : ℝ → spherePoint3 := fun θ => ⟨base θ, hnorm θ⟩
  have hlift : Continuous lift := Continuous.subtype_mk hbase fun θ => hnorm θ
  have hEq : equatorSpherePoint = lift := by
    funext θ
    apply Subtype.ext
    rfl
  simpa [hEq] using hlift

@[simp] lemma equatorSpherePoint_add_two_pi (θ : ℝ) :
    equatorSpherePoint (θ + 2 * Real.pi) = equatorSpherePoint θ := by
  apply Subtype.ext
  simp [equatorSpherePoint, Real.cos_add, Real.sin_add]

lemma equatorRestrictionFromSphere_periodic (f : spherePoint3 → ℝ) :
    Function.Periodic (equatorRestrictionFromSphereLinear f) (2 * Real.pi) := by
  intro θ
  simp [equatorRestrictionFromSphereLinear, equatorSpherePoint_add_two_pi]

def northEquatorAverageLinear : C(spherePoint3, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ)
  map_add' := by
    intro f g
    have hf :
        IntervalIntegrable (fun θ : ℝ => f (equatorSpherePoint θ))
          MeasureTheory.volume 0 (2 * Real.pi) :=
      (f.continuous.comp continuous_equatorSpherePoint).intervalIntegrable _ _
    have hg :
        IntervalIntegrable (fun θ : ℝ => g (equatorSpherePoint θ))
          MeasureTheory.volume 0 (2 * Real.pi) :=
      (g.continuous.comp continuous_equatorSpherePoint).intervalIntegrable _ _
    change (2 * Real.pi)⁻¹ *
        ∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ) + g (equatorSpherePoint θ) =
      ((2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ)) +
        ((2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, g (equatorSpherePoint θ))
    rw [intervalIntegral.integral_add hf hg]
    ring_nf
  map_smul' := by
    intro c f
    simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    ring_nf

@[simp] theorem northEquatorAverageLinear_apply
    (f : C(spherePoint3, ℝ)) :
    northEquatorAverageLinear f =
      (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ) := by
  rfl

@[simp] theorem northEquatorAverageLinear_const (c : ℝ) :
    northEquatorAverageLinear (ContinuousMap.const _ c) = c := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  rw [northEquatorAverageLinear_apply]
  change (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, c = c
  rw [intervalIntegral.integral_const]
  field_simp [hpi]
  simp [smul_eq_mul, mul_comm]

theorem northEquatorAverage_shift_quarter
    (f : C(spherePoint3, ℝ)) :
    ∫ θ in 0..2 * Real.pi, f (equatorSpherePoint (θ + Real.pi / 2)) =
      ∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ) := by
  rw [intervalIntegral.integral_comp_add_right
      (fun θ ↦ f (equatorSpherePoint θ)) (Real.pi / 2)]
  simpa [zero_add, add_assoc, add_left_comm, add_comm] using
    (equatorRestrictionFromSphere_periodic (f := (f : spherePoint3 → ℝ))).intervalIntegral_add_eq
      (Real.pi / 2) 0

theorem two_mul_northEquatorAverageLinear_apply_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule) :
    2 * northEquatorAverageLinear f = f sphereE1 + f sphereE2 := by
  let g : ℝ → ℝ := equatorRestrictionFromSphereLinear (f : spherePoint3 → ℝ)
  have hframe : IsSphereFrameFunction (f : spherePoint3 → ℝ) := hf
  have hsum : ∀ θ : ℝ, g θ + g (θ + Real.pi / 2) = f sphereE1 + f sphereE2 := by
    intro θ
    have h :=
      hframe (equatorSpherePoint θ) (equatorSpherePoint (θ + Real.pi / 2)) sphereE3
        (equatorSpherePoint_inner_quarter_turn θ)
        (equatorSpherePoint_inner_sphereE3 θ)
        (equatorSpherePoint_inner_sphereE3 (θ + Real.pi / 2))
    exact add_right_cancel (by simpa [g, equatorRestrictionFromSphereLinear, add_assoc] using h)
  have hcont_g : Continuous g := f.continuous.comp continuous_equatorSpherePoint
  have hint_g :
      IntervalIntegrable g MeasureTheory.volume 0 (2 * Real.pi) :=
    hcont_g.intervalIntegrable _ _
  have hcont_shift : Continuous (fun θ : ℝ => g (θ + Real.pi / 2)) :=
    hcont_g.comp (continuous_id.add continuous_const)
  have hint_shift :
      IntervalIntegrable (fun θ : ℝ => g (θ + Real.pi / 2)) MeasureTheory.volume 0 (2 * Real.pi) :=
    hcont_shift.intervalIntegrable _ _
  have hint_eq :=
    congrArg (fun h : ℝ → ℝ => ∫ θ in 0..2 * Real.pi, h θ) (funext hsum)
  change ∫ θ in 0..2 * Real.pi, g θ + g (θ + Real.pi / 2) =
      ∫ θ in 0..2 * Real.pi, (f sphereE1 + f sphereE2) at hint_eq
  rw [intervalIntegral.integral_add hint_g hint_shift] at hint_eq
  have hshift_eq :
      ∫ θ in 0..2 * Real.pi, g (θ + Real.pi / 2) =
        ∫ θ in 0..2 * Real.pi, g θ := by
    simpa [g, equatorRestrictionFromSphereLinear] using northEquatorAverage_shift_quarter f
  rw [hshift_eq] at hint_eq
  have hI :
      2 * ∫ θ in 0..2 * Real.pi, g θ =
        (2 * Real.pi) * f sphereE1 + (2 * Real.pi) * f sphereE2 := by
    simpa [two_mul, intervalIntegral.integral_const, add_mul] using hint_eq
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hI' := congrArg (fun t : ℝ => (2 * Real.pi)⁻¹ * t) hI
  rw [northEquatorAverageLinear_apply]
  ring_nf at hI' ⊢
  simpa [g, equatorRestrictionFromSphereLinear, hpi] using hI'

def sphereFrameCenter (f : C(spherePoint3, ℝ)) : ℝ :=
  (f sphereE1 + f sphereE2 + f sphereE3) / 3

def sphereFrameCentered (f : C(spherePoint3, ℝ)) : C(spherePoint3, ℝ) :=
  f - ContinuousMap.const _ (sphereFrameCenter f)

@[simp] theorem sphereFrameCentered_apply
    (f : C(spherePoint3, ℝ)) (x : spherePoint3) :
    sphereFrameCentered f x = f x - sphereFrameCenter f := by
  rfl

theorem northEquatorAverageCLM_centered_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule) :
    northEquatorAverageLinear (sphereFrameCentered f) =
      -((sphereFrameCentered f) sphereE3) / 2 := by
  have hconst_mem : ContinuousMap.const _ (sphereFrameCenter f) ∈ continuousSphereFrameSubmodule := by
    show IsSphereFrameFunction fun _ : spherePoint3 => sphereFrameCenter f
    intro x y z hxy hxz hyz
    simp [sphereFrameCenter]
  have hcenter_mem : sphereFrameCentered f ∈ continuousSphereFrameSubmodule := by
    exact continuousSphereFrameSubmodule.sub_mem hf hconst_mem
  have havg :
      2 * northEquatorAverageLinear (sphereFrameCentered f) =
        sphereFrameCentered f sphereE1 + sphereFrameCentered f sphereE2 :=
    two_mul_northEquatorAverageLinear_apply_of_mem_continuousSphereFrameSubmodule hcenter_mem
  have hsum0 :
      sphereFrameCentered f sphereE1 +
          sphereFrameCentered f sphereE2 +
          sphereFrameCentered f sphereE3 = 0 := by
    simp [sphereFrameCentered, sphereFrameCenter]
    ring
  have hcenter :
      2 * northEquatorAverageLinear (sphereFrameCentered f) =
        -(sphereFrameCentered f sphereE3) := by
    have hneg :
        sphereFrameCentered f sphereE1 + sphereFrameCentered f sphereE2 =
          -(sphereFrameCentered f sphereE3) := by
      linarith
    exact havg.trans hneg
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  apply (eq_div_iff htwo).2
  linarith
