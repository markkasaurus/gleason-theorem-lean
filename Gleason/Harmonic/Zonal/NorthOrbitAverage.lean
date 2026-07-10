import Gleason.Harmonic.GreatCircle.GreatCirclePointRotation
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Group.CompactOpen
import Mathlib.Analysis.Normed.Lp.ProdLp

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

lemma northRotationOrbitContinuous (f : C(spherePoint3, ℝ)) :
    Continuous (fun t : ℝ => spherePrecomp (northRotation t) f) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have hcircle : Continuous fun p : ℝ × spherePoint3 => (((Circle.exp p.1 : Circle) : ℂ)) := by
    exact continuous_subtype_val.comp (Circle.exp.continuous.comp continuous_fst)
  have hfst : Continuous fun p : ℝ × spherePoint3 => (((Circle.exp p.1 : Circle) : ℂ) * p.2.1.fst) := by
    exact hcircle.mul
      (((WithLp.continuous_fst 2 ℂ ℝ).comp continuous_subtype_val).comp continuous_snd)
  have hsnd : Continuous fun p : ℝ × spherePoint3 => p.2.1.snd := by
    exact ((WithLp.continuous_snd 2 ℂ ℝ).comp continuous_subtype_val).comp continuous_snd
  have hcont0 :
      Continuous fun p : ℝ × spherePoint3 =>
        WithLp.toLp 2 ((((Circle.exp p.1 : Circle) : ℂ) * p.2.1.fst), p.2.1.snd) :=
    (WithLp.prod_continuous_toLp 2 ℂ ℝ).comp (hfst.prodMk hsnd)
  have hmap0 : Continuous fun p : ℝ × spherePoint3 => northRotation p.1 p.2.1 := by
    simpa [northRotation_apply] using hcont0
  have hmap : Continuous fun p : ℝ × spherePoint3 => sphereMap (northRotation p.1) p.2 := by
    exact Continuous.subtype_mk hmap0 fun p =>
      by simpa [sphereMap] using (sphereMap (northRotation p.1) p.2).2
  exact f.continuous.comp hmap

lemma northRotationOrbit_intervalIntegrable (f : C(spherePoint3, ℝ)) :
    IntervalIntegrable (fun t : ℝ => spherePrecomp (northRotation t) f) volume 0 (2 * Real.pi) := by
  exact (northRotationOrbitContinuous f).intervalIntegrable 0 (2 * Real.pi)

def northOrbitAverage (f : C(spherePoint3, ℝ)) : C(spherePoint3, ℝ) :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ t in 0..2 * Real.pi, spherePrecomp (northRotation t) f

@[simp] theorem northOrbitAverage_apply (f : C(spherePoint3, ℝ)) (x : spherePoint3) :
    northOrbitAverage f x = ((2 * Real.pi)⁻¹ : ℝ) *
      ∫ t in 0..2 * Real.pi, f (sphereMap (northRotation t) x) := by
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hInt :
      Integrable (fun t : ℝ => spherePrecomp (northRotation t) f)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    exact (northRotationOrbitContinuous f).integrableOn_Ioc
  rw [northOrbitAverage, ContinuousMap.smul_apply, smul_eq_mul]
  rw [intervalIntegral_eq_integral_uIoc]
  simp [hpi]
  rw [ContinuousMap.integral_apply hInt x]
  simp [intervalIntegral_eq_integral_uIoc, hpi, spherePrecomp_apply]

theorem northOrbitAverage_sphereE3 (f : C(spherePoint3, ℝ)) :
    northOrbitAverage f sphereE3 = f sphereE3 := by
  rw [northOrbitAverage_apply]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hconst :
      (∫ t in 0..2 * Real.pi, f (sphereMap (northRotation t) sphereE3)) =
        (2 * Real.pi) * f sphereE3 := by
    simp [sphereMap_northRotation_sphereE3]
  rw [hconst]
  field_simp [hpi.ne']

theorem northOrbitAverage_ne_zero_of_sphereE3_ne_zero
    {f : C(spherePoint3, ℝ)} (hf : f sphereE3 ≠ 0) :
    northOrbitAverage f ≠ 0 := by
  intro hzero
  apply hf
  rw [← northOrbitAverage_sphereE3 f]
  simp [hzero]

theorem northOrbitAverage_mem_continuousSphereGreatCirclePointConstraintSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereGreatCirclePointConstraintSubmodule) :
    northOrbitAverage f ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
  intro x y z hxy hxz hyz
  let L : C(spherePoint3, ℝ) →L[ℝ] ℝ := greatCirclePointConstraintCLM x y z hxy hxz hyz
  have hzero :
      ∀ t : ℝ, L (spherePrecomp (northRotation t) f) = 0 := by
    intro t
    have hmem :
        spherePrecomp (northRotation t) f ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
      exact continuousSphereGreatCirclePointConstraintSubmodule_invariant_under_spherePrecomp
        (northRotation t) hf
    simpa [L, greatCirclePointConstraintCLM_apply] using hmem x y z hxy hxz hyz
  have hcomm :=
    (ContinuousLinearMap.intervalIntegral_comp_comm L (northRotationOrbit_intervalIntegrable f)).symm
  calc
    greatCirclePointConstraintLinear x y z hxy hxz hyz (northOrbitAverage f)
      = L (((2 * Real.pi)⁻¹ : ℝ) •
          ∫ t in 0..2 * Real.pi, spherePrecomp (northRotation t) f) := by
            rfl
    _ = ((2 * Real.pi)⁻¹ : ℝ) * L (∫ t in 0..2 * Real.pi, spherePrecomp (northRotation t) f) := by
          simp
    _ = ((2 * Real.pi)⁻¹ : ℝ) *
          ∫ t in 0..2 * Real.pi, L (spherePrecomp (northRotation t) f) := by
            rw [hcomm]
    _ = 0 := by
          simp [hzero]

theorem exists_nonzero_northOrbitAverage_mem_continuousSphereGreatCirclePointConstraintSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf_mem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hf_north : f sphereE3 ≠ 0) :
    northOrbitAverage f ∈ continuousSphereGreatCirclePointConstraintSubmodule ∧
      northOrbitAverage f ≠ 0 := by
  exact ⟨northOrbitAverage_mem_continuousSphereGreatCirclePointConstraintSubmodule hf_mem,
    northOrbitAverage_ne_zero_of_sphereE3_ne_zero hf_north⟩
