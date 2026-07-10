import Gleason.Continuity.Auxiliary.ClosedFrame
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

noncomputable section

open Complex InnerProductSpace

local instance : ProperSpace (WithLp 2 (ℂ × ℝ)) := by
  infer_instance

def spherePoint3HomeomorphSphere :
    spherePoint3 ≃ₜ Metric.sphere (0 : WithLp 2 (ℂ × ℝ)) 1 where
  toEquiv :=
    { toFun := fun x => ⟨x.1, by simpa [Metric.mem_sphere, dist_eq_norm] using x.2⟩
      invFun := fun x => ⟨x.1, by simpa [Metric.mem_sphere, dist_eq_norm] using x.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; cases x; rfl }
  continuous_toFun := continuous_subtype_val.subtype_mk fun x =>
    by simpa [Metric.mem_sphere, dist_eq_norm] using x.2
  continuous_invFun := continuous_subtype_val.subtype_mk fun x =>
    by simpa [Metric.mem_sphere, dist_eq_norm] using x.2

instance : CompactSpace spherePoint3 :=
  letI : CompactSpace (Metric.sphere (0 : WithLp 2 (ℂ × ℝ)) 1) :=
    Metric.sphere.compactSpace _ _
  Homeomorph.compactSpace spherePoint3HomeomorphSphere.symm

def sphereCoordRe : C(spherePoint3, ℝ) where
  toFun x := x.1.fst.re
  continuous_toFun := continuous_re.comp <|
    WithLp.continuous_fst 2 ℂ ℝ |>.comp continuous_subtype_val

def sphereCoordIm : C(spherePoint3, ℝ) where
  toFun x := x.1.fst.im
  continuous_toFun := continuous_im.comp <|
    WithLp.continuous_fst 2 ℂ ℝ |>.comp continuous_subtype_val

def sphereCoordZ : C(spherePoint3, ℝ) where
  toFun x := x.1.snd
  continuous_toFun := WithLp.continuous_snd 2 ℂ ℝ |>.comp continuous_subtype_val

def sphereCoordinateSubalgebra : Subalgebra ℝ C(spherePoint3, ℝ) :=
  Algebra.adjoin ℝ ({sphereCoordRe, sphereCoordIm, sphereCoordZ} : Set C(spherePoint3, ℝ))

theorem sphereCoordinateSubalgebra_separatesPoints :
    sphereCoordinateSubalgebra.SeparatesPoints := by
  intro x y hxy
  by_cases hRe : sphereCoordRe x ≠ sphereCoordRe y
  · refine ⟨sphereCoordRe, ⟨sphereCoordRe, Algebra.subset_adjoin ?_, rfl⟩, hRe⟩
    simp [sphereCoordinateSubalgebra]
  by_cases hIm : sphereCoordIm x ≠ sphereCoordIm y
  · refine ⟨sphereCoordIm, ⟨sphereCoordIm, Algebra.subset_adjoin ?_, rfl⟩, hIm⟩
    simp [sphereCoordinateSubalgebra]
  by_cases hZ : sphereCoordZ x ≠ sphereCoordZ y
  · refine ⟨sphereCoordZ, ⟨sphereCoordZ, Algebra.subset_adjoin ?_, rfl⟩, hZ⟩
    simp [sphereCoordinateSubalgebra]
  exfalso
  have hReEq : sphereCoordRe x = sphereCoordRe y := by exact not_not.mp hRe
  have hImEq : sphereCoordIm x = sphereCoordIm y := by exact not_not.mp hIm
  have hZEq : sphereCoordZ x = sphereCoordZ y := by exact not_not.mp hZ
  apply hxy
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  change (x.1.fst, x.1.snd) = (y.1.fst, y.1.snd)
  refine Prod.ext ?_ ?_
  · apply Complex.ext
    · simpa [sphereCoordRe] using hReEq
    · simpa [sphereCoordIm] using hImEq
  · simpa [sphereCoordZ] using hZEq

theorem sphereCoordinateSubalgebra_closure_eq_top :
    sphereCoordinateSubalgebra.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    sphereCoordinateSubalgebra sphereCoordinateSubalgebra_separatesPoints
