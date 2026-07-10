import Gleason.Harmonic.GreatCircle.GreatCircleBasisGeneral

noncomputable section

open Complex InnerProductSpace

theorem pairSum_eq_of_same_pole_of_mem_continuousSphereGreatCirclePointConstraintSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (x y x' y' z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (hxy' : inner (𝕜 := ℝ) x'.1 y'.1 = 0)
    (hxz' : inner (𝕜 := ℝ) x'.1 z.1 = 0)
    (hyz' : inner (𝕜 := ℝ) y'.1 z.1 = 0) :
    f x + f y = f x' + f y' := by
  have hf' := (mem_continuousSphereGreatCirclePointConstraintSubmodule_iff f).1 hf
  have h0 := hf' x y z hxy hxz hyz
  have h1 := hf' x' y' z hxy' hxz' hyz'
  have havg :
      greatCircleAverageLinear x y z hxy hxz hyz f =
        greatCircleAverageLinear x' y' z hxy' hxz' hyz' f :=
    greatCircleAverageLinear_eq_of_same_pole x y x' y' z hxy hxz hyz hxy' hxz' hyz' f
  linarith

theorem pairSum_eq_of_same_pole_of_mem_continuousSphereGreatCirclePointConstraintSubmodule'
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (x y x' y' z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (hxy' : inner (𝕜 := ℝ) x'.1 y'.1 = 0)
    (hxz' : inner (𝕜 := ℝ) x'.1 z.1 = 0)
    (hyz' : inner (𝕜 := ℝ) y'.1 z.1 = 0) :
    f x + f y + f z = f x' + f y' + f z := by
  have hsum :=
    pairSum_eq_of_same_pole_of_mem_continuousSphereGreatCirclePointConstraintSubmodule
      hf x y x' y' z hxy hxz hyz hxy' hxz' hyz'
  linarith
