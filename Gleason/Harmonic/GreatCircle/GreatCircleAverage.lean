import Gleason.Harmonic.Rotation.ArbitraryRotation

noncomputable section

open Complex InnerProductSpace

def greatCircleAverageLinear
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    C(spherePoint3, ℝ) →ₗ[ℝ] ℝ :=
  northEquatorAverageLinear.comp (spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz))

@[simp] theorem greatCircleAverageLinear_apply
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    greatCircleAverageLinear x y z hxy hxz hyz f =
      northEquatorAverageLinear (spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) f) := by
  simp [greatCircleAverageLinear]

theorem two_mul_greatCircleAverageLinear_apply_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    2 * greatCircleAverageLinear x y z hxy hxz hyz f = f x + f y := by
  simpa [greatCircleAverageLinear_apply] using
    two_mul_northEquatorAverageLinear_spherePrecomp_sphereTripleIsometryEquiv_of_mem_continuousSphereFrameSubmodule
      hf x y z hxy hxz hyz

theorem sphereFrameCenter_spherePrecomp_sphereTripleIsometryEquiv_eq
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereFrameCenter (spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) f) =
      sphereFrameCenter f := by
  exact sphereFrameCenter_spherePrecomp_sphereTripleIsometryEquiv_of_mem_continuousSphereFrameSubmodule
    hf x y z hxy hxz hyz

theorem greatCircleAverageCentered_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    greatCircleAverageLinear x y z hxy hxz hyz (sphereFrameCentered f) =
      -((sphereFrameCentered f) z) / 2 := by
  have hcenter :
      sphereFrameCenter (spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) f) =
        sphereFrameCenter f := by
    exact sphereFrameCenter_spherePrecomp_sphereTripleIsometryEquiv_of_mem_continuousSphereFrameSubmodule
      hf x y z hxy hxz hyz
  have hcomm :
      spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) (sphereFrameCentered f) =
        sphereFrameCentered (spherePrecomp (sphereTripleIsometryEquiv x y z hxy hxz hyz) f) := by
    ext w
    simp [sphereFrameCentered_apply, spherePrecomp_apply, hcenter]
  rw [greatCircleAverageLinear_apply]
  rw [hcomm]
  rw [northEquatorAverageCLM_centered_spherePrecomp_sphereTripleIsometryEquiv_of_mem_continuousSphereFrameSubmodule
    hf x y z hxy hxz hyz]

theorem two_mul_greatCircleAverageLinear_centered_of_mem_continuousSphereFrameSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    2 * greatCircleAverageLinear x y z hxy hxz hyz (sphereFrameCentered f) =
      -((sphereFrameCentered f) z) := by
  have h :=
    greatCircleAverageCentered_of_mem_continuousSphereFrameSubmodule hf x y z hxy hxz hyz
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  linarith
