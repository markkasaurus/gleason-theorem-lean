import Gleason.Harmonic.Sphere.SphereSectors

noncomputable section

open Complex InnerProductSpace

def sphereE1 : spherePoint3 :=
  ⟨WithLp.toLp 2 (((1 : ℂ)), (0 : ℝ)), by simp⟩

def sphereE2 : spherePoint3 :=
  ⟨WithLp.toLp 2 ((Complex.I), (0 : ℝ)), by simp⟩

def sphereE3 : spherePoint3 :=
  ⟨WithLp.toLp 2 (((0 : ℂ)), (1 : ℝ)), by simp⟩

@[simp] lemma sphereE1_inner_sphereE2 :
    inner (𝕜 := ℝ) sphereE1.1 sphereE2.1 = 0 := by
  simp [sphereE1, sphereE2]

@[simp] lemma sphereE1_inner_sphereE3 :
    inner (𝕜 := ℝ) sphereE1.1 sphereE3.1 = 0 := by
  simp [sphereE1, sphereE3]

@[simp] lemma sphereE2_inner_sphereE3 :
    inner (𝕜 := ℝ) sphereE2.1 sphereE3.1 = 0 := by
  simp [sphereE2, sphereE3]

@[simp] lemma equatorSpherePoint_inner_sphereE3 (θ : ℝ) :
    inner (𝕜 := ℝ) (equatorSpherePoint θ).1 sphereE3.1 = 0 := by
  simp [equatorSpherePoint, sphereE3]

@[simp] lemma sphereE3_inner_equatorSpherePoint (θ : ℝ) :
    inner (𝕜 := ℝ) sphereE3.1 (equatorSpherePoint θ).1 = 0 := by
  simp [equatorSpherePoint, sphereE3]

@[simp] lemma equatorSpherePoint_inner_quarter_turn (θ : ℝ) :
    inner (𝕜 := ℝ) (equatorSpherePoint θ).1 (equatorSpherePoint (θ + Real.pi / 2)).1 = 0 := by
  simp [equatorSpherePoint, Real.cos_add, Real.sin_add]
  ring

def IsSphereFrameFunction (f : spherePoint3 → ℝ) : Prop :=
  ∀ x y z : spherePoint3,
    inner (𝕜 := ℝ) x.1 y.1 = 0 →
    inner (𝕜 := ℝ) x.1 z.1 = 0 →
    inner (𝕜 := ℝ) y.1 z.1 = 0 →
    f x + f y + f z = f sphereE1 + f sphereE2 + f sphereE3

def sphereFrameSubmodule : Submodule ℝ (spherePoint3 → ℝ) where
  carrier := {f | IsSphereFrameFunction f}
  zero_mem' := by
    intro x y z hxy hxz hyz
    simp
  add_mem' := by
    intro f g hf hg x y z hxy hxz hyz
    specialize hf x y z hxy hxz hyz
    specialize hg x y z hxy hxz hyz
    calc
      (f + g) x + (f + g) y + (f + g) z
          = (f x + f y + f z) + (g x + g y + g z) := by
              simp [Pi.add_apply]
              ring
      _ = (f sphereE1 + f sphereE2 + f sphereE3) + (g sphereE1 + g sphereE2 + g sphereE3) := by
            rw [hf, hg]
      _ = (f + g) sphereE1 + (f + g) sphereE2 + (f + g) sphereE3 := by
            simp [Pi.add_apply]
            ring
  smul_mem' := by
    intro c f hf x y z hxy hxz hyz
    specialize hf x y z hxy hxz hyz
    calc
      (c • f) x + (c • f) y + (c • f) z
          = c * (f x + f y + f z) := by
              simp [Pi.smul_apply]
              ring
      _ = c * (f sphereE1 + f sphereE2 + f sphereE3) := by rw [hf]
      _ = (c • f) sphereE1 + (c • f) sphereE2 + (c • f) sphereE3 := by
            simp [Pi.smul_apply]
            ring

def continuousSphereFrameSubmodule : Submodule ℝ C(spherePoint3, ℝ) :=
  sphereFrameSubmodule.comap (ContinuousMap.coeFnLinearMap ℝ)

lemma sphereFrameFunction_equator_circleFrame
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f) :
    circleFrameFunction (equatorRestrictionFromSphereLinear f) := by
  refine ⟨f sphereE1 + f sphereE2, ?_⟩
  intro θ
  have hsum :=
    hf (equatorSpherePoint θ) (equatorSpherePoint (θ + Real.pi / 2)) sphereE3
      (equatorSpherePoint_inner_quarter_turn θ)
      (equatorSpherePoint_inner_sphereE3 θ)
      (equatorSpherePoint_inner_sphereE3 (θ + Real.pi / 2))
  have hsum' := congrArg (fun t : ℝ => t - f sphereE3) hsum
  simpa [equatorRestrictionFromSphereLinear] using hsum'

theorem sphereFrameSubmodule_le_equatorFrameAdmissible :
    sphereFrameSubmodule ≤
      (frameAdmissibleCircleSubmodule.comap equatorRestrictionFromSphereLinear) := by
  intro f hf
  exact sphereFrameFunction_equator_circleFrame hf

theorem not_harmonicSphereDegreeSubmodule_le_sphereFrameSubmodule_of_mod_ne_two
    {n : ℕ} (hn : 0 < n) (hmod : n % 4 ≠ 2) :
    ¬ harmonicSphereDegreeSubmodule n ≤ sphereFrameSubmodule := by
  intro hle
  let f : WithLp 2 (ℂ × ℝ) → ℝ := surfaceModeAL2 n
  have hfmem : sphereRestrictionLinear f ∈ harmonicSphereDegreeSubmodule n := by
    refine ⟨f, ?_, rfl⟩
    exact ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩
  have hsphere : sphereRestrictionLinear f ∈ sphereFrameSubmodule := hle hfmem
  have hcircleSphere :
      sphereRestrictionLinear f ∈
        frameAdmissibleCircleSubmodule.comap equatorRestrictionFromSphereLinear :=
    sphereFrameSubmodule_le_equatorFrameAdmissible hsphere
  have hcircle : circleFrameFunction (equatorRestrictionL2 f) := by
    simpa [equatorRestrictionFromSphere_sphereRestriction] using hcircleSphere
  exact
    surfaceModeAL2_not_circleFrame_of_mod_ne_two (n := n) hn hmod hcircle

theorem not_harmonicSphereDegreeSubmodule_one_le_sphereFrameSubmodule :
    ¬ harmonicSphereDegreeSubmodule 1 ≤ sphereFrameSubmodule := by
  apply not_harmonicSphereDegreeSubmodule_le_sphereFrameSubmodule_of_mod_ne_two
  · norm_num
  · norm_num

theorem not_harmonicSphereDegreeSubmodule_gt_two_le_sphereFrameSubmodule {n : ℕ} (hn : 2 < n) :
    ¬ harmonicSphereDegreeSubmodule n ≤ sphereFrameSubmodule := by
  intro hle
  have hle' :
      harmonicSphereDegreeSubmodule n ≤
        (frameAdmissibleCircleSubmodule.comap equatorRestrictionFromSphereLinear) := by
    intro f hf
    exact sphereFrameSubmodule_le_equatorFrameAdmissible (hle hf)
  exact not_harmonicSphereDegreeSubmodule_le_frameAdmissible hn hle'
