import Gleason.Harmonic.Sphere.S2FrameBridge

noncomputable section

open Complex InnerProductSpace

namespace GleasonS2Bridge

open SphericalHarmonics

def spherePoint3Rotate (ρ : Rotation) : spherePoint3 → spherePoint3 :=
  fun x => s2ToSpherePoint3 (ρ.toSphereEquiv.symm (spherePoint3ToS2 x))

lemma continuous_spherePoint3Rotate (ρ : Rotation) :
    Continuous (spherePoint3Rotate ρ) := by
  unfold spherePoint3Rotate
  exact spherePoint3EquivS2.symm.continuous.comp
    (ρ.toSphereEquiv.symm.continuous.comp spherePoint3EquivS2.continuous)

lemma coordDot_e3ToCoord (x y : E3) :
    coordDot (e3ToCoord x) (e3ToCoord y) = inner ℝ x y := by
  rw [PiLp.inner_apply]
  simp [coordDot, e3ToCoord, Fin.sum_univ_three, mul_comm]

lemma inner_spherePoint3ToS2 (x y : spherePoint3) :
    inner ℝ (spherePoint3ToS2 x : E3) (spherePoint3ToS2 y : E3) =
      inner (𝕜 := ℝ) x.1 y.1 := by
  rw [← coordDot_e3ToCoord (spherePoint3ToS2 x : E3) (spherePoint3ToS2 y : E3)]
  simpa [spherePoint3ToS2_apply] using coordDot_spherePointCoord x y

lemma inner_spherePoint3Rotate (ρ : Rotation) (x y : spherePoint3) :
    inner (𝕜 := ℝ) (spherePoint3Rotate ρ x).1 (spherePoint3Rotate ρ y).1 =
      inner (𝕜 := ℝ) x.1 y.1 := by
  calc
    inner (𝕜 := ℝ) (spherePoint3Rotate ρ x).1 (spherePoint3Rotate ρ y).1
        = inner ℝ (spherePoint3ToS2 (spherePoint3Rotate ρ x) : E3)
            (spherePoint3ToS2 (spherePoint3Rotate ρ y) : E3) := by
              symm
              exact inner_spherePoint3ToS2 (spherePoint3Rotate ρ x) (spherePoint3Rotate ρ y)
    _ = inner ℝ (ρ.toSphereEquiv.symm (spherePoint3ToS2 x) : E3)
          (ρ.toSphereEquiv.symm (spherePoint3ToS2 y) : E3) := by
            simp [spherePoint3Rotate]
    _ = inner ℝ (spherePoint3ToS2 x : E3) (spherePoint3ToS2 y : E3) := by
          change inner ℝ (ρ.symm (spherePoint3ToS2 x : E3))
              (ρ.symm (spherePoint3ToS2 y : E3)) =
            inner ℝ (spherePoint3ToS2 x : E3) (spherePoint3ToS2 y : E3)
          simpa using ρ.symm.inner_map_map
            (spherePoint3ToS2 x : E3) (spherePoint3ToS2 y : E3)
    _ = inner (𝕜 := ℝ) x.1 y.1 := inner_spherePoint3ToS2 x y

theorem isSphereFrameFunction_comp_spherePoint3Rotate
    (ρ : Rotation) {f : spherePoint3 → ℝ}
    (hf : IsSphereFrameFunction f) :
    IsSphereFrameFunction (fun x => f (spherePoint3Rotate ρ x)) := by
  intro x y z hxy hxz hyz
  have hxy' :
      inner (𝕜 := ℝ) (spherePoint3Rotate ρ x).1 (spherePoint3Rotate ρ y).1 = 0 := by
    rw [inner_spherePoint3Rotate ρ x y, hxy]
  have hxz' :
      inner (𝕜 := ℝ) (spherePoint3Rotate ρ x).1 (spherePoint3Rotate ρ z).1 = 0 := by
    rw [inner_spherePoint3Rotate ρ x z, hxz]
  have hyz' :
      inner (𝕜 := ℝ) (spherePoint3Rotate ρ y).1 (spherePoint3Rotate ρ z).1 = 0 := by
    rw [inner_spherePoint3Rotate ρ y z, hyz]
  have hE12 :
      inner (𝕜 := ℝ) (spherePoint3Rotate ρ sphereE1).1 (spherePoint3Rotate ρ sphereE2).1 = 0 := by
    rw [inner_spherePoint3Rotate ρ sphereE1 sphereE2, sphereE1_inner_sphereE2]
  have hE13 :
      inner (𝕜 := ℝ) (spherePoint3Rotate ρ sphereE1).1 (spherePoint3Rotate ρ sphereE3).1 = 0 := by
    rw [inner_spherePoint3Rotate ρ sphereE1 sphereE3, sphereE1_inner_sphereE3]
  have hE23 :
      inner (𝕜 := ℝ) (spherePoint3Rotate ρ sphereE2).1 (spherePoint3Rotate ρ sphereE3).1 = 0 := by
    rw [inner_spherePoint3Rotate ρ sphereE2 sphereE3, sphereE2_inner_sphereE3]
  have hconst :=
    hf (spherePoint3Rotate ρ sphereE1) (spherePoint3Rotate ρ sphereE2) (spherePoint3Rotate ρ sphereE3)
      hE12 hE13 hE23
  calc
    f (spherePoint3Rotate ρ x) + f (spherePoint3Rotate ρ y) + f (spherePoint3Rotate ρ z)
        = f sphereE1 + f sphereE2 + f sphereE3 := by
              exact hf (spherePoint3Rotate ρ x) (spherePoint3Rotate ρ y) (spherePoint3Rotate ρ z)
                hxy' hxz' hyz'
    _ = f (spherePoint3Rotate ρ sphereE1) +
          f (spherePoint3Rotate ρ sphereE2) +
          f (spherePoint3Rotate ρ sphereE3) := by
            symm
            exact hconst

@[simp] lemma s2Pullback_compContinuous
    (ρ : Rotation) (f : C(S2, ℝ)) :
    s2Pullback (Rotation.compContinuous ρ f) =
      ⟨fun x => s2Pullback f (spherePoint3Rotate ρ x),
        (s2Pullback f).continuous.comp (continuous_spherePoint3Rotate ρ)⟩ := by
  ext x
  simp [s2Pullback_apply, spherePoint3Rotate, Rotation.compContinuous_apply]

theorem continuousSphereFrameSubmoduleS2_invariant_under_compContinuous
    (ρ : Rotation) :
    continuousSphereFrameSubmoduleS2 ≤
      continuousSphereFrameSubmoduleS2.comap (Rotation.compContinuous ρ) := by
  intro f hf
  change s2Pullback (Rotation.compContinuous ρ f) ∈ continuousSphereFrameSubmodule
  rw [s2Pullback_compContinuous]
  exact isSphereFrameFunction_comp_spherePoint3Rotate ρ hf

end GleasonS2Bridge
