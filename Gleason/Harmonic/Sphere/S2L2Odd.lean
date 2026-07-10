import Gleason.Harmonic.Sphere.S2L2Frame
import Gleason.Harmonic.Sphere.S2L2ToContinuous
import Gleason.Harmonic.Sphere.SphericalBridge
import Gleason.Continuity.Auxiliary.FrameEven
import Gleason.Harmonic.Zonal.NorthZonalParity
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

noncomputable section

namespace GleasonS2Bridge

open SphericalHarmonics

noncomputable def antipodeRotation : Rotation :=
  LinearIsometryEquiv.neg ℝ

noncomputable def s2Antipode : S2 → S2 :=
  Rotation.toSphere antipodeRotation

@[simp] theorem antipodeRotation_symm :
    antipodeRotation.symm = antipodeRotation := by
  ext x i
  fin_cases i <;> simp [antipodeRotation]

@[simp] theorem s2Antipode_apply_val (x : S2) :
    ((s2Antipode x : S2) : E3) = -(x : E3) := rfl

@[simp] theorem spherePoint3ToS2_sphereAntipode (x : spherePoint3) :
    spherePoint3ToS2 (sphereAntipode x) = s2Antipode (spherePoint3ToS2 x) := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [spherePoint3ToS2, sphereAntipode, sphereMap, s2Antipode, antipodeRotation,
      coordToE3, spherePointCoord, sphereCoordVec, sphereCoordRe, sphereCoordIm, sphereCoordZ]

@[simp] theorem s2ToSpherePoint3_s2Antipode (x : S2) :
    s2ToSpherePoint3 (s2Antipode x) = sphereAntipode (s2ToSpherePoint3 x) := by
  apply spherePointCoord_injective
  ext <;>
    simp [s2ToSpherePoint3, s2Antipode, antipodeRotation, sphereAntipode, spherePointCoord,
      ambientPointOfCoords, sphereCoordVec, sphereCoordRe, sphereCoordIm, sphereCoordZ, e3ToCoord]

@[simp] theorem spherePoint3Rotate_antipodeRotation (x : spherePoint3) :
    spherePoint3Rotate antipodeRotation x = sphereAntipode x := by
  simpa [spherePoint3Rotate, s2Antipode, antipodeRotation_symm] using
    (s2ToSpherePoint3_s2Antipode (spherePoint3ToS2 x))

@[simp] theorem s2Pullback_compContinuous_antipode
    (f : C(S2, ℝ)) :
    s2Pullback (Rotation.compContinuous antipodeRotation f) =
      spherePrecomp (LinearIsometryEquiv.neg ℝ) (s2Pullback f) := by
  ext x
  change f (s2Antipode (spherePoint3ToS2 x)) =
    f (spherePoint3ToS2 (sphereAntipode x))
  rw [spherePoint3ToS2_sphereAntipode]

theorem mem_continuousSphereFrameSubmoduleS2_even
    {f : C(S2, ℝ)} (hf : f ∈ continuousSphereFrameSubmoduleS2) (x : S2) :
    f (s2Antipode x) = f x := by
  have hpull :
      s2Pullback (Rotation.compContinuous antipodeRotation f) =
        s2Pullback f := by
    ext y
    simpa [s2Pullback_compContinuous_antipode, spherePrecomp_apply] using
      mem_continuousSphereFrameSubmodule_even hf y
  have hEq : Rotation.compContinuous antipodeRotation f = f := by
    exact s2Pullback.injective hpull
  simpa [Rotation.compContinuous_apply, s2Antipode, antipodeRotation] using
    congrArg (fun g : C(S2, ℝ) => g x) hEq

theorem sector_compContinuous_antipode
    {n : ℕ} {f : C(S2, ℝ)} (hf : f ∈ sector n) :
    Rotation.compContinuous antipodeRotation f = (-1 : ℝ) ^ n • f := by
  apply s2Pullback.injective
  have hpull : s2Pullback f ∈ continuousHarmonicSphereDegreeSubmodule n :=
    s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule hf
  ext x
  calc
    s2Pullback (Rotation.compContinuous antipodeRotation f) x
        = (s2Pullback f) (sphereAntipode x) := by
            simp [s2Pullback_compContinuous_antipode, spherePrecomp_apply]
    _ = (-1 : ℝ) ^ n * (s2Pullback f) x :=
          sphereRestriction_sphereNeg_of_mem_continuousHarmonicSphereDegreeSubmodule hpull x
    _ = s2Pullback (((-1 : ℝ) ^ n) • f) x := by
          simp [s2Pullback_apply]

theorem compL2Rotation_antipode_eq_self_of_mem_continuousSphereFrameImageL2S2
    {x : L2S2Geom} (hx : x ∈ continuousSphereFrameImageL2S2) :
    Rotation.compL2Rotation antipodeRotation x = x := by
  rcases hx with ⟨f, hf, rfl⟩
  calc
    Rotation.compL2Rotation antipodeRotation (continuousToLp f)
        = continuousToLp (Rotation.compContinuous antipodeRotation f) := by
            simpa using continuousToLp_compContinuous_symm antipodeRotation f
    _ = continuousToLp f := by
          congr
          ext y
          exact mem_continuousSphereFrameSubmoduleS2_even hf y

theorem compL2Rotation_antipode_eq_self_of_mem_continuousSphereFrameClosedSubmoduleL2S2
    {x : L2S2Geom} (hx : x ∈ continuousSphereFrameClosedSubmoduleL2S2.toSubmodule) :
    Rotation.compL2Rotation antipodeRotation x = x := by
  let T : L2S2Geom →L[ℝ] L2S2Geom :=
    (Rotation.compL2Rotation antipodeRotation).toContinuousLinearMap - ContinuousLinearMap.id ℝ L2S2Geom
  have himage :
      continuousSphereFrameImageL2S2 ≤ LinearMap.ker T := by
    intro y hy
    change Rotation.compL2Rotation antipodeRotation y - y = 0
    rw [sub_eq_zero]
    exact compL2Rotation_antipode_eq_self_of_mem_continuousSphereFrameImageL2S2 hy
  have hclosed : IsClosed ((LinearMap.ker T : Submodule ℝ L2S2Geom) : Set L2S2Geom) := by
    simpa using (ContinuousLinearMap.isClosed_ker T)
  have hker :
      x ∈ LinearMap.ker T := by
    have hclosure :
        continuousSphereFrameImageL2S2.topologicalClosure ≤ LinearMap.ker T :=
      Submodule.topologicalClosure_minimal
        (s := continuousSphereFrameImageL2S2) himage hclosed
    exact hclosure hx
  change Rotation.compL2Rotation antipodeRotation x - x = 0 at hker
  exact sub_eq_zero.mp hker

theorem compL2Rotation_antipode_eq_neg_of_mem_sectorL2_odd
    {n : ℕ} (hnodd : Odd n) {x : L2S2Geom} (hx : x ∈ sectorL2 n) :
    Rotation.compL2Rotation antipodeRotation x = -x := by
  rcases sectorToSectorL2_surjective n ⟨x, hx⟩ with ⟨f, hfx⟩
  rw [Subtype.ext_iff] at hfx
  dsimp at hfx
  have hpow : (-1 : ℝ) ^ n = -1 := by
    rcases hnodd with ⟨k, hk⟩
    rw [hk]
    calc
      (-1 : ℝ) ^ (2 * k + 1) = (-1 : ℝ) ^ (2 * k) * (-1 : ℝ) := by
        rw [show 2 * k + 1 = 2 * k + 1 by rfl, pow_add]
        simp
      _ = 1 * (-1 : ℝ) := by simp
      _ = -1 := by ring
  rw [← hfx]
  calc
    Rotation.compL2Rotation antipodeRotation (continuousToLp f)
        = continuousToLp (Rotation.compContinuous antipodeRotation f) := by
            simpa using continuousToLp_compContinuous_symm antipodeRotation f
    _ = continuousToLp (((-1 : ℝ) ^ n) • f) := by
          rw [sector_compContinuous_antipode f.property]
    _ = continuousToLp (-f) := by
          congr
          ext y
          simp [hpow]
    _ = -continuousToLp f := by simp

theorem continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_eq_bot_of_odd
    {n : ℕ} (hnodd : Odd n) :
    continuousSphereFrameClosedSubmoduleL2S2.toSubmodule ⊓ sectorL2 n = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hfix :=
    compL2Rotation_antipode_eq_self_of_mem_continuousSphereFrameClosedSubmoduleL2S2 hx.1
  have hneg :=
    compL2Rotation_antipode_eq_neg_of_mem_sectorL2_odd hnodd hx.2
  have hxx : x = -x := by simpa [hfix] using hneg
  have hnegx : -x = x := by simpa using hxx.symm
  have hadd : x + x = 0 := by
    calc
      x + x = x + (-x) := by
        nth_rewrite 2 [hxx]
        rfl
      _ = 0 := by simp
  have htwo : (2 : ℝ) • x = 0 := by
    simpa [two_smul] using hadd
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp htwo).resolve_left h2

end GleasonS2Bridge
