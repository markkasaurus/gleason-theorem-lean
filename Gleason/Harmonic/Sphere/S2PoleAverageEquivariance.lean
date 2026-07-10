import Gleason.Harmonic.Sphere.S2PoleAverageOperator
import Gleason.Harmonic.Sphere.S2FrameRotation
import Gleason.Harmonic.Fischer.FischerHarmonicBridge
import SphericalHarmonics.ZonalFixed
import Mathlib.Analysis.InnerProductSpace.LinearMap

noncomputable section

open Complex InnerProductSpace

namespace GleasonS2Bridge

open SphericalHarmonics

private def ambientCoordTuple (x : WithLp 2 (ℂ × ℝ)) : ℝ × ℝ × ℝ :=
  (ambientCoordFun 0 x, (ambientCoordFun 1 x, ambientCoordFun 2 x))

private theorem coordDot_ambientCoordTuple (x y : WithLp 2 (ℂ × ℝ)) :
    coordDot (ambientCoordTuple x) (ambientCoordTuple y) = inner ℝ x y := by
  simp [ambientCoordTuple, ambientCoordFun, complexProjL, realProjL, coordDot,
    Complex.mul_re, add_assoc, mul_comm]

/-- The explicit real-linear identification `WithLp 2 (ℂ × ℝ) ≃ ℝ³`. -/
def ambientToE3LinearEquiv : WithLp 2 (ℂ × ℝ) ≃ₗ[ℝ] E3 where
  toFun x := WithLp.toLp 2 (fun i => ambientCoordFun i x)
  invFun x := ambientPointOfCoords fun i => x i
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp [ambientCoordFun, map_add]
  map_smul' := by
    intro c x
    ext i
    fin_cases i <;> simp [ambientCoordFun, map_smul]
  left_inv := by
    intro x
    apply WithLp.ofLp_injective
    change ((ambientPointOfCoords fun i => ambientCoordFun i x) : WithLp 2 (ℂ × ℝ)).ofLp = x.ofLp
    ext
    · apply Complex.ext <;> simp [ambientPointOfCoords, ambientCoordFun, complexProjL, realProjL]
    · simp [ambientPointOfCoords, ambientCoordFun, complexProjL, realProjL]
  right_inv := by
    intro x
    ext i
    fin_cases i <;> simp [ambientPointOfCoords, ambientCoordFun, complexProjL, realProjL]

@[simp] theorem ambientToE3LinearEquiv_apply
    (x : WithLp 2 (ℂ × ℝ)) :
    ambientToE3LinearEquiv x = WithLp.toLp 2 (fun i => ambientCoordFun i x) := by
  rfl

private theorem ambientToE3LinearEquiv_inner
    (x y : WithLp 2 (ℂ × ℝ)) :
    inner ℝ (ambientToE3LinearEquiv x) (ambientToE3LinearEquiv y) = inner ℝ x y := by
  rw [← coordDot_e3ToCoord (ambientToE3LinearEquiv x) (ambientToE3LinearEquiv y)]
  simpa [ambientToE3LinearEquiv, ambientCoordTuple, e3ToCoord] using
    coordDot_ambientCoordTuple x y

/-- The ambient real-linear isometry `WithLp 2 (ℂ × ℝ) ≃ₗᵢ ℝ³`. -/
def ambientToE3 : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] E3 :=
  ambientToE3LinearEquiv.isometryOfInner ambientToE3LinearEquiv_inner

@[simp] theorem ambientToE3_apply
    (x : WithLp 2 (ℂ × ℝ)) :
    ambientToE3 x = WithLp.toLp 2 (fun i => ambientCoordFun i x) := by
  rfl

@[simp] theorem ambientToE3_apply_spherePoint3
    (x : spherePoint3) :
    ambientToE3 x.1 = spherePoint3ToS2 x := by
  ext i
  fin_cases i <;>
    simp [ambientToE3, ambientToE3LinearEquiv, spherePoint3ToS2, coordToE3,
      spherePointCoord, ambientCoordFun, complexProjL, realProjL]

/-- The ambient linear isometry corresponding to the `S²` rotation `ρ`, acting on
`WithLp 2 (ℂ × ℝ)`. -/
def ambientRotation (ρ : Rotation) : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ) :=
  ((ambientToE3.trans ρ.symm).trans ambientToE3.symm)

@[simp] theorem ambientToE3_ambientRotation
    (ρ : Rotation) (x : WithLp 2 (ℂ × ℝ)) :
    ambientToE3 (ambientRotation ρ x) = ρ.symm (ambientToE3 x) := by
  simp [ambientRotation, LinearIsometryEquiv.trans_apply]

@[simp] theorem sphereMap_ambientRotation
    (ρ : Rotation) (x : spherePoint3) :
    sphereMap (ambientRotation ρ) x = spherePoint3Rotate ρ x := by
  apply Subtype.ext
  apply ambientToE3.injective
  calc
    ambientToE3 ((sphereMap (ambientRotation ρ) x).1)
        = ambientToE3 ((ambientRotation ρ) x.1) := by
            rfl
    _ = ρ.symm (ambientToE3 x.1) := by
          simpa using ambientToE3_ambientRotation ρ x.1
    _ = ρ.symm (spherePoint3ToS2 x : S2) := by
          rw [ambientToE3_apply_spherePoint3 x]
    _ = (ρ.toSphereEquiv.symm (spherePoint3ToS2 x) : S2) := by
          rfl
    _ = ambientToE3 ((s2ToSpherePoint3 (ρ.toSphereEquiv.symm (spherePoint3ToS2 x))).1) := by
          symm
          simpa using ambientToE3_apply_spherePoint3
            (s2ToSpherePoint3 (ρ.toSphereEquiv.symm (spherePoint3ToS2 x)))
    _ = ambientToE3 ((spherePoint3Rotate ρ x).1) := by
          rfl

@[simp] theorem s2Pullback_compContinuous_eq_spherePrecomp_ambientRotation
    (ρ : Rotation) (f : C(S2, ℝ)) :
    s2Pullback (Rotation.compContinuous ρ f) =
      spherePrecomp (ambientRotation ρ) (s2Pullback f) := by
  ext x
  rw [s2Pullback_compContinuous]
  simp [spherePrecomp_apply, sphereMap_ambientRotation]

set_option maxHeartbeats 400000 in
theorem s2PoleAverageLinear_compContinuous_apply
    (ρ : Rotation) (f : C(S2, ℝ)) (z : S2) :
    s2PoleAverageLinear (Rotation.compContinuous ρ f) z =
      s2PoleAverageLinear f (ρ.toSphereEquiv.symm z) := by
  have hsphere :
      sphereMap (ambientRotation ρ) (s2ToSpherePoint3 z) =
        s2ToSpherePoint3 (ρ.toSphereEquiv.symm z) := by
    calc
      sphereMap (ambientRotation ρ) (s2ToSpherePoint3 z)
          = spherePoint3Rotate ρ (s2ToSpherePoint3 z) := by
              exact sphereMap_ambientRotation ρ (s2ToSpherePoint3 z)
      _ = s2ToSpherePoint3 (ρ.toSphereEquiv.symm z) := by
            simp [spherePoint3Rotate]
  rw [s2PoleAverageLinear_apply, s2PoleAverageLinear_apply]
  rw [s2Pullback_compContinuous_eq_spherePrecomp_ambientRotation]
  rw [poleAverageLinear_spherePrecomp (ambientRotation ρ) (s2Pullback f) (s2ToSpherePoint3 z)]
  rw [hsphere]

theorem s2PoleAverageLinear_eq_of_mem_northFixedSubmodule
    {f : C(S2, ℝ)}
    (hf : f ∈ (northFixedSubmodule : Submodule ℝ C(S2, ℝ)))
    (t : ℝ) (z : S2) :
    s2PoleAverageLinear f ((rotation01 t).toSphereEquiv.symm z) =
      s2PoleAverageLinear f z := by
  have hf' : ∀ s : ℝ, Rotation.compContinuous (rotation01 s) f = f :=
    (mem_northFixedSubmodule_iff f).1 hf
  have hrot :
      Rotation.compContinuous (rotation01 t) f = f :=
    hf' t
  rw [← s2PoleAverageLinear_compContinuous_apply (rotation01 t) f z]
  simp [hrot]

end GleasonS2Bridge
