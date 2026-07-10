import SphericalHarmonics.Polynomial
import Gleason.Harmonic.Fischer.FischerHarmonicBridge
import Gleason.Harmonic.Fischer.FischerNorthRotation
import Gleason.Harmonic.Auxiliary.GlobalOscillationBridge

noncomputable section

open Complex InnerProductSpace
open scoped BigOperators

namespace GleasonS2Bridge

open SphericalHarmonics

def coordToE3 : ℝ × ℝ × ℝ → E3 :=
  fun r => WithLp.toLp 2 (fun i : Fin 3 =>
    match i with
    | 0 => r.1
    | 1 => r.2.1
    | 2 => r.2.2)

def e3ToCoord (x : E3) : ℝ × ℝ × ℝ :=
  (x 0, (x 1, x 2))

@[simp] lemma coordToE3_apply_zero (r : ℝ × ℝ × ℝ) :
    coordToE3 r 0 = r.1 := by
  simp [coordToE3]

@[simp] lemma coordToE3_apply_one (r : ℝ × ℝ × ℝ) :
    coordToE3 r 1 = r.2.1 := by
  simp [coordToE3]

@[simp] lemma coordToE3_apply_two (r : ℝ × ℝ × ℝ) :
    coordToE3 r 2 = r.2.2 := by
  simp [coordToE3]

@[simp] lemma e3ToCoord_coordToE3 (r : ℝ × ℝ × ℝ) :
    e3ToCoord (coordToE3 r) = r := by
  ext <;> simp [e3ToCoord]

@[simp] lemma coordToE3_e3ToCoord (x : E3) :
    coordToE3 (e3ToCoord x) = x := by
  ext i
  fin_cases i <;> simp [e3ToCoord]

lemma coordToE3_norm_sq (r : ℝ × ℝ × ℝ) :
    ‖coordToE3 r‖ ^ 2 = r.1 ^ 2 + r.2.1 ^ 2 + r.2.2 ^ 2 := by
  rw [EuclideanSpace.norm_eq]
  have hnonneg : 0 ≤ ∑ i : Fin 3, ‖coordToE3 r i‖ ^ 2 := by positivity
  rw [Real.sq_sqrt hnonneg]
  simp [Fin.sum_univ_three, pow_two]

lemma ambientPointOfCoords_norm_sq (r : Fin 3 → ℝ) :
    ‖ambientPointOfCoords r‖ ^ 2 = r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 := by
  have hinner := (WithLp.prod_inner_apply (𝕜 := ℝ) (ambientPointOfCoords r) (ambientPointOfCoords r))
  have hnormsq :
      ‖ambientPointOfCoords r‖ ^ 2 = ‖((r 0 : ℂ) + Complex.I * (r 1 : ℂ))‖ ^ 2 + r 2 ^ 2 := by
    simpa [ambientPointOfCoords, inner_self_eq_norm_sq_to_K, pow_two] using hinner
  have hcomplex : ‖((r 0 : ℂ) + Complex.I * (r 1 : ℂ))‖ ^ 2 = r 0 ^ 2 + r 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  nlinarith

lemma continuous_coordToE3 : Continuous coordToE3 := by
  have hcoords : Continuous (fun r : ℝ × ℝ × ℝ => fun i : Fin 3 =>
      match i with
      | 0 => r.1
      | 1 => r.2.1
      | 2 => r.2.2) := by
    rw [continuous_pi_iff]
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd.fst
    · exact continuous_snd.snd
  simpa [coordToE3] using (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp hcoords

lemma continuous_ambientPointOfCoordsE3 :
    Continuous (fun x : E3 => ambientPointOfCoords (fun i => x i)) := by
  have h0 : Continuous fun x : E3 => x 0 := PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0
  have h1 : Continuous fun x : E3 => x 1 := PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1
  have h2 : Continuous fun x : E3 => x 2 := PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2
  have hpair : Continuous fun x : E3 => (((x 0 : ℂ) + Complex.I * (x 1 : ℂ)), x 2) := by
    continuity
  simpa [ambientPointOfCoords, Function.comp] using
    (WithLp.prod_continuous_toLp (p := 2) (α := ℂ) (β := ℝ)).comp hpair

def spherePoint3ToS2 (x : spherePoint3) : S2 := by
  refine ⟨coordToE3 (spherePointCoord x), ?_⟩
  have hcoord : ‖coordToE3 (spherePointCoord x)‖ ^ 2 = 1 := by
    rw [coordToE3_norm_sq]
    exact spherePointCoord_sq_sum x
  have hnorm : ‖coordToE3 (spherePointCoord x)‖ = 1 := by
    have hnn : 0 ≤ ‖coordToE3 (spherePointCoord x)‖ := norm_nonneg _
    nlinarith
  simpa [Metric.mem_sphere, dist_eq_norm] using hnorm

@[simp] lemma spherePoint3ToS2_apply (x : spherePoint3) :
    e3ToCoord (spherePoint3ToS2 x : E3) = spherePointCoord x := by
  simp [spherePoint3ToS2, e3ToCoord]

def s2ToSpherePoint3 (x : S2) : spherePoint3 := by
  refine ⟨ambientPointOfCoords (fun i => (x : E3) i), ?_⟩
  have hsum : ((x : E3) 0) ^ 2 + ((x : E3) 1) ^ 2 + ((x : E3) 2) ^ 2 = 1 := by
    have hcoord : ‖coordToE3 (e3ToCoord (x : E3))‖ ^ 2 =
        ((x : E3) 0) ^ 2 + ((x : E3) 1) ^ 2 + ((x : E3) 2) ^ 2 := by
      simpa [e3ToCoord] using coordToE3_norm_sq (e3ToCoord (x : E3))
    have hnorm : ‖coordToE3 (e3ToCoord (x : E3))‖ ^ 2 = 1 := by
      simpa [coordToE3_e3ToCoord] using S2.norm_sq_eq_one x
    nlinarith
  have hnormsq : ‖ambientPointOfCoords (fun i => (x : E3) i)‖ ^ 2 = 1 := by
    rw [ambientPointOfCoords_norm_sq]
    exact hsum
  have hnorm : ‖ambientPointOfCoords (fun i => (x : E3) i)‖ = 1 := by
    have hnn : 0 ≤ ‖ambientPointOfCoords (fun i => (x : E3) i)‖ := norm_nonneg _
    nlinarith
  simpa using hnorm

@[simp] lemma spherePointCoord_s2ToSpherePoint3 (x : S2) :
    spherePointCoord (s2ToSpherePoint3 x) = e3ToCoord (x : E3) := by
  ext <;>
    simp [s2ToSpherePoint3, spherePointCoord, ambientPointOfCoords, e3ToCoord]

lemma spherePointCoord_injective : Function.Injective spherePointCoord := by
  intro x y hxy
  apply Subtype.ext
  apply WithLp.ofLp_injective (p := 2)
  apply Prod.ext
  · apply Complex.ext
    · exact congrArg Prod.fst hxy
    · exact congrArg (fun r : ℝ × ℝ × ℝ => r.2.1) hxy
  · exact congrArg (fun r : ℝ × ℝ × ℝ => r.2.2) hxy

@[simp] lemma spherePoint3ToS2_symm_apply (x : spherePoint3) :
    s2ToSpherePoint3 (spherePoint3ToS2 x) = x := by
  apply spherePointCoord_injective
  rw [spherePointCoord_s2ToSpherePoint3, spherePoint3ToS2_apply]

@[simp] lemma s2ToSpherePoint3_symm_apply (x : S2) :
    spherePoint3ToS2 (s2ToSpherePoint3 x) = x := by
  apply Subtype.ext
  ext i
  fin_cases i <;>
    simp [spherePoint3ToS2, s2ToSpherePoint3, coordToE3, spherePointCoord,
      ambientPointOfCoords]

def spherePoint3EquivS2 : spherePoint3 ≃ₜ S2 where
  toEquiv :=
    { toFun := spherePoint3ToS2
      invFun := s2ToSpherePoint3
      left_inv := spherePoint3ToS2_symm_apply
      right_inv := s2ToSpherePoint3_symm_apply }
  continuous_toFun := by
    exact (continuous_coordToE3.comp continuous_spherePointCoord).subtype_mk (fun x => by
      exact (spherePoint3ToS2 x).2)
  continuous_invFun := by
    exact (continuous_ambientPointOfCoordsE3.comp continuous_subtype_val).subtype_mk (fun x => by
      exact (s2ToSpherePoint3 x).2)

def s2Pullback : C(S2, ℝ) ≃ₗ[ℝ] C(spherePoint3, ℝ) where
  toFun f := f.comp spherePoint3EquivS2
  invFun f := f.comp spherePoint3EquivS2.symm
  map_add' f g := by
    ext x
    rfl
  map_smul' a f := by
    ext x
    rfl
  left_inv f := by
    ext x
    simp [spherePoint3EquivS2]
  right_inv f := by
    ext x
    simp [spherePoint3EquivS2]

@[simp] lemma s2Pullback_apply (f : C(S2, ℝ)) (x : spherePoint3) :
    s2Pullback f x = f (spherePoint3ToS2 x) := rfl

lemma laplacian_eq_polyLaplacian :
    SphericalHarmonics.laplacian = polyLaplacian := by
  ext p
  simp [SphericalHarmonics.laplacian, polyLaplacian, Fin.sum_univ_three,
    add_assoc, add_left_comm, add_comm]

lemma harmonicHomogeneousSubmodule_eq_harmonicPolyHomogeneousSubmodule (n : ℕ) :
    SphericalHarmonics.harmonicHomogeneousSubmodule n = harmonicPolyHomogeneousSubmodule n := by
  ext p
  simp [SphericalHarmonics.harmonicHomogeneousSubmodule, SphericalHarmonics.harmonicSubmodule,
    harmonicPolyHomogeneousSubmodule, laplacian_eq_polyLaplacian]

theorem s2Pullback_restrictToSphere (p : Poly3) :
    s2Pullback (restrictToSphere p) = sphereCoordMvEval p := by
  ext x
  rw [s2Pullback_apply, restrictToSphere_apply, sphereCoordMvEval_apply]
  congr
  funext i
  fin_cases i <;>
    simp [spherePoint3ToS2, coordToE3, spherePointCoord, sphereCoordVec, sphereCoordRe,
      sphereCoordIm, sphereCoordZ]

theorem s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule
    {n : ℕ} {f : C(S2, ℝ)} (hf : f ∈ sector n) :
    s2Pullback f ∈ continuousHarmonicSphereDegreeSubmodule n := by
  rcases hf with ⟨p, hp, rfl⟩
  rw [s2Pullback_restrictToSphere]
  exact harmonicPolyHomogeneousImage_le_continuousHarmonicSphereDegreeSubmodule n
    ⟨p, by simpa [harmonicHomogeneousSubmodule_eq_harmonicPolyHomogeneousSubmodule n] using hp, rfl⟩

end GleasonS2Bridge
