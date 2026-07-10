import SphericalHarmonics.NorthFixedDimension
import Gleason.Harmonic.HighDegree.EvenBoundedLowDegree
import Gleason.Harmonic.HighDegree.EvenBoundedQ02
import Gleason.Harmonic.Sphere.SphericalBridge
import Gleason.Harmonic.Sphere.S2NorthZonalBridge
import Gleason.Harmonic.Fischer.FischerDirect

noncomputable section

open Complex InnerProductSpace Polynomial

namespace GleasonNorthFixed

open SphericalHarmonics
open GleasonS2Bridge

theorem restrictToSphere_mem_northFixedSubmodule_of_mem_northFixedAmbientHarmonicSubmodule
    {n : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n) :
    restrictToSphere p ∈ northFixedSubmodule := by
  rw [mem_northFixedSubmodule_iff]
  intro t
  calc
    Rotation.compContinuous (rotation01 t) (restrictToSphere p)
        = restrictToSphere ((rotation01 t).compPolynomial p) := by
            simpa using (Rotation.restrictToSphere_compPolynomial (rotation01 t) p).symm
    _ = restrictToSphere p := by rw [hp.2 t]

theorem sphereCoordMvEval_eq_zero_of_northMeridianPolynomial_eq_zero_of_mem_northFixedAmbientHarmonicSubmodule
    {n : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n)
    (hmer : northMeridianPolynomial p = 0) :
    sphereCoordMvEval p = 0 := by
  have hfix :
      restrictToSphere p ∈ northFixedSubmodule :=
    restrictToSphere_mem_northFixedSubmodule_of_mem_northFixedAmbientHarmonicSubmodule hp
  have hgz : IsNorthZonal (sphereCoordMvEval p) := by
    rw [← s2Pullback_restrictToSphere]
    exact isNorthZonal_s2Pullback_of_mem_northFixedSubmodule hfix
  ext x
  have hprof := northZonalProfile_eq_of_isNorthZonal hgz x
  calc
    sphereCoordMvEval p x
        = northZonalProfile (sphereCoordMvEval p) ⟨sphereCoordZ x, snd_mem_Icc x⟩ := by
            simpa [sphereCoordZ] using hprof.symm
    _ = (northMeridianPolynomial p).eval (sphereCoordZ x) := by
          simpa using
            northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal
              hgz (rfl : sphereCoordMvEval p = sphereCoordMvEval p)
              ⟨sphereCoordZ x, snd_mem_Icc x⟩
    _ = 0 := by simp [hmer]

theorem eq_zero_of_northMeridianPolynomial_eq_zero_of_mem_northFixedAmbientHarmonicSubmodule
    {n : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n)
    (hmer : northMeridianPolynomial p = 0) :
    p = 0 := by
  apply eq_of_sphereCoordMvEval_eq_of_mem_homogeneousSubmodule hp.1.1
    (Submodule.zero_mem _)
  simpa using
    sphereCoordMvEval_eq_zero_of_northMeridianPolynomial_eq_zero_of_mem_northFixedAmbientHarmonicSubmodule
      hp hmer

theorem northMeridianPolynomial_ne_zero_of_mem_northFixedAmbientHarmonicSubmodule
    {n : ℕ} {p : Poly3}
    (hp : p ∈ northFixedAmbientHarmonicSubmodule n)
    (hp0 : p ≠ 0) :
    northMeridianPolynomial p ≠ 0 := by
  intro hmer
  exact hp0
    (eq_zero_of_northMeridianPolynomial_eq_zero_of_mem_northFixedAmbientHarmonicSubmodule hp hmer)

end GleasonNorthFixed
