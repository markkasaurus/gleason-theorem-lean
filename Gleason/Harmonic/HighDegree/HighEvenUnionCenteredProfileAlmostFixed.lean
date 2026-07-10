import Gleason.Harmonic.HighDegree.HighEvenUnionNorthProfileAlmostFixed
import Gleason.Harmonic.HighDegree.EvenBoundedQ02
import Gleason.Harmonic.Zonal.NorthZonalPolynomialOperator

noncomputable section

open Complex InnerProductSpace Polynomial

set_option maxHeartbeats 800000

private lemma northZonalScalarPolynomial_sub_const
    (p : ℝ[X]) (a : ℝ) :
    northZonalScalarPolynomial (p - Polynomial.C a) =
      northZonalScalarPolynomial p - Polynomial.C (2 * a) := by
  ext n
  cases n with
  | zero =>
      simp [coeff_northZonalScalarPolynomial, northZonalScalarCoeff_zero]
      ring
  | succ n =>
      simp [coeff_northZonalScalarPolynomial]

theorem exists_fixed_northZonal_centeredProfile_poly_almost_fixed_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      g sphereE3 ≠ 0 ∧
      ∀ {ε : ℝ}, 0 < ε → ε < ‖g sphereE3‖ →
        ∃ h : C(spherePoint3, ℝ), ∃ c : ℝ[X],
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          h sphereE3 ≠ 0 ∧
          (∀ z : Set.Icc (-1 : ℝ) 1,
            centeredNorthZonalProfile h z = c.eval z.1) ∧
          ‖northZonalContinuousMap h - northZonalContinuousMap g‖ < ε ∧
          ∀ r : Set.Icc (0 : ℝ) 1,
            |(northZonalScalarPolynomial c).eval r.1 - c.eval r.1| < 4 * ε := by
  rcases exists_fixed_northZonal_northProfile_poly_almost_fixed_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, hgpole, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, hgpole, ?_⟩
  intro ε hε hεpole
  rcases happ hε hεpole with ⟨h, p, hhHigh, hhz, hhpole, hp, hdist, hpfix⟩
  let c : ℝ[X] := p - Polynomial.C (p.eval 0)
  refine ⟨h, c, hhHigh, hhz, hhpole, ?_, hdist, ?_⟩
  · intro z
    calc
      centeredNorthZonalProfile h z = northZonalProfile h z - northZonalProfile h zeroIcc := by
        rfl
      _ = p.eval z.1 - p.eval 0 := by
        rw [hp z]
        congr 1
        have hzero := hp zeroIcc
        simpa [zeroIcc] using hzero
      _ = c.eval z.1 := by
        simp [c]
  · intro r
    have hcalc :
        (northZonalScalarPolynomial c).eval r.1 - c.eval r.1 =
          (northZonalScalarPolynomial p).eval r.1 - (p.eval r.1 + p.eval 0) := by
      rw [show c = p - Polynomial.C (p.eval 0) by rfl]
      rw [northZonalScalarPolynomial_sub_const]
      simp
      ring
    rw [hcalc]
    exact hpfix r
