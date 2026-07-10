import Gleason.Harmonic.HighDegree.EvenBoundedLowDegree
import Gleason.Harmonic.HighDegree.EvenBoundedWitness
import Gleason.Harmonic.Zonal.NorthZonalQuadraticQ02
import Gleason.Harmonic.Auxiliary.PointConstraintFrame

noncomputable section

open Complex InnerProductSpace

theorem northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal
    {g : C(spherePoint3, ℝ)} {p : MvPolynomial (Fin 3) ℝ}
    (hgz : IsNorthZonal g)
    (hpEval : sphereCoordMvEval p = g)
    (z : Set.Icc (-1 : ℝ) 1) :
    northZonalProfile g z = (northMeridianPolynomial p).eval z.1 := by
  have hpos :
      MvPolynomial.eval (meridianPosCoord z.1) p = g (northSection z) := by
    calc
      MvPolynomial.eval (meridianPosCoord z.1) p
          = sphereCoordMvEval p (northSection z) := by
              rw [sphereCoordMvEval_apply, sphereCoordVec_northSection_eq_meridianPosCoord]
      _ = g (northSection z) := by
            simpa using congrArg (fun f : C(spherePoint3, ℝ) => f (northSection z)) hpEval
  have hneg :
      MvPolynomial.eval (meridianNegCoord z.1) p =
        g (sphereMap (northRotation Real.pi) (northSection z)) := by
    calc
      MvPolynomial.eval (meridianNegCoord z.1) p
          = sphereCoordMvEval p (sphereMap (northRotation Real.pi) (northSection z)) := by
              rw [sphereCoordMvEval_apply,
                sphereCoordVec_northRotation_pi_northSection_eq_meridianNegCoord]
      _ = g (sphereMap (northRotation Real.pi) (northSection z)) := by
            simpa using congrArg (fun f : C(spherePoint3, ℝ) =>
              f (sphereMap (northRotation Real.pi) (northSection z))) hpEval
  have hsame :
      g (sphereMap (northRotation Real.pi) (northSection z)) = g (northSection z) := by
    apply eq_of_isNorthZonal_of_snd_eq hgz
    simp [sphereMap, northRotation_apply, northSection]
  calc
    northZonalProfile g z = g (northSection z) := by rfl
    _ = ((2 : ℝ)⁻¹) *
          (MvPolynomial.eval (meridianPosCoord z.1) p +
            MvPolynomial.eval (meridianNegCoord z.1) p) := by
              rw [hpos, hneg, hsame]
              ring
    _ = (northMeridianPolynomial p).eval z.1 := by
          symm
          exact northMeridianPolynomial_eval p z

theorem centeredNorthZonalProfile_eq_northMeridianPolynomial_sub_const_of_isNorthZonal
    {g : C(spherePoint3, ℝ)} {p : MvPolynomial (Fin 3) ℝ}
    (hgz : IsNorthZonal g)
    (hpEval : sphereCoordMvEval p = g) :
    ∀ z : Set.Icc (-1 : ℝ) 1,
      centeredNorthZonalProfile g z =
        (northMeridianPolynomial p - Polynomial.C ((northMeridianPolynomial p).eval 0)).eval z.1 := by
  intro z
  have hz := northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal hgz hpEval z
  have h0 := northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal hgz hpEval zeroIcc
  rw [centeredNorthZonalProfile]
  rw [hz, h0]
  simp [zeroIcc]

theorem mem_sup_zero_two_of_isNorthZonal_mem_frame_of_mvPolynomial
    {g : C(spherePoint3, ℝ)} {p : MvPolynomial (Fin 3) ℝ}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hpEval : sphereCoordMvEval p = g) :
    g ∈ continuousHarmonicSphereDegreeSubmodule 0 ⊔
        continuousHarmonicSphereDegreeSubmodule 2 := by
  have hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
    rw [continuousSphereGreatCirclePointConstraintSubmodule_eq_continuousSphereFrameSubmodule]
    exact hgframe
  let q : Polynomial ℝ :=
    northMeridianPolynomial p - Polynomial.C ((northMeridianPolynomial p).eval 0)
  have hpoly :
      ∀ z : Set.Icc (-1 : ℝ) 1,
        centeredNorthZonalProfile g z = q.eval z.1 := by
    intro z
    simpa [q] using
      centeredNorthZonalProfile_eq_northMeridianPolynomial_sub_const_of_isNorthZonal hgz hpEval z
  have hgquad :
      g ∈ continuousSphereQuadraticSubmodule :=
    mem_continuousSphereQuadraticSubmodule_of_isNorthZonal_pointConstraint_polynomial
      hgpc hgz q hpoly
  exact mem_sup_zero_two_of_isNorthZonal_mem_quadratic_pointConstraint hgquad hgpc hgz

theorem exists_nonzero_mem_sup_zero_two_of_isClosed_of_rotationInvariant_of_le_evenBounded_of_le_frame
    {N : ℕ} {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGbounded : G ≤ evenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (hGframe : G ≤ continuousSphereFrameSubmodule)
    (hGne : G ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ G ∧ g ≠ 0 ∧
      g ∈ continuousHarmonicSphereDegreeSubmodule 0 ⊔
        continuousHarmonicSphereDegreeSubmodule 2 := by
  rcases exists_nonzero_northZonal_even_bounded_mvPolynomial_of_isClosed_of_rotationInvariant_of_le_evenBounded_of_le_frame
      hGclosed hGrot hGbounded hGframe hGne with
    ⟨g, p, hgG, hgne, hgz, hpdeg, hpEval, hpEven⟩
  refine ⟨g, hgG, hgne, ?_⟩
  exact mem_sup_zero_two_of_isNorthZonal_mem_frame_of_mvPolynomial (hGframe hgG) hgz hpEval
