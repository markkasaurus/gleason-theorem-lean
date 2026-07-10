import Gleason.Harmonic.HighDegree.EvenBoundedQ02
import Gleason.Harmonic.Zonal.NorthZonalQuadraticQ02
import Gleason.Harmonic.Fischer.FischerExact
import Gleason.Harmonic.Fischer.FischerBasic

noncomputable section

open Complex InnerProductSpace

def lowHarmonicPolyHomogeneousImageSubmodule : Submodule ℝ C(spherePoint3, ℝ) :=
  harmonicPolyHomogeneousImageSubmodule 0 ⊔ harmonicPolyHomogeneousImageSubmodule 2

lemma one_mem_harmonicPolyHomogeneousImageSubmodule_zero :
    (1 : C(spherePoint3, ℝ)) ∈ harmonicPolyHomogeneousImageSubmodule 0 := by
  refine ⟨MvPolynomial.C (1 : ℝ), ?_, ?_⟩
  · change MvPolynomial.C (1 : ℝ) ∈ harmonicPolyHomogeneousSubmodule 0
    constructor
    · change (MvPolynomial.C (1 : ℝ)).IsHomogeneous 0
      exact MvPolynomial.isHomogeneous_C (σ := Fin 3) (R := ℝ) (1 : ℝ)
    · simp [LinearMap.mem_ker, polyLaplacian]
  · ext x
    simp

def zonalQuadraticPoly : MvPolynomial (Fin 3) ℝ :=
  rhoPoly - 3 * MvPolynomial.X 2 ^ 2

lemma zonalQuadraticPoly_mem_harmonicPolyHomogeneousSubmodule_two :
    zonalQuadraticPoly ∈ harmonicPolyHomogeneousSubmodule 2 := by
  refine ⟨?_, ?_⟩
  · unfold zonalQuadraticPoly
    have hrho : rhoPoly ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 2 := by
      simpa [rhoPoly, add_assoc, add_left_comm, add_comm] using
        (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 0 2).add
          ((MvPolynomial.isHomogeneous_X_pow (R := ℝ) 1 2).add
            (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 2 2))
    have hX2 : MvPolynomial.X 2 ^ 2 ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 2 := by
      simpa using (MvPolynomial.isHomogeneous_X_pow (R := ℝ) 2 2)
    have hX2smul :
        (3 * MvPolynomial.X 2 ^ 2 : MvPolynomial (Fin 3) ℝ) ∈
          MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 2 := by
      simpa [Algebra.smul_def] using
        (Submodule.smul_mem (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 2) (3 : ℝ) hX2)
    exact Submodule.sub_mem (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ 2) hrho hX2smul
  · change polyLaplacian zonalQuadraticPoly = 0
    have hX2 : polyLaplacian (MvPolynomial.X 2 ^ 2) = 2 := by
      calc
        polyLaplacian (MvPolynomial.X 2 ^ 2)
            = MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (MvPolynomial.X 2 ^ 2)) +
                MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 (MvPolynomial.X 2 ^ 2)) +
                MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 (MvPolynomial.X 2 ^ 2)) := by
                  rfl
        _ = 0 + 0 + (2 : MvPolynomial (Fin 3) ℝ) := by
              simp [pow_two]
              norm_num
        _ = 2 := by simp
    have hX2smul : polyLaplacian (3 * MvPolynomial.X 2 ^ 2) = 3 * 2 := by
      have hmul :
          (3 * MvPolynomial.X 2 ^ 2 : MvPolynomial (Fin 3) ℝ) =
            (3 : ℝ) • (MvPolynomial.X 2 ^ 2) := by
        change (MvPolynomial.C (3 : ℝ)) * MvPolynomial.X 2 ^ 2 =
          (3 : ℝ) • (MvPolynomial.X 2 ^ 2)
        simp [Algebra.smul_def]
      calc
        polyLaplacian (3 * MvPolynomial.X 2 ^ 2)
            = polyLaplacian ((3 : ℝ) • (MvPolynomial.X 2 ^ 2)) := by rw [hmul]
        _ = (3 : ℝ) • polyLaplacian (MvPolynomial.X 2 ^ 2) := by
              rw [LinearMap.map_smul]
        _ = 3 * 2 := by
              rw [hX2]
              rw [MvPolynomial.smul_eq_C_mul]
              rw [show (3 : MvPolynomial (Fin 3) ℝ) = MvPolynomial.C (3 : ℝ) by rfl]
    calc
      polyLaplacian zonalQuadraticPoly
          = polyLaplacian rhoPoly - polyLaplacian (3 * MvPolynomial.X 2 ^ 2) := by
              simp [zonalQuadraticPoly]
      _ = 6 - 3 * 2 := by rw [polyLaplacian_rhoPoly, hX2smul]
      _ = 0 := by norm_num

lemma sphereCoordMvEval_X_two_sq :
    sphereCoordMvEval (MvPolynomial.X 2 ^ 2) = fun x : spherePoint3 => sphereCoordZ x ^ 2 := by
  ext x
  simp [sphereCoordVec, sphereCoordZ]

lemma zonalQuadraticMode_mem_harmonicPolyHomogeneousImageSubmodule_two :
    zonalQuadraticMode ∈ harmonicPolyHomogeneousImageSubmodule 2 := by
  refine ⟨zonalQuadraticPoly, zonalQuadraticPoly_mem_harmonicPolyHomogeneousSubmodule_two, ?_⟩
  ext x
  simp [zonalQuadraticMode_apply, zonalQuadraticPoly, sphereCoordMvEval_rhoPoly]

theorem mem_lowHarmonicPolyHomogeneousImageSubmodule_of_isNorthZonal_mem_frame_of_mvPolynomial
    {g : C(spherePoint3, ℝ)} {p : MvPolynomial (Fin 3) ℝ}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hpEval : sphereCoordMvEval p = g) :
    g ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
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
  rcases exists_const_add_sq_of_isNorthZonal_mem_quadratic_pointConstraint hgquad hgpc hgz with
    ⟨a, b, hab⟩
  have hdecomp :
      g = (a + b / 3) • (1 : C(spherePoint3, ℝ)) + (-b / 3) • zonalQuadraticMode := by
    ext x
    rw [hab x]
    simp [Pi.smul_apply, zonalQuadraticMode_apply]
    ring
  rw [hdecomp]
  apply Submodule.add_mem_sup
  · exact Submodule.smul_mem _ (a + b / 3) one_mem_harmonicPolyHomogeneousImageSubmodule_zero
  · exact Submodule.smul_mem _ (-b / 3) zonalQuadraticMode_mem_harmonicPolyHomogeneousImageSubmodule_two

theorem exists_nonzero_mem_lowHarmonicPolyHomogeneousImageSubmodule_of_isClosed_of_rotationInvariant_of_le_evenBounded_of_le_frame
    {N : ℕ} {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGbounded : G ≤ evenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (hGframe : G ≤ continuousSphereFrameSubmodule)
    (hGne : G ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ G ∧ g ≠ 0 ∧ g ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
  rcases exists_nonzero_northZonal_even_bounded_mvPolynomial_of_isClosed_of_rotationInvariant_of_le_evenBounded_of_le_frame
      hGclosed hGrot hGbounded hGframe hGne with
    ⟨g, p, hgG, hgne, hgz, hpdeg, hpEval, hpEven⟩
  refine ⟨g, hgG, hgne, ?_⟩
  exact
    mem_lowHarmonicPolyHomogeneousImageSubmodule_of_isNorthZonal_mem_frame_of_mvPolynomial
      (hGframe hgG) hgz hpEval
