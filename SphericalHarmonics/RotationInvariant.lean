import SphericalHarmonics.FiniteDimensional

namespace SphericalHarmonics

namespace Rotation

@[simp] theorem toSphereEquiv_symm (ρ : Rotation) :
    (Rotation.toSphereEquiv ρ).symm = Rotation.toSphereEquiv ρ.symm := rfl

@[simp] theorem toSphereEquiv_symm_symm (ρ : Rotation) :
    (Rotation.toSphereEquiv ρ.symm).symm = Rotation.toSphereEquiv ρ := rfl

theorem coeff_sum_mul_coeff_eq (ρ : Rotation) (j k : Fin 3) :
    ∑ i : Fin 3, coeff ρ j i * coeff ρ k i = if j = k then 1 else 0 := by
  calc
    ∑ i : Fin 3, coeff ρ j i * coeff ρ k i
        = inner ℝ (ρ (EuclideanSpace.single j (1 : ℝ))) (ρ (EuclideanSpace.single k (1 : ℝ))) := by
            rw [PiLp.inner_apply]
            simp [coeff, Fin.sum_univ_three]
            ring
    _ = inner ℝ (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single k (1 : ℝ)) := by
          simpa using
            (ρ.inner_map_map (EuclideanSpace.single j (1 : ℝ))
              (EuclideanSpace.single k (1 : ℝ))).symm
    _ = if j = k then 1 else 0 := by
          by_cases h : j = k
          · subst h
            simp
          · simp [EuclideanSpace.inner_single_left, h]

theorem pderiv_comm (i j : Fin 3) (p : Poly3) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  fin_cases i <;> fin_cases j
  all_goals
    ext d
    simp [coeff_pderiv, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]

theorem pderiv_compPolynomial (ρ : Rotation) (i : Fin 3) (p : Poly3) :
    MvPolynomial.pderiv i (ρ.compPolynomial p) =
      ∑ j : Fin 3, MvPolynomial.C (coeff ρ j i) * ρ.compPolynomial (MvPolynomial.pderiv j p) := by
  classical
  refine MvPolynomial.induction_on
    (motive := fun p : Poly3 =>
      MvPolynomial.pderiv i (ρ.compPolynomial p) =
        ∑ j : Fin 3, MvPolynomial.C (coeff ρ j i) * ρ.compPolynomial (MvPolynomial.pderiv j p))
    p ?_ ?_ ?_
  · intro a
    simp [Rotation.compPolynomial]
  · intro p q hp hq
    simp [hp, hq, Finset.sum_add_distrib, left_distrib]
  · intro p k hp
    rw [show ρ.compPolynomial (p * MvPolynomial.X k) =
        ρ.compPolynomial p * coordPoly ρ k by
        simpa [Rotation.compPolynomial] using
          (ρ.compPolynomial).map_mul p (MvPolynomial.X k)]
    rw [Derivation.leibniz, hp, pderiv_coordPoly]
    fin_cases k
    all_goals
      simp [Rotation.compPolynomial, Fin.sum_univ_three, MvPolynomial.pderiv_X,
        MvPolynomial.C_mul', mul_add, mul_assoc, mul_left_comm, mul_comm]
      ring_nf

theorem laplacian_compPolynomial (ρ : Rotation) (p : Poly3) :
    laplacian (ρ.compPolynomial p) = ρ.compPolynomial (laplacian p) := by
  classical
  have h00 : (ρ.coeff 0 0 : ℝ) * ρ.coeff 0 0 + ρ.coeff 0 1 * ρ.coeff 0 1 +
      ρ.coeff 0 2 * ρ.coeff 0 2 = 1 := by
    simpa [Fin.sum_univ_three] using Rotation.coeff_sum_mul_coeff_eq ρ 0 0
  have h11 : (ρ.coeff 1 0 : ℝ) * ρ.coeff 1 0 + ρ.coeff 1 1 * ρ.coeff 1 1 +
      ρ.coeff 1 2 * ρ.coeff 1 2 = 1 := by
    simpa [Fin.sum_univ_three] using Rotation.coeff_sum_mul_coeff_eq ρ 1 1
  have h22 : (ρ.coeff 2 0 : ℝ) * ρ.coeff 2 0 + ρ.coeff 2 1 * ρ.coeff 2 1 +
      ρ.coeff 2 2 * ρ.coeff 2 2 = 1 := by
    simpa [Fin.sum_univ_three] using Rotation.coeff_sum_mul_coeff_eq ρ 2 2
  have h01 : (ρ.coeff 0 0 : ℝ) * ρ.coeff 1 0 + ρ.coeff 0 1 * ρ.coeff 1 1 +
      ρ.coeff 0 2 * ρ.coeff 1 2 = 0 := by
    simpa [Fin.sum_univ_three] using Rotation.coeff_sum_mul_coeff_eq ρ 0 1
  have h02 : (ρ.coeff 0 0 : ℝ) * ρ.coeff 2 0 + ρ.coeff 0 1 * ρ.coeff 2 1 +
      ρ.coeff 0 2 * ρ.coeff 2 2 = 0 := by
    simpa [Fin.sum_univ_three] using Rotation.coeff_sum_mul_coeff_eq ρ 0 2
  have h12 : (ρ.coeff 1 0 : ℝ) * ρ.coeff 2 0 + ρ.coeff 1 1 * ρ.coeff 2 1 +
      ρ.coeff 1 2 * ρ.coeff 2 2 = 0 := by
    simpa [Fin.sum_univ_three] using Rotation.coeff_sum_mul_coeff_eq ρ 1 2
  have h00' :
      (((MvPolynomial.C (ρ.coeff 0 0) : Poly3) ^ 2 + (MvPolynomial.C (ρ.coeff 0 1) : Poly3) ^ 2 +
          (MvPolynomial.C (ρ.coeff 0 2) : Poly3) ^ 2 : Poly3)) = 1 := by
    simpa [pow_two, MvPolynomial.C_mul] using congrArg MvPolynomial.C h00
  have h11' :
      (((MvPolynomial.C (ρ.coeff 1 0) : Poly3) ^ 2 + (MvPolynomial.C (ρ.coeff 1 1) : Poly3) ^ 2 +
          (MvPolynomial.C (ρ.coeff 1 2) : Poly3) ^ 2 : Poly3)) = 1 := by
    simpa [pow_two, MvPolynomial.C_mul] using congrArg MvPolynomial.C h11
  have h22' :
      (((MvPolynomial.C (ρ.coeff 2 0) : Poly3) ^ 2 + (MvPolynomial.C (ρ.coeff 2 1) : Poly3) ^ 2 +
          (MvPolynomial.C (ρ.coeff 2 2) : Poly3) ^ 2 : Poly3)) = 1 := by
    simpa [pow_two, MvPolynomial.C_mul] using congrArg MvPolynomial.C h22
  have h01' :
      (((MvPolynomial.C (ρ.coeff 0 0) : Poly3) * MvPolynomial.C (ρ.coeff 1 0) +
          MvPolynomial.C (ρ.coeff 0 1) * MvPolynomial.C (ρ.coeff 1 1) +
          MvPolynomial.C (ρ.coeff 0 2) * MvPolynomial.C (ρ.coeff 1 2) : Poly3)) = 0 := by
    simpa [MvPolynomial.C_mul] using congrArg MvPolynomial.C h01
  have h02' :
      (((MvPolynomial.C (ρ.coeff 0 0) : Poly3) * MvPolynomial.C (ρ.coeff 2 0) +
          MvPolynomial.C (ρ.coeff 0 1) * MvPolynomial.C (ρ.coeff 2 1) +
          MvPolynomial.C (ρ.coeff 0 2) * MvPolynomial.C (ρ.coeff 2 2) : Poly3)) = 0 := by
    simpa [MvPolynomial.C_mul] using congrArg MvPolynomial.C h02
  have h12' :
      (((MvPolynomial.C (ρ.coeff 1 0) : Poly3) * MvPolynomial.C (ρ.coeff 2 0) +
          MvPolynomial.C (ρ.coeff 1 1) * MvPolynomial.C (ρ.coeff 2 1) +
          MvPolynomial.C (ρ.coeff 1 2) * MvPolynomial.C (ρ.coeff 2 2) : Poly3)) = 0 := by
    simpa [MvPolynomial.C_mul] using congrArg MvPolynomial.C h12
  let p00 := ρ.compPolynomial (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 p))
  let p11 := ρ.compPolynomial (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 1 p))
  let p22 := ρ.compPolynomial (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2 p))
  let p01 := ρ.compPolynomial (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 p))
  let p02 := ρ.compPolynomial (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 2 p))
  let p12 := ρ.compPolynomial (MvPolynomial.pderiv 1 (MvPolynomial.pderiv 2 p))
  unfold laplacian
  calc
    laplacian (ρ.compPolynomial p)
        =
          (((MvPolynomial.C (ρ.coeff 0 0) : Poly3) ^ 2 + (MvPolynomial.C (ρ.coeff 0 1) : Poly3) ^ 2 +
                (MvPolynomial.C (ρ.coeff 0 2) : Poly3) ^ 2) * p00 +
            ((MvPolynomial.C (ρ.coeff 1 0) : Poly3) ^ 2 + (MvPolynomial.C (ρ.coeff 1 1) : Poly3) ^ 2 +
                (MvPolynomial.C (ρ.coeff 1 2) : Poly3) ^ 2) * p11 +
            ((MvPolynomial.C (ρ.coeff 2 0) : Poly3) ^ 2 + (MvPolynomial.C (ρ.coeff 2 1) : Poly3) ^ 2 +
                (MvPolynomial.C (ρ.coeff 2 2) : Poly3) ^ 2) * p22 +
            (((MvPolynomial.C (ρ.coeff 0 0) : Poly3) * MvPolynomial.C (ρ.coeff 1 0) +
                  MvPolynomial.C (ρ.coeff 0 1) * MvPolynomial.C (ρ.coeff 1 1) +
                  MvPolynomial.C (ρ.coeff 0 2) * MvPolynomial.C (ρ.coeff 1 2)) *
                ((2 : Poly3) * p01)) +
            (((MvPolynomial.C (ρ.coeff 0 0) : Poly3) * MvPolynomial.C (ρ.coeff 2 0) +
                  MvPolynomial.C (ρ.coeff 0 1) * MvPolynomial.C (ρ.coeff 2 1) +
                  MvPolynomial.C (ρ.coeff 0 2) * MvPolynomial.C (ρ.coeff 2 2)) *
                ((2 : Poly3) * p02)) +
            (((MvPolynomial.C (ρ.coeff 1 0) : Poly3) * MvPolynomial.C (ρ.coeff 2 0) +
                  MvPolynomial.C (ρ.coeff 1 1) * MvPolynomial.C (ρ.coeff 2 1) +
                  MvPolynomial.C (ρ.coeff 1 2) * MvPolynomial.C (ρ.coeff 2 2)) *
                ((2 : Poly3) * p12))) := by
          subst p00 p11 p22 p01 p02 p12
          unfold laplacian
          simp [Fin.sum_univ_three, Rotation.pderiv_compPolynomial, pderiv_comm]
          ring
    _ = p00 + p11 + p22 := by rw [h00', h11', h22', h01', h02', h12']; simp
    _ = ρ.compPolynomial (laplacian p) := by
          subst p00 p11 p22
          simp [laplacian, Fin.sum_univ_three]

theorem compPolynomial_mem_harmonicSubmodule (ρ : Rotation) {p : Poly3}
    (hp : p ∈ harmonicSubmodule) :
    ρ.compPolynomial p ∈ harmonicSubmodule := by
  change laplacian (ρ.compPolynomial p) = 0
  rw [laplacian_compPolynomial, show laplacian p = 0 from hp]
  simp

theorem compPolynomial_mem_harmonicHomogeneousSubmodule (ρ : Rotation) (n : ℕ) {p : Poly3}
    (hp : p ∈ harmonicHomogeneousSubmodule n) :
    ρ.compPolynomial p ∈ harmonicHomogeneousSubmodule n := by
  rcases Submodule.mem_inf.mp hp with ⟨hpn, hph⟩
  exact Submodule.mem_inf.mpr
    ⟨(MvPolynomial.mem_homogeneousSubmodule n _).mpr
      (compPolynomial_isHomogeneous ρ ((MvPolynomial.mem_homogeneousSubmodule n p).mp hpn)),
      compPolynomial_mem_harmonicSubmodule ρ hph⟩

end Rotation

theorem compContinuous_mem_sector (ρ : Rotation) (n : ℕ) {f : C(S2, ℝ)}
    (hf : f ∈ sector n) :
    Rotation.compContinuous ρ f ∈ sector n := by
  rcases hf with ⟨p, hp, rfl⟩
  refine ⟨ρ.compPolynomial p, Rotation.compPolynomial_mem_harmonicHomogeneousSubmodule ρ n hp, ?_⟩
  simpa using (Rotation.restrictToSphere_compPolynomial ρ p).symm

theorem compContinuous_map_sector (ρ : Rotation) (n : ℕ) :
    Submodule.map (Rotation.compContinuous ρ) (sector n) = sector n := by
  apply le_antisymm
  · intro f hf
    rcases hf with ⟨g, hg, rfl⟩
    exact compContinuous_mem_sector ρ n hg
  · intro f hf
    refine ⟨Rotation.compContinuous ρ.symm f, compContinuous_mem_sector ρ.symm n hf, ?_⟩
    ext x
    simpa [Rotation.compContinuous_apply] using congrArg f
      ((Rotation.toSphereEquiv ρ).apply_symm_apply x)

theorem continuousToLp_compContinuous_symm (ρ : Rotation) (f : C(S2, ℝ)) :
    Rotation.compL2Rotation ρ (continuousToLp f) =
      continuousToLp (Rotation.compContinuous ρ.symm f) := by
  rfl

theorem compL2Rotation_mem_sectorL2 (ρ : Rotation) (n : ℕ) {f : MeasureTheory.Lp ℝ 2 rotationMeasure}
    (hf : f ∈ sectorL2 n) :
    Rotation.compL2Rotation ρ f ∈ sectorL2 n := by
  rcases hf with ⟨g, hg, rfl⟩
  refine ⟨Rotation.compContinuous ρ.symm g, compContinuous_mem_sector ρ.symm n hg, ?_⟩
  simpa using (continuousToLp_compContinuous_symm ρ g).symm

theorem compL2Rotation_map_sectorL2 (ρ : Rotation) (n : ℕ) :
    Submodule.map (Rotation.compL2Rotation ρ).toLinearMap (sectorL2 n) = sectorL2 n := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · intro f hf
    rcases hf with ⟨g, hg, rfl⟩
    exact compL2Rotation_mem_sectorL2 ρ n hg
  · rw [← LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective (Rotation.compL2Rotation ρ).toLinearMap
        (Rotation.compL2Rotation ρ).injective (sectorL2 n))]

private theorem measurePreserving_toSphereEquiv_rotationMeasure (ρ : Rotation) :
    MeasureTheory.MeasurePreserving
      ((Rotation.toSphereEquiv ρ).toHomeomorph.toMeasurableEquiv)
      rotationMeasure rotationMeasure := by
  exact ⟨((Rotation.toSphereEquiv ρ).toHomeomorph.toMeasurableEquiv).measurable,
    by simpa using Rotation.map_rotationMeasure ρ⟩

theorem compL2Rotation_compL2Rotation_symm_apply (ρ : Rotation)
    (f : MeasureTheory.Lp ℝ 2 rotationMeasure) :
    Rotation.compL2Rotation ρ (Rotation.compL2Rotation ρ.symm f) = f := by
  apply Subtype.ext
  apply MeasureTheory.AEEqFun.ext
  have houter :
      (Rotation.compL2Rotation ρ (Rotation.compL2Rotation ρ.symm f)
          : MeasureTheory.Lp ℝ 2 rotationMeasure) =ᵐ[rotationMeasure]
        (Rotation.compL2Rotation ρ.symm f : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘
          (Rotation.toSphereEquiv ρ) := by
    simpa [Rotation.compL2Rotation] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving
        (g := Rotation.compL2Rotation ρ.symm f)
        (hf := measurePreserving_toSphereEquiv_rotationMeasure ρ))
  have hinner :
      (Rotation.compL2Rotation ρ.symm f : MeasureTheory.Lp ℝ 2 rotationMeasure) =ᵐ[rotationMeasure]
        (f : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘ (Rotation.toSphereEquiv ρ.symm) := by
    simpa [Rotation.compL2Rotation] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := f)
        (hf := measurePreserving_toSphereEquiv_rotationMeasure ρ.symm))
  have hcomp :
      (Rotation.compL2Rotation ρ.symm f : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘
          (Rotation.toSphereEquiv ρ) =ᵐ[rotationMeasure]
        (f : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘
          (Rotation.toSphereEquiv ρ.symm) ∘ (Rotation.toSphereEquiv ρ) :=
    Filter.EventuallyEq.comp_tendsto hinner
      (measurePreserving_toSphereEquiv_rotationMeasure ρ).quasiMeasurePreserving.tendsto_ae
  exact houter.trans <| hcomp.trans <| by
    filter_upwards with x
    simpa using congrArg (fun y => (f : MeasureTheory.Lp ℝ 2 rotationMeasure) y)
      ((Rotation.toSphereEquiv ρ).symm_apply_apply x)

theorem sectorL2_starProjection_compL2Rotation_apply (ρ : Rotation) (n : ℕ)
    (f : MeasureTheory.Lp ℝ 2 rotationMeasure) :
    (sectorL2 n).starProjection (Rotation.compL2Rotation ρ f) =
      Rotation.compL2Rotation ρ ((sectorL2 n).starProjection f) := by
  have hmap : Submodule.map (Rotation.compL2Rotation ρ) (sectorL2 n) = sectorL2 n := by
    simpa using compL2Rotation_map_sectorL2 ρ n
  simpa [hmap] using
    (LinearIsometry.map_starProjection'
      (f := Rotation.compL2Rotation ρ) (p := sectorL2 n) f).symm

end SphericalHarmonics
