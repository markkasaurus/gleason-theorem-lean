import SphericalHarmonics.Zonal

open scoped BigOperators

namespace SphericalHarmonics

/-- Every homogeneous polynomial of degree `0` is harmonic. -/
theorem mem_harmonicHomogeneousSubmodule_zero_of_mem_homogeneousSubmodule
    {p : Poly3} (hp : p ∈ homogeneousSubmodule 0) :
    p ∈ harmonicHomogeneousSubmodule 0 := by
  refine Submodule.mem_inf.mpr ⟨hp, ?_⟩
  have hconst : ∃ c : ℝ, p = MvPolynomial.C c := by
    have hzero : homogeneousSubmodule 0 = (1 : Submodule ℝ Poly3) := by
      simpa using (MvPolynomial.homogeneousSubmodule_zero (σ := Fin 3) (R := ℝ))
    rw [hzero] at hp
    rcases (show ∃ y, MvPolynomial.C y = p by simpa [Submodule.mem_one] using hp) with ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  rcases hconst with ⟨c, rfl⟩
  simp [harmonicSubmodule, laplacian, Fin.sum_univ_three]

/-- Restricting a degree-`0` homogeneous polynomial lands in the degree-`0` sector. -/
theorem restrict_mem_sector_zero_of_mem_homogeneousSubmodule
    {p : Poly3} (hp : p ∈ homogeneousSubmodule 0) :
    restrictToSphere p ∈ sector 0 :=
  restrict_mem_sector <| mem_harmonicHomogeneousSubmodule_zero_of_mem_homogeneousSubmodule hp

/-- Every homogeneous polynomial of degree `1` is harmonic. -/
theorem mem_harmonicHomogeneousSubmodule_one_of_mem_homogeneousSubmodule
    {p : Poly3} (hp : p ∈ homogeneousSubmodule 1) :
    p ∈ harmonicHomogeneousSubmodule 1 := by
  have hp' : p.IsHomogeneous 1 := (MvPolynomial.mem_homogeneousSubmodule 1 p).mp hp
  refine Submodule.mem_inf.mpr ⟨hp, ?_⟩
  show laplacian p = 0
  have hconst : ∀ i : Fin 3, ∃ c : ℝ, MvPolynomial.pderiv i p = MvPolynomial.C c := by
    intro i
    have hi : (MvPolynomial.pderiv i p).IsHomogeneous 0 := by
      simpa using (hp'.pderiv (i := i))
    have hmem : MvPolynomial.pderiv i p ∈ homogeneousSubmodule 0 :=
      (MvPolynomial.mem_homogeneousSubmodule 0 (MvPolynomial.pderiv i p)).mpr hi
    refine ⟨MvPolynomial.coeff 0 (MvPolynomial.pderiv i p), ?_⟩
    rw [← MvPolynomial.homogeneousComponent_zero (φ := MvPolynomial.pderiv i p)]
    simpa using (MvPolynomial.homogeneousComponent_of_mem (m := 0) hmem).symm
  have hzero : ∀ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p) = 0 := by
    intro i
    rcases hconst i with ⟨c, hc⟩
    rw [hc]
    simp
  unfold laplacian
  simp [Fin.sum_univ_three, hzero]

/-- Restricting a degree-`1` homogeneous polynomial lands in the degree-`1` sector. -/
theorem restrict_mem_sector_one_of_mem_homogeneousSubmodule
    {p : Poly3} (hp : p ∈ homogeneousSubmodule 1) :
    restrictToSphere p ∈ sector 1 :=
  restrict_mem_sector <| mem_harmonicHomogeneousSubmodule_one_of_mem_homogeneousSubmodule hp

/-- The quadratic harmonic correction of a homogeneous quadratic polynomial. -/
noncomputable def quadraticHarmonicCorrection (p : Poly3) : Poly3 :=
  p - (MvPolynomial.coeff 0 (laplacian p) / 6) • radiusSq

@[simp] theorem quadraticHarmonicCorrection_sub (p : Poly3) :
    quadraticHarmonicCorrection p =
      p - (MvPolynomial.coeff 0 (laplacian p) / 6) • radiusSq := rfl

/-- The standard quadratic Fischer decomposition step in `ℝ^3`: subtracting the radial part from a
homogeneous quadratic polynomial produces a harmonic quadratic polynomial. -/
theorem quadraticHarmonicCorrection_mem_harmonicHomogeneousSubmodule
    {p : Poly3} (hp : p ∈ homogeneousSubmodule 2) :
    quadraticHarmonicCorrection p ∈ harmonicHomogeneousSubmodule 2 := by
  have hp' : p.IsHomogeneous 2 := (MvPolynomial.mem_homogeneousSubmodule 2 p).mp hp
  refine Submodule.mem_inf.mpr ?_
  constructor
  · have hrad :
        ((MvPolynomial.coeff 0 (laplacian p) / 6) • radiusSq).IsHomogeneous 2 := by
        simpa [Algebra.smul_def] using
          radiusSq_isHomogeneous.C_mul (MvPolynomial.coeff 0 (laplacian p) / 6)
    exact hp'.sub hrad
  · show laplacian (quadraticHarmonicCorrection p) = 0
    have hconst : laplacian p = MvPolynomial.C (MvPolynomial.coeff 0 (laplacian p)) := by
      rw [← MvPolynomial.homogeneousComponent_zero (φ := laplacian p)]
      have hmem : laplacian p ∈ homogeneousSubmodule 0 := by
        refine (MvPolynomial.mem_homogeneousSubmodule 0 (laplacian p)).mpr ?_
        simpa using laplacian_isHomogeneous hp'
      simpa using (MvPolynomial.homogeneousComponent_of_mem (m := 0) hmem).symm
    rw [quadraticHarmonicCorrection_sub, LinearMap.map_sub, LinearMap.map_smul, hconst]
    have hsix : (6 : Poly3) = MvPolynomial.C (6 : ℝ) := rfl
    ext d
    by_cases hd : d = 0
    · subst hd
      simp [hsix, MvPolynomial.coeff_C]
    · have h0d : ¬ (0 : Fin 3 →₀ ℕ) = d := by
        intro h
        exact hd h.symm
      simp [hsix, MvPolynomial.coeff_C, h0d]

/-- On the sphere, the radial correction collapses to a constant. -/
theorem restrictToSphere_quadraticHarmonicCorrection_add
    {p : Poly3} :
    restrictToSphere p =
      restrictToSphere (quadraticHarmonicCorrection p) +
        (MvPolynomial.coeff 0 (laplacian p) / 6 : ℝ) • (1 : C(S2, ℝ)) := by
  ext x
  simp [quadraticHarmonicCorrection_sub]

/-- Restricting a homogeneous quadratic polynomial lands in the sum of the degree-`0` and
degree-`2` sectors. -/
theorem restrict_mem_sector_zero_sup_sector_two_of_mem_homogeneousSubmodule
    {p : Poly3} (hp : p ∈ homogeneousSubmodule 2) :
    restrictToSphere p ∈ sector 0 ⊔ sector 2 := by
  have hharm :
      quadraticHarmonicCorrection p ∈ harmonicHomogeneousSubmodule 2 :=
    quadraticHarmonicCorrection_mem_harmonicHomogeneousSubmodule hp
  have hz0 : zonal0 = (1 : C(S2, ℝ)) := by
    ext x
    simp [zonal0, zonalFromPolynomial]
  have hconst :
      (MvPolynomial.coeff 0 (laplacian p) / 6 : ℝ) • (1 : C(S2, ℝ)) ∈ sector 0 := by
    rw [← hz0]
    exact (sector 0).smul_mem _ zonal0_mem_sector
  have hharm' : restrictToSphere (quadraticHarmonicCorrection p) ∈ sector 2 :=
    restrict_mem_sector hharm
  rw [restrictToSphere_quadraticHarmonicCorrection_add]
  refine Submodule.add_mem (sector 0 ⊔ sector 2)
    (Submodule.mem_sup_right hharm') ?_
  exact Submodule.mem_sup_left hconst

/-- The low-degree spherical sector span. -/
noncomputable def lowDegreeSector : Submodule ℝ C(S2, ℝ) :=
  sector 0 ⊔ sector 1 ⊔ sector 2

/-- Every polynomial restriction of total degree at most `2` belongs to the sum of the degree
`0`, `1`, and `2` sectors. -/
theorem restrict_mem_lowDegreeSector_of_totalDegree_le_two
    {p : Poly3} (hp : p.totalDegree ≤ 2) :
    restrictToSphere p ∈ lowDegreeSector := by
  have hsum := MvPolynomial.sum_homogeneousComponent (φ := p)
  have hle0 : sector 0 ≤ lowDegreeSector := by
    rw [lowDegreeSector]
    exact le_trans le_sup_left le_sup_left
  have hle1 : sector 1 ≤ lowDegreeSector := by
    rw [lowDegreeSector]
    exact le_trans le_sup_right le_sup_left
  have hle2 : sector 2 ≤ lowDegreeSector := by
    rw [lowDegreeSector]
    exact le_sup_right
  have hle02 : sector 0 ⊔ sector 2 ≤ lowDegreeSector := sup_le hle0 hle2
  have hsum_mem :
      ∑ i ∈ Finset.range (p.totalDegree + 1),
        restrictToSphere (MvPolynomial.homogeneousComponent i p) ∈ lowDegreeSector := by
    refine Submodule.sum_mem _ ?_
    intro i hi
    have hi_le : i ≤ 2 := by
      exact le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp
    have hmem :
        MvPolynomial.homogeneousComponent i p ∈ homogeneousSubmodule i :=
      (MvPolynomial.mem_homogeneousSubmodule i _).mpr
        (MvPolynomial.homogeneousComponent_isHomogeneous (n := i) (φ := p))
    interval_cases i
    · exact hle0 <| restrict_mem_sector_zero_of_mem_homogeneousSubmodule hmem
    · exact hle1 <| restrict_mem_sector_one_of_mem_homogeneousSubmodule hmem
    · exact hle02 <| restrict_mem_sector_zero_sup_sector_two_of_mem_homogeneousSubmodule hmem
  rw [← hsum]
  simpa using hsum_mem

end SphericalHarmonics
