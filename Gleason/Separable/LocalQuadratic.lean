import Gleason.Separable.FiniteRestriction

/-!
# Local Quadraticity

The quadratic function associated to a projection measure is restricted to a
finite-dimensional subspace containing an independent triple and the vectors
under consideration. The finite-dimensional theorem then supplies the
parallelogram identity. Subspaces of measure zero are handled directly by
positivity.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ProjectionMeasure

/-- The rank hypothesis provides a linearly independent triple. -/
theorem exists_independent_triple
    (hdim : (3 : Cardinal) ≤ Module.rank ℂ H) :
    ∃ s : Finset H, s.card = 3 ∧
      LinearIndependent ℂ ((↑) : ↥(s : Set H) → H) :=
  (le_rank_iff_exists_linearIndependent_finset (K := ℂ) (V := H) (n := 3)).mp hdim

/-- The rank-one quadratic function satisfies the parallelogram identity. -/
theorem quadraticValue_parallelogram
    (m : ProjectionMeasure ℂ H) (hdim : (3 : Cardinal) ≤ Module.rank ℂ H)
    (x y : H) :
    m.quadraticValue (x + y) + m.quadraticValue (x - y) =
      2 * m.quadraticValue x + 2 * m.quadraticValue y := by
  classical
  obtain ⟨s, hs_card, hs_indep⟩ := exists_independent_triple (H := H) hdim
  let t : Finset H := insert x (insert y s)
  let K : Submodule ℂ H := Submodule.span ℂ (t : Set H)
  letI : FiniteDimensional ℂ K := by infer_instance
  letI : CompleteSpace K := FiniteDimensional.complete ℂ K

  have hs_span_le : Submodule.span ℂ (s : Set H) ≤ K := by
    apply Submodule.span_mono
    intro z hz
    simp only [K, t, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
    exact Or.inr (Or.inr hz)
  have hs_finrank : Module.finrank ℂ (Submodule.span ℂ (s : Set H)) = 3 := by
    have h := finrank_span_eq_card hs_indep
    rw [show Set.range ((↑) : ↥(s : Set H) → H) = (s : Set H) by
      ext z
      simp] at h
    simpa [hs_card] using h
  have hdimK : 3 ≤ Module.finrank ℂ K := by
    rw [← hs_finrank]
    exact Submodule.finrank_mono hs_span_le

  have hxK : x ∈ K := by
    apply Submodule.subset_span
    simp [K, t]
  have hyK : y ∈ K := by
    apply Submodule.subset_span
    simp [K, t]
  let xK : K := ⟨x, hxK⟩
  let yK : K := ⟨y, hyK⟩

  by_cases hKzero : m.μ (FiniteRestriction.subspaceProjection K) = 0
  · have hxy := FiniteRestriction.quadraticValue_coe_eq_zero_of_subspace_measure_eq_zero
      K m hKzero (xK + yK)
    have hxy' := FiniteRestriction.quadraticValue_coe_eq_zero_of_subspace_measure_eq_zero
      K m hKzero (xK - yK)
    have hx := FiniteRestriction.quadraticValue_coe_eq_zero_of_subspace_measure_eq_zero
      K m hKzero xK
    have hy := FiniteRestriction.quadraticValue_coe_eq_zero_of_subspace_measure_eq_zero
      K m hKzero yK
    have hxy0 : m.quadraticValue (x + y) = 0 := by simpa [xK, yK] using hxy
    have hxy0' : m.quadraticValue (x - y) = 0 := by simpa [xK, yK] using hxy'
    have hx0 : m.quadraticValue x = 0 := by simpa [xK] using hx
    have hy0 : m.quadraticValue y = 0 := by simpa [yK] using hy
    simp [hxy0, hxy0', hx0, hy0]
  · have hKpos : 0 < m.μ (FiniteRestriction.subspaceProjection K) :=
      lt_of_le_of_ne (m.nonneg _) (Ne.symm hKzero)
    have hpara := frame_quadratic_full_parallelogram_from_oscillation
      hdimK (FiniteRestriction.frameFunction K m hKpos) xK yK
    simp_rw [FiniteRestriction.frame_quadratic_eq_div K m hKpos] at hpara
    field_simp [hKzero] at hpara
    simpa [xK, yK, mul_add] using hpara

/-- The rank-one quadratic function is a bounded complex quadratic form. -/
theorem quadraticValue_isBoundedQuadraticForm
    (m : ProjectionMeasure ℂ H) (hdim : (3 : Cardinal) ≤ Module.rank ℂ H) :
    IsBoundedQuadraticForm m.quadraticValue where
  sq_hom := m.quadraticValue_smul
  parallelogram := m.quadraticValue_parallelogram hdim
  bounded := ⟨m.μ 1, m.abs_quadraticValue_le⟩

end ProjectionMeasure

end ClassicalGleason.Separable
