import Gleason.Harmonic.HighDegree.HighEvenUnionClosed
import Gleason.Harmonic.HighDegree.HighEvenUnionNorthZonalApprox

noncomputable section

open Complex InnerProductSpace

theorem exists_fixed_northZonal_with_highEvenUnion_approx_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      ∀ {ε : ℝ}, 0 < ε →
        ∃ h : C(spherePoint3, ℝ),
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          ‖h - g‖ < ε := by
  rcases exists_nonzero_northZonal_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz⟩
  have hfix : northOrbitAverage g = g := northOrbitAverage_eq_self_of_isNorthZonal hgz
  refine ⟨g, hg, hgne, hgz, hfix, ?_⟩
  intro ε hε
  exact exists_northZonal_mem_highEvenUnion_close_of_mem_topologicalClosure_highEvenUnion_of_isNorthZonal
    hg.1 hgz hε
