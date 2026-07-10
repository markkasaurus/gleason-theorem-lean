import Gleason.Harmonic.HighDegree.HighEvenUnionFixedApprox

noncomputable section

open Complex InnerProductSpace

theorem exists_nonzero_northZonal_mem_topologicalClosure_highEvenUnion_inf_frame_with_pole_ne_zero
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      g sphereE3 ≠ 0 := by
  let G : Submodule ℝ C(spherePoint3, ℝ) :=
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule
  have hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)) := by
    simpa [G] using
      (isClosed_topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule).inter
        isClosed_continuousSphereFrameSubmodule
  have hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G := by
    intro e
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨?_, continuousSphereFrameSubmodule_invariant_under_spherePrecomp e hg.2⟩
      have hmap :
          spherePrecomp e g ∈
            (highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure).map
              (spherePrecompLinearEquiv e).toLinearMap := by
        exact ⟨g, hg.1, rfl⟩
      simpa [topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv e]
        using hmap
    · intro hf
      refine ⟨spherePrecomp e.symm f, ?_, ?_⟩
      · refine ⟨?_, continuousSphereFrameSubmodule_invariant_under_spherePrecomp e.symm hf.2⟩
        have hmap :
            spherePrecomp e.symm f ∈
              (highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure).map
                (spherePrecompLinearEquiv e.symm).toLinearMap := by
          exact ⟨f, hf.1, rfl⟩
        simpa [topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule_map_spherePrecompLinearEquiv e.symm]
          using hmap
      · ext x
        simp [spherePrecompLinearEquiv, spherePrecomp]
  have hGnorth :
      ∀ t : ℝ, G ≤ G.comap (spherePrecomp (northRotation t)) := by
    intro t g hg
    have hmap :
        spherePrecomp (northRotation t) g ∈
          G.map (spherePrecompLinearEquiv (northRotation t)).toLinearMap := by
      exact ⟨g, hg, rfl⟩
    simpa [hGrot (northRotation t)] using hmap
  have hbotlt : ⊥ < G := bot_lt_iff_ne_bot.mpr hne
  rcases SetLike.exists_of_lt hbotlt with ⟨f, hfG, hf0⟩
  have hfne : f ≠ 0 := by
    intro h
    exact hf0 (by simp [h])
  rcases exists_point_ne_zero_of_ne_zero hfne with ⟨z, hz⟩
  rcases exists_orthonormal_completion_of_spherePoint z with ⟨x, y, hxy, hxz, hyz⟩
  let e := sphereTripleIsometryEquiv x y z hxy hxz hyz
  have hmap :
      spherePrecomp e f ∈ G.map (spherePrecompLinearEquiv e).toLinearMap := by
    exact ⟨f, hfG, rfl⟩
  have hfe : spherePrecomp e f ∈ G := by
    simpa [hGrot e] using hmap
  have hpole : spherePrecomp e f sphereE3 ≠ 0 := by
    simpa [spherePrecomp_apply, e, sphereMap_sphereTripleIsometryEquiv_sphereE3] using hz
  let g := northOrbitAverage (spherePrecomp e f)
  have hgG : g ∈ G :=
    northOrbitAverage_mem_of_isClosed_of_invariant hGclosed hGnorth hfe
  have hgne : g ≠ 0 :=
    northOrbitAverage_ne_zero_of_sphereE3_ne_zero hpole
  have hgz : IsNorthZonal g :=
    northOrbitAverage_isNorthZonal (spherePrecomp e f)
  have hgpole : g sphereE3 ≠ 0 := by
    have hEq : g sphereE3 = (spherePrecomp e f) sphereE3 := by
      simpa [g] using northOrbitAverage_sphereE3 (spherePrecomp e f)
    rw [hEq]
    exact hpole
  exact ⟨g, hgG, hgne, hgz, hgpole⟩

theorem exists_fixed_northZonal_with_highEvenUnion_approx_of_nontrivial_tail_with_pole_ne_zero
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
      ∀ {ε : ℝ}, 0 < ε →
        ∃ h : C(spherePoint3, ℝ),
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          ‖h - g‖ < ε := by
  rcases exists_nonzero_northZonal_mem_topologicalClosure_highEvenUnion_inf_frame_with_pole_ne_zero hne with
    ⟨g, hg, hgne, hgz, hgpole⟩
  refine ⟨g, hg, hgne, hgz, northOrbitAverage_eq_self_of_isNorthZonal hgz, hgpole, ?_⟩
  intro ε hε
  exact exists_northZonal_mem_highEvenUnion_close_of_mem_topologicalClosure_highEvenUnion_of_isNorthZonal
    hg.1 hgz hε
