import Gleason.Harmonic.Zonal.NorthZonalReduction
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

lemma northOrbitAverage_eq_setAverage
    (f : C(spherePoint3, ℝ)) :
    northOrbitAverage f =
      ⨍ t in Set.Ioc 0 (2 * Real.pi), spherePrecomp (northRotation t) f ∂volume := by
  rw [northOrbitAverage, MeasureTheory.setAverage_eq]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  rw [intervalIntegral_eq_integral_uIoc]
  simp [hpi]

lemma northOrbitAverage_mem_of_isClosed_of_invariant
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGinv :
      ∀ t : ℝ, G ≤ G.comap (spherePrecomp (northRotation t)))
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ G) :
    northOrbitAverage f ∈ G := by
  have h0 : volume (Set.Ioc 0 (2 * Real.pi)) ≠ 0 := by
    rw [Real.volume_Ioc]
    rw [ENNReal.ofReal_ne_zero_iff]
    nlinarith [Real.pi_pos]
  have ht : volume (Set.Ioc 0 (2 * Real.pi)) ≠ ⊤ := by
    simpa using (measure_Ioc_lt_top (μ := volume) (a := 0) (b := 2 * Real.pi)).ne
  have hfs :
      ∀ᵐ t ∂volume.restrict (Set.Ioc 0 (2 * Real.pi)),
        spherePrecomp (northRotation t) f ∈ (G : Set C(spherePoint3, ℝ)) := by
    exact Filter.Eventually.of_forall fun t => hGinv t hf
  have hfi :
      IntegrableOn (fun t : ℝ => spherePrecomp (northRotation t) f)
        (Set.Ioc 0 (2 * Real.pi)) volume := by
    exact (northRotationOrbitContinuous f).integrableOn_Ioc
  rw [northOrbitAverage_eq_setAverage]
  exact G.convex.set_average_mem hGclosed h0 ht hfs hfi

theorem exists_nonzero_northZonal_mem_of_isClosed_of_rotationInvariant
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGne : G ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ), g ∈ G ∧ g ≠ 0 ∧ IsNorthZonal g := by
  have hGnorth :
      ∀ t : ℝ, G ≤ G.comap (spherePrecomp (northRotation t)) := by
    intro t g hg
    have hmap :
        spherePrecomp (northRotation t) g ∈
          G.map (spherePrecompLinearEquiv (northRotation t)).toLinearMap := by
      exact ⟨g, hg, rfl⟩
    simpa [hGrot (northRotation t)] using hmap
  have hbotlt : ⊥ < G := bot_lt_iff_ne_bot.mpr hGne
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
  have hnorth :
      spherePrecomp e f sphereE3 ≠ 0 := by
    simpa [spherePrecomp_apply, e, sphereMap_sphereTripleIsometryEquiv_sphereE3] using hz
  let g := northOrbitAverage (spherePrecomp e f)
  have hgG : g ∈ G :=
    northOrbitAverage_mem_of_isClosed_of_invariant hGclosed hGnorth hfe
  have hgne : g ≠ 0 := northOrbitAverage_ne_zero_of_sphereE3_ne_zero hnorth
  exact ⟨g, hgG, hgne, northOrbitAverage_isNorthZonal (spherePrecomp e f)⟩
