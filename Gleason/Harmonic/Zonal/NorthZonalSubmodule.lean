import Gleason.Harmonic.Zonal.NorthZonalProperties

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

def northZonalSubmodule : Submodule ℝ C(spherePoint3, ℝ) where
  carrier := {f | IsNorthZonal f}
  zero_mem' := by
    intro t
    ext x
    simp [IsNorthZonal, spherePrecomp_apply]
  add_mem' := by
    intro f g hf hg t
    ext x
    simp [hf t, hg t, spherePrecomp_apply]
  smul_mem' := by
    intro c f hf t
    ext x
    simp [hf t, spherePrecomp_apply]

@[simp] lemma mem_northZonalSubmodule_iff
    (f : C(spherePoint3, ℝ)) :
    f ∈ northZonalSubmodule ↔ IsNorthZonal f := by
  rfl

lemma isClosed_setOf_northRotation_fixed (t : ℝ) :
    IsClosed {f : C(spherePoint3, ℝ) | spherePrecomp (northRotation t) f = f} := by
  simpa [spherePrecompCLM_apply] using
    isClosed_eq (spherePrecompCLM (northRotation t)).continuous continuous_id

theorem isClosed_northZonalSubmodule :
    IsClosed (northZonalSubmodule : Set C(spherePoint3, ℝ)) := by
  have hEq :
      (northZonalSubmodule : Set C(spherePoint3, ℝ)) =
        ⋂ t : ℝ, {f : C(spherePoint3, ℝ) | spherePrecomp (northRotation t) f = f} := by
    ext f
    simp [northZonalSubmodule, IsNorthZonal]
  rw [hEq]
  exact isClosed_iInter isClosed_setOf_northRotation_fixed

def northZonalClosedSubmodule : ClosedSubmodule ℝ C(spherePoint3, ℝ) :=
  ⟨northZonalSubmodule, isClosed_northZonalSubmodule⟩

lemma northOrbitAverage_mem_northZonalSubmodule
    (f : C(spherePoint3, ℝ)) :
    northOrbitAverage f ∈ northZonalSubmodule := by
  exact northOrbitAverage_isNorthZonal f

lemma northOrbitAverage_eq_self_of_mem_northZonalSubmodule
    {f : C(spherePoint3, ℝ)} (hf : f ∈ northZonalSubmodule) :
    northOrbitAverage f = f := by
  exact northOrbitAverage_eq_self_of_isNorthZonal hf

lemma northOrbitAverage_mem_inf_of_isClosed_of_invariant
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGinv :
      ∀ t : ℝ, G ≤ G.comap (spherePrecomp (northRotation t)))
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ G) :
    northOrbitAverage f ∈ G ⊓ northZonalSubmodule := by
  refine ⟨northOrbitAverage_mem_of_isClosed_of_invariant hGclosed hGinv hf,
    northOrbitAverage_mem_northZonalSubmodule f⟩
