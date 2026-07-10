import Gleason.Harmonic.HighDegree.HighEvenUnionClosed
import Gleason.Harmonic.Zonal.NorthZonalProperties
import Gleason.Harmonic.HighDegree.HighEvenBoundedClosure
import Gleason.Harmonic.Fischer.FischerNorthOrbit
import Mathlib.Topology.Instances.ENNReal.Lemmas

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral
open scoped Topology

theorem northOrbitAverage_add (f g : C(spherePoint3, ℝ)) :
    northOrbitAverage (f + g) = northOrbitAverage f + northOrbitAverage g := by
  ext x
  have hIntf :
      IntervalIntegrable (fun t : ℝ => f (sphereMap (northRotation t) x))
        volume 0 (2 * Real.pi) := by
    have hcont : Continuous (fun t : ℝ => f (sphereMap (northRotation t) x)) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  have hIntg :
      IntervalIntegrable (fun t : ℝ => g (sphereMap (northRotation t) x))
        volume 0 (2 * Real.pi) := by
    have hcont : Continuous (fun t : ℝ => g (sphereMap (northRotation t) x)) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  simp [northOrbitAverage_apply, ContinuousMap.add_apply]
  rw [intervalIntegral.integral_add]
  · ring
  · exact hIntf
  · exact hIntg

theorem northOrbitAverage_smul (c : ℝ) (f : C(spherePoint3, ℝ)) :
    northOrbitAverage (c • f) = c • northOrbitAverage f := by
  ext x
  simp [northOrbitAverage_apply, Pi.smul_apply, intervalIntegral.integral_const_mul,
    mul_assoc, mul_left_comm, mul_comm]

theorem northOrbitAverage_sub (f g : C(spherePoint3, ℝ)) :
    northOrbitAverage (f - g) = northOrbitAverage f - northOrbitAverage g := by
  ext x
  have hIntf :
      IntervalIntegrable (fun t : ℝ => f (sphereMap (northRotation t) x))
        volume 0 (2 * Real.pi) := by
    have hcont : Continuous (fun t : ℝ => f (sphereMap (northRotation t) x)) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  have hIntg :
      IntervalIntegrable (fun t : ℝ => g (sphereMap (northRotation t) x))
        volume 0 (2 * Real.pi) := by
    have hcont : Continuous (fun t : ℝ => g (sphereMap (northRotation t) x)) := by
      continuity
    exact hcont.intervalIntegrable 0 (2 * Real.pi)
  simp [northOrbitAverage_apply]
  rw [intervalIntegral.integral_sub]
  · ring
  · exact hIntf
  · exact hIntg

theorem norm_northOrbitAverage_le (f : C(spherePoint3, ℝ)) :
    ‖northOrbitAverage f‖ ≤ ‖f‖ := by
  haveI : Nonempty spherePoint3 := ⟨sphereE1⟩
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 ?_
  intro x
  rw [northOrbitAverage_apply]
  have hpos : 0 < 2 * Real.pi := by positivity
  have hInt :
      ‖∫ t in 0..2 * Real.pi, f (sphereMap (northRotation t) x)‖ ≤
        ‖f‖ * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro t ht
    exact f.norm_coe_le_norm (sphereMap (northRotation t) x)
  calc
    ‖((2 * Real.pi)⁻¹ : ℝ) * ∫ t in 0..2 * Real.pi, f (sphereMap (northRotation t) x)‖
        = ‖((2 * Real.pi)⁻¹ : ℝ)‖ *
            ‖∫ t in 0..2 * Real.pi, f (sphereMap (northRotation t) x)‖ := by
              rw [norm_mul]
    _ ≤ ‖((2 * Real.pi)⁻¹ : ℝ)‖ * (‖f‖ * |2 * Real.pi - 0|) := by
          gcongr
    _ = ‖f‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
          rw [sub_zero, abs_of_pos hpos]
          field_simp [hpos.ne']

theorem norm_northOrbitAverage_sub_le (f g : C(spherePoint3, ℝ)) :
    ‖northOrbitAverage f - northOrbitAverage g‖ ≤ ‖f - g‖ := by
  rw [← northOrbitAverage_sub]
  exact norm_northOrbitAverage_le (f - g)

theorem dist_northOrbitAverage_le (f g : C(spherePoint3, ℝ)) :
    dist (northOrbitAverage f) (northOrbitAverage g) ≤ dist f g := by
  simpa [dist_eq_norm] using norm_northOrbitAverage_sub_le f g

theorem northOrbitAverage_mem_highEvenUnionHarmonicPolyHomogeneousImageSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule) :
    northOrbitAverage f ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule := by
  have hmono : Monotone (fun N : ℕ => highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) := by
    intro N M hNM
    exact highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono hNM
  have hbounded :
      ∀ {N : ℕ} {f : C(spherePoint3, ℝ)},
        f ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N →
          northOrbitAverage f ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
    intro N f hfN
    have hclosed :
        IsClosed
          ((highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N :
            Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ)) :=
      isClosed_highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N
    have hinv :
        ∀ t : ℝ,
          highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ≤
            (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).comap
              (spherePrecomp (northRotation t)) := by
      intro t g hg
      have hmap :
          spherePrecomp (northRotation t) g ∈
            (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).map
              (spherePrecompLinearEquiv (northRotation t)).toLinearMap := by
        exact ⟨g, hg, rfl⟩
      simpa [highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_invariant_under_spherePrecomp
        N (northRotation t)] using hmap
    exact northOrbitAverage_mem_of_isClosed_of_invariant hclosed hinv hfN
  obtain ⟨N, hN⟩ :=
    (Submodule.mem_iSup_of_directed (R := ℝ)
      (S := fun N : ℕ => highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
      hmono.directed_le).1 hf
  exact Submodule.mem_iSup_of_mem N <|
    hbounded hN

theorem exists_northZonal_mem_highEvenUnion_close_of_mem_topologicalClosure_highEvenUnion_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg : g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure)
    (hgz : IsNorthZonal g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : C(spherePoint3, ℝ),
      h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
      IsNorthZonal h ∧
      ‖h - g‖ < ε := by
  rcases Metric.mem_closure_iff.1
      (by simpa [Submodule.topologicalClosure_coe] using hg) ε hε with
    ⟨h0, hh0, hh0dist⟩
  refine ⟨northOrbitAverage h0,
    northOrbitAverage_mem_highEvenUnionHarmonicPolyHomogeneousImageSubmodule hh0,
    northOrbitAverage_isNorthZonal h0, ?_⟩
  calc
    ‖northOrbitAverage h0 - g‖
        = ‖northOrbitAverage h0 - northOrbitAverage g‖ := by
            rw [northOrbitAverage_eq_self_of_isNorthZonal hgz]
    _ ≤ ‖h0 - g‖ := norm_northOrbitAverage_sub_le h0 g
    _ < ε := by
          simpa [dist_eq_norm, norm_sub_rev] using hh0dist
