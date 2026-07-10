import Gleason.Continuity.Auxiliary.FrameEven
import Gleason.Harmonic.Sphere.SphereCoordsAlgebra
import Mathlib.Topology.ContinuousMap.Algebra

noncomputable section

open Complex InnerProductSpace

def sphereAntipodeCont : C(spherePoint3, spherePoint3) :=
  ⟨sphereAntipode, continuous_sphereMap (LinearIsometryEquiv.neg ℝ)⟩

def sphereAntipodeAlgHom :
    C(spherePoint3, ℝ) →ₐ[ℝ] C(spherePoint3, ℝ) :=
  ContinuousMap.compRightAlgHom ℝ ℝ sphereAntipodeCont

@[simp] theorem sphereAntipodeAlgHom_apply
    (f : C(spherePoint3, ℝ)) (x : spherePoint3) :
    sphereAntipodeAlgHom f x = f (sphereAntipode x) := by
  rfl

@[simp] theorem sphereAntipode_involutive (x : spherePoint3) :
    sphereAntipode (sphereAntipode x) = x := by
  apply Subtype.ext
  simp [sphereAntipode, sphereMap, LinearIsometryEquiv.coe_neg]

@[simp] theorem sphereAntipodeAlgHom_sphereCoordRe :
    sphereAntipodeAlgHom sphereCoordRe = -sphereCoordRe := by
  ext x
  simp [sphereAntipodeAlgHom, sphereAntipodeCont, sphereAntipode, sphereCoordRe,
    sphereMap, LinearIsometryEquiv.coe_neg]

@[simp] theorem sphereAntipodeAlgHom_sphereCoordIm :
    sphereAntipodeAlgHom sphereCoordIm = -sphereCoordIm := by
  ext x
  simp [sphereAntipodeAlgHom, sphereAntipodeCont, sphereAntipode, sphereCoordIm,
    sphereMap, LinearIsometryEquiv.coe_neg]

@[simp] theorem sphereAntipodeAlgHom_sphereCoordZ :
    sphereAntipodeAlgHom sphereCoordZ = -sphereCoordZ := by
  ext x
  simp [sphereAntipodeAlgHom, sphereAntipodeCont, sphereAntipode, sphereCoordZ,
    sphereMap, LinearIsometryEquiv.coe_neg]

theorem sphereAntipodeAlgHom_mem_sphereCoordinateSubalgebra
    {f : C(spherePoint3, ℝ)} (hf : f ∈ sphereCoordinateSubalgebra) :
    sphereAntipodeAlgHom f ∈ sphereCoordinateSubalgebra := by
  have hmap :
      sphereCoordinateSubalgebra.map sphereAntipodeAlgHom ≤ sphereCoordinateSubalgebra := by
    rw [sphereCoordinateSubalgebra, AlgHom.map_adjoin]
    apply Algebra.adjoin_le
    intro g hg
    rcases (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg) with rfl | rfl | rfl
    · simpa using
        (Subalgebra.neg_mem sphereCoordinateSubalgebra
          (Algebra.subset_adjoin (by simp)))
    · simpa using
        (Subalgebra.neg_mem sphereCoordinateSubalgebra
          (Algebra.subset_adjoin (by simp)))
    · simpa using
        (Subalgebra.neg_mem sphereCoordinateSubalgebra
          (Algebra.subset_adjoin (by simp)))
  exact hmap <| Subalgebra.mem_map.mpr ⟨f, hf, rfl⟩

def sphereEvenSymmLinear : C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ) :=
  ((2 : ℝ)⁻¹) • (LinearMap.id + sphereAntipodeAlgHom.toLinearMap)

def sphereEvenSymm (f : C(spherePoint3, ℝ)) : C(spherePoint3, ℝ) :=
  sphereEvenSymmLinear f

@[simp] theorem sphereEvenSymm_apply
    (f : C(spherePoint3, ℝ)) (x : spherePoint3) :
    sphereEvenSymm f x = ((2 : ℝ)⁻¹) * (f x + f (sphereAntipode x)) := by
  simp [sphereEvenSymm, sphereEvenSymmLinear, sphereAntipodeAlgHom_apply]
  ring

theorem sphereEvenSymm_mem_sphereCoordinateSubalgebra
    {f : C(spherePoint3, ℝ)} (hf : f ∈ sphereCoordinateSubalgebra) :
    sphereEvenSymm f ∈ sphereCoordinateSubalgebra := by
  rw [sphereEvenSymm, sphereEvenSymmLinear]
  exact Subalgebra.smul_mem (S := sphereCoordinateSubalgebra)
    (Subalgebra.add_mem sphereCoordinateSubalgebra hf
      (sphereAntipodeAlgHom_mem_sphereCoordinateSubalgebra hf))
    ((2 : ℝ)⁻¹)

theorem sphereEvenSymm_mem_continuousSphereEvenSubmodule
    (f : C(spherePoint3, ℝ)) :
    sphereEvenSymm f ∈ continuousSphereEvenSubmodule := by
  intro x
  rw [sphereEvenSymm_apply, sphereEvenSymm_apply, sphereAntipode_involutive]
  ring

theorem sphereEvenSymm_eq_of_mem_continuousSphereEvenSubmodule
    {f : C(spherePoint3, ℝ)} (hf : f ∈ continuousSphereEvenSubmodule) :
    sphereEvenSymm f = f := by
  ext x
  rw [sphereEvenSymm_apply, hf x]
  ring

lemma norm_sphereAntipodeAlgHom_le (f : C(spherePoint3, ℝ)) :
    ‖sphereAntipodeAlgHom f‖ ≤ ‖f‖ := by
  haveI : Nonempty spherePoint3 := ⟨sphereE1⟩
  refine (ContinuousMap.norm_le_of_nonempty (f := sphereAntipodeAlgHom f) (M := ‖f‖)).2 ?_
  intro x
  simpa [sphereAntipodeAlgHom_apply] using f.norm_coe_le_norm (sphereAntipode x)

lemma norm_sphereEvenSymm_le (f : C(spherePoint3, ℝ)) :
    ‖sphereEvenSymm f‖ ≤ ‖f‖ := by
  calc
    ‖sphereEvenSymm f‖
      = ‖((2 : ℝ)⁻¹) • (f + sphereAntipodeAlgHom f)‖ := by
          simp [sphereEvenSymm, sphereEvenSymmLinear]
    _ ≤ ((2 : ℝ)⁻¹) * (‖f‖ + ‖sphereAntipodeAlgHom f‖) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          gcongr
          exact norm_add_le _ _
    _ ≤ ((2 : ℝ)⁻¹) * (‖f‖ + ‖f‖) := by
          gcongr
          exact norm_sphereAntipodeAlgHom_le f
    _ = ‖f‖ := by ring

theorem dist_sphereEvenSymm_le
    (f g : C(spherePoint3, ℝ)) :
    dist (sphereEvenSymm f) (sphereEvenSymm g) ≤ dist f g := by
  simpa [dist_eq_norm, sphereEvenSymm, map_sub] using norm_sphereEvenSymm_le (f - g)

theorem exists_even_coordinate_near_of_mem_continuousSphereEvenSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereEvenSubmodule)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : C(spherePoint3, ℝ),
      p ∈ sphereCoordinateSubalgebra ∧
      p ∈ continuousSphereEvenSubmodule ∧
      dist p f < ε := by
  have hfcl : f ∈ sphereCoordinateSubalgebra.topologicalClosure := by
    rw [sphereCoordinateSubalgebra_closure_eq_top]
    simp
  have hfcl' : f ∈ (sphereCoordinateSubalgebra.topologicalClosure : Set C(spherePoint3, ℝ)) := hfcl
  rw [Subalgebra.topologicalClosure_coe] at hfcl'
  rcases (mem_closure_iff_nhds.mp hfcl') (Metric.ball f ε) (Metric.ball_mem_nhds _ hε) with
    ⟨g, hgball, hgA⟩
  let p := sphereEvenSymm g
  refine ⟨p, sphereEvenSymm_mem_sphereCoordinateSubalgebra hgA,
    sphereEvenSymm_mem_continuousSphereEvenSubmodule g, ?_⟩
  have hdist :
      dist (sphereEvenSymm g) (sphereEvenSymm f) ≤ dist g f :=
    dist_sphereEvenSymm_le g f
  have hfFix : sphereEvenSymm f = f :=
    sphereEvenSymm_eq_of_mem_continuousSphereEvenSubmodule hf
  have hgdist : dist g f < ε := by
    simpa [Metric.mem_ball, dist_comm] using hgball
  rw [hfFix] at hdist
  exact lt_of_le_of_lt hdist hgdist

def continuousSphereEvenCoordinateSubmodule : Submodule ℝ C(spherePoint3, ℝ) :=
  sphereCoordinateSubalgebra.toSubmodule ⊓ continuousSphereEvenSubmodule

theorem continuousSphereFrameSubmodule_le_evenCoordinateClosure :
    continuousSphereFrameSubmodule ≤
      continuousSphereEvenCoordinateSubmodule.topologicalClosure := by
  intro f hf
  change f ∈ (continuousSphereEvenCoordinateSubmodule.topologicalClosure : Set C(spherePoint3, ℝ))
  rw [Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  rcases exists_even_coordinate_near_of_mem_continuousSphereEvenSubmodule
      (continuousSphereFrameSubmodule_le_continuousSphereEvenSubmodule hf) hε with
    ⟨p, hpA, hpE, hpdist⟩
  refine ⟨p, ?_, ?_⟩
  · exact ⟨hpA, hpE⟩
  · simpa [dist_comm] using hpdist
