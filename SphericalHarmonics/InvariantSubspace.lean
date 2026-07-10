import Mathlib

open scoped BigOperators ENNReal

namespace SphericalHarmonics

section FiniteOrthogonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (V : ι → Submodule 𝕜 E) [∀ i, CompleteSpace (V i)]

/-- For a finite orthogonal sector family spanning the ambient Hilbert space, any submodule that is
stable under all orthogonal sector projections is the sum of its sector intersections. This is the
finite-dimensional direct-sum template used later for low-mode separation arguments. -/
theorem submodule_eq_iSup_inf_of_projection_invariant
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (hspan : iSup V = ⊤) (K : Submodule 𝕜 E)
    (hK : ∀ i x, x ∈ K → ((V i).orthogonalProjection x : E) ∈ K) :
    K = ⨆ i, K ⊓ V i := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hxspan : x ∈ iSup V := by
      simp [hspan]
    rw [← hV.sum_projection_of_mem_iSup x hxspan]
    have hsum :
        ∑ i ∈ Finset.univ, ((V i).orthogonalProjection x : E) ∈ ⨆ i, K ⊓ V i :=
      Submodule.sum_mem (⨆ i, K ⊓ V i) (by
        intro i hi
        exact Submodule.mem_iSup_of_mem i <|
          Submodule.mem_inf.mpr ⟨hK i x hx, ((V i).orthogonalProjection x).property⟩)
    simpa using hsum
  · refine iSup_le fun i => ?_
    exact inf_le_left

/-- Closed-submodule version of `submodule_eq_iSup_inf_of_projection_invariant`. -/
theorem ClosedSubmodule.toSubmodule_eq_iSup_inf_of_projection_invariant
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (hspan : iSup V = ⊤) (K : ClosedSubmodule 𝕜 E)
    (hK : ∀ i x, x ∈ K.toSubmodule → ((V i).orthogonalProjection x : E) ∈ K.toSubmodule) :
    K.toSubmodule = ⨆ i, K.toSubmodule ⊓ V i :=
  submodule_eq_iSup_inf_of_projection_invariant V hV hspan K.toSubmodule hK

end FiniteOrthogonal

section HilbertSumOrthogonal

variable {ι : Type*} [DecidableEq ι]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable (V : ι → Submodule 𝕜 E) [∀ i, CompleteSpace (V i)]

/-- In an internal Hilbert sum decomposition, the orthogonal projection onto a sector is the
corresponding one-coordinate truncation under the canonical isometric equivalence with `ℓ²`. -/
theorem IsHilbertSum.starProjection_eq_linearIsometryEquiv_symm_single
    (hV : IsHilbertSum 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (i : ι) (x : E) :
    (V i).starProjection x =
      hV.linearIsometryEquiv.symm (lp.single 2 i (hV.linearIsometryEquiv x i)) := by
  refine (V i).eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · simp
  · intro w hw
    have hw' : lp.single 2 i ⟨w, hw⟩ = hV.linearIsometryEquiv w := by
      apply hV.linearIsometryEquiv.symm.injective
      simp
    have hinner :
        inner 𝕜
          (hV.linearIsometryEquiv
            (x - hV.linearIsometryEquiv.symm (lp.single 2 i (hV.linearIsometryEquiv x i))))
          (hV.linearIsometryEquiv w) = 0 := by
      rw [map_sub, LinearIsometryEquiv.apply_symm_apply, ← hw']
      rw [lp.inner_single_right]
      simp
    rw [← hV.linearIsometryEquiv.inner_map_map
      (x - hV.linearIsometryEquiv.symm (lp.single 2 i (hV.linearIsometryEquiv x i))) w]
    exact hinner

/-- For an internal Hilbert sum of orthogonal sectors, any closed submodule that is stable under
all sector projections is the closure of the sum of its sector intersections. -/
theorem ClosedSubmodule.toSubmodule_eq_topologicalClosure_iSup_inf_of_isHilbertSum_projection_invariant
    (hV : IsHilbertSum 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (K : ClosedSubmodule 𝕜 E)
    (hK : ∀ i x, x ∈ K.toSubmodule → ((V i).starProjection x : E) ∈ K.toSubmodule) :
    K.toSubmodule = (⨆ i, K.toSubmodule ⊓ V i).topologicalClosure := by
  refine le_antisymm ?_ ?_
  · intro x hx
    let w : lp (fun i => V i) 2 := hV.linearIsometryEquiv x
    have hsum : HasSum (fun i : ι => ((w i : V i) : E)) x := by
      simpa [w] using hV.hasSum_linearIsometryEquiv_symm w
    have hpartial :
        ∀ s : Finset ι, ∑ i ∈ s, ((w i : V i) : E) ∈ ⨆ i, K.toSubmodule ⊓ V i := by
      intro s
      refine Submodule.sum_mem _ ?_
      intro i hi
      have hproj : ((w i : V i) : E) = (V i).starProjection x := by
        symm
        calc
          (V i).starProjection x
              = hV.linearIsometryEquiv.symm (lp.single 2 i (w i)) := by
                  simpa [w] using
                    IsHilbertSum.starProjection_eq_linearIsometryEquiv_symm_single
                      (V := V) hV i x
          _ = ((w i : V i) : E) := by
                  simp
      refine Submodule.mem_iSup_of_mem i ?_
      exact Submodule.mem_inf.mpr
        ⟨by simpa [hproj] using hK i x hx,
          by simp [hproj]⟩
    exact mem_closure_of_tendsto hsum (Filter.Eventually.of_forall hpartial)
  · exact Submodule.topologicalClosure_minimal (s := ⨆ i, K.toSubmodule ⊓ V i)
      (iSup_le fun i => inf_le_left) K.isClosed

end HilbertSumOrthogonal

end SphericalHarmonics
