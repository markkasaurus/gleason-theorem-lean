import Mathlib
import Gleason.Finite.FrameFunction
import Gleason.Finite.Quadratic.Basic
import Gleason.Finite.Quadratic.Homogeneity
import Gleason.Finite.OrthogonalComplement
import Gleason.Finite.ThreeVectorFrame
import Gleason.Finite.Quadratic.Parallelogram

noncomputable section

open RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

namespace GleasonBridge

/-!
## Regularity bridge in dimension at least three

Gleason's key "regularity bridge" is that in dimension ≥ 3, a nonnegative finitely additive
measure on projections forces a 2D quadratic behavior on any orthonormal pair.

The precise regularity property is `μ.HasQuad2D`. The theorem
`hasQuad2D_of_finrank_ge_three` derives it from the dimension hypothesis.
It implies the full parallelogram identity for `frame_quadratic μ`, which
feeds the polarization and operator-representation argument.
-/

lemma frame_quadratic_eq_mu_rankOne
    (μ : FrameFunction H) (x : H) (hx : ‖x‖ = (1 : ℝ)) :
    frame_quadratic (H := H) μ x =
      μ.μ (rankOneProjection (H := H) x (by
        intro h0
        simpa [h0] using hx)) := by
  classical
  have hx0 : x ≠ 0 := by
    intro h0
    simpa [h0] using hx
  have hn : ‖x‖ ^ 2 = (1 : ℝ) := by simp [hx]
  simp [frame_quadratic, hx0, hn]

/-!
### A unit vector orthogonal to two given vectors
-/

theorem exists_unit_orthogonal_to_pair
    (hdim : 3 ≤ Module.finrank ℂ H) (u v : H) :
    ∃ w : H, ‖w‖ = (1 : ℝ) ∧ inner (𝕜 := ℂ) u w = 0 ∧ inner (𝕜 := ℂ) v w = 0 := by
  classical
  rcases exists_ortho_vector_of_dim_ge_3 (H := H) hdim u v with ⟨w0, hw0, hw0u, hw0v⟩
  have hw0_norm_ne : ‖w0‖ ≠ 0 := by simpa [norm_eq_zero] using hw0
  let w : H := ((‖w0‖)⁻¹ : ℂ) • w0
  have hw : ‖w‖ = 1 := by
    calc
      ‖w‖ = ‖((‖w0‖)⁻¹ : ℂ)‖ * ‖w0‖ := by simp [w, norm_smul]
      _ = (‖w0‖ : ℝ)⁻¹ * ‖w0‖ := by simp
      _ = 1 := by simpa using (inv_mul_cancel₀ hw0_norm_ne)
  have huw : inner (𝕜 := ℂ) u w = 0 := by
    have : inner (𝕜 := ℂ) u w0 = 0 := (inner_eq_zero_symm).2 hw0u
    simpa [w, inner_smul_right, this]
  have hvw : inner (𝕜 := ℂ) v w = 0 := by
    have : inner (𝕜 := ℂ) v w0 = 0 := (inner_eq_zero_symm).2 hw0v
    simpa [w, inner_smul_right, this]
  exact ⟨w, hw, huw, hvw⟩

/-!
### Plane-invariance of the orthonormal sum `Q(u)+Q(v)`

If two orthonormal pairs span the same 2D subspace, then the sum of `frame_quadratic μ`
over the pair is the same. The proof extends each pair to the same orthonormal triple by
choosing a common orthogonal unit vector, then uses `C1.three_vector_sum`.
-/

theorem frame_quadratic_orthonormal_sum_eq_of_span_eq
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H)
    (u v u' v' : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1) (huv' : inner (𝕜 := ℂ) u' v' = 0)
    (h_span : Submodule.span ℂ ({u, v} : Set H) = Submodule.span ℂ ({u', v'} : Set H)) :
    frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v =
      frame_quadratic (H := H) μ u' + frame_quadratic (H := H) μ v' := by
  classical
  -- Choose `w ⟂ u` and `w ⟂ v`.
  rcases exists_unit_orthogonal_to_pair (H := H) hdim u v with ⟨w, hw, huw, hvw⟩

  -- `w` is orthogonal to the whole plane `span{u,v}`.
  have hwperp : w ∈ (Submodule.span ℂ ({u, v} : Set H) : Submodule ℂ H)ᗮ := by
    refine (Submodule.mem_orthogonal (K := Submodule.span ℂ ({u, v} : Set H)) (v := w)).2 ?_
    intro z hz
    rcases (Submodule.mem_span_pair.mp hz) with ⟨a, b, rfl⟩
    simp [inner_add_left, inner_smul_left, huw, hvw]

  -- Hence `u' ⟂ w` and `v' ⟂ w` since `u',v'` lie in the same plane.
  have hu'_mem : u' ∈ Submodule.span ℂ ({u, v} : Set H) := by
    -- `u' ∈ span{u',v'}` and transport via `h_span`
    have : u' ∈ Submodule.span ℂ ({u', v'} : Set H) :=
      Submodule.subset_span (by simp)
    simpa [h_span] using this
  have hv'_mem : v' ∈ Submodule.span ℂ ({u, v} : Set H) := by
    have : v' ∈ Submodule.span ℂ ({u', v'} : Set H) :=
      Submodule.subset_span (by simp)
    simpa [h_span] using this

  have hu'w : inner (𝕜 := ℂ) u' w = 0 := by
    have hz : inner (𝕜 := ℂ) u' w = 0 :=
      (Submodule.mem_orthogonal (K := Submodule.span ℂ ({u, v} : Set H)) (v := w)).1 hwperp u' hu'_mem
    simpa using hz
  have hv'w : inner (𝕜 := ℂ) v' w = 0 := by
    have hz : inner (𝕜 := ℂ) v' w = 0 :=
      (Submodule.mem_orthogonal (K := Submodule.span ℂ ({u, v} : Set H)) (v := w)).1 hwperp v' hv'_mem
    simpa using hz

  -- Apply the 3-vector sum lemma twice, for the triples `(u,v,w)` and `(u',v',w)`.
  have hsum1 :
      frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v + frame_quadratic (H := H) μ w =
        μ.μ (GleasonRankOne.projectionOntoSpan (H := H) ({u, v, w} : Set H)) :=
    GleasonRankOne.three_vector_sum (H := H) μ u v w hu hv hw huv huw hvw

  have hsum2 :
      frame_quadratic (H := H) μ u' + frame_quadratic (H := H) μ v' + frame_quadratic (H := H) μ w =
        μ.μ (GleasonRankOne.projectionOntoSpan (H := H) ({u', v', w} : Set H)) :=
    GleasonRankOne.three_vector_sum (H := H) μ u' v' w hu' hv' hw huv' hu'w hv'w

  -- The spans of the two triples agree (same plane + same `w`).
  have hspan3 :
      Submodule.span ℂ ({u, v, w} : Set H) = Submodule.span ℂ ({u', v', w} : Set H) := by
    -- rewrite each triple as `insert w {u,v}` and use `Submodule.span_insert` and `h_span`
    have hs1 : ({u, v, w} : Set H) = Set.insert w ({u, v} : Set H) := by
      ext z
      constructor
      · intro hz
        have : z = u ∨ z = v ∨ z = w := by simpa using hz
        rcases this with rfl | rfl | rfl
        · -- z = u
          exact (Set.mem_insert_iff.2 <| Or.inr <| by simp)
        · -- z = v
          exact (Set.mem_insert_iff.2 <| Or.inr <| by simp)
        · -- z = w
          exact (Set.mem_insert_iff.2 <| Or.inl rfl)
      · intro hz
        have hz' : z = w ∨ z ∈ ({u, v} : Set H) := (Set.mem_insert_iff.1 hz)
        rcases hz' with rfl | hzuv
        · simp
        · have : z = u ∨ z = v := by simpa using hzuv
          rcases this with rfl | rfl <;> simp
    have hs2 : ({u', v', w} : Set H) = Set.insert w ({u', v'} : Set H) := by
      ext z
      constructor
      · intro hz
        have : z = u' ∨ z = v' ∨ z = w := by simpa using hz
        rcases this with rfl | rfl | rfl
        · exact (Set.mem_insert_iff.2 <| Or.inr <| by simp)
        · exact (Set.mem_insert_iff.2 <| Or.inr <| by simp)
        · exact (Set.mem_insert_iff.2 <| Or.inl rfl)
      · intro hz
        have hz' : z = w ∨ z ∈ ({u', v'} : Set H) := (Set.mem_insert_iff.1 hz)
        rcases hz' with rfl | hzuv
        · simp
        · have : z = u' ∨ z = v' := by simpa using hzuv
          rcases this with rfl | rfl <;> simp
    -- now reduce to `span_insert` and rewrite the plane via `h_span`
    -- `span (insert w S) = span {w} ⊔ span S`
    rw [hs1, hs2]
    -- expand each side with `span_insert`, then rewrite the plane with `h_span`
    calc
      Submodule.span ℂ (Set.insert w ({u, v} : Set H))
          = Submodule.span ℂ ({w} : Set H) ⊔ Submodule.span ℂ ({u, v} : Set H) := by
              simpa using (Submodule.span_insert (R := ℂ) w ({u, v} : Set H))
      _   = Submodule.span ℂ ({w} : Set H) ⊔ Submodule.span ℂ ({u', v'} : Set H) := by
              simpa [h_span]
      _   = Submodule.span ℂ (Set.insert w ({u', v'} : Set H)) := by
              symm
              simpa using (Submodule.span_insert (R := ℂ) w ({u', v'} : Set H))

  have hproj :
      GleasonRankOne.projectionOntoSpan (H := H) ({u, v, w} : Set H) =
        GleasonRankOne.projectionOntoSpan (H := H) ({u', v', w} : Set H) := by
    -- both are projections onto equal submodules
    -- (by definitional unfolding of `projectionOntoSpan`)
    simp [GleasonRankOne.projectionOntoSpan, GleasonRankOne.projectionOntoSubmodule, hspan3]

  -- Replace the RHS of `hsum2` with the RHS of `hsum1` and cancel `Q(w)`.
  have hsum2' :
      frame_quadratic (H := H) μ u' + frame_quadratic (H := H) μ v' + frame_quadratic (H := H) μ w =
        μ.μ (GleasonRankOne.projectionOntoSpan (H := H) ({u, v, w} : Set H)) := by
    simpa [hproj] using hsum2

  -- Now `linarith` cancels `Q(w)` and the common RHS.
  linarith [hsum1, hsum2']

end GleasonBridge
