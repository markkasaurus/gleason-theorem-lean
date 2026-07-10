import Mathlib
import Gleason.Finite.FrameFunction
import Gleason.Finite.ProjectionSum
import Gleason.Finite.Quadratic.Basic
import Gleason.Finite.Quadratic.Bound
import Gleason.Finite.TraceNormalization

noncomputable section

open scoped BigOperators

namespace GleasonRankOne

open RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Orthogonal projection onto a submodule, packaged as a `Projection H`. -/
def projectionOntoSubmodule (K : Submodule ℂ H) : Projection H := by
  classical
  haveI : CompleteSpace (↥K) := by infer_instance
  haveI : K.HasOrthogonalProjection := by infer_instance
  refine ⟨K.starProjection, ?_, ?_⟩
  ·
    have hId : IsIdempotentElem K.starProjection := by
      simpa using (Submodule.isIdempotentElem_starProjection (K := K))
    simpa [IsIdempotentElem] using hId
  ·
    intro u v
    have hv : v - K.starProjection v ∈ Kᗮ := by
      simpa using (Submodule.sub_starProjection_mem_orthogonal (K := K) v)
    have hu : K.starProjection u ∈ K := by
      simpa using (Submodule.starProjection_apply_mem (U := K) u)
    have hv0 :
        ∀ w ∈ K, inner (𝕜 := ℂ) w (v - K.starProjection v) = (0 : ℂ) :=
      (Submodule.mem_orthogonal (K := K) (v := v - K.starProjection v)).1 hv
    exact hv0 (K.starProjection u) hu

/-- Orthogonal projection onto the span of a set, packaged as a `Projection H`. -/
def projectionOntoSpan (s : Set H) : Projection H :=
  projectionOntoSubmodule (H := H) (Submodule.span ℂ s)

/-- If `x` has norm `1`, then `frame_quadratic μ x = μ` of the corresponding rank-one projection. -/
lemma frame_quadratic_eq_mu_rankOne (μ : FrameFunction H) (x : H) (hx : ‖x‖ = (1 : ℝ)) :
    frame_quadratic (H := H) μ x = μ.μ (RankOne.rankOneProjection (H := H) x (by
      intro h0
      simpa [h0] using hx)) := by
  classical
  have hx0 : x ≠ 0 := by
    intro h0
    simpa [h0] using hx
  -- `‖x‖^2 = 1` under `hx`.
  have hn : ‖x‖ ^ 2 = (1 : ℝ) := by
    simp [hx]
  simp [frame_quadratic, hx0, hn]

/-- Main: additivity on three pairwise-orthogonal rank-one projections. -/
theorem three_vector_sum (μ : FrameFunction H) (u v w : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0) :
    frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v + frame_quadratic (H := H) μ w =
      μ.μ (projectionOntoSpan (H := H) ({u, v, w} : Set H)) := by
  classical
  have hu0 : u ≠ 0 := by intro h0; simpa [h0] using hu
  have hv0 : v ≠ 0 := by intro h0; simpa [h0] using hv
  have hw0 : w ≠ 0 := by intro h0; simpa [h0] using hw

  let Pu : Projection H := RankOne.rankOneProjection (H := H) u hu0
  let Pv : Projection H := RankOne.rankOneProjection (H := H) v hv0
  let Pw : Projection H := RankOne.rankOneProjection (H := H) w hw0

  have huq : frame_quadratic (H := H) μ u = μ.μ Pu := by
    simpa [Pu] using frame_quadratic_eq_mu_rankOne (H := H) μ u hu
  have hvq : frame_quadratic (H := H) μ v = μ.μ Pv := by
    simpa [Pv] using frame_quadratic_eq_mu_rankOne (H := H) μ v hv
  have hwq : frame_quadratic (H := H) μ w = μ.μ Pw := by
    simpa [Pw] using frame_quadratic_eq_mu_rankOne (H := H) μ w hw

  have hPuPv : Projection.orthogonal Pu Pv :=
    rankOneProjection_orthogonal_of_inner_eq_zero (H := H) (x := u) (y := v) hu0 hv0 huv
  have hPuPw : Projection.orthogonal Pu Pw :=
    rankOneProjection_orthogonal_of_inner_eq_zero (H := H) (x := u) (y := w) hu0 hw0 huw
  have hPvPw : Projection.orthogonal Pv Pw :=
    rankOneProjection_orthogonal_of_inner_eq_zero (H := H) (x := v) (y := w) hv0 hw0 hvw

  let P : Fin 3 → Projection H := fun i =>
    match (i : Nat) with
    | 0 => Pu
    | 1 => Pv
    | _ => Pw

  let s : Finset (Fin 3) :=
    {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩}

  have hOrth : ∀ i j : Fin 3, i ≠ j → Projection.orthogonal (P i) (P j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · cases hij rfl
    · simpa [P, Pu, Pv] using hPuPv
    · simpa [P, Pu, Pw] using hPuPw
    · -- swap (0,1)
      simpa [P, Pu, Pv] using (Projection.orthogonal_comm (H := H) Pu Pv hPuPv)
    · cases hij rfl
    · simpa [P, Pv, Pw] using hPvPw
    · -- swap (0,2)
      simpa [P, Pu, Pw] using (Projection.orthogonal_comm (H := H) Pu Pw hPuPw)
    · -- swap (1,2)
      simpa [P, Pv, Pw] using (Projection.orthogonal_comm (H := H) Pv Pw hPvPw)
    · cases hij rfl

  let Psum : Projection H :=
    Projection.sum (H := H) (ι := Fin 3) (s := s) P hOrth

  have hSum : μ.μ Psum = s.sum (fun i => μ.μ (P i)) := by
    simpa [Psum] using FrameFunction.map_sum (H := H) μ s P hOrth

  have hx_sum3 (x : H) : Psum.1 x = Pu.1 x + Pv.1 x + Pw.1 x := by
    -- compute the explicit `Finset` sum
    have hcoe :
        Psum.1 = s.sum (fun i => (P i).1) := by
      simpa [Psum] using (Projection.sum_coe (H := H) (ι := Fin 3) (s := s) (P := P) (h := hOrth))
    -- turn operator equality into pointwise and simplify the finset sum
    have : Psum.1 x = s.sum (fun i => (P i).1 x) := by
      simpa [ContinuousLinearMap.sum_apply] using congrArg (fun f : H →L[ℂ] H => f x) hcoe
    -- now `simp` evaluates `s.sum`
    simpa [s, P, Pu, Pv, Pw, Finset.sum_insert, Finset.sum_singleton, Finset.sum_pair, add_assoc,
      add_left_comm, add_comm] using this

  have hProj : projectionOntoSpan (H := H) ({u, v, w} : Set H) = Psum := by
    classical
    let K : Submodule ℂ H := Submodule.span ℂ ({u, v, w} : Set H)
    haveI : CompleteSpace (↥K) := by infer_instance
    haveI : K.HasOrthogonalProjection := by infer_instance
    apply Subtype.ext
    ext x

    have hx_mem : Psum.1 x ∈ K := by
      -- each summand lies in the span
      have huK : u ∈ K := Submodule.subset_span (by simp)
      have hvK : v ∈ K := Submodule.subset_span (by simp)
      have hwK : w ∈ K := Submodule.subset_span (by simp)
      -- use the explicit sum form
      have hx' : Psum.1 x = Pu.1 x + Pv.1 x + Pw.1 x := hx_sum3 (x := x)
      -- each term is in the corresponding line, hence in K
      have hPu : Pu.1 x ∈ (ℂ ∙ u : Submodule ℂ H) := by
        simpa [Pu, RankOne.rankOneProjection] using
          (Submodule.starProjection_apply_mem (U := (ℂ ∙ u : Submodule ℂ H)) x)
      have hPv : Pv.1 x ∈ (ℂ ∙ v : Submodule ℂ H) := by
        simpa [Pv, RankOne.rankOneProjection] using
          (Submodule.starProjection_apply_mem (U := (ℂ ∙ v : Submodule ℂ H)) x)
      have hPw : Pw.1 x ∈ (ℂ ∙ w : Submodule ℂ H) := by
        simpa [Pw, RankOne.rankOneProjection] using
          (Submodule.starProjection_apply_mem (U := (ℂ ∙ w : Submodule ℂ H)) x)
      have hleu : (ℂ ∙ u : Submodule ℂ H) ≤ K := by
        refine Submodule.span_le.2 ?_
        intro z hz
        simpa [Set.mem_singleton_iff] using hz ▸ huK
      have hlev : (ℂ ∙ v : Submodule ℂ H) ≤ K := by
        refine Submodule.span_le.2 ?_
        intro z hz
        simpa [Set.mem_singleton_iff] using hz ▸ hvK
      have hlew : (ℂ ∙ w : Submodule ℂ H) ≤ K := by
        refine Submodule.span_le.2 ?_
        intro z hz
        simpa [Set.mem_singleton_iff] using hz ▸ hwK
      have hPuK : Pu.1 x ∈ K := hleu hPu
      have hPvK : Pv.1 x ∈ K := hlev hPv
      have hPwK : Pw.1 x ∈ K := hlew hPw
      -- close by add_mem
      simpa [hx'] using K.add_mem (K.add_mem hPuK hPvK) hPwK

    have hx_orth : x - Psum.1 x ∈ Kᗮ := by
      refine (Submodule.mem_orthogonal (K := K) (v := x - Psum.1 x)).2 ?_
      intro y hy
      refine Submodule.span_induction (R := ℂ) (s := ({u, v, w} : Set H))
        (p := fun z _hz => inner (𝕜 := ℂ) z (x - Psum.1 x) = 0) ?mem ?zero ?add ?smul hy
      · intro z hz
        have hz' : z = u ∨ z = v ∨ z = w := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
        have hx' : Psum.1 x = Pu.1 x + Pv.1 x + Pw.1 x := hx_sum3 (x := x)
        -- now split on `z ∈ {u,v,w}` and compute directly
        rcases hz' with rfl | hz'
        · -- z = u
          have hPu_z : Pu.1 z = z := by
            have : z ∈ (ℂ ∙ z : Submodule ℂ H) := Submodule.subset_span (by simp)
            simpa [Pu, RankOne.rankOneProjection] using
              (Submodule.starProjection_eq_self_of_mem (K := (ℂ ∙ z : Submodule ℂ H)) this)
          have hz_main : inner (𝕜 := ℂ) z x = inner (𝕜 := ℂ) z (Pu.1 x) := by
            have hz0 : inner (𝕜 := ℂ) z (x - Pu.1 x) = 0 := by
              have := Pu.inner_err z x
              simpa [hPu_z] using this
            have : inner (𝕜 := ℂ) z x - inner (𝕜 := ℂ) z (Pu.1 x) = 0 := by
              simpa [inner_sub_right] using hz0
            exact sub_eq_zero.mp this
          have hz_v : inner (𝕜 := ℂ) z (Pv.1 x) = 0 := by
            have := Projection.inner_orthogonal (H := H) Pu Pv hPuPv z x
            simpa [hPu_z] using this
          have hz_w : inner (𝕜 := ℂ) z (Pw.1 x) = 0 := by
            have := Projection.inner_orthogonal (H := H) Pu Pw hPuPw z x
            simpa [hPu_z] using this
          calc
            inner (𝕜 := ℂ) z (x - Psum.1 x)
                = inner (𝕜 := ℂ) z x - inner (𝕜 := ℂ) z (Psum.1 x) := by
                    simp [inner_sub_right]
            _   = inner (𝕜 := ℂ) z x
                    - (inner (𝕜 := ℂ) z (Pu.1 x) + inner (𝕜 := ℂ) z (Pv.1 x)
                        + inner (𝕜 := ℂ) z (Pw.1 x)) := by
                    simp [hx', inner_add_right, add_assoc]
            _   = inner (𝕜 := ℂ) z (Pu.1 x) - (inner (𝕜 := ℂ) z (Pu.1 x) + 0 + 0) := by
                    simp [hz_main, hz_v, hz_w]
            _   = 0 := by ring
        · rcases hz' with rfl | rfl
          · -- z = v
            have hPv_z : Pv.1 z = z := by
              have : z ∈ (ℂ ∙ z : Submodule ℂ H) := Submodule.subset_span (by simp)
              simpa [Pv, RankOne.rankOneProjection] using
                (Submodule.starProjection_eq_self_of_mem (K := (ℂ ∙ z : Submodule ℂ H)) this)
            have hz_main : inner (𝕜 := ℂ) z x = inner (𝕜 := ℂ) z (Pv.1 x) := by
              have hz0 : inner (𝕜 := ℂ) z (x - Pv.1 x) = 0 := by
                have := Pv.inner_err z x
                simpa [hPv_z] using this
              have : inner (𝕜 := ℂ) z x - inner (𝕜 := ℂ) z (Pv.1 x) = 0 := by
                simpa [inner_sub_right] using hz0
              exact sub_eq_zero.mp this
            have hz_u : inner (𝕜 := ℂ) z (Pu.1 x) = 0 := by
              have := Projection.inner_orthogonal (H := H) Pv Pu
                (Projection.orthogonal_comm (H := H) Pu Pv hPuPv) z x
              simpa [hPv_z] using this
            have hz_w : inner (𝕜 := ℂ) z (Pw.1 x) = 0 := by
              have := Projection.inner_orthogonal (H := H) Pv Pw hPvPw z x
              simpa [hPv_z] using this
            calc
              inner (𝕜 := ℂ) z (x - Psum.1 x)
                  = inner (𝕜 := ℂ) z x - inner (𝕜 := ℂ) z (Psum.1 x) := by
                      simp [inner_sub_right]
              _   = inner (𝕜 := ℂ) z x
                      - (inner (𝕜 := ℂ) z (Pu.1 x) + inner (𝕜 := ℂ) z (Pv.1 x)
                          + inner (𝕜 := ℂ) z (Pw.1 x)) := by
                      simp [hx', inner_add_right, add_assoc]
              _   = inner (𝕜 := ℂ) z (Pv.1 x) - (0 + inner (𝕜 := ℂ) z (Pv.1 x) + 0) := by
                      simp [hz_main, hz_u, hz_w, add_assoc, add_comm, add_left_comm]
              _   = 0 := by ring
          · -- z = w
            have hPw_z : Pw.1 z = z := by
              have : z ∈ (ℂ ∙ z : Submodule ℂ H) := Submodule.subset_span (by simp)
              simpa [Pw, RankOne.rankOneProjection] using
                (Submodule.starProjection_eq_self_of_mem (K := (ℂ ∙ z : Submodule ℂ H)) this)
            have hz_main : inner (𝕜 := ℂ) z x = inner (𝕜 := ℂ) z (Pw.1 x) := by
              have hz0 : inner (𝕜 := ℂ) z (x - Pw.1 x) = 0 := by
                have := Pw.inner_err z x
                simpa [hPw_z] using this
              have : inner (𝕜 := ℂ) z x - inner (𝕜 := ℂ) z (Pw.1 x) = 0 := by
                simpa [inner_sub_right] using hz0
              exact sub_eq_zero.mp this
            have hz_u : inner (𝕜 := ℂ) z (Pu.1 x) = 0 := by
              have := Projection.inner_orthogonal (H := H) Pw Pu
                (Projection.orthogonal_comm (H := H) Pu Pw hPuPw) z x
              simpa [hPw_z] using this
            have hz_v : inner (𝕜 := ℂ) z (Pv.1 x) = 0 := by
              have := Projection.inner_orthogonal (H := H) Pw Pv
                (Projection.orthogonal_comm (H := H) Pv Pw hPvPw) z x
              simpa [hPw_z] using this
            calc
              inner (𝕜 := ℂ) z (x - Psum.1 x)
                  = inner (𝕜 := ℂ) z x - inner (𝕜 := ℂ) z (Psum.1 x) := by
                      simp [inner_sub_right]
              _   = inner (𝕜 := ℂ) z x
                      - (inner (𝕜 := ℂ) z (Pu.1 x) + inner (𝕜 := ℂ) z (Pv.1 x)
                          + inner (𝕜 := ℂ) z (Pw.1 x)) := by
                      simp [hx', inner_add_right, add_assoc]
              _   = inner (𝕜 := ℂ) z (Pw.1 x) - (0 + 0 + inner (𝕜 := ℂ) z (Pw.1 x)) := by
                      simp [hz_main, hz_u, hz_v, add_assoc, add_comm, add_left_comm]
              _   = 0 := by ring
      · simp
      · intro x1 x2 _hx1 _hx2 h1 h2
        -- keep `x - Psum x` intact: just rewrite by linearity in the left argument
        rw [inner_add_left]
        simpa [h1, h2]
      · intro a x1 _hx1 h1
        -- and likewise for scalar multiplication
        rw [inner_smul_left]
        simpa [h1]

    -- uniqueness of starProjection onto K
    have : (Submodule.span ℂ ({u, v, w} : Set H)).starProjection x = Psum.1 x :=
      Submodule.eq_starProjection_of_mem_orthogonal (K := K) (u := x) (v := Psum.1 x) hx_mem hx_orth
    simpa [projectionOntoSpan, projectionOntoSubmodule, K, Psum] using this

  -- evaluate the finite sum on the three indices
  have hsμ : s.sum (fun i => μ.μ (P i)) = μ.μ Pu + μ.μ Pv + μ.μ Pw := by
    simp [s, P, Pu, Pv, Pw, Finset.sum_insert, Finset.sum_singleton, Finset.sum_pair, add_assoc,
      add_left_comm, add_comm]

  calc
    frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v + frame_quadratic (H := H) μ w
        = μ.μ Pu + μ.μ Pv + μ.μ Pw := by simpa [huq, hvq, hwq]
    _ = s.sum (fun i => μ.μ (P i)) := by simpa [hsμ]
    _ = μ.μ Psum := by simpa [hSum]
    _ = μ.μ (projectionOntoSpan (H := H) ({u, v, w} : Set H)) := by simpa [hProj]

/-- Any unit vector in the span has quadratic value bounded by the value of the span projection. -/
theorem three_vector_constraint (μ : FrameFunction H) (u v w : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (x : H) (hx : x ∈ Submodule.span ℂ ({u, v, w} : Set H)) (hxnorm : ‖x‖ = 1) :
    frame_quadratic (H := H) μ x ≤ μ.μ (projectionOntoSpan (H := H) ({u, v, w} : Set H)) := by
  classical
  have hx0 : x ≠ 0 := by
    intro h0; simpa [h0] using hxnorm

  have hxq :
      frame_quadratic (H := H) μ x = μ.μ (RankOne.rankOneProjection (H := H) x hx0) := by
    simpa using frame_quadratic_eq_mu_rankOne (H := H) μ x hxnorm

  let K : Submodule ℂ H := Submodule.span ℂ ({u, v, w} : Set H)
  let L : Submodule ℂ H := (ℂ ∙ x)
  let M : Submodule ℂ H := K ⊓ Lᗮ

  have hLle : L ≤ K := by
    intro y hy
    rcases Submodule.mem_span_singleton.mp hy with ⟨c, rfl⟩
    exact K.smul_mem c hx

  haveI : CompleteSpace (↥K) := by infer_instance
  haveI : K.HasOrthogonalProjection := by infer_instance
  haveI : CompleteSpace (↥L) := by infer_instance
  haveI : L.HasOrthogonalProjection := by infer_instance
  haveI : CompleteSpace (↥M) := by infer_instance
  haveI : M.HasOrthogonalProjection := by infer_instance

  let PK : Projection H := projectionOntoSubmodule (H := H) K
  let PL : Projection H := projectionOntoSubmodule (H := H) L
  let PM : Projection H := projectionOntoSubmodule (H := H) M

  -- PL is the rank-one projection onto `x`.
  have hPLop : PL = RankOne.rankOneProjection (H := H) x hx0 := by
    rfl

  -- Orthogonality: `M ≤ Lᗮ`, hence projecting to `L` after `M` gives zero.
  have hOrth : Projection.orthogonal PL PM := by
    classical
    unfold Projection.orthogonal
    ext y
    have hMy : PM.1 y ∈ M := by
      simpa [PM, projectionOntoSubmodule] using (Submodule.starProjection_apply_mem (U := M) y)
    have hLy : PM.1 y ∈ Lᗮ := (show M ≤ Lᗮ from inf_le_right) hMy
    -- starProjection onto `L` kills vectors in `Lᗮ`
    have hkill :
        L.starProjection (PM.1 y) = 0 :=
      Submodule.starProjection_eq_zero_of_mem_orthogonal (K := L) (v := PM.1 y) hLy
    simpa [PL, PM, projectionOntoSubmodule, ContinuousLinearMap.mul_apply] using hkill

  -- Decomposition: `K.starProjection = L.starProjection + M.starProjection`.
  have hDecomp : PK = Projection.add (H := H) PL PM hOrth := by
    classical
    apply Subtype.ext
    ext y
    -- use uniqueness of `K.starProjection` applied to the candidate `L⋆ y + M⋆ y`
    let cand : H := L.starProjection y + M.starProjection y
    have hcandK : cand ∈ K := by
      have hLy : L.starProjection y ∈ L := by
        simpa using (Submodule.starProjection_apply_mem (U := L) y)
      have hMy : M.starProjection y ∈ M := by
        simpa using (Submodule.starProjection_apply_mem (U := M) y)
      have hLK : L.starProjection y ∈ K := hLle hLy
      have hMK : M.starProjection y ∈ K := (inf_le_left : M ≤ K) hMy
      exact K.add_mem hLK hMK
    have hcandOrth : y - cand ∈ Kᗮ := by
      refine (Submodule.mem_orthogonal (K := K) (v := y - cand)).2 ?_
      intro z hz
      -- decompose z into L-part and M-part inside K
      let zL : H := L.starProjection z
      let zM : H := z - zL
      have hzL : zL ∈ L := by
        simpa [zL] using (Submodule.starProjection_apply_mem (U := L) z)
      have hzM : zM ∈ M := by
        have hzK : z ∈ K := hz
        have hzLK : zL ∈ K := hLle hzL
        have hzMK : zM ∈ K := K.sub_mem hzK hzLK
        have hzMorth : zM ∈ Lᗮ := by
          -- z - L⋆z ∈ Lᗮ
          simpa [zM, zL] using (Submodule.sub_starProjection_mem_orthogonal (K := L) z)
        exact ⟨hzMK, hzMorth⟩
      -- show `y - cand` is in both Lᗮ and Mᗮ, hence orthogonal to zL and zM
      have hyL : y - cand ∈ Lᗮ := by
        have h1 : y - L.starProjection y ∈ Lᗮ := by
          simpa using (Submodule.sub_starProjection_mem_orthogonal (K := L) y)
        have h2 : M.starProjection y ∈ Lᗮ := (show M ≤ Lᗮ from inf_le_right)
          (by simpa using (Submodule.starProjection_apply_mem (U := M) y))
        -- (y - (L⋆y + M⋆y)) = (y - L⋆y) - M⋆y
        simpa [cand, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (Lᗮ).sub_mem h1 h2
      have hyM : y - cand ∈ Mᗮ := by
        have h1 : y - M.starProjection y ∈ Mᗮ := by
          simpa using (Submodule.sub_starProjection_mem_orthogonal (K := M) y)
        have h2 : L.starProjection y ∈ Mᗮ := by
          -- L ≤ Mᗮ since M ≤ Lᗮ
          have hLM : L ≤ Mᗮ := by
            intro t ht
            refine (Submodule.mem_orthogonal (K := M) (v := t)).2 ?_
            intro m hm
            have hmL : (m : H) ∈ Lᗮ := (show M ≤ Lᗮ from inf_le_right) hm
            -- `hmL` gives `⟪t,m⟫ = 0`; flip to `⟪m,t⟫ = 0`
            exact inner_eq_zero_symm.mp
              ((Submodule.mem_orthogonal (K := L) (v := (m : H))).1 hmL t ht)
          exact hLM (by
            simpa using (Submodule.starProjection_apply_mem (U := L) y))
        -- (y - (L⋆y + M⋆y)) = (y - M⋆y) - L⋆y
        simpa [cand, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          (Mᗮ).sub_mem h1 h2
      have hzL0 : inner (𝕜 := ℂ) (zL : H) (y - cand) = 0 :=
        (Submodule.mem_orthogonal (K := L) (v := y - cand)).1 hyL zL hzL
      have hzM0 : inner (𝕜 := ℂ) (zM : H) (y - cand) = 0 :=
        (Submodule.mem_orthogonal (K := M) (v := y - cand)).1 hyM zM hzM
      -- z = zL + zM
      have hzdecomp : z = zL + zM := by simp [zM, zL]
      -- finish
      simpa [hzdecomp, inner_add_left, hzL0, hzM0] 
    have huniq :
        K.starProjection y = cand :=
      Submodule.eq_starProjection_of_mem_orthogonal (K := K) (u := y) (v := cand) hcandK hcandOrth
    -- unfold projections
    simpa [PK, PL, PM, projectionOntoSubmodule, Projection.add, cand] using huniq

  have hμadd : μ.μ PK = μ.μ PL + μ.μ PM := by
    simpa [hDecomp] using μ.additive PL PM hOrth
  have hPMnonneg : 0 ≤ μ.μ PM := μ.nonneg PM
  have hxle : μ.μ (RankOne.rankOneProjection (H := H) x hx0) ≤ μ.μ PK := by
    -- μ(PK) = μ(PL) + μ(PM) ≥ μ(PL)
    have : μ.μ PL ≤ μ.μ PK := by linarith
    simpa [hPLop] using this

  -- conclude for `frame_quadratic`
  -- `PK = projectionOntoSpan {u,v,w}` by definition.
  simpa [hxq, PK, projectionOntoSpan, projectionOntoSubmodule, K] using hxle

end GleasonRankOne
