
import Mathlib

import Gleason.Finite.Projection
import Gleason.Finite.RankOneProjection
import Gleason.Finite.FrameFunction
import Gleason.Finite.Quadratic.Basic
import Gleason.Finite.Quadratic.Homogeneity

import Gleason.Finite.Quadratic.Bound
import Gleason.Finite.Polarization.OperatorRepresentation

noncomputable section

open scoped BigOperators ComplexConjugate


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Two projections are equal if their underlying operators are equal. -/
theorem Projection.ext {P Q : Projection H} (h : P.1 = Q.1) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

namespace Submodule

/-- If `v ∈ Kᗮ` then the orthogonal projection onto `K` is zero. -/
lemma starProjection_eq_zero_of_mem_orthogonal
    {K : Submodule ℂ H} [CompleteSpace K] [K.HasOrthogonalProjection]
    {v : H} (hv : v ∈ Kᗮ) : K.starProjection v = 0 := by
  -- Let `z` be the projection of `v` onto `K`. If `v ⟂ K`, then `z` is both in `K` and in `Kᗮ`.
  have hv_sub : v - K.starProjection v ∈ Kᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (K := K) v
  have hz_orth : K.starProjection v ∈ Kᗮ := by
    have : v - (v - K.starProjection v) ∈ Kᗮ := sub_mem hv hv_sub
    simpa [sub_sub, sub_self, sub_zero] using this
  have hz_mem : K.starProjection v ∈ K := by
    simpa using (Submodule.starProjection_apply_mem (U := K) v)
  -- Using `z ∈ Kᗮ` with `u = z ∈ K`, we get `⟪z,z⟫ = 0`, hence `z = 0`.
  have hz_inner : inner ℂ (K.starProjection v) (K.starProjection v) = 0 := by
    have hz_orth' : ∀ u ∈ K, inner ℂ u (K.starProjection v) = 0 :=
      (Submodule.mem_orthogonal (K := K) (v := K.starProjection v)).1 hz_orth
    simpa using hz_orth' (K.starProjection v) hz_mem
  exact (inner_self_eq_zero.mp hz_inner)

/-- If `v ∈ K` then the orthogonal projection onto `K` fixes `v`. -/
lemma starProjection_eq_self_of_mem
    {K : Submodule ℂ H} [CompleteSpace K] [K.HasOrthogonalProjection]
    {v : H} (hv : v ∈ K) : K.starProjection v = v := by
  -- Let `p` be the projection. Then `v - p` lies both in `K` and in `Kᗮ`, hence is zero.
  have hdiff_orth : v - K.starProjection v ∈ Kᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (K := K) v
  have hp_mem : K.starProjection v ∈ K := by
    simpa using (Submodule.starProjection_apply_mem (U := K) v)
  have hdiff_mem : v - K.starProjection v ∈ K := sub_mem hv hp_mem
  have hdiff_inner : inner ℂ (v - K.starProjection v) (v - K.starProjection v) = 0 := by
    have horth' : ∀ u ∈ K, inner ℂ u (v - K.starProjection v) = 0 :=
      (Submodule.mem_orthogonal (K := K) (v := v - K.starProjection v)).1 hdiff_orth
    simpa using horth' (v - K.starProjection v) hdiff_mem
  have hdiff0 : v - K.starProjection v = 0 := inner_self_eq_zero.mp hdiff_inner
  exact (sub_eq_zero.mp hdiff0).symm

end Submodule


/-- For any frame function, `μ(0)=0`, derived from additivity. -/
theorem FrameFunction.mu_zero (μ : FrameFunction H) : μ.μ (Projection.zero : Projection H) = 0 := by
  classical
  have horth : Projection.orthogonal (Projection.zero : Projection H) (Projection.zero : Projection H) := by
    simp [Projection.orthogonal, Projection.zero]
  have hadd := μ.additive (Projection.zero : Projection H) (Projection.zero : Projection H) horth
  have : μ.μ (Projection.zero : Projection H) =
      μ.μ (Projection.zero : Projection H) + μ.μ (Projection.zero : Projection H) := by
    simpa [Projection.add, Projection.zero] using hadd
  linarith

/-- If `⟪x,y⟫ = 0`, then `span{y} ≤ (span{x})ᗮ`. -/
theorem span_singleton_le_orthogonal_span_singleton
    (x y : H) (hxy : inner (𝕜 := ℂ) x y = 0) :
    (ℂ ∙ y : Submodule ℂ H) ≤ (ℂ ∙ x : Submodule ℂ H)ᗮ := by
  intro z hz
  refine (Submodule.mem_orthogonal (K := (ℂ ∙ x : Submodule ℂ H)) (v := z)).2 ?_
  intro w hw
  rcases Submodule.mem_span_singleton.mp hw with ⟨a, rfl⟩
  rcases Submodule.mem_span_singleton.mp hz with ⟨b, rfl⟩
  simp [inner_smul_left, inner_smul_right, hxy]

/-- Rank-one projections onto orthogonal vectors are orthogonal (composition is zero). -/
theorem rankOneProjection_orthogonal_of_inner_eq_zero
    (x y : H) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : inner (𝕜 := ℂ) x y = 0) :
    Projection.orthogonal (RankOne.rankOneProjection x hx) (RankOne.rankOneProjection y hy) := by
  classical
  let Kx : Submodule ℂ H := (ℂ ∙ x)
  let Ky : Submodule ℂ H := (ℂ ∙ y)
  have hsub : Ky ≤ Kxᗮ := span_singleton_le_orthogonal_span_singleton (x := x) (y := y) hxy
  -- unfold orthogonality
  ext v
  have hy_mem : Ky.starProjection v ∈ Ky := by
    simpa [Ky] using (Submodule.starProjection_apply_mem (U := Ky) v)
  have hy_orth : Ky.starProjection v ∈ Kxᗮ := hsub hy_mem
  have hz :
      Kx.starProjection (Ky.starProjection v) = 0 :=
    Submodule.starProjection_eq_zero_of_mem_orthogonal (K := Kx) (v := Ky.starProjection v) hy_orth
  -- simplify to the rank-one projection maps
  simpa [Projection.orthogonal, RankOne.rankOneProjection, Kx, Ky, ContinuousLinearMap.mul_apply] using hz

/-- The frame operator obtained from the Riesz representation has trace `1`. -/
theorem frame_operator_trace_one
    (μ : FrameFunction H)
    (h_para : ∀ x y, frame_quadratic μ (x + y) + frame_quadratic μ (x - y) =
      2 * frame_quadratic μ x + 2 * frame_quadratic μ y) :
    let hq : IsBoundedQuadraticForm (frame_quadratic μ) :=
      frame_quadratic_is_bounded_quadratic (μ := μ) h_para
    let T : H →L[ℂ] H := (polarization_eq_inner_product (H := H) (q := frame_quadratic μ) hq).choose
    LinearMap.trace ℂ H T.toLinearMap = 1 := by
  classical
  intro hq T
  have hT :
      (∀ x y, polarization (frame_quadratic μ) x y = inner (𝕜 := ℂ) y (T x)) ∧
      (∀ x, frame_quadratic μ x = (inner (𝕜 := ℂ) x (T x)).re) :=
    (polarization_eq_inner_product (H := H) (q := frame_quadratic μ) hq).choose_spec

  -- Orthonormal basis indexed by `Fin (finrank)`.
  let ι : Type := Fin (Module.finrank ℂ H)
  let e : OrthonormalBasis ι ℂ H := stdOrthonormalBasis ℂ H

  -- Rank-one projection onto `ℂ∙(e i)`.
  have hene : ∀ i : ι, (e i : H) ≠ 0 := by
    intro i
    have hnorm : ‖(e i : H)‖ = (1 : ℝ) := by simpa using e.norm_eq i
    intro hi
    have : (0 : ℝ) = 1 := by simpa [hi] using hnorm
    exact (zero_ne_one (α := ℝ)) this

  let P : ι → Projection H := fun i =>
    RankOne.rankOneProjection (e i) (hene i)

  -- Build the orthogonal sum projection over a finset, together with map/μ formulas.
  have sumData :
      ∀ s : Finset ι, ∃ Q : Projection H,
        (Q.1 = s.sum (fun i => (P i).1)) ∧ (μ.μ Q = s.sum (fun i => μ.μ (P i))) := by
    intro s
    classical
    refine Finset.induction_on s ?base ?step
    · refine ⟨Projection.zero, ?_, ?_⟩
      · simp [Projection.zero]
      · simpa using (FrameFunction.mu_zero (μ := μ))
    · intro i s hi hs
      rcases hs with ⟨Q, hQmap, hQmu⟩
      -- orthogonality of `P i` with the existing sum `Q`
      have horth : Projection.orthogonal (P i) Q := by
        -- show (P i).1 * Q.1 = 0 by expanding Q.1 as a sum
        ext v
        have hterm : ∀ j ∈ s, (P i).1 ((P j).1 v) = 0 := by
          intro j hj
          have hij : i ≠ j := by
            exact fun h => hi (by simpa [h] using hj)
          have hor : Orthonormal ℂ e := e.orthonormal
          have hinner : inner (𝕜 := ℂ) (e i) (e j) = 0 := by
            simpa [hij] using hor i j
          have hop : Projection.orthogonal (P i) (P j) := by
            simpa [P] using
              (rankOneProjection_orthogonal_of_inner_eq_zero (H := H)
                (x := e i) (y := e j)
                (hx := (hene i))
                (hy := (hene j))
                hinner)
          have hop' : (P i).1 * (P j).1 = 0 := hop
          have := congrArg (fun f : H →L[ℂ] H => f v) hop'
          simpa [ContinuousLinearMap.mul_apply] using this
        calc
          (P i).1 (Q.1 v)
              = (P i).1 (s.sum (fun j => (P j).1 v)) := by
                  simpa [hQmap, ContinuousLinearMap.sum_apply]
          _ = s.sum (fun j => (P i).1 ((P j).1 v)) := by
            simpa using (map_sum (P i).1 (fun j => (P j).1 v) s)
          _ = 0 := by
            refine Finset.sum_eq_zero ?_
            intro j hj
            exact hterm j hj

      refine ⟨Projection.add (P i) Q horth, ?_, ?_⟩
      · -- operator formula
        simp [Projection.add, hQmap, Finset.sum_insert hi, add_assoc]
      · -- μ formula
        have hadd := μ.additive (P i) Q horth
        -- `μ(add Pi Q) = μ Pi + μ Q`
        -- rewrite with IH and `sum_insert`
        simpa [hQmu, Finset.sum_insert hi, add_assoc] using hadd

  -- Full sum over the basis.
  let Qall : Projection H := Classical.choose (sumData (Finset.univ : Finset ι))
  have hQall_map : Qall.1 = (Finset.univ : Finset ι).sum (fun i => (P i).1) :=
    (Classical.choose_spec (sumData (Finset.univ : Finset ι))).1
  have hQall_mu : μ.μ Qall = (Finset.univ : Finset ι).sum (fun i => μ.μ (P i)) :=
    (Classical.choose_spec (sumData (Finset.univ : Finset ι))).2

  -- Show the sum of rank-one projections is the identity map.
  have hsum_id : ((Finset.univ : Finset ι).sum (fun i => (P i).1)) = (1 : H →L[ℂ] H) := by
    have h_on_basis : ∀ k : ι, ((Finset.univ : Finset ι).sum (fun i => (P i).1)) (e k) = e k := by
      intro k
      have hk : k ∈ (Finset.univ : Finset ι) := by simp
      -- split the sum into `k` and the rest
      have hsplit :=
        (Finset.sum_eq_add_sum_diff_singleton (s := (Finset.univ : Finset ι))
          (f := fun i => (P i).1 (e k)) hk)
      -- main term: projection fixes its own basis vector
      have hPk : (P k).1 (e k) = e k := by
        have hmem : e k ∈ (ℂ ∙ e k : Submodule ℂ H) := by
          exact Submodule.subset_span (by simp)
        have := Submodule.starProjection_eq_self_of_mem (H := H) (K := (ℂ ∙ e k : Submodule ℂ H)) (v := e k) hmem
        simpa [P, RankOne.rankOneProjection] using this
      -- other terms: projection onto `e i` kills `e k` when i ≠ k
      have hPne : ∀ i ∈ (Finset.univ.erase k), (P i).1 (e k) = 0 := by
        intro i hi
        have hik : i ≠ k := Finset.ne_of_mem_erase hi
        have hor : Orthonormal ℂ e := e.orthonormal
        have hinner : inner (𝕜 := ℂ) (e i) (e k) = 0 := by
          simpa [hik] using hor i k
        have hk_orth : e k ∈ (ℂ ∙ e i : Submodule ℂ H)ᗮ := by
          refine (Submodule.mem_orthogonal (K := (ℂ ∙ e i : Submodule ℂ H)) (v := e k)).2 ?_
          intro w hw
          rcases Submodule.mem_span_singleton.mp hw with ⟨a, rfl⟩
          simp [inner_smul_left, hinner]
        have := Submodule.starProjection_eq_zero_of_mem_orthogonal (K := (ℂ ∙ e i : Submodule ℂ H)) (v := e k) hk_orth
        simpa [P, RankOne.rankOneProjection] using this
      have hrest : ((Finset.univ.erase k).sum (fun i => (P i).1 (e k))) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        exact hPne i hi
      -- use the split equality and simplify
      calc
        ((Finset.univ : Finset ι).sum (fun i => (P i).1)) (e k)
            = (Finset.univ : Finset ι).sum (fun i => (P i).1 (e k)) := by
                simpa [ContinuousLinearMap.sum_apply]
        _ = (P k).1 (e k) + (Finset.univ.erase k).sum (fun i => (P i).1 (e k)) := by
                simpa [Finset.sdiff_singleton_eq_erase] using hsplit
        _ = e k := by simp [hPk, hrest]

    -- upgrade pointwise identity on basis to operator equality
    have hlin :
        ( ((Finset.univ : Finset ι).sum (fun i => (P i).1)).toLinearMap )
          = (1 : H →ₗ[ℂ] H) := by
      refine (e.toBasis.ext fun k => ?_)
      simpa using h_on_basis k
    ext v
    simpa using congrArg (fun f : H →ₗ[ℂ] H => f v) hlin

  -- Hence the projection sum equals `1`.
  have hQall_one : Qall = Projection.one := by
    apply Projection.ext
    calc
      Qall.1 = (Finset.univ : Finset ι).sum (fun i => (P i).1) := hQall_map
      _ = (1 : H →L[ℂ] H) := hsum_id

  -- Sum of μ over basis rank-one projections is `1`.
  have hsum_mu : ((Finset.univ : Finset ι).sum (fun i => μ.μ (P i))) = 1 := by
    have hμQall : μ.μ Qall = 1 := by
      simpa [hQall_one] using μ.normalized
    -- use `hQall_mu : μ Qall = sum μ`
    simpa using
      (show (Finset.univ : Finset ι).sum (fun i => μ.μ (P i)) = μ.μ Qall from hQall_mu.symm).trans hμQall

  -- Trace as a sum of diagonal inner products over an orthonormal basis.
  have htrace :
      LinearMap.trace ℂ H T.toLinearMap
        = ∑ i : ι, inner (𝕜 := ℂ) (e i) (T (e i)) := by
    simpa using (LinearMap.trace_eq_sum_inner (T := T.toLinearMap) (b := e))

  -- Diagonal entries: `⟪e i, T e i⟫ = q(e i)` as a complex number.
  have hdiag : ∀ i : ι, inner ℂ (e i) (T (e i)) = (frame_quadratic μ (e i) : ℂ) := by
    intro i
    have hre : (inner ℂ (e i) (T (e i))).re = frame_quadratic μ (e i) := by
      simpa using (Eq.symm (hT.2 (e i)))
    have hz_conj : inner ℂ (e i) (T (e i)) = conj (inner ℂ (e i) (T (e i))) := by
      have hpol : polarization (frame_quadratic μ) (e i) (e i) = inner ℂ (e i) (T (e i)) := by
        simpa using (hT.1 (e i) (e i))
      have hconj : polarization (frame_quadratic μ) (e i) (e i) =
          conj (polarization (frame_quadratic μ) (e i) (e i)) := by
        simpa using (polarization_conj_symm (q := frame_quadratic μ) hq (e i) (e i))
      calc
        inner ℂ (e i) (T (e i)) = polarization (frame_quadratic μ) (e i) (e i) := by
          simpa using hpol.symm
        _ = conj (polarization (frame_quadratic μ) (e i) (e i)) := hconj
        _ = conj (inner ℂ (e i) (T (e i))) := by
          simpa using congrArg conj hpol
    have hz_im : (inner ℂ (e i) (T (e i))).im = 0 := by
      have hz_conj' : conj (inner ℂ (e i) (T (e i))) = inner ℂ (e i) (T (e i)) := by
        simpa using hz_conj.symm
      exact (Complex.conj_eq_iff_im).1 hz_conj'
    apply Complex.ext
    · simp [hre]
    · simp [hz_im]


  -- Convert the sum of `frame_quadratic` values into the μ-sum (using `‖e i‖ = 1`).
  have hq_sum_real : (∑ i : ι, frame_quadratic μ (e i)) = 1 := by
    have hterm : ∀ i : ι, frame_quadratic μ (e i) = μ.μ (P i) := by
      intro i
      have hne : (e i : H) ≠ 0 := hene i
      have hnorm : ‖(e i : H)‖ = 1 := by simpa using (e.norm_eq i)
      simp [frame_quadratic, hne, P, hnorm]
    -- rewrite the fintype sum as a finset sum and apply `hsum_mu`
    -- `Fintype.sum` on `Fin` is `Finset.univ.sum`
    simpa [hterm] using hsum_mu

  -- Finish.
  calc
    LinearMap.trace ℂ H T.toLinearMap
        = ∑ i : ι, inner (𝕜 := ℂ) (e i) (T (e i)) := htrace
    _ = ∑ i : ι, (frame_quadratic μ (e i) : ℂ) := by
      simp [hdiag]
    _ = (1 : ℂ) := by
      classical
      have hsum_real_univ :
          (Finset.univ : Finset ι).sum (fun i => frame_quadratic μ (e i)) = 1 := by
        simpa using hq_sum_real
      have hfinset :
          (Finset.univ : Finset ι).sum (fun i => (frame_quadratic μ (e i) : ℂ)) = 1 := by
        calc
          (Finset.univ : Finset ι).sum (fun i => (frame_quadratic μ (e i) : ℂ))
              = ((Finset.univ : Finset ι).sum (fun i => frame_quadratic μ (e i)) : ℂ) := by
                  simpa using
                    (map_sum Complex.ofRealHom (fun i : ι => frame_quadratic μ (e i))
                      (Finset.univ : Finset ι)).symm
          _ = (1 : ℂ) := by
            simpa using congrArg (fun r : ℝ => (r : ℂ)) hsum_real_univ
      -- `∑ i : ι, _` is definitional equal to `Finset.univ.sum`.
      simpa using hfinset
