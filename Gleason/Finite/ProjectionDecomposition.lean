import Mathlib
import Gleason.Finite.RankOneProjection
import Gleason.Finite.ProjectionSum

noncomputable section
open scoped BigOperators
open RankOne

namespace Projection

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-!
Small utilities
-/

/-- Apply a `Finset.sum` of linear maps. -/
lemma finset_sum_apply {ι} (s : Finset ι) (f : ι → (H →L[ℂ] H)) (x : H) :
    (Finset.sum s f) x = Finset.sum s (fun i => f i x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    simp [ha, ih]

/-- Uniqueness of orthogonal projection. -/
lemma eq_starProjection_of_mem_of_sub_mem_orthogonal
    (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (x u : H) (hu : u ∈ K) (hxu : x - u ∈ Kᗮ) :
    u = K.starProjection x := by
  classical
  -- `Submodule.eq_starProjection_of_mem_orthogonal` is the standard uniqueness lemma.
  have h := (Submodule.eq_starProjection_of_mem_orthogonal (K := K) (u := x) (v := u) hu hxu)
  simpa using h.symm

/-- Star projection fixes vectors in the subspace. -/
lemma starProjection_eq_self_of_mem
    (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    {x : H} (hx : x ∈ K) :
    K.starProjection x = x := by
  have := eq_starProjection_of_mem_of_sub_mem_orthogonal
    (K := K) (x := x) (u := x) hx (by simpa)
  simpa using this.symm

/-- Star projection kills orthogonal vectors. -/
lemma starProjection_eq_zero_of_mem_orthogonal
    (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    {x : H} (hx : x ∈ Kᗮ) :
    K.starProjection x = 0 := by
  have := eq_starProjection_of_mem_of_sub_mem_orthogonal
    (K := K) (x := x) (u := 0)
    (by simp) (by simpa)
  simpa using this.symm

/-- A projection equals the orthogonal projection onto its range. -/
lemma coe_eq_starProjection_range (P : Projection H) :
    P.1 = (LinearMap.range P.1.toLinearMap).starProjection := by
  classical
  let K := LinearMap.range P.1.toLinearMap
  haveI : K.HasOrthogonalProjection := by infer_instance

  ext x

  have hxK : P.1 x ∈ K := ⟨x, rfl⟩

  have hxOrth : x - P.1 x ∈ Kᗮ := by
    refine (Submodule.mem_orthogonal (K := K) (v := x - P.1 x)).2 ?_
    intro y hy
    rcases hy with ⟨u, rfl⟩
    simpa [inner_sub_right] using (P.inner_err u x)

  have := eq_starProjection_of_mem_of_sub_mem_orthogonal
    (K := K) (x := x) (u := P.1 x) hxK hxOrth

  simpa [K] using this

/-- Rank-one projections from orthogonal vectors are orthogonal. -/
lemma rankOneProjection_orthogonal_of_orthogonal
    (u v : H) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : inner ℂ u v = 0) :
    Projection.orthogonal
      (rankOneProjection u hu)
      (rankOneProjection v hv) := by
  classical
  let Uu : Submodule ℂ H := ℂ ∙ u
  let Uv : Submodule ℂ H := ℂ ∙ v
  haveI : Uu.HasOrthogonalProjection := by infer_instance
  haveI : Uv.HasOrthogonalProjection := by infer_instance

  unfold Projection.orthogonal
  ext x

  have hx : (Uv.starProjection x) ∈ Uuᗮ := by
    refine (Submodule.mem_orthogonal (K := Uu) (v := Uv.starProjection x)).2 ?_
    intro y hy
    rcases Submodule.mem_span_singleton.mp hy with ⟨c, rfl⟩
    -- `Uv.starProjection x` lies in `Uv = ℂ∙v`, so it is a scalar multiple of `v`.
    have hxv : Uv.starProjection x ∈ Uv := by
      simpa using (Submodule.starProjection_apply_mem (U := Uv) x)
    rcases Submodule.mem_span_singleton.mp hxv with ⟨d, hd⟩
    -- Reduce to the given orthogonality `⟪u,v⟫ = 0`.
    have hd' : Uv.starProjection x = d • v := by
      simpa using hd.symm
    simp [hd', inner_smul_left, inner_smul_right, h]

  have hkill := starProjection_eq_zero_of_mem_orthogonal (K := Uu) (x := Uv.starProjection x) hx
  simpa [RankOne.rankOneProjection, Uu, Uv, ContinuousLinearMap.mul_apply] using hkill

/-!
Main theorem
-/

theorem projection_eq_sum_rankOne (P : Projection H) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
      (b : ι → H) (hb : ∀ i, b i ≠ 0),
      ∃ (horth : ∀ i j, i ≠ j →
        Projection.orthogonal
          (rankOneProjection (b i) (hb i))
          (rankOneProjection (b j) (hb j))),
      P =
        Projection.sum Finset.univ
          (fun i => rankOneProjection (b i) (hb i))
          horth := by
  classical

  let K := LinearMap.range P.1.toLinearMap
  haveI : FiniteDimensional ℂ K := by infer_instance

  -- ONB of K
  let ι := Fin (Module.finrank ℂ K)
  let e := stdOrthonormalBasis ℂ K

  let b : ι → H := fun i => (e i : H)

  have hb : ∀ i, b i ≠ 0 := by
    intro i
    intro hi
    have hneK : (e i : K) ≠ 0 := by
      simpa using (Orthonormal.ne_zero (𝕜 := ℂ) e.orthonormal i)
    apply hneK
    ext
    simpa [b] using hi

  have horth :
      ∀ i j, i ≠ j →
        Projection.orthogonal
          (rankOneProjection (b i) (hb i))
          (rankOneProjection (b j) (hb j)) := by
    intro i j hij
    have h0 : inner ℂ (b i) (b j) = 0 := by
      simpa [b] using (OrthonormalBasis.inner_eq_zero (b := e) hij)
    simpa using
      (rankOneProjection_orthogonal_of_orthogonal (u := b i) (v := b j) (hu := hb i) (hv := hb j) h0)

  have hP := coe_eq_starProjection_range (P := P)

  refine ⟨ι, inferInstance, inferInstance, b, hb, ⟨horth, ?_⟩⟩
  -- It suffices to show the underlying operators agree.
  apply Subtype.ext
  -- We show the sum is the orthogonal projection onto `K = range P`.
  ext x
  haveI : K.HasOrthogonalProjection := by infer_instance

  -- Abbreviation for the rank-one family.
  let R : ι → Projection H := fun i => rankOneProjection (b i) (hb i)
  let Q : Projection H := Projection.sum (H := H) (ι := ι) Finset.univ R horth

  -- `P` is the orthogonal projection onto its range.
  have hP' : P.1 = K.starProjection := by
    simpa [K] using hP

  -- Reduce to showing `Q.1 x` satisfies the characterization of `K.starProjection x`.
  have hQ_mem : Q.1 x ∈ K := by
    -- Expand `Q.1 x` as a finite sum and show each term lies in `K`.
    have hQcoe :
        Q.1 = Finset.sum (Finset.univ : Finset ι) (fun i => (R i).1) := by
      simpa [Q, R] using (Projection.sum_coe (H := H) (ι := ι) (s := (Finset.univ : Finset ι)) (P := R)
        (h := horth))
    have hQx :
        Q.1 x = Finset.sum (Finset.univ : Finset ι) (fun i => (R i).1 x) := by
      simpa [finset_sum_apply] using congrArg (fun f : H →L[ℂ] H => f x) hQcoe
    -- Each basis vector lies in `K`, hence its span is contained in `K`.
    have hbK : ∀ i : ι, b i ∈ K := by
      intro i
      -- `e i : K` by definition.
      simpa [b] using (e i).property
    have hspan_le : ∀ i : ι, (ℂ ∙ b i : Submodule ℂ H) ≤ K := by
      intro i y hy
      rcases Submodule.mem_span_singleton.mp hy with ⟨c, rfl⟩
      exact K.smul_mem c (hbK i)
    have hterm : ∀ i : ι, (R i).1 x ∈ K := by
      intro i
      have hmem_span : (R i).1 x ∈ (ℂ ∙ b i : Submodule ℂ H) := by
        -- `rankOneProjection` projects onto `ℂ∙(b i)`.
        simpa [R, RankOne.rankOneProjection] using
          (Submodule.starProjection_apply_mem (U := (ℂ ∙ b i : Submodule ℂ H)) x)
      exact hspan_le i hmem_span
    -- Now sum.
    simpa [hQx] using (K.sum_mem fun i _hi => hterm i)

  have hQ_orth : x - Q.1 x ∈ Kᗮ := by
    -- It suffices to show orthogonality against an arbitrary `y ∈ K`.
    refine (Submodule.mem_orthogonal (K := K) (v := x - Q.1 x)).2 ?_
    intro y hy
    -- View `y` as an element of `K` and expand it in the orthonormal basis `e`.
    let yK : K := ⟨y, hy⟩
    have hyK :
        (yK : H) = (∑ i : ι, (e.repr yK).ofLp i • (b i)) := by
      -- Coerce the `K`-valued expansion to `H`.
      have hy0 : (∑ i : ι, (e.repr yK).ofLp i • e i) = yK :=
        OrthonormalBasis.sum_repr e yK
      have hy1 := congrArg (fun z : K => (z : H)) hy0
      -- Turn `(e i : K)` into `b i : H`.
      simpa [b] using hy1.symm

    -- First show `⟪b k, x - Q x⟫ = 0` for each basis vector `b k`.
    have hb_inner_zero : ∀ k : ι, inner ℂ (b k) (x - Q.1 x) = 0 := by
      intro k
      -- Expand `Q.1 x` as a sum.
      have hQcoe :
          Q.1 = Finset.sum (Finset.univ : Finset ι) (fun i => (R i).1) := by
        simpa [Q, R] using (Projection.sum_coe (H := H) (ι := ι) (s := (Finset.univ : Finset ι)) (P := R)
          (h := horth))
      have hQx :
          Q.1 x = Finset.sum (Finset.univ : Finset ι) (fun i => (R i).1 x) := by
        simpa [finset_sum_apply] using congrArg (fun f : H →L[ℂ] H => f x) hQcoe
      -- Use `Finset.sum_eq_add_sum_diff_singleton` to isolate the `k`-term.
      have hk : k ∈ (Finset.univ : Finset ι) := by simp
      have hsplit :=
        (Finset.sum_eq_add_sum_diff_singleton (s := (Finset.univ : Finset ι))
          (f := fun i => (R i).1 x) hk)

      -- The `k`-term captures the `b k` component.
      have hdiag :
          inner ℂ (b k) ((R k).1 x) = inner ℂ (b k) x := by
        -- `x - (R k).1 x` is orthogonal to `ℂ∙(b k)`.
        have hx_orth' : x - (R k).1 x ∈ (ℂ ∙ b k : Submodule ℂ H)ᗮ := by
          simpa [R, RankOne.rankOneProjection] using
            (Submodule.sub_starProjection_mem_orthogonal (K := (ℂ ∙ b k : Submodule ℂ H)) x)
        have hb_mem : b k ∈ (ℂ ∙ b k : Submodule ℂ H) := Submodule.subset_span (by simp)
        have h0 :
            inner ℂ (b k) (x - (R k).1 x) = 0 :=
          (Submodule.mem_orthogonal (K := (ℂ ∙ b k : Submodule ℂ H)) (v := x - (R k).1 x)).1
            hx_orth' (b k) hb_mem
        have hEq : inner ℂ (b k) x = inner ℂ (b k) ((R k).1 x) := by
          -- `inner b k (x - proj) = inner b k x - inner b k (proj)`
          refine sub_eq_zero.mp ?_
          simpa [inner_sub_right] using h0
        simpa using hEq.symm

      -- Off-diagonal terms vanish by orthogonality.
      have hoff :
          inner ℂ (b k) ((Finset.univ \ {k}).sum (fun i => (R i).1 x)) = 0 := by
        classical
        -- Each summand lies in `(ℂ∙b k)ᗮ`, hence so does the sum.
        have hsum_orth :
            (Finset.univ \ {k}).sum (fun i => (R i).1 x) ∈ (ℂ ∙ b k : Submodule ℂ H)ᗮ := by
          refine ((ℂ ∙ b k : Submodule ℂ H)ᗮ).sum_mem ?_
          intro i hi
          have hik : i ≠ k := by
            have : i ∉ ({k} : Finset ι) := by
              simpa using (Finset.mem_sdiff.mp hi).2
            simpa using this
          have hinner : inner ℂ (b i) (b k) = 0 := by
            simpa [b] using (OrthonormalBasis.inner_eq_zero (b := e) hik)
          have hspan_le : (ℂ ∙ b i : Submodule ℂ H) ≤ (ℂ ∙ b k : Submodule ℂ H)ᗮ := by
            intro z hz
            refine (Submodule.mem_orthogonal (K := (ℂ ∙ b k : Submodule ℂ H)) (v := z)).2 ?_
            intro w hw
            rcases Submodule.mem_span_singleton.mp hz with ⟨c, rfl⟩
            rcases Submodule.mem_span_singleton.mp hw with ⟨d, rfl⟩
            have hinner' : inner ℂ (b k) (b i) = 0 := by
              simpa [inner_eq_zero_symm] using hinner
            simp [inner_smul_left, inner_smul_right, hinner, hinner']
          have hz_span : (R i).1 x ∈ (ℂ ∙ b i : Submodule ℂ H) := by
            simpa [R, RankOne.rankOneProjection] using
              (Submodule.starProjection_apply_mem (U := (ℂ ∙ b i : Submodule ℂ H)) x)
          exact hspan_le hz_span

        have hb_mem : b k ∈ (ℂ ∙ b k : Submodule ℂ H) := Submodule.subset_span (by simp)
        exact
          (Submodule.mem_orthogonal (K := (ℂ ∙ b k : Submodule ℂ H))
            (v := (Finset.univ \ {k}).sum (fun i => (R i).1 x))).1
            hsum_orth (b k) hb_mem

      -- Put it together: inner with `x - Qx` is zero.
      -- We only need the fact `inner (b k) (Qx) = inner (b k) x`.
      have hQ_inner : inner ℂ (b k) (Q.1 x) = inner ℂ (b k) x := by
        -- Using the split sum, off-diagonal terms vanish and the diagonal term matches.
        -- Expand `Q.1 x` as `k`-term plus the rest.
        have : Q.1 x = (R k).1 x + (Finset.univ \ {k}).sum (fun i => (R i).1 x) := by
          -- `hsplit` is exactly this equality.
          simpa [hQx] using hsplit.symm
        calc
          inner ℂ (b k) (Q.1 x)
              = inner ℂ (b k) ((R k).1 x + (Finset.univ \ {k}).sum (fun i => (R i).1 x)) := by
                  simpa [this]
          _   = inner ℂ (b k) ((R k).1 x) + inner ℂ (b k) ((Finset.univ \ {k}).sum (fun i => (R i).1 x)) := by
                  simp [inner_add_right]
          _   = inner ℂ (b k) x := by
                  calc
                    inner ℂ (b k) ((R k).1 x) +
                        inner ℂ (b k) ((Finset.univ \ {k}).sum (fun i => (R i).1 x))
                        = inner ℂ (b k) x + 0 := by
                            rw [hdiag, hoff]
                    _ = inner ℂ (b k) x := by simp

      -- Finish.
      simpa [inner_sub_right, hQ_inner] 

    -- Now use linearity (in the first argument: `sum_inner`) to conclude for arbitrary `y`.
    -- Rewrite `y` in terms of the basis `b i`.
    -- `hyK` gives `y = ∑ i, c i • b i`.
    -- Then each basis term has inner `0` with `x - Qx`.
    -- (We keep the proof simple: rewrite and let `simp` handle sum/scalar.)
    -- Convert `y` to the `Finset` sum form.
    have hy' : y = (∑ i : ι, (e.repr yK).ofLp i • (b i)) := by
      simpa using congrArg (fun z : H => z) hyK
    -- Now compute the inner product.
    simp [hy', hb_inner_zero, sum_inner, inner_smul_left]

  -- Apply the characterization of `K.starProjection x`.
  have hproj : K.starProjection x = Q.1 x :=
    Submodule.eq_starProjection_of_mem_orthogonal (K := K) (u := x) (v := Q.1 x) hQ_mem hQ_orth

  -- Conclude `P.1 x = Q.1 x`.
  have hPx : P.1 x = K.starProjection x := by
    simpa using congrArg (fun f : H →L[ℂ] H => f x) hP'
  calc
    P.1 x = K.starProjection x := hPx
    _ = Q.1 x := hproj

end Projection
