import Mathlib

import Gleason.Finite.RankOneProjection
import Gleason.Finite.FrameFunction
import Gleason.Finite.Quadratic.Homogeneity

import Gleason.Finite.Polarization.OperatorRepresentation
import Gleason.Finite.Quadratic.Bound
import Gleason.Finite.TraceNormalization

noncomputable section

open scoped BigOperators
open RankOne

namespace Gleason

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- Minimal "density operator" wrapper (only the bundled operator is used here). -/
structure DensityOperator (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H] where
  ρ : H →L[ℂ] H

namespace RankOne

/-- A convenient normalized representative for the line spanned by `x`. -/
def normalize (x : H) : H := ((‖x‖ : ℂ)⁻¹) • x

lemma normalize_ne_zero {x : H} (hx : x ≠ 0) : normalize (H := H) x ≠ 0 := by
  classical
  have hn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hx
  have hcx : ((‖x‖ : ℂ)) ≠ 0 := by exact_mod_cast hn
  have hc : ((‖x‖ : ℂ)⁻¹) ≠ 0 := inv_ne_zero hcx
  simpa [normalize] using smul_ne_zero hc hx

lemma rankOneProjection_normalize (x : H) (hx : x ≠ 0) :
    rankOneProjection (H := H) (normalize (H := H) x) (normalize_ne_zero (H := H) hx)
      =
    rankOneProjection (H := H) x hx := by
  classical
  -- scaling by a nonzero scalar does not change the projection
  have hn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hx
  have hcx : ((‖x‖ : ℂ)) ≠ 0 := by exact_mod_cast hn
  have hc : ((‖x‖ : ℂ)⁻¹) ≠ 0 := inv_ne_zero hcx
  simpa [normalize] using
    (RankOne.rankOneProjection_smul (H := H) x hx ((‖x‖ : ℂ)⁻¹) hc)

end RankOne

/-- Trace of an operator composed with a rank-one projection. -/
theorem trace_comp_rankOneProjection (A : H →L[ℂ] H) (x : H) (hx : x ≠ 0) :
    LinearMap.trace ℂ H
        (A.toLinearMap.comp (rankOneProjection (H := H) x hx).1.toLinearMap)
      =
    (inner (𝕜 := ℂ) x (A x)) / (inner (𝕜 := ℂ) x x) := by
  classical
  -- Normalize `x` so the projection has the simple formula `⟪u,·⟫ • u`.
  let u : H := RankOne.normalize (H := H) x
  have hu : u ≠ 0 := RankOne.normalize_ne_zero (H := H) hx
  have hPu :
      rankOneProjection (H := H) u hu = rankOneProjection (H := H) x hx :=
    (RankOne.rankOneProjection_normalize (H := H) x hx)

  -- Reduce to the normalized vector.
  have htrace_u :
      LinearMap.trace ℂ H (A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap)
        =
      inner (𝕜 := ℂ) u (A u) := by
    -- Extend `{u}` to an orthonormal basis indexed by a finset of vectors.
    let v : Set H := {u}
    have hv : Orthonormal ℂ ((↑) : v → H) := by
      classical
      -- in a singleton set, everything is `u`, so it suffices to check `‖u‖ = 1`
      rw [orthonormal_iff_ite]
      intro a b
      have ha : (a : H) = u := by
        have : (a : H) ∈ ({u} : Set H) := by simpa [v] using a.property
        exact (Set.mem_singleton_iff.mp this)
      have hb : (b : H) = u := by
        have : (b : H) ∈ ({u} : Set H) := by simpa [v] using b.property
        exact (Set.mem_singleton_iff.mp this)
      have hab : a = b := by
        ext
        simpa [ha, hb]
      subst hab
      -- now show `⟪u,u⟫ = 1`
      have hn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hx
      have hu_norm : ‖u‖ = 1 := by
        have hscalar : ‖((‖x‖ : ℂ)⁻¹)‖ = (‖x‖)⁻¹ := by simp
        calc
          ‖u‖ = ‖((‖x‖ : ℂ)⁻¹)‖ * ‖x‖ := by
                simpa [u, RankOne.normalize, norm_smul, mul_comm]
          _ = (‖x‖)⁻¹ * ‖x‖ := by simpa [hscalar]
          _ = 1 := by
                field_simp [hn]
      -- `⟪u,u⟫ = (‖u‖ : ℂ)^2 = 1`
      have hu_inner : inner (𝕜 := ℂ) u u = (‖u‖ : ℂ) ^ 2 := by
        simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u)
      simpa [ha, hu_inner, hu_norm]

    obtain ⟨s, b, hvsub, hb⟩ :=
      Orthonormal.exists_orthonormalBasis_extension (𝕜 := ℂ) (E := H) (v := v) hv

    -- Use `trace_eq_sum_inner` with this orthonormal basis.
    have htrace :
        LinearMap.trace ℂ H (A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap)
          =
        ∑ i : (↥s), inner (𝕜 := ℂ) (b i)
            ((A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap) (b i)) := by
      simpa using
        (LinearMap.trace_eq_sum_inner
          (T := (A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap))
          (b := b))

    -- Identify the distinguished index corresponding to `u`.
    have hu_mem : u ∈ s := by
      have : u ∈ (v : Set H) := by simp [v]
      exact hvsub this
    let iu : ↥s := ⟨u, hu_mem⟩

    -- `P(u) u = u`
    have hP_u : (rankOneProjection (H := H) u hu).1 u = u := by
      -- projection onto `ℂ∙u` fixes `u`
      have hu_span : u ∈ (ℂ ∙ u : Submodule ℂ H) := Submodule.subset_span (by simp)
      simpa [RankOne.rankOneProjection] using
        (Submodule.starProjection_eq_self_of_mem (H := H) (K := (ℂ ∙ u : Submodule ℂ H)) (v := u) hu_span)

    -- For `i ≠ iu`, `P(u) (b i) = 0`.
    have hP_other : ∀ i : ↥s, i ≠ iu → (rankOneProjection (H := H) u hu).1 (b i) = 0 := by
      intro i hiu
      -- use that `b` is orthonormal and `b iu = u`
      have hbi : b iu = u := by
        have := congrArg (fun f => f iu) hb
        simpa [iu] using this
      have hb0 : inner (𝕜 := ℂ) u (b i) = 0 := by
        -- `⟪b iu, b i⟫ = 0`
        have h0 : inner (𝕜 := ℂ) (b iu) (b i) = 0 := by
          have : iu ≠ i := by
            intro hEq
            exact hiu hEq.symm
          simpa using (OrthonormalBasis.inner_eq_zero (b := b) this)
        simpa [hbi] using h0
      -- hence `b i ∈ (ℂ∙u)ᗮ`
      have hmem : (b i) ∈ (ℂ ∙ u : Submodule ℂ H)ᗮ := by
        refine (Submodule.mem_orthogonal (K := (ℂ ∙ u : Submodule ℂ H)) (v := b i)).2 ?_
        intro z hz
        rcases Submodule.mem_span_singleton.mp hz with ⟨c, rfl⟩
        simpa [inner_smul_left, hb0]
      -- projection kills orthogonal vectors
      simpa [RankOne.rankOneProjection] using
        (Submodule.starProjection_eq_zero_of_mem_orthogonal (K := (ℂ ∙ u : Submodule ℂ H)) (v := b i) hmem)

    -- Collapse the trace sum: only the `iu` term survives.
    have hsum :
        (∑ i : (↥s),
          inner (𝕜 := ℂ) (b i)
            ((A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap) (b i)))
          =
        inner (𝕜 := ℂ) u (A u) := by
      classical
      -- rewrite `b` as the inclusion, so `b i = i`
      have hb' : ∀ i : ↥s, b i = (i : H) := by
        intro i
        have := congrArg (fun f => f i) hb
        simpa using this

      -- pointwise vanishing for `i ≠ iu`
      have hterm0 :
          ∀ i : ↥s, i ≠ iu →
            inner (𝕜 := ℂ) (b i)
              ((A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap) (b i)) = 0 := by
        intro i hi
        have hPi : (rankOneProjection (H := H) u hu).1 (b i) = 0 := hP_other i hi
        have hAPi :
            (A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap) (b i) = 0 := by
          simp [LinearMap.comp_apply, hPi]
        simp [hAPi]

      -- compute the `iu` term
      have htermu :
          inner (𝕜 := ℂ) (b iu)
              ((A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap) (b iu))
            =
          inner (𝕜 := ℂ) u (A u) := by
        simp [hb' iu, iu, hP_u]

      -- collapse the sum to the single surviving index `iu`
      have hsingle :
          (∑ i : ↥s,
            inner (𝕜 := ℂ) (b i)
              ((A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap) (b i)))
            =
          inner (𝕜 := ℂ) (b iu)
              ((A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap) (b iu)) := by
        -- unfold the `Fintype` sum
        change (Finset.univ.sum (fun i : ↥s =>
          inner (𝕜 := ℂ) (b i)
            ((A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap) (b i))))
          =
          inner (𝕜 := ℂ) (b iu)
            ((A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap) (b iu))
        refine Finset.sum_eq_single iu ?_ ?_
        · intro i _hi hi_ne
          exact hterm0 i hi_ne
        · intro hiu_not
          exfalso
          exact hiu_not (by simp)

      calc
        (∑ i : ↥s,
          inner (𝕜 := ℂ) (b i)
            ((A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap) (b i)))
            =
          inner (𝕜 := ℂ) (b iu)
            ((A.toLinearMap.comp (rankOneProjection (H := H) u hu).1.toLinearMap) (b iu)) := hsingle
        _ = inner (𝕜 := ℂ) u (A u) := htermu

    -- conclude `trace = ⟪u, A u⟫`
    simpa [htrace] using htrace.trans hsum

  -- Now rewrite back in terms of `x`.
  -- First use `hPu` to replace projections.
  have htrace' :
      LinearMap.trace ℂ H (A.toLinearMap.comp (rankOneProjection (H := H) x hx).1.toLinearMap)
        =
      inner (𝕜 := ℂ) u (A u) := by
    simpa [hPu] using htrace_u

  -- Compute `⟪u, A u⟫ = ⟪x, A x⟫ / ⟪x, x⟫`.
  have hinner :
      inner (𝕜 := ℂ) u (A u) = (inner (𝕜 := ℂ) x (A x)) / (inner (𝕜 := ℂ) x x) := by
    have hn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hx
    have hcx : ((‖x‖ : ℂ)) ≠ 0 := by exact_mod_cast hn
    have : inner (𝕜 := ℂ) x x = (‖x‖ : ℂ) ^ 2 := by simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x)
    -- expand `u` and simplify using sesquilinearity; finish with a small ring-normalization
    -- (using that `‖x‖` is real, hence `star ((‖x‖ : ℂ)⁻¹) = (‖x‖ : ℂ)⁻¹`).
    simp [u, RankOne.normalize, this, inner_smul_left, inner_smul_right, map_smul,
      div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    ring_nf

  simpa [htrace', hinner]


/-- Gleason's theorem specialized to rank-one projections. -/
theorem gleason_rank_one
    (μ : FrameFunction H)
    (h_para :
      ∀ x y : H,
        frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
          = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y)
    (x : H) (hx : x ≠ 0) :
    let T :=
      (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ)
        (frame_quadratic_is_bounded_quadratic (H := H) μ h_para)).choose
    let ρ : DensityOperator H := ⟨T⟩
    μ.μ (rankOneProjection (H := H) x hx)
      =
    (LinearMap.trace ℂ H (ρ.ρ.toLinearMap.comp (rankOneProjection (H := H) x hx).1.toLinearMap)).re := by
  classical
  intro T ρ

  -- Step (1): μ(Px) = frame_quadratic μ x / ‖x‖²
  have hxnorm : (‖x‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hx)
  have h_def :
      frame_quadratic (H := H) μ x = μ.μ (rankOneProjection (H := H) x hx) * ‖x‖ ^ 2 := by
    simp [frame_quadratic, hx]
  have h_mu :
      μ.μ (rankOneProjection (H := H) x hx)
        = frame_quadratic (H := H) μ x / ‖x‖ ^ 2 := by
    have := congrArg (fun t => t / (‖x‖ ^ 2)) h_def
    simpa [mul_div_assoc, hxnorm] using this.symm

  -- Step (2): frame_quadratic μ x = re ⟪x, T x⟫
  have hTq : frame_quadratic (H := H) μ x = (inner (𝕜 := ℂ) x (T x)).re := by
    simpa [T] using
      (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ)
        (frame_quadratic_is_bounded_quadratic (H := H) μ h_para)).choose_spec.2 x

  have h_mu2 :
      μ.μ (rankOneProjection (H := H) x hx)
        = (inner (𝕜 := ℂ) x (T x)).re / ‖x‖ ^ 2 := by
    simpa [h_mu, hTq]

  -- Step (3): trace formula for rank-one composition
  have htr :
      LinearMap.trace ℂ H
        (ρ.ρ.toLinearMap.comp (rankOneProjection (H := H) x hx).1.toLinearMap)
        =
      (inner (𝕜 := ℂ) x (T x)) / (inner (𝕜 := ℂ) x x) := by
    -- `ρ.ρ = T`
    simpa [ρ, DensityOperator.ρ] using (trace_comp_rankOneProjection (A := T) (x := x) hx)

  -- Convert `re (⟪x,Tx⟫ / ⟪x,x⟫)` into `re⟪x,Tx⟫ / ‖x‖²`.
  have hdiv_re :
      ((inner (𝕜 := ℂ) x (T x)) / (inner (𝕜 := ℂ) x x)).re
        = (inner (𝕜 := ℂ) x (T x)).re / ‖x‖ ^ 2 := by
    -- rewrite the denominator as a real scalar
    have hx_inner : (inner (𝕜 := ℂ) x x) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      -- `⟪x,x⟫ = (‖x‖ : ℂ)^2` and `((‖x‖ : ℂ)^2) = (‖x‖^2 : ℂ)`
      simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x)
    -- now `Complex.div_ofReal_re` applies
    calc
      ((inner (𝕜 := ℂ) x (T x)) / (inner (𝕜 := ℂ) x x)).re
          = ((inner (𝕜 := ℂ) x (T x)) / (‖x‖ ^ 2 : ℝ)).re := by
              simpa [hx_inner]
      _ = (inner (𝕜 := ℂ) x (T x)).re / ‖x‖ ^ 2 := by
              -- compute the real part of division by a real scalar
              exact (Complex.div_ofReal_re (inner (𝕜 := ℂ) x (T x)) (‖x‖ ^ 2))

  -- Final assembly
  calc
    μ.μ (rankOneProjection (H := H) x hx)
        = (inner (𝕜 := ℂ) x (T x)).re / ‖x‖ ^ 2 := h_mu2
    _ = ((inner (𝕜 := ℂ) x (T x)) / (inner (𝕜 := ℂ) x x)).re := by
          symm
          exact hdiv_re
    _ = (LinearMap.trace ℂ H (ρ.ρ.toLinearMap.comp (rankOneProjection (H := H) x hx).1.toLinearMap)).re := by
          simpa [htr]

end Gleason
