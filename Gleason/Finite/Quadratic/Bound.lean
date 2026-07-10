import Mathlib
import Gleason.Finite.Polarization.BoundedQuadraticForm
import Gleason.Finite.FrameFunction
import Gleason.Finite.RankOneProjection
import Gleason.Finite.Quadratic.Basic
import Gleason.Finite.Quadratic.Homogeneity

noncomputable section

open RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

namespace FrameQuadratic

/-- The orthogonal complement projection to the rank-one projection onto `ℂ ∙ x`. -/
def rankOneComplementProjection (x : H) (hx : x ≠ 0) : Projection H := by
  classical
  let K : Submodule ℂ H := (ℂ ∙ x)
  haveI : CompleteSpace (↥(Kᗮ)) := by infer_instance
  haveI : (Kᗮ).HasOrthogonalProjection := by infer_instance
  refine ⟨(Kᗮ).starProjection, ?_, ?_⟩
  ·
    have hId : IsIdempotentElem (Kᗮ).starProjection := by
      simpa using (Submodule.isIdempotentElem_starProjection (K := (Kᗮ)))
    simpa [IsIdempotentElem] using hId
  ·
    intro u v
    have hv : v - (Kᗮ).starProjection v ∈ (Kᗮ)ᗮ := by
      simpa using (Submodule.sub_starProjection_mem_orthogonal (K := (Kᗮ)) v)
    have hu : (Kᗮ).starProjection u ∈ (Kᗮ) := by
      simpa using (Submodule.starProjection_apply_mem (U := (Kᗮ)) u)
    have hv0 :
        ∀ w ∈ (Kᗮ), inner (𝕜 := ℂ) w (v - (Kᗮ).starProjection v) = (0 : ℂ) :=
      (Submodule.mem_orthogonal (K := (Kᗮ)) (v := v - (Kᗮ).starProjection v)).1 hv
    exact hv0 ((Kᗮ).starProjection u) hu

/-- If `v ∈ Kᗮ` then the orthogonal projection onto `K` sends `v` to `0`. -/
theorem starProjection_eq_zero_of_mem_orthogonal
    (K : Submodule ℂ H) (v : H) (hv : v ∈ Kᗮ) :
    K.starProjection v = 0 := by
  classical
  set p : H := K.starProjection v
  have hpK : p ∈ K := by
    simpa [p] using (Submodule.starProjection_apply_mem (U := K) v)
  have hdiff : v - p ∈ Kᗮ := by
    simpa [p] using (Submodule.sub_starProjection_mem_orthogonal (K := K) v)
  have hpKo : p ∈ Kᗮ := by
    have : v - (v - p) ∈ Kᗮ := sub_mem hv hdiff
    simpa [p, sub_sub_cancel] using this
  have hp0 : inner (𝕜 := ℂ) p p = (0 : ℂ) := by
    have hpKo' :
        ∀ w ∈ K, inner (𝕜 := ℂ) w p = (0 : ℂ) :=
      (Submodule.mem_orthogonal (K := K) (v := p)).1 hpKo
    exact hpKo' p hpK
  have : p = 0 := (inner_self_eq_zero.mp hp0)
  simpa [p, this]

/-- If `v ∈ K` then the orthogonal projection onto `K` fixes `v`. -/
theorem starProjection_eq_self_of_mem
    (K : Submodule ℂ H) (v : H) (hv : v ∈ K) :
    K.starProjection v = v := by
  classical
  set p : H := K.starProjection v
  have hpK : p ∈ K := by
    simpa [p] using (Submodule.starProjection_apply_mem (U := K) v)
  have hdiff : v - p ∈ Kᗮ := by
    simpa [p] using (Submodule.sub_starProjection_mem_orthogonal (K := K) v)
  have hdiffK : v - p ∈ K := sub_mem hv hpK
  have hdiff0 : inner (𝕜 := ℂ) (v - p) (v - p) = (0 : ℂ) := by
    have hdiffKo' :
        ∀ w ∈ K, inner (𝕜 := ℂ) w (v - p) = (0 : ℂ) :=
      (Submodule.mem_orthogonal (K := K) (v := v - p)).1 hdiff
    exact hdiffKo' (v - p) hdiffK
  have : v - p = 0 := (inner_self_eq_zero.mp hdiff0)
  have hvp : v = p := sub_eq_zero.mp this
  simpa [p] using hvp.symm

/-- For `K = ℂ ∙ x`, the sum of the projections onto `K` and `Kᗮ` is `1`. -/
theorem starProjection_add_starProjection_orthogonal_eq_id
    (x : H) (hx : x ≠ 0) :
    (( ( (ℂ ∙ x : Submodule ℂ H).starProjection )
        + ( ( (ℂ ∙ x : Submodule ℂ H)ᗮ ).starProjection ) ) : H →L[ℂ] H)
      = 1 := by
  classical
  let K : Submodule ℂ H := (ℂ ∙ x)
  haveI : CompleteSpace (↥(Kᗮ)) := by infer_instance
  haveI : (Kᗮ).HasOrthogonalProjection := by infer_instance
  ext y
  set p : H := K.starProjection y
  have hyKo : y - p ∈ Kᗮ := by
    simpa [p] using (Submodule.sub_starProjection_mem_orthogonal (K := K) y)
  have hfix : (Kᗮ).starProjection (y - p) = (y - p) :=
    starProjection_eq_self_of_mem (K := Kᗮ) (v := y - p) hyKo

  have hpK : p ∈ K := by
    simpa [p] using (Submodule.starProjection_apply_mem (U := K) y)

  have hp_in_double : p ∈ (Kᗮ)ᗮ := by
    refine (Submodule.mem_orthogonal (K := Kᗮ) (v := p)).2 ?_
    intro w hw
    have hw0 :
        inner (𝕜 := ℂ) p w = (0 : ℂ) :=
      (Submodule.mem_orthogonal (K := K) (v := w)).1 hw p hpK
    exact (inner_eq_zero_symm.mp hw0)

  have hkill : (Kᗮ).starProjection p = 0 :=
    starProjection_eq_zero_of_mem_orthogonal (K := Kᗮ) (v := p) hp_in_double

  have hproj : (Kᗮ).starProjection y = y - p := by
    have hy : y = p + (y - p) := by abel
    calc
      (Kᗮ).starProjection y
          = (Kᗮ).starProjection (p + (y - p)) := by
              -- avoid simp recursion depth
              exact congrArg (fun z => (Kᗮ).starProjection z) hy
      _   = (Kᗮ).starProjection p + (Kᗮ).starProjection (y - p) := by
              simpa using ( (Kᗮ).starProjection.map_add p (y - p) )
      _   = 0 + (y - p) := by simpa [hkill, hfix]
      _   = y - p := by simp

  -- final simplification
  calc
    ((K.starProjection + (Kᗮ).starProjection : H →L[ℂ] H) y)
        = p + (Kᗮ).starProjection y := by simpa [p]
    _   = p + (y - p) := by simpa [hproj]
    _   = y := by abel

/-- For a rank-one projection `P` onto `ℂ∙x`, `μ P ≤ 1`. -/
theorem mu_rankOne_le_one (μ : FrameFunction H) (x : H) (hx : x ≠ 0) :
    μ.μ (rankOneProjection (H := H) x hx) ≤ 1 := by
  classical
  let K : Submodule ℂ H := (ℂ ∙ x)
  let P : Projection H := rankOneProjection (H := H) x hx
  let Q : Projection H := rankOneComplementProjection (H := H) x hx

  -- Orthogonality: P ⟂ Q
  have horth : Projection.orthogonal (H := H) P Q := by
    -- show `P.1 * Q.1 = 0`
    ext y
    -- `Q.1 y` lies in `Kᗮ`, so projecting it onto `K` gives `0`
    have hQmem : (Q.1 y) ∈ Kᗮ := by
      dsimp [Q, rankOneComplementProjection, K]
      simpa using (Submodule.starProjection_apply_mem (U := (Kᗮ)) y)
    -- unfold `P.1` to `K.starProjection` and use the lemma
    dsimp [P, RankOne.rankOneProjection, K]
    -- `(P.1 * Q.1) y = P.1 (Q.1 y)`
    simpa [ContinuousLinearMap.mul_apply] using
      starProjection_eq_zero_of_mem_orthogonal (K := K) (v := (Q.1 y)) hQmem

  -- `P + Q = 1` as operators
  have haddop : (Projection.add (H := H) P Q horth).1 = (Projection.one (H := H)).1 := by
    -- `Projection.add` uses operator sum
    have hsum :
        ((K.starProjection + (Kᗮ).starProjection : H →L[ℂ] H) = 1) := by
      simpa [K] using starProjection_add_starProjection_orthogonal_eq_id (H := H) x hx
    -- unfold the operators behind `P` and `Q`
    dsimp [Projection.add, P, Q, RankOne.rankOneProjection, rankOneComplementProjection, K] at hsum
    simpa using hsum

  have hadd :
      μ.μ (Projection.add (H := H) P Q horth) = μ.μ P + μ.μ Q :=
    μ.additive P Q horth

  have hone : μ.μ (Projection.add (H := H) P Q horth) = 1 := by
    have : Projection.add (H := H) P Q horth = Projection.one (H := H) := by
      apply Subtype.ext
      exact haddop
    simpa [this] using μ.normalized

  have hQnonneg : 0 ≤ μ.μ Q := μ.nonneg Q
  have hsum1 : μ.μ P + μ.μ Q = 1 := by simpa [hone] using hadd.symm
  have : μ.μ P ≤ 1 := by linarith
  simpa [P] using this

end FrameQuadratic

/-- `frame_quadratic μ` is bounded with constant `C = 1`. -/
theorem frame_quadratic_bounded (μ : FrameFunction H) :
    ∃ C : ℝ, ∀ x : H, |frame_quadratic (H := H) μ x| ≤ C * ‖x‖ ^ 2 := by
  classical
  refine ⟨1, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst hx
    simp [frame_quadratic]
  ·
    have hx' : x ≠ 0 := hx
    have hμle : μ.μ (rankOneProjection (H := H) x hx') ≤ 1 :=
      FrameQuadratic.mu_rankOne_le_one (H := H) μ x hx'
    have hnonneg : 0 ≤ frame_quadratic (H := H) μ x :=
      frame_quadratic_nonneg (H := H) μ x
    have hdef : frame_quadratic (H := H) μ x = μ.μ (rankOneProjection (H := H) x hx') * ‖x‖ ^ 2 := by
      simp [frame_quadratic, hx]
    have hn : 0 ≤ ‖x‖ ^ 2 := by
      have : 0 ≤ ‖x‖ := norm_nonneg x
      nlinarith
    have habs : |frame_quadratic (H := H) μ x| = frame_quadratic (H := H) μ x :=
      abs_of_nonneg hnonneg
    have hmul : μ.μ (rankOneProjection (H := H) x hx') * ‖x‖ ^ 2 ≤ 1 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hμle hn
    have hμnonneg : 0 ≤ μ.μ (rankOneProjection (H := H) x hx') := μ.nonneg _
    have hμabs : |μ.μ (rankOneProjection (H := H) x hx')| = μ.μ (rankOneProjection (H := H) x hx') := by
      exact abs_of_nonneg hμnonneg
    simpa [habs, hdef, one_mul, hμabs] using hmul

/-- `frame_quadratic μ` is a bounded quadratic form. -/
theorem frame_quadratic_is_bounded_quadratic (μ : FrameFunction H)
    (h_para :
      ∀ x y : H,
        frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
          = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y) :
    IsBoundedQuadraticForm (H := H) (frame_quadratic (H := H) μ) := by
  refine
    { sq_hom := by
        intro c x
        simpa using frame_quadratic_sq_hom (H := H) μ c x
      parallelogram := by
        intro x y
        simpa using h_para x y
      bounded := by
        simpa using frame_quadratic_bounded (H := H) μ }
