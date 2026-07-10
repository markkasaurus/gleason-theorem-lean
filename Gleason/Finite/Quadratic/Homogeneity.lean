import Mathlib
import Gleason.Finite.RankOneProjection
import Gleason.Finite.FrameFunction

noncomputable section

open RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

namespace RankOne

/-- Scaling by a nonzero scalar does not change the rank-one projection. -/
theorem rankOneProjection_smul (x : H) (hx : x ≠ 0) (c : ℂ) (hc : c ≠ 0) :
    rankOneProjection (H := H) (c • x) (smul_ne_zero hc hx) =
      rankOneProjection (H := H) x hx := by
  classical
  apply Subtype.ext
  ext u
  have hcUnit : IsUnit c := (isUnit_iff_ne_zero).2 hc
  have hspan : (ℂ ∙ (c • x)) = (ℂ ∙ x) := by
    simpa using (Submodule.span_singleton_smul_eq (R := ℂ) (r := c) hcUnit x)
  simp [rankOneProjection, hspan]

end RankOne

theorem frame_quadratic_sq_hom (μ : FrameFunction H) (c : ℂ) (x : H) :
    frame_quadratic (H := H) μ (c • x) =
      ‖c‖ ^ 2 * frame_quadratic (H := H) μ x := by
  classical
  by_cases hx0 : x = 0
  · subst hx0
    simp [frame_quadratic]
  ·
    have hx : x ≠ 0 := hx0
    by_cases hc0 : c = 0
    · subst hc0
      simp [frame_quadratic, hx]
    ·
      have hc : c ≠ 0 := hc0
      have hcx : c • x ≠ 0 := smul_ne_zero hc hx

      have hr0 :
          rankOneProjection (H := H) (c • x) (smul_ne_zero hc hx) =
            rankOneProjection (H := H) x hx :=
        RankOne.rankOneProjection_smul (H := H) x hx c hc
      have hEq : hcx = smul_ne_zero hc hx := Subsingleton.elim _ _
      have hr :
          rankOneProjection (H := H) (c • x) hcx =
            rankOneProjection (H := H) x hx := by
        simpa [hEq] using hr0

      have hnorm : ‖c • x‖ ^ 2 = ‖c‖ ^ 2 * ‖x‖ ^ 2 := by
        simp [norm_smul, mul_pow]

      calc
        frame_quadratic (H := H) μ (c • x)
            = μ.μ (rankOneProjection (H := H) (c • x) hcx) * ‖c • x‖ ^ 2 := by
                simp [frame_quadratic, hcx]
        _   = μ.μ (rankOneProjection (H := H) x hx) * (‖c‖ ^ 2 * ‖x‖ ^ 2) := by
                simp [hr, hnorm]
        _   = ‖c‖ ^ 2 * (μ.μ (rankOneProjection (H := H) x hx) * ‖x‖ ^ 2) := by
                ring
        _   = ‖c‖ ^ 2 * frame_quadratic (H := H) μ x := by
                simp [frame_quadratic, hx]

theorem frame_quadratic_neg (μ : FrameFunction H) (x : H) :
    frame_quadratic (H := H) μ (-x) = frame_quadratic (H := H) μ x := by
  classical
  -- (-x) = (-1 : ℂ) • x
  simpa [neg_one_smul] using
    (frame_quadratic_sq_hom (H := H) μ (-1 : ℂ) x)
