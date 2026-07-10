import Gleason.Continuity.CircleFrame
import Gleason.Continuity.Defect.Basic

noncomputable section

open Real GleasonBridge

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

/-- Restriction of `frame_quadratic` to the great circle spanned by an orthonormal pair. -/
def greatCircleRestriction (μ : FrameFunction H) (u v : H) (θ : ℝ) : ℝ :=
  frame_quadratic μ ((Real.cos θ : ℂ) • u + (Real.sin θ : ℂ) • v)

lemma greatCircleRestriction_quarter_turn
    (μ : FrameFunction H) (u v : H) (θ : ℝ) :
    greatCircleRestriction μ u v (θ + π / 2) =
      frame_quadratic μ ((Real.sin θ : ℂ) • u - (Real.cos θ : ℂ) • v) := by
  unfold greatCircleRestriction
  rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  have hvec :
      ((-(Real.sin θ) : ℝ) : ℂ) • u + ((Real.cos θ : ℝ) : ℂ) • v =
        -(((Real.sin θ : ℝ) : ℂ) • u - ((Real.cos θ : ℝ) : ℂ) • v) := by
    simp [sub_eq_add_neg, add_comm]
  rw [hvec, frame_quadratic_neg]

lemma greatCircleRestriction_circleFrameFunction
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    circleFrameFunction (greatCircleRestriction μ u v) := by
  refine ⟨frame_quadratic μ u + frame_quadratic μ v, ?_⟩
  intro θ
  have hab : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hgc :=
    GleasonBridge.great_circle_constancy hdim μ u v hu hv huv (Real.cos θ) (Real.sin θ) hab
  rw [greatCircleRestriction_quarter_turn]
  simpa [greatCircleRestriction, sub_eq_add_neg] using hgc

lemma greatCircleRestriction_phase_circleFrameFunction
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (φ : ℝ) :
    circleFrameFunction (fun θ => greatCircleRestriction μ u v (θ + φ)) := by
  exact circleFrameFunction_comp_add_const
    (greatCircleRestriction_circleFrameFunction hdim μ u v hu hv huv) φ

theorem greatCircleRestriction_eq_phase_cos_mode_imp
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    {n : ℕ} {φ : ℝ}
    (hEq : ∀ θ : ℝ, greatCircleRestriction μ u v θ = Real.cos ((n : ℝ) * θ + φ)) :
    n = 0 ∨ n ≡ 2 [MOD 4] := by
  have hframe : circleFrameFunction (fun θ => Real.cos ((n : ℝ) * θ + φ)) := by
    rcases greatCircleRestriction_circleFrameFunction hdim μ u v hu hv huv with ⟨W, hW⟩
    refine ⟨W, ?_⟩
    intro θ
    simpa [hEq θ, hEq (θ + π / 2)] using hW θ
  exact (circleCosMode_phase_frame_iff n φ).1 hframe
