import Gleason.Continuity.GreatCircleGeometry
import Gleason.Continuity.NearInfimumOscillation

noncomputable section

open Real

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

lemma equatorPoint_eq_greatCirclePoint (u v p : H) (θ : ℝ) :
    equatorPoint u v p θ =
      ((Real.cos θ : ℂ) • u + (Real.sin θ : ℂ) • v) := by
  simp [equatorPoint, realFramePoint, add_assoc]

lemma greatCircleRestriction_eq_equatorPoint
    (μ : FrameFunction H) (u v p : H) (θ : ℝ) :
    greatCircleRestriction μ u v θ = frame_quadratic μ (equatorPoint u v p θ) := by
  rw [equatorPoint_eq_greatCirclePoint]
  rfl

lemma equatorPoint_mem_coordSphereImage (u v p : H) (θ : ℝ) :
    equatorPoint u v p θ ∈ coordSphereImage u v p := by
  refine ⟨(Real.cos θ, (Real.sin θ, 0)), ?_, ?_⟩
  · show Real.cos θ ^ 2 + Real.sin θ ^ 2 + 0 ^ 2 = 1
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · simp [coordPoint, equatorPoint, realFramePoint, add_assoc]

lemma continuous_equatorPoint (u v p : H) :
    Continuous (equatorPoint u v p) := by
  unfold equatorPoint realFramePoint
  have hcosC : Continuous fun t : ℝ => ((Real.cos t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp Real.continuous_cos
  have hsinC : Continuous fun t : ℝ => ((Real.sin t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp Real.continuous_sin
  have hzeroC : Continuous fun _ : ℝ => (0 : ℂ) := continuous_const
  have hu : Continuous fun _ : ℝ => u := continuous_const
  have hv : Continuous fun _ : ℝ => v := continuous_const
  have hp : Continuous fun _ : ℝ => p := continuous_const
  simpa [add_assoc] using
    (hcosC.smul hu).add ((hsinC.smul hv).add (hzeroC.smul hp))

lemma continuous_greatCircleRestriction_of_zero_at_p
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic μ p = 0) :
    Continuous (greatCircleRestriction μ u v) := by
  have hcontOn :
      ContinuousOn (fun x : H => frame_quadratic μ x) (coordSphereImage u v p) :=
    frame_quadratic_continuousOn_coordSphereImage_of_zero_at_p
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hp0
  have hmaps : Set.MapsTo (equatorPoint u v p) Set.univ (coordSphereImage u v p) := by
    intro θ hθ
    exact equatorPoint_mem_coordSphereImage u v p θ
  have hcomp : ContinuousOn ((fun x : H => frame_quadratic μ x) ∘ equatorPoint u v p) Set.univ :=
    ContinuousOn.comp hcontOn (continuous_equatorPoint u v p).continuousOn hmaps
  have hcomp' : Continuous ((fun x : H => frame_quadratic μ x) ∘ equatorPoint u v p) := by
    rwa [continuousOn_univ] at hcomp
  have hEq :
      ((fun x : H => frame_quadratic μ x) ∘ equatorPoint u v p) = greatCircleRestriction μ u v := by
    funext θ
    symm
    exact greatCircleRestriction_eq_equatorPoint μ u v p θ
  simpa [hEq] using hcomp'
