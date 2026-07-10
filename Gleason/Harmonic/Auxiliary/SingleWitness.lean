import Gleason.Harmonic.Sectors.HarmonicBWitness
import Gleason.Harmonic.Auxiliary.Exclusion
import Gleason.Harmonic.Rotation.RotatedHarmonic

noncomputable section

open Real Complex InnerProductSpace

lemma surfaceModeAL2_homogeneous (n : ℕ) (t : ℝ) (p : WithLp 2 (ℂ × ℝ)) :
    surfaceModeAL2 n (t • p) = t ^ n * surfaceModeAL2 n p := by
  calc
    surfaceModeAL2 n (t • p)
      = ((complexProjL (t • p)) ^ n).re := by rfl
    _ = (((t : ℂ) * complexProjL p) ^ n).re := by rw [map_smul]; simp
    _ = t ^ n * surfaceModeAL2 n p := by
      simpa [surfaceModeAL2] using (complexRePow_homogeneous n (complexProjL p) t)

theorem surfaceModeAL2_not_circleFrame_of_mod_ne_two {n : ℕ}
    (hn : 0 < n) (hmod : n % 4 ≠ 2) :
    ¬ circleFrameFunction
      (fun θ =>
        surfaceModeAL2 n
          (WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), 0))) := by
  intro hframe
  have hA : circleFrameFunction (fun θ => surfaceModeA n (Real.cos θ) (Real.sin θ) 0) := by
    convert hframe using 1
  have hcos : circleFrameFunction (circleCosMode n) := by
    simpa [circleCosMode, surfaceModeA_equator] using hA
  exact not_circleCosMode_frame_of_pos_of_mod_ne_two hn hmod hcos

lemma one_quarter_sq_add_three_quarter_sq : ((1 / 2 : ℝ) ^ 2) + (Real.sqrt 3 / 2) ^ 2 = 1 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := by
    nlinarith [sq_sqrt (show (0 : ℝ) ≤ 3 by positivity)]
  nlinarith

theorem exists_explicit_harmonic_surface_mode_not_circleFrame {n : ℕ} (hn : 2 < n) :
    ∃ f : WithLp 2 (ℂ × ℝ) → ℝ,
      (∀ p : WithLp 2 (ℂ × ℝ), HarmonicAt f p) ∧
      (∀ (t : ℝ) (p : WithLp 2 (ℂ × ℝ)), f (t • p) = t ^ n * f p) ∧
      ¬ circleFrameFunction
        (fun θ =>
          f (WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), 0))) := by
  by_cases hmod : n % 4 = 2
  · refine ⟨rotatedSurfaceModeAL2 n (1 / 2) (Real.sqrt 3 / 2), ?_, ?_, ?_⟩
    · intro p
      exact rotatedSurfaceModeAL2_harmonicAt n one_quarter_sq_add_three_quarter_sq p
    · intro t p
      calc
        rotatedSurfaceModeAL2 n (1 / 2) (Real.sqrt 3 / 2) (t • p)
          = (((t : ℂ) * rotatedComplexProjL (1 / 2) (Real.sqrt 3 / 2) p) ^ n).re := by
              rw [rotatedSurfaceModeAL2]
              rw [map_smul]
              simp
        _ = t ^ n * rotatedSurfaceModeAL2 n (1 / 2) (Real.sqrt 3 / 2) p := by
              simpa [rotatedSurfaceModeAL2] using
                (complexRePow_homogeneous n
                  (rotatedComplexProjL (1 / 2) (Real.sqrt 3 / 2) p) t)
    · exact rotated_harmonic_surface_mode_not_circleFrame_of_mod_four_eq_two
        hn hmod one_quarter_sq_add_three_quarter_sq (by norm_num) (by norm_num)
  · refine ⟨surfaceModeAL2 n, ?_, ?_, ?_⟩
    · intro p
      exact surfaceModeAL2_harmonicAt n p
    · intro t p
      exact surfaceModeAL2_homogeneous n t p
    · exact surfaceModeAL2_not_circleFrame_of_mod_ne_two (by omega) hmod

def equatorRestrictionL2 (f : WithLp 2 (ℂ × ℝ) → ℝ) : ℝ → ℝ :=
  fun θ => f (WithLp.toLp 2 (((Real.cos θ : ℂ) + Complex.I * Real.sin θ), 0))

def HarmonicHomogeneousDegree (n : ℕ) (f : WithLp 2 (ℂ × ℝ) → ℝ) : Prop :=
  (∀ p : WithLp 2 (ℂ × ℝ), HarmonicAt f p) ∧
    (∀ (t : ℝ) (p : WithLp 2 (ℂ × ℝ)), f (t • p) = t ^ n * f p)

theorem not_all_harmonicHomogeneousDegree_have_circleFrame {n : ℕ} (hn : 2 < n) :
    ¬ ∀ f : WithLp 2 (ℂ × ℝ) → ℝ,
        HarmonicHomogeneousDegree n f → circleFrameFunction (equatorRestrictionL2 f) := by
  intro hall
  rcases exists_explicit_harmonic_surface_mode_not_circleFrame hn with
    ⟨f, hfHarm, hfHom, hnot⟩
  exact hnot (hall f ⟨hfHarm, hfHom⟩)
