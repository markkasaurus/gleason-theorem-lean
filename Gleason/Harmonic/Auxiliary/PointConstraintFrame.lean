import Gleason.Harmonic.Auxiliary.PointConstraintSamePole
import Gleason.Continuity.Auxiliary.ClosedFrame

noncomputable section

open Complex InnerProductSpace

lemma exists_common_orthogonal_spherePoint
    (u v : spherePoint3) :
    ∃ w : spherePoint3,
      inner (𝕜 := ℝ) u.1 w.1 = 0 ∧
      inner (𝕜 := ℝ) v.1 w.1 = 0 := by
  let s : Finset (WithLp 2 (ℂ × ℝ)) := {u.1, v.1}
  let S : Submodule ℝ (WithLp 2 (ℂ × ℝ)) := Submodule.span ℝ (s : Set (WithLp 2 (ℂ × ℝ)))
  have hS : Module.finrank ℝ S ≤ 2 := by
    have h1 : Module.finrank ℝ S ≤ s.card := by
      simpa [Set.finrank, S] using (finrank_span_finset_le_card (R := ℝ) s)
    have h2 : s.card ≤ 2 := by
      simpa [s] using (Finset.card_insert_le (a := u.1) (s := ({v.1} : Finset (WithLp 2 (ℂ × ℝ)))))
    exact le_trans h1 h2
  have hsum :
      Module.finrank ℝ S + Module.finrank ℝ Sᗮ =
        Module.finrank ℝ (WithLp 2 (ℂ × ℝ)) := by
    simpa using (Submodule.finrank_add_finrank_orthogonal (K := S))
  have hdim : 3 ≤ Module.finrank ℝ (WithLp 2 (ℂ × ℝ)) := by
    simpa [finrank_real_withLp_complex_prod_real]
  have hpos : 0 < Module.finrank ℝ Sᗮ := by
    have h3 : 3 ≤ Module.finrank ℝ S + Module.finrank ℝ Sᗮ := by
      simpa [hsum] using hdim
    have h1 : 1 ≤ Module.finrank ℝ Sᗮ := by
      omega
    exact Nat.succ_le_iff.mp h1
  rcases (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := Sᗮ)).1 hpos with ⟨w0, hw0⟩
  have hwS : ∀ z ∈ S, inner (𝕜 := ℝ) z (w0 : WithLp 2 (ℂ × ℝ)) = 0 :=
    (Submodule.mem_orthogonal (K := S) (v := (w0 : WithLp 2 (ℂ × ℝ)))).1 w0.property
  have huS : u.1 ∈ S := Submodule.subset_span (by simp [s])
  have hvS : v.1 ∈ S := Submodule.subset_span (by simp [s])
  let w : WithLp 2 (ℂ × ℝ) := (‖(w0 : WithLp 2 (ℂ × ℝ))‖)⁻¹ • (w0 : WithLp 2 (ℂ × ℝ))
  have hw_norm : ‖w‖ = 1 := by
    have hw0_norm_ne : ‖(w0 : WithLp 2 (ℂ × ℝ))‖ ≠ 0 := by
      simpa [norm_eq_zero] using hw0
    calc
      ‖w‖ = ‖(‖(w0 : WithLp 2 (ℂ × ℝ))‖)⁻¹‖ * ‖(w0 : WithLp 2 (ℂ × ℝ))‖ := by
              simp [w, norm_smul]
      _ = (‖(w0 : WithLp 2 (ℂ × ℝ))‖)⁻¹ * ‖(w0 : WithLp 2 (ℂ × ℝ))‖ := by simp
      _ = 1 := by simpa using (inv_mul_cancel₀ hw0_norm_ne)
  refine ⟨⟨w, hw_norm⟩, ?_, ?_⟩
  · have hu0 : inner (𝕜 := ℝ) u.1 (w0 : WithLp 2 (ℂ × ℝ)) = 0 := hwS u.1 huS
    simpa [w, inner_smul_right, hu0]
  · have hv0 : inner (𝕜 := ℝ) v.1 (w0 : WithLp 2 (ℂ × ℝ)) = 0 := hwS v.1 hvS
    simpa [w, inner_smul_right, hv0]

theorem continuousSphereGreatCirclePointConstraintSubmodule_le_continuousSphereFrameSubmodule :
    continuousSphereGreatCirclePointConstraintSubmodule ≤ continuousSphereFrameSubmodule := by
  intro f hf
  rw [mem_continuousSphereFrameSubmodule_iff]
  intro x y z hxy hxz hyz
  rcases exists_common_orthogonal_spherePoint z sphereE3 with ⟨w, hwz, hw3⟩
  rcases exists_common_orthogonal_spherePoint z w with ⟨u, hzu, hwu⟩
  rcases exists_common_orthogonal_spherePoint sphereE3 w with ⟨u0, h3u0, hwu0⟩
  have hwz' : inner (𝕜 := ℝ) w.1 z.1 = 0 := (inner_eq_zero_symm).2 hwz
  have huz : inner (𝕜 := ℝ) u.1 z.1 = 0 := (inner_eq_zero_symm).2 hzu
  have huw : inner (𝕜 := ℝ) u.1 w.1 = 0 := (inner_eq_zero_symm).2 hwu
  have hu03 : inner (𝕜 := ℝ) u0.1 sphereE3.1 = 0 := (inner_eq_zero_symm).2 h3u0
  have hu0w : inner (𝕜 := ℝ) u0.1 w.1 = 0 := (inner_eq_zero_symm).2 hwu0
  have hw3' : inner (𝕜 := ℝ) w.1 sphereE3.1 = 0 := (inner_eq_zero_symm).2 hw3
  have hxy_zw :
      f x + f y = f w + f u := by
    exact
      pairSum_eq_of_same_pole_of_mem_continuousSphereGreatCirclePointConstraintSubmodule
        hf x y w u z hxy hxz hyz hwu hwz' huz
  have hzu0_w :
      f u + f z = f u0 + f sphereE3 := by
    exact
      pairSum_eq_of_same_pole_of_mem_continuousSphereGreatCirclePointConstraintSubmodule
        hf u z u0 sphereE3 w huz huw hwz hu03 hu0w hw3
  have hu0w_std :
      f u0 + f w = f sphereE1 + f sphereE2 := by
    exact
      pairSum_eq_of_same_pole_of_mem_continuousSphereGreatCirclePointConstraintSubmodule
        hf u0 w sphereE1 sphereE2 sphereE3 hu0w hu03 hw3'
          sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  have hsum0 : f x + f y + f z = f w + f u + f z := by linarith
  have hsum1 : f w + f u + f z = f w + f u0 + f sphereE3 := by linarith
  have hsum2 : f w + f u0 + f sphereE3 = f sphereE1 + f sphereE2 + f sphereE3 := by
    linarith
  have hsum : f x + f y + f z = f sphereE1 + f sphereE2 + f sphereE3 := by
    linarith
  simpa [sphereFrameConstraintCLM_apply] using sub_eq_zero.mpr hsum

theorem continuousSphereGreatCirclePointConstraintSubmodule_eq_continuousSphereFrameSubmodule :
    continuousSphereGreatCirclePointConstraintSubmodule = continuousSphereFrameSubmodule := by
  apply le_antisymm
  · exact continuousSphereGreatCirclePointConstraintSubmodule_le_continuousSphereFrameSubmodule
  · exact continuousSphereFrameSubmodule_le_continuousSphereGreatCirclePointConstraintSubmodule
