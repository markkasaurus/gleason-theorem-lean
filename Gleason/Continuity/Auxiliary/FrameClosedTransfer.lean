import Gleason.Harmonic.Auxiliary.PointConstraintFrame
import Gleason.Harmonic.Auxiliary.ExceptionalDegreeVanishing

noncomputable section

open Complex InnerProductSpace

theorem eq_bot_of_isClosed_of_rotationInvariant_of_le_ne_zero_two_degree_of_le_frame
    {n : ℕ} (hn : n ≠ 0) (hn2 : n ≠ 2)
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGdeg : G ≤ continuousHarmonicSphereDegreeSubmodule n)
    (hGframe : G ≤ continuousSphereFrameSubmodule) :
    G = ⊥ := by
  apply eq_bot_of_isClosed_of_rotationInvariant_of_le_ne_zero_two_degree_of_le_pointConstraint
    hn hn2 hGclosed hGrot hGdeg
  calc
    G ≤ continuousSphereFrameSubmodule := hGframe
    _ ≤ continuousSphereGreatCirclePointConstraintSubmodule :=
      continuousSphereFrameSubmodule_le_continuousSphereGreatCirclePointConstraintSubmodule

theorem eq_bot_of_isClosed_of_rotationInvariant_of_le_gt_two_degree_of_le_frame
    {n : ℕ} (hn : 2 < n)
    {G : Submodule ℝ C(spherePoint3, ℝ)}
    (hGclosed : IsClosed (G : Set C(spherePoint3, ℝ)))
    (hGrot :
      ∀ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
        G.map (spherePrecompLinearEquiv e).toLinearMap = G)
    (hGdeg : G ≤ continuousHarmonicSphereDegreeSubmodule n)
    (hGframe : G ≤ continuousSphereFrameSubmodule) :
    G = ⊥ := by
  apply eq_bot_of_isClosed_of_rotationInvariant_of_le_ne_zero_two_degree_of_le_frame
  · exact ne_of_gt (lt_trans Nat.zero_lt_two hn)
  · exact ne_of_gt hn
  · exact hGclosed
  · exact hGrot
  · exact hGdeg
  · exact hGframe
