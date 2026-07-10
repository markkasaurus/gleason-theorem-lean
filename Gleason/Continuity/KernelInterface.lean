import Gleason.Continuity.Defect.KernelSymmetry

noncomputable section

open GleasonBridge RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

def hard_kernel_transport_s0
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) : Prop :=
  ∀ r : ℝ, 0 < r → r < 1 →
    (|local_defect_g μ u v r| / (1 + r ^ 2))
      ≤
    (|local_defect_g μ u v ((1 - r) / (1 + r))| /
      (1 + ((1 - r) / (1 + r)) ^ 2))

def hard_kernel_gap_positive_anchor_s0
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) : Prop :=
  (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ 0 < local_defect_g_normalized_gap μ u v r
lemma hadamard_bridge_error_zero_all_of_hard_kernel_s0
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport :
      hard_kernel_transport_s0 hdim μ u v hu hv huv)
    (hgap0 :
      hard_kernel_gap_positive_anchor_s0 hdim μ u v hu hv huv) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_transport_s0_kernel_gap_positive
      hdim μ u v hu hv huv htransport hgap0
