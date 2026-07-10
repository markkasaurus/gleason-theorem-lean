import Gleason.Continuity.Defect.NormalizedGap

noncomputable section

open GleasonBridge RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

lemma hadamard_bridge_error_second_diff_transport_of_local_defect_g_transport_shift_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hshift0 :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
          |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2)
          +
        (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) -
            hadamard_bridge_error μ u v ((1 - r) / (1 + r))| +
          |hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
            hadamard_bridge_error μ u v (-((1 - r) / (1 + r)))| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) /
          (1 + ((1 - r) / (1 + r)) ^ 2)
          = 0) :
    ∀ s r : ℝ, 0 < r → r < 1 →
      (|hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2))
        ≤
      (|hadamard_bridge_error_second_diff μ u v s ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro s r hr0 hr1
  have htr :=
    hadamard_bridge_error_second_diff_transport_with_shift_error
      hdim μ u v hu hv huv htransport_g s r hr0 hr1
  have h0 := hshift0 s r hr0 hr1
  linarith [htr, h0]

lemma hadamard_bridge_error_second_diff_noninvariance_witness_of_local_defect_g_margin
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hmargin :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
            |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
            2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2)
            +
          (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) -
              hadamard_bridge_error μ u v ((1 - r) / (1 + r))| +
            |hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
              hadamard_bridge_error μ u v (-((1 - r) / (1 + r)))| +
            2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) /
            (1 + ((1 - r) / (1 + r)) ^ 2)
            <
          |(|local_defect_g μ u v r| / (1 + r ^ 2)) -
            (|local_defect_g μ u v ((1 - r) / (1 + r))| /
              (1 + ((1 - r) / (1 + r)) ^ 2))|) :
    ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2))
          ≠
        (|hadamard_bridge_error_second_diff μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro s hker
  rcases hmargin s hker with ⟨r, hr0, hr1, hmr⟩
  refine ⟨r, hr0, hr1, ?_⟩
  exact
    hadamard_bridge_error_second_diff_noninvariance_of_local_defect_g_margin
      hdim μ u v hu hv huv s r hmr

lemma hadamard_bridge_error_zero_all_of_local_defect_g_transport_shift_zero_margin
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hshift0 :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
          |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2)
          +
        (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) -
            hadamard_bridge_error μ u v ((1 - r) / (1 + r))| +
          |hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
            hadamard_bridge_error μ u v (-((1 - r) / (1 + r)))| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) /
          (1 + ((1 - r) / (1 + r)) ^ 2)
          = 0)
    (hmargin :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
            |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
            2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2)
            +
          (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) -
              hadamard_bridge_error μ u v ((1 - r) / (1 + r))| +
            |hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
              hadamard_bridge_error μ u v (-((1 - r) / (1 + r)))| +
            2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) /
            (1 + ((1 - r) / (1 + r)) ^ 2)
            <
          |(|local_defect_g μ u v r| / (1 + r ^ 2)) -
            (|local_defect_g μ u v ((1 - r) / (1 + r))| /
              (1 + ((1 - r) / (1 + r)) ^ 2))|) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have htransportE :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|hadamard_bridge_error μ u v (s + r) +
            hadamard_bridge_error μ u v (s - r) -
            2 * hadamard_bridge_error μ u v s| / (1 + r ^ 2))
          ≤
        (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) +
            hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
            2 * hadamard_bridge_error μ u v s| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    intro s r hr0 hr1
    simpa [hadamard_bridge_error_second_diff] using
      (hadamard_bridge_error_second_diff_transport_of_local_defect_g_transport_shift_zero
        hdim μ u v hu hv huv htransport_g hshift0 s r hr0 hr1)
  have hneqE :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|hadamard_bridge_error μ u v (s + r) +
              hadamard_bridge_error μ u v (s - r) -
              2 * hadamard_bridge_error μ u v s| / (1 + r ^ 2))
            ≠
          (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) +
              hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
              2 * hadamard_bridge_error μ u v s| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    intro s hker
    rcases
      (hadamard_bridge_error_second_diff_noninvariance_witness_of_local_defect_g_margin
        hdim μ u v hu hv huv hmargin s hker) with
      ⟨r, hr0, hr1, hne⟩
    refine ⟨r, hr0, hr1, ?_⟩
    simpa [hadamard_bridge_error_second_diff] using hne
  exact
    hadamard_bridge_error_zero_all_of_second_diff_transport_neq
      hdim μ u v hu hv huv htransportE hneqE

lemma swapped_bridge_kernel_s0_eq_neg_two_local_defect_g
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    swapped_bridge_kernel μ v u 0 t = -2 * local_defect_g μ u v t := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hker :
      swapped_bridge_kernel μ v u 0 t =
        2 * hadamard_bridge_error_second_diff μ u v 0 t := by
    unfold hadamard_bridge_error_second_diff
    simpa [add_assoc, add_left_comm, add_comm] using
      swapped_bridge_kernel_eq_two_hadamard_bridge_error_second_diff
        hdim μ v u hv hu hvu 0 t
  have hs0 :
      hadamard_bridge_error_second_diff μ u v 0 t = -local_defect_g μ u v t :=
    hadamard_bridge_error_second_diff_s0_eq_neg_local_defect_g hdim μ u v hu hv huv t
  linarith [hker, hs0]

lemma swapped_bridge_kernel_s0_ne_zero_iff_local_defect_g_ne_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    swapped_bridge_kernel μ v u 0 t ≠ 0 ↔ local_defect_g μ u v t ≠ 0 := by
  constructor
  · intro hK hG
    apply hK
    rw [swapped_bridge_kernel_s0_eq_neg_two_local_defect_g hdim μ u v hu hv huv t, hG]
    ring
  · intro hG hK0
    rw [swapped_bridge_kernel_s0_eq_neg_two_local_defect_g hdim μ u v hu hv huv t] at hK0
    have h2 : (-2 : ℝ) ≠ 0 := by norm_num
    have hG0 : local_defect_g μ u v t = 0 := (mul_eq_zero.mp hK0).resolve_left h2
    exact hG hG0

lemma exists_swapped_bridge_kernel_s0_ne_zero_iff_exists_local_defect_g_ne_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) ↔
      ∃ t : ℝ, local_defect_g μ u v t ≠ 0 := by
  constructor
  · intro h
    rcases h with ⟨t, ht⟩
    exact ⟨t, (swapped_bridge_kernel_s0_ne_zero_iff_local_defect_g_ne_zero
      hdim μ u v hu hv huv t).1 ht⟩
  · intro h
    rcases h with ⟨t, ht⟩
    exact ⟨t, (swapped_bridge_kernel_s0_ne_zero_iff_local_defect_g_ne_zero
      hdim μ u v hu hv huv t).2 ht⟩

lemma exists_local_defect_g_ne_zero_in_unit_interval
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ local_defect_g μ u v r ≠ 0 := by
  intro hg_nz
  rcases hg_nz with ⟨t, ht_nz⟩
  have ht0 : t ≠ 0 := by
    intro ht0
    apply ht_nz
    simpa [ht0] using (GleasonBridge.local_defect_g_zero_eq_zero μ u v)
  have habs_nz : local_defect_g μ u v |t| ≠ 0 := by
    by_cases htnn : 0 ≤ t
    · simpa [abs_of_nonneg htnn] using ht_nz
    · have htlt : t < 0 := lt_of_not_ge htnn
      have habs : |t| = -t := abs_of_neg htlt
      rw [habs]
      intro hneg0
      have heven : local_defect_g μ u v (-t) = local_defect_g μ u v t := by
        simpa using (GleasonBridge.local_defect_g_even μ u v t)
      apply ht_nz
      have ht0' : local_defect_g μ u v t = 0 := by
        linarith [heven, hneg0]
      exact ht0'
  by_cases hlt1 : |t| < 1
  · refine ⟨|t|, abs_pos.mpr ht0, hlt1, habs_nz⟩
  · have hge1 : 1 ≤ |t| := le_of_not_gt hlt1
    have hne1 : |t| ≠ 1 := by
      intro h1
      have hzero_at_one : local_defect_g μ u v (1 : ℝ) = 0 :=
        GleasonBridge.local_defect_g_one_eq_zero hdim μ u v hu hv huv
      have hzero_abs : local_defect_g μ u v |t| = 0 := by simpa [h1] using hzero_at_one
      exact habs_nz hzero_abs
    have hgt1 : 1 < |t| := lt_of_le_of_ne hge1 (Ne.symm hne1)
    set r : ℝ := 1 / |t|
    have habs_pos : 0 < |t| := by linarith [hge1]
    have hr0 : 0 < r := by
      dsimp [r]
      exact one_div_pos.mpr habs_pos
    have hr1 : r < 1 := by
      dsimp [r]
      exact (div_lt_iff₀ habs_pos).2 (by simpa using hgt1)
    have habs_ne0 : (|t| : ℝ) ≠ 0 := by exact abs_ne_zero.mpr ht0
    have hrec :
        local_defect_g μ u v |t| =
          -(|t| ^ 2) * local_defect_g μ u v r := by
      simpa [r] using
        (GleasonBridge.local_defect_g_inversion hdim μ u v hu hv huv habs_ne0)
    have hr_nz : local_defect_g μ u v r ≠ 0 := by
      intro hr0g
      have hzero_abs : local_defect_g μ u v |t| = 0 := by
        rw [hrec, hr0g]
        ring
      exact habs_nz hzero_abs
    exact ⟨r, hr0, hr1, hr_nz⟩

lemma exists_local_defect_g_normalized_abs_ne_zero_in_unit_interval
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2)) ≠ 0 := by
  intro hg_nz
  rcases exists_local_defect_g_ne_zero_in_unit_interval hdim μ u v hu hv huv hg_nz with
    ⟨r, hr0, hr1, hr_nz⟩
  refine ⟨r, hr0, hr1, ?_⟩
  exact div_ne_zero (abs_ne_zero.mpr hr_nz) (by positivity)

lemma hadamard_bridge_error_second_diff_transport_s0_iff_local_defect_g_transport
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∀ r : ℝ, 0 < r → r < 1 →
      (|hadamard_bridge_error_second_diff μ u v 0 r| / (1 + r ^ 2))
        ≤
      (|hadamard_bridge_error_second_diff μ u v 0 ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)))
      ↔
    (∀ r : ℝ, 0 < r → r < 1 →
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        ≤
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2))) := by
  constructor
  · intro h r hr0 hr1
    have hr := h r hr0 hr1
    simpa [hadamard_bridge_error_second_diff_s0_eq_neg_local_defect_g hdim μ u v hu hv huv,
      abs_neg] using hr
  · intro h r hr0 hr1
    have hr := h r hr0 hr1
    simpa [hadamard_bridge_error_second_diff_s0_eq_neg_local_defect_g hdim μ u v hu hv huv,
      abs_neg] using hr

lemma hadamard_bridge_error_second_diff_noninvariance_s0_iff_local_defect_g_noninvariance
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (|hadamard_bridge_error_second_diff μ u v 0 r| / (1 + r ^ 2))
        ≠
      (|hadamard_bridge_error_second_diff μ u v 0 ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)))
      ↔
    (∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        ≠
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2))) := by
  constructor
  · intro h
    rcases h with ⟨r, hr0, hr1, hne⟩
    refine ⟨r, hr0, hr1, ?_⟩
    simpa [hadamard_bridge_error_second_diff_s0_eq_neg_local_defect_g hdim μ u v hu hv huv,
      abs_neg] using hne
  · intro h
    rcases h with ⟨r, hr0, hr1, hne⟩
    refine ⟨r, hr0, hr1, ?_⟩
    simpa [hadamard_bridge_error_second_diff_s0_eq_neg_local_defect_g hdim μ u v hu hv huv,
      abs_neg] using hne

lemma hadamard_bridge_error_second_diff_witness_s0_of_local_defect_g_witness
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hneq_g :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    (∀ r : ℝ, 0 < r → r < 1 →
      (|hadamard_bridge_error_second_diff μ u v 0 r| / (1 + r ^ 2))
        ≤
      (|hadamard_bridge_error_second_diff μ u v 0 ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)))
    ∧
    ((∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|hadamard_bridge_error_second_diff μ u v 0 r| / (1 + r ^ 2))
          ≠
        (|hadamard_bridge_error_second_diff μ u v 0 ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) := by
  constructor
  · exact
      (hadamard_bridge_error_second_diff_transport_s0_iff_local_defect_g_transport
        hdim μ u v hu hv huv).2 htransport_g
  · intro hker_nz
    have hg_nz : ∃ t : ℝ, local_defect_g μ u v t ≠ 0 := by
      exact
        (exists_swapped_bridge_kernel_s0_ne_zero_iff_exists_local_defect_g_ne_zero
          hdim μ u v hu hv huv).1 hker_nz
    have hne_g :
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := hneq_g hg_nz
    exact
      (hadamard_bridge_error_second_diff_noninvariance_s0_iff_local_defect_g_noninvariance
        hdim μ u v hu hv huv).2 hne_g

lemma hadamard_bridge_error_shift_oscillation_pair_s0
    (μ : FrameFunction H) (u v : H) (r : ℝ) :
    hadamard_bridge_error_shift_oscillation_pair μ u v 0 r = 0 := by
  simp [hadamard_bridge_error_shift_oscillation_pair]

lemma local_defect_g_neq_witness_of_s0_shift_oscillation_margin
    (μ : FrameFunction H) (u v : H)
    (hmargin0 :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          hadamard_bridge_error_shift_oscillation_pair μ u v 0 r <
            local_defect_g_normalized_gap μ u v r) :
    (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro hg_nz
  rcases hmargin0 hg_nz with ⟨r, hr0, hr1, hlt⟩
  have hshift0 :
      hadamard_bridge_error_shift_oscillation_pair μ u v 0 r = 0 :=
    hadamard_bridge_error_shift_oscillation_pair_s0 μ u v r
  have hgap_pos : 0 < local_defect_g_normalized_gap μ u v r := by
    linarith [hshift0, hlt]
  refine ⟨r, hr0, hr1, ?_⟩
  exact (local_defect_g_normalized_gap_pos_iff μ u v r).1 hgap_pos

lemma local_defect_g_s0_shift_oscillation_margin_of_neq_witness
    (μ : FrameFunction H) (u v : H)
    (hneq_g :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        hadamard_bridge_error_shift_oscillation_pair μ u v 0 r <
          local_defect_g_normalized_gap μ u v r := by
  intro hg_nz
  rcases hneq_g hg_nz with ⟨r, hr0, hr1, hne⟩
  have hgap_pos : 0 < local_defect_g_normalized_gap μ u v r :=
    (local_defect_g_normalized_gap_pos_iff μ u v r).2 hne
  have hshift0 :
      hadamard_bridge_error_shift_oscillation_pair μ u v 0 r = 0 :=
    hadamard_bridge_error_shift_oscillation_pair_s0 μ u v r
  refine ⟨r, hr0, hr1, ?_⟩
  linarith [hshift0, hgap_pos]

lemma local_defect_g_neq_witness_iff_s0_shift_oscillation_margin
    (μ : FrameFunction H) (u v : H) :
    ((∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
      ↔
    ((∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        hadamard_bridge_error_shift_oscillation_pair μ u v 0 r <
          local_defect_g_normalized_gap μ u v r) := by
  constructor
  · exact local_defect_g_s0_shift_oscillation_margin_of_neq_witness μ u v
  · exact local_defect_g_neq_witness_of_s0_shift_oscillation_margin μ u v

lemma local_defect_g_zero_all_of_transport_neq_witness_pre
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hneq_g :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ t : ℝ, local_defect_g μ u v t = 0 := by
  intro t
  by_contra ht
  have hg_nz : ∃ z : ℝ, local_defect_g μ u v z ≠ 0 := ⟨t, ht⟩
  rcases hneq_g hg_nz with ⟨r, hr0, hr1, hne⟩
  have heq :
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    exact
      hadamard_mobius_transport_eq_on_unit_interval
        (G := fun x => |local_defect_g μ u v x| / (1 + x ^ 2))
        htransport_g r hr0 hr1
  exact hne heq

lemma hadamard_bridge_error_zero_all_of_local_defect_g_zero_all_pre
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hg0 : ∀ t : ℝ, local_defect_g μ u v t = 0) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  intro x
  by_cases h1px : 1 + x ≠ 0
  · have hres :
        hadamard_residual_one μ u v x = 0 := by
      have hmob :=
        hadamard_residual_one_eq_mobius_scaled_local_defect
          hdim μ u v hu hv huv x h1px
      rw [hg0 ((1 - x) / (1 + x)), mul_zero] at hmob
      exact hmob
    unfold hadamard_bridge_error
    rw [hres, hg0 x]
    ring
  · have hx0 : 1 + x = 0 := by
      by_contra hx0
      exact h1px hx0
    have hx : x = -1 := by linarith [hx0]
    simpa [hx] using hadamard_bridge_error_neg_one hdim μ u v hu hv huv

lemma hadamard_bridge_error_zero_all_of_local_defect_g_transport_neq_witness_pre
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hneq_g :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have hg0 :
      ∀ t : ℝ, local_defect_g μ u v t = 0 :=
    local_defect_g_zero_all_of_transport_neq_witness_pre
      hdim μ u v hu hv huv htransport_g hneq_g
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_zero_all_pre
      hdim μ u v hu hv huv hg0

lemma hadamard_bridge_error_zero_all_of_local_defect_g_transport_s0_shift_oscillation_margin
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hmargin0 :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          hadamard_bridge_error_shift_oscillation_pair μ u v 0 r <
            local_defect_g_normalized_gap μ u v r) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have hneq_g :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) :=
    local_defect_g_neq_witness_of_s0_shift_oscillation_margin μ u v hmargin0
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_transport_neq_witness_pre
      hdim μ u v hu hv huv htransport_g hneq_g

lemma local_defect_g_neq_witness_of_s0_kernel_shift_oscillation_margin
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hmargin0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          hadamard_bridge_error_shift_oscillation_pair μ u v 0 r <
            local_defect_g_normalized_gap μ u v r) :
    (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  apply local_defect_g_neq_witness_of_s0_shift_oscillation_margin μ u v
  intro hg_nz
  have hker_nz :
      ∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0 :=
    (exists_swapped_bridge_kernel_s0_ne_zero_iff_exists_local_defect_g_ne_zero
      hdim μ u v hu hv huv).2 hg_nz
  exact hmargin0 hker_nz

lemma hadamard_bridge_error_zero_all_of_local_defect_g_transport_s0_kernel_shift_oscillation_margin
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hmargin0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          hadamard_bridge_error_shift_oscillation_pair μ u v 0 r <
            local_defect_g_normalized_gap μ u v r) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have hneq_g :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) :=
    local_defect_g_neq_witness_of_s0_kernel_shift_oscillation_margin
      hdim μ u v hu hv huv hmargin0
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_transport_neq_witness_pre
      hdim μ u v hu hv huv htransport_g hneq_g

lemma local_defect_g_s0_kernel_shift_oscillation_margin_of_gap_positive
    (μ : FrameFunction H) (u v : H)
    (hgap0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          0 < local_defect_g_normalized_gap μ u v r) :
    (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        hadamard_bridge_error_shift_oscillation_pair μ u v 0 r <
          local_defect_g_normalized_gap μ u v r := by
  intro hker_nz
  rcases hgap0 hker_nz with ⟨r, hr0, hr1, hgap_pos⟩
  have hshift0 :
      hadamard_bridge_error_shift_oscillation_pair μ u v 0 r = 0 :=
    hadamard_bridge_error_shift_oscillation_pair_s0 μ u v r
  refine ⟨r, hr0, hr1, ?_⟩
  linarith [hshift0, hgap_pos]

lemma local_defect_g_s0_kernel_shift_oscillation_margin_of_amplified_gap
    (μ : FrameFunction H) (u v : H)
    (κ : ℝ) (hκ : κ < 1)
    (hamp0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          0 < local_defect_g_normalized_gap μ u v r ∧
          hadamard_bridge_error_shift_oscillation_pair μ u v 0 r ≤
            κ * local_defect_g_normalized_gap μ u v r) :
    (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        hadamard_bridge_error_shift_oscillation_pair μ u v 0 r <
          local_defect_g_normalized_gap μ u v r := by
  intro hker_nz
  rcases hamp0 hker_nz with ⟨r, hr0, hr1, hgap_pos, hamp⟩
  refine ⟨r, hr0, hr1, ?_⟩
  nlinarith [hamp, hκ, hgap_pos]

lemma local_defect_g_neq_witness_of_s0_kernel_shift_oscillation_amplified
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (κ : ℝ) (hκ : κ < 1)
    (hamp0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          0 < local_defect_g_normalized_gap μ u v r ∧
          hadamard_bridge_error_shift_oscillation_pair μ u v 0 r ≤
            κ * local_defect_g_normalized_gap μ u v r) :
    (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  have hmargin0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          hadamard_bridge_error_shift_oscillation_pair μ u v 0 r <
            local_defect_g_normalized_gap μ u v r :=
    local_defect_g_s0_kernel_shift_oscillation_margin_of_amplified_gap
      μ u v κ hκ hamp0
  exact
    local_defect_g_neq_witness_of_s0_kernel_shift_oscillation_margin
      hdim μ u v hu hv huv hmargin0

lemma local_defect_g_neq_witness_iff_s0_kernel_gap_positive
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ((∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
      ↔
    ((∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        0 < local_defect_g_normalized_gap μ u v r) := by
  constructor
  · intro hneq_g hker_nz
    have hg_nz :
        ∃ t : ℝ, local_defect_g μ u v t ≠ 0 :=
      (exists_swapped_bridge_kernel_s0_ne_zero_iff_exists_local_defect_g_ne_zero
        hdim μ u v hu hv huv).1 hker_nz
    rcases hneq_g hg_nz with ⟨r, hr0, hr1, hne⟩
    refine ⟨r, hr0, hr1, ?_⟩
    exact (local_defect_g_normalized_gap_pos_iff μ u v r).2 hne
  · intro hgap0 hg_nz
    have hker_nz :
        ∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0 :=
      (exists_swapped_bridge_kernel_s0_ne_zero_iff_exists_local_defect_g_ne_zero
        hdim μ u v hu hv huv).2 hg_nz
    rcases hgap0 hker_nz with ⟨r, hr0, hr1, hgap_pos⟩
    refine ⟨r, hr0, hr1, ?_⟩
    exact (local_defect_g_normalized_gap_pos_iff μ u v r).1 hgap_pos

lemma hadamard_bridge_error_zero_all_of_local_defect_g_transport_s0_kernel_gap_positive
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hgap0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          0 < local_defect_g_normalized_gap μ u v r) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have hmargin0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          hadamard_bridge_error_shift_oscillation_pair μ u v 0 r <
            local_defect_g_normalized_gap μ u v r :=
    local_defect_g_s0_kernel_shift_oscillation_margin_of_gap_positive μ u v hgap0
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_transport_s0_kernel_shift_oscillation_margin
      hdim μ u v hu hv huv htransport_g hmargin0

lemma hadamard_bridge_error_zero_all_of_local_defect_g_shift_bound_transport_s0_kernel_gap_positive
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_gap :
      let C : ℝ := Classical.choose
        (hadamard_bridge_error_shift_error_double_bundle_uniform_bound
          hdim μ u v hu hv huv)
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hgap0 :
      let C : ℝ := Classical.choose
        (hadamard_bridge_error_shift_error_double_bundle_uniform_bound
          hdim μ u v hu hv huv)
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          C < local_defect_g_normalized_gap μ u v r) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  let C : ℝ := Classical.choose
    (hadamard_bridge_error_shift_error_double_bundle_uniform_bound
      hdim μ u v hu hv huv)
  have hCspec :
      0 ≤ C ∧ ∀ s r : ℝ,
        (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
          |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2)
          +
        (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) -
            hadamard_bridge_error μ u v ((1 - r) / (1 + r))| +
          |hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
            hadamard_bridge_error μ u v (-((1 - r) / (1 + r)))| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) /
          (1 + ((1 - r) / (1 + r)) ^ 2)
          ≤ C * (1 + s ^ 2) := by
    simpa [C] using
      (Classical.choose_spec
        (hadamard_bridge_error_shift_error_double_bundle_uniform_bound
          hdim μ u v hu hv huv))
  have htransport_gap' :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    simpa [C] using htransport_gap
  have hCzero : C = 0 :=
    local_defect_g_shift_bound_transport_forces_C_zero
      μ u v C hCspec.1 htransport_gap'
  have htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) :=
    local_defect_g_transport_of_shift_bound_transport
      μ u v C hCzero htransport_gap'
  have hgap0' :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          0 < local_defect_g_normalized_gap μ u v r := by
    intro hker_nz
    have hgap0C :
        (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
          ∃ r : ℝ, 0 < r ∧ r < 1 ∧
            C < local_defect_g_normalized_gap μ u v r := by
      simpa [C] using hgap0
    rcases hgap0C hker_nz with ⟨r, hr0, hr1, hstrict⟩
    refine ⟨r, hr0, hr1, ?_⟩
    linarith [hstrict, hCzero]
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_transport_s0_kernel_gap_positive
      hdim μ u v hu hv huv htransport_g hgap0'

lemma swapped_bridge_kernel_zero_t_of_transport_strict_single
    (μ : FrameFunction H) (u v : H) (s : ℝ)
    (htransport1 :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
          ≤
        (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hstrict1 :
      (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
            <
          (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ t : ℝ, swapped_bridge_kernel μ u v s t = 0 := by
  intro t
  by_contra hne
  have hnz : ∃ z : ℝ, swapped_bridge_kernel μ u v s z ≠ 0 := ⟨t, hne⟩
  rcases hstrict1 hnz with ⟨r, hr0, hr1, hslt⟩
  have heq :
      (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
        =
      (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    exact
      hadamard_mobius_transport_eq_on_unit_interval
        (G := fun x =>
          |swapped_bridge_kernel μ u v s x| / (1 + x ^ 2))
        (htransport := htransport1)
        r hr0 hr1
  linarith [hslt, heq]

lemma swapped_bridge_kernel_zero_t_of_transport_neq_single
    (μ : FrameFunction H) (u v : H) (s : ℝ)
    (htransport1 :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
          ≤
        (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hneq1 :
      (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
            ≠
          (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ t : ℝ, swapped_bridge_kernel μ u v s t = 0 := by
  have hstrict1 :
      (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
            <
          (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    intro hnz
    rcases hneq1 hnz with ⟨r, hr0, hr1, hne⟩
    by_cases hlt :
        (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
          <
        (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))
    · exact ⟨r, hr0, hr1, hlt⟩
    · have hgt :
          (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))
            <
          (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2)) := by
        exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
      set φ : ℝ := (1 - r) / (1 + r)
      have hφ : 0 < φ ∧ φ < 1 := by
        simpa [φ] using hadamard_mobius_pos_lt_one_of_pos_lt_one (r := r) hr0 hr1
      have h1pr : 1 + r ≠ 0 := by linarith
      have hφφ : (1 - φ) / (1 + φ) = r := by
        simpa [φ] using hadamard_mobius_involutive r h1pr
      refine ⟨φ, hφ.1, hφ.2, ?_⟩
      simpa [φ, hφφ] using hgt
  exact
    swapped_bridge_kernel_zero_t_of_transport_strict_single
      μ u v s htransport1 hstrict1

lemma local_defect_g_zero_all_of_transport_neq_witness
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hneq_g :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ t : ℝ, local_defect_g μ u v t = 0 := by
  have hs0 :=
    hadamard_bridge_error_second_diff_witness_s0_of_local_defect_g_witness
      hdim μ u v hu hv huv htransport_g hneq_g
  rcases hs0 with ⟨htransportE0, hneqE0⟩
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have htransportK0 :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|swapped_bridge_kernel μ v u 0 r| / (1 + r ^ 2))
          ≤
        (|swapped_bridge_kernel μ v u 0 ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    intro r hr0 hr1
    have hE := htransportE0 r hr0 hr1
    have hK_r :
        (|swapped_bridge_kernel μ v u 0 r| / (1 + r ^ 2))
          =
        2 * (|hadamard_bridge_error_second_diff μ u v 0 r| / (1 + r ^ 2)) := by
      simpa [hadamard_bridge_error_second_diff, add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ v u hv hu hvu 0 r
    have hK_φ :
        (|swapped_bridge_kernel μ v u 0 ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))
          =
        2 *
          (|hadamard_bridge_error_second_diff μ u v 0 ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
      simpa [hadamard_bridge_error_second_diff, add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ v u hv hu hvu 0 ((1 - r) / (1 + r))
    rw [hK_r, hK_φ]
    nlinarith [hE]
  have hneqK0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|swapped_bridge_kernel μ v u 0 r| / (1 + r ^ 2))
            ≠
          (|swapped_bridge_kernel μ v u 0 ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    intro hker_nz
    rcases hneqE0 hker_nz with ⟨r, hr0, hr1, hneE⟩
    refine ⟨r, hr0, hr1, ?_⟩
    have hK_r :
        (|swapped_bridge_kernel μ v u 0 r| / (1 + r ^ 2))
          =
        2 * (|hadamard_bridge_error_second_diff μ u v 0 r| / (1 + r ^ 2)) := by
      simpa [hadamard_bridge_error_second_diff, add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ v u hv hu hvu 0 r
    have hK_φ :
        (|swapped_bridge_kernel μ v u 0 ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))
          =
        2 *
          (|hadamard_bridge_error_second_diff μ u v 0 ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
      simpa [hadamard_bridge_error_second_diff, add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ v u hv hu hvu 0 ((1 - r) / (1 + r))
    intro hEqK
    apply hneE
    nlinarith [hK_r, hK_φ, hEqK]
  have hK0 :
      ∀ t : ℝ, swapped_bridge_kernel μ v u 0 t = 0 := by
    exact
      swapped_bridge_kernel_zero_t_of_transport_neq_single
        μ v u 0 htransportK0 hneqK0
  intro t
  have hk : swapped_bridge_kernel μ v u 0 t = 0 := hK0 t
  rw [swapped_bridge_kernel_s0_eq_neg_two_local_defect_g hdim μ u v hu hv huv t] at hk
  have h2 : (-2 : ℝ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hk).resolve_left h2

lemma hadamard_bridge_error_zero_all_of_local_defect_g_zero_all
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hg0 : ∀ t : ℝ, local_defect_g μ u v t = 0) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  intro x
  by_cases h1px : 1 + x ≠ 0
  · have hres :
        hadamard_residual_one μ u v x = 0 := by
      have hmob :=
        hadamard_residual_one_eq_mobius_scaled_local_defect
          hdim μ u v hu hv huv x h1px
      rw [hg0 ((1 - x) / (1 + x)), mul_zero] at hmob
      exact hmob
    unfold hadamard_bridge_error
    rw [hres, hg0 x]
    ring
  · have hx0 : 1 + x = 0 := by
      by_contra hx0
      exact h1px hx0
    have hx : x = -1 := by linarith [hx0]
    simpa [hx] using hadamard_bridge_error_neg_one hdim μ u v hu hv huv

lemma hadamard_bridge_error_zero_all_of_local_defect_g_transport_neq_witness
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hneq_g :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have hg0 :
      ∀ t : ℝ, local_defect_g μ u v t = 0 :=
    local_defect_g_zero_all_of_transport_neq_witness
      hdim μ u v hu hv huv htransport_g hneq_g
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_zero_all
      hdim μ u v hu hv huv hg0

lemma hadamard_bridge_error_zero_all_of_local_defect_g_shift_bound_transport_neq_collapse
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_gap :
      let C : ℝ := Classical.choose
        (hadamard_bridge_error_shift_error_double_bundle_uniform_bound
          hdim μ u v hu hv huv)
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hneq_gap :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  let C : ℝ := Classical.choose
    (hadamard_bridge_error_shift_error_double_bundle_uniform_bound
      hdim μ u v hu hv huv)
  have hCspec :
      0 ≤ C ∧ ∀ s r : ℝ,
        (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
          |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2)
          +
        (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) -
            hadamard_bridge_error μ u v ((1 - r) / (1 + r))| +
          |hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
            hadamard_bridge_error μ u v (-((1 - r) / (1 + r)))| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) /
          (1 + ((1 - r) / (1 + r)) ^ 2)
          ≤ C * (1 + s ^ 2) := by
    simpa [C] using
      (Classical.choose_spec
        (hadamard_bridge_error_shift_error_double_bundle_uniform_bound
          hdim μ u v hu hv huv))
  have htransport_gap' :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    simpa [C] using htransport_gap
  have hCzero : C = 0 :=
    local_defect_g_shift_bound_transport_forces_C_zero
      μ u v C hCspec.1 htransport_gap'
  have htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) :=
    local_defect_g_transport_of_shift_bound_transport
      μ u v C hCzero htransport_gap'
  have hneq_g :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    intro hg_nz
    have hker_nz :
        ∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0 :=
      (exists_swapped_bridge_kernel_s0_ne_zero_iff_exists_local_defect_g_ne_zero
        hdim μ u v hu hv huv).2 hg_nz
    rcases hneq_gap 0 hker_nz with ⟨r, hr0, hr1, hne⟩
    exact ⟨r, hr0, hr1, hne⟩
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_transport_neq_witness
      hdim μ u v hu hv huv htransport_g hneq_g

lemma hadamard_bridge_error_zero_all_of_local_defect_g_shift_bound_transport_neq_collapse_s0
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_gap :
      let C : ℝ := Classical.choose
        (hadamard_bridge_error_shift_error_double_bundle_uniform_bound
          hdim μ u v hu hv huv)
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hneq_gap0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  let C : ℝ := Classical.choose
    (hadamard_bridge_error_shift_error_double_bundle_uniform_bound
      hdim μ u v hu hv huv)
  have hCspec :
      0 ≤ C ∧ ∀ s r : ℝ,
        (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
          |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2)
          +
        (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) -
            hadamard_bridge_error μ u v ((1 - r) / (1 + r))| +
          |hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
            hadamard_bridge_error μ u v (-((1 - r) / (1 + r)))| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) /
          (1 + ((1 - r) / (1 + r)) ^ 2)
          ≤ C * (1 + s ^ 2) := by
    simpa [C] using
      (Classical.choose_spec
        (hadamard_bridge_error_shift_error_double_bundle_uniform_bound
          hdim μ u v hu hv huv))
  have htransport_gap' :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    simpa [C] using htransport_gap
  have hCzero : C = 0 :=
    local_defect_g_shift_bound_transport_forces_C_zero
      μ u v C hCspec.1 htransport_gap'
  have htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) :=
    local_defect_g_transport_of_shift_bound_transport
      μ u v C hCzero htransport_gap'
  have hneq_g :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    intro hg_nz
    have hker_nz :
        ∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0 :=
      (exists_swapped_bridge_kernel_s0_ne_zero_iff_exists_local_defect_g_ne_zero
        hdim μ u v hu hv huv).2 hg_nz
    rcases hneq_gap0 hker_nz with ⟨r, hr0, hr1, hne⟩
    exact ⟨r, hr0, hr1, hne⟩
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_transport_neq_witness
      hdim μ u v hu hv huv htransport_g hneq_g

lemma swapped_bridge_kernel_ne_zero_iff_hadamard_bridge_error_second_diff_ne_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    swapped_bridge_kernel μ v u s t ≠ 0 ↔
      hadamard_bridge_error_second_diff μ u v s t ≠ 0 := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hker :
      swapped_bridge_kernel μ v u s t =
        2 * hadamard_bridge_error_second_diff μ u v s t := by
    unfold hadamard_bridge_error_second_diff
    simpa [add_assoc, add_left_comm, add_comm] using
      swapped_bridge_kernel_eq_two_hadamard_bridge_error_second_diff
        hdim μ v u hv hu hvu s t
  constructor
  · intro hK hE
    apply hK
    rw [hker, hE]
    ring
  · intro hE hK0
    rw [hker] at hK0
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have hE0 : hadamard_bridge_error_second_diff μ u v s t = 0 :=
      (mul_eq_zero.mp hK0).resolve_left h2
    exact hE hE0

lemma exists_swapped_bridge_kernel_ne_zero_iff_exists_hadamard_bridge_error_second_diff_ne_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s : ℝ) :
    (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) ↔
      ∃ t : ℝ, hadamard_bridge_error_second_diff μ u v s t ≠ 0 := by
  constructor
  · intro h
    rcases h with ⟨t, ht⟩
    exact ⟨t, (swapped_bridge_kernel_ne_zero_iff_hadamard_bridge_error_second_diff_ne_zero
      hdim μ u v hu hv huv s t).1 ht⟩
  · intro h
    rcases h with ⟨t, ht⟩
    exact ⟨t, (swapped_bridge_kernel_ne_zero_iff_hadamard_bridge_error_second_diff_ne_zero
      hdim μ u v hu hv huv s t).2 ht⟩

lemma hadamard_bridge_error_second_diff_normalized_eq_half_swapped_kernel
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    |hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2)
      =
    (1 / 2 : ℝ) *
      (|swapped_bridge_kernel μ v u s t| / (1 + t ^ 2)) := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hker :
      swapped_bridge_kernel μ v u s t =
        2 * hadamard_bridge_error_second_diff μ u v s t := by
    unfold hadamard_bridge_error_second_diff
    simpa [add_assoc, add_left_comm, add_comm] using
      swapped_bridge_kernel_eq_two_hadamard_bridge_error_second_diff
        hdim μ v u hv hu hvu s t
  have h2nn : (0 : ℝ) ≤ 2 := by norm_num
  calc
    |hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2)
        = (1 / 2 : ℝ) *
            (2 * |hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2)) := by ring
    _ = (1 / 2 : ℝ) *
          (|2 * hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2)) := by
            rw [abs_mul, abs_of_nonneg h2nn]
    _ = (1 / 2 : ℝ) *
          (|swapped_bridge_kernel μ v u s t| / (1 + t ^ 2)) := by
            rw [hker]

lemma hadamard_bridge_error_second_diff_swap_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    hadamard_bridge_error_second_diff μ v u s t =
      -hadamard_bridge_error_second_diff μ u v s t := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hker_uv :
      swapped_bridge_kernel μ u v s t =
        2 * hadamard_bridge_error_second_diff μ v u s t := by
    unfold hadamard_bridge_error_second_diff
    simpa [add_assoc, add_left_comm, add_comm] using
      swapped_bridge_kernel_eq_two_hadamard_bridge_error_second_diff
        hdim μ u v hu hv huv s t
  have hker_vu :
      swapped_bridge_kernel μ v u s t =
        2 * hadamard_bridge_error_second_diff μ u v s t := by
    unfold hadamard_bridge_error_second_diff
    simpa [add_assoc, add_left_comm, add_comm] using
      swapped_bridge_kernel_eq_two_hadamard_bridge_error_second_diff
        hdim μ v u hv hu hvu s t
  have hswap :
      swapped_bridge_kernel μ u v s t = -swapped_bridge_kernel μ v u s t :=
    swapped_bridge_kernel_swap_neg hdim μ u v hu hv huv s t
  have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
  apply (mul_right_inj' h2_ne).1
  calc
    2 * hadamard_bridge_error_second_diff μ v u s t
        = swapped_bridge_kernel μ u v s t := hker_uv.symm
    _ = -swapped_bridge_kernel μ v u s t := hswap
    _ = 2 * (-hadamard_bridge_error_second_diff μ u v s t) := by
          rw [hker_vu]
          ring

lemma hadamard_bridge_error_second_diff_normalized_uniform_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s r : ℝ,
      |hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2) ≤
        C * (1 + s ^ 2) := by
  rcases hadamard_bridge_error_second_diff_growth_bound_two_vars
      hdim μ u v hu hv huv with ⟨C0, hC0nn, hC0⟩
  refine ⟨C0, hC0nn, ?_⟩
  intro s r
  have hden_pos : 0 < (1 + r ^ 2 : ℝ) := by
    nlinarith [sq_nonneg r]
  have hratio :
      (1 + s ^ 2 + r ^ 2) / (1 + r ^ 2) ≤ 1 + s ^ 2 := by
    refine (div_le_iff₀ hden_pos).2 ?_
    ring_nf
    nlinarith [sq_nonneg s, sq_nonneg r]
  have hdiv :
      |hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2)
        ≤
      C0 * ((1 + s ^ 2 + r ^ 2) / (1 + r ^ 2)) := by
    have hbase :
        |hadamard_bridge_error_second_diff μ u v s r|
          ≤ C0 * (1 + s ^ 2 + r ^ 2) := by
      simpa [hadamard_bridge_error_second_diff] using hC0 s r
    have hdiv' :
        |hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2)
          ≤ (C0 * (1 + s ^ 2 + r ^ 2)) / (1 + r ^ 2) :=
      div_le_div_of_nonneg_right hbase (le_of_lt hden_pos)
    have hrew :
        (C0 * (1 + s ^ 2 + r ^ 2)) / (1 + r ^ 2) =
          C0 * ((1 + s ^ 2 + r ^ 2) / (1 + r ^ 2)) := by ring
    simpa [hrew] using hdiv'
  have hmul :
      C0 * ((1 + s ^ 2 + r ^ 2) / (1 + r ^ 2)) ≤ C0 * (1 + s ^ 2) :=
    mul_le_mul_of_nonneg_left hratio hC0nn
  exact le_trans hdiv hmul

lemma hadamard_bridge_error_zero_all_of_swapped_kernel_zero_all
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hker0 : ∀ s t : ℝ, swapped_bridge_kernel μ v u s t = 0) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have hmid_gap :
      ∀ s t : ℝ,
        defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) =
          2 * defect_one_gap μ u v s := by
    intro s t
    have hk : swapped_bridge_kernel μ v u s t = 0 := hker0 s t
    unfold swapped_bridge_kernel at hk
    linarith [hk]
  exact
    hadamard_bridge_error_zero_of_defect_one_gap_midpoint
      hdim μ u v hu hv huv hmid_gap

lemma swapped_bridge_kernel_bridge_eq_of_normalized_gauge_zero_all
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hG0 : ∀ s r : ℝ, swapped_bridge_kernel_normalized_gauge μ u v s r = 0) :
    ∀ s t : ℝ,
      local_quad2DDefect μ (v + u + (s : ℂ) • (v - u)) (v - u) 1 t +
        local_quad2DDefect μ (v - u + (s : ℂ) • (v + u)) (v + u) 1 t
        =
      local_quad2DDefect μ (v + (s : ℂ) • u) u 1 t +
        local_quad2DDefect μ (v - (s : ℂ) • u) u 1 t := by
  intro s t
  have hk0 :
      swapped_bridge_kernel μ u v s t = 0 := by
    exact swapped_bridge_kernel_zero_of_normalized_gauge_zero μ u v s t (hG0 s t)
  exact (swapped_bridge_kernel_gap_closure hdim μ u v hu hv huv s t).1 hk0

lemma defect_one_gap_midpoint_iff_local_A_bridge
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∀ s t : ℝ,
      defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) =
        2 * defect_one_gap μ u v s)
      ↔
    (∀ s t : ℝ,
      local_quad2DDefect μ (u + v + (s : ℂ) • (u - v)) (u - v) 1 t +
        local_quad2DDefect μ (u - v + (s : ℂ) • (u + v)) (u + v) 1 t
        =
      local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
        2 * local_defect_g μ u v s) := by
  constructor
  · intro hmid s t
    have hA := local_A_func_second_diff hdim μ u v hu hv huv s t
    have hmid' :
        defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) -
          2 * defect_one_gap μ u v s = 0 := by
      linarith [hmid s t]
    have hdef :
        defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) -
          2 * defect_one_gap μ u v s
          =
        (local_A_func μ u v (s + t) + local_A_func μ u v (s - t) -
          2 * local_A_func μ u v s) -
        (local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
          2 * local_defect_g μ u v s) := by
      unfold defect_one_gap local_A_func local_defect_g
      ring
    have hAeq :
        local_A_func μ u v (s + t) + local_A_func μ u v (s - t) -
          2 * local_A_func μ u v s
          =
        local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
          2 * local_defect_g μ u v s := by
      linarith [hdef, hmid']
    linarith [hA, hAeq]
  · intro hbridge s t
    have hA := local_A_func_second_diff hdim μ u v hu hv huv s t
    have hAeq := hbridge s t
    have hA0 :
        local_A_func μ u v (s + t) + local_A_func μ u v (s - t) -
          2 * local_A_func μ u v s
          =
        local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
          2 * local_defect_g μ u v s := by
      linarith [hA, hAeq]
    have hmid0 :
        defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) -
          2 * defect_one_gap μ u v s = 0 := by
      have hdef :
          defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) -
            2 * defect_one_gap μ u v s
            =
          (local_A_func μ u v (s + t) + local_A_func μ u v (s - t) -
            2 * local_A_func μ u v s) -
          (local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
            2 * local_defect_g μ u v s) := by
        unfold defect_one_gap local_A_func local_defect_g
        ring
      linarith [hdef, hA0]
    linarith [hmid0]

lemma local_A_bridge_iff_hadamard_bridge_error_zero_all
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∀ s t : ℝ,
      local_quad2DDefect μ (u + v + (s : ℂ) • (u - v)) (u - v) 1 t +
        local_quad2DDefect μ (u - v + (s : ℂ) • (u + v)) (u + v) 1 t
        =
      local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
        2 * local_defect_g μ u v s)
      ↔
    (∀ r : ℝ, hadamard_bridge_error μ u v r = 0) := by
  exact
    (defect_one_gap_midpoint_iff_local_A_bridge hdim μ u v hu hv huv).symm.trans
      (defect_one_gap_midpoint_iff_hadamard_bridge_error_zero_all hdim μ u v hu hv huv)

lemma local_A_bridge_implies_local_defect_g_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hbridge : ∀ s t : ℝ,
      local_quad2DDefect μ (u + v + (s : ℂ) • (u - v)) (u - v) 1 t +
        local_quad2DDefect μ (u - v + (s : ℂ) • (u + v)) (u + v) 1 t
        =
      local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
        2 * local_defect_g μ u v s) :
    ∀ t : ℝ, local_defect_g μ u v t = 0 := by
  intro t
  set X : H := u + v
  set Y : H := u - v
  have h0 := hbridge 0 t
  have hXY : local_quad2DDefect μ X Y 1 t + local_quad2DDefect μ Y X 1 t = 0 := by
    simpa [X, Y] using local_quad2DDefect_X_Y_sum_zero hdim μ u v hu hv huv t
  have h0' :
      local_quad2DDefect μ X Y 1 t + local_quad2DDefect μ Y X 1 t =
        local_defect_g μ u v t + local_defect_g μ u v (-t) -
          2 * local_defect_g μ u v 0 := by
    simpa [X, Y, zero_smul] using h0
  have heven : local_defect_g μ u v (-t) = local_defect_g μ u v t := by
    simpa using GleasonBridge.local_defect_g_even μ u v t
  have hzero : local_defect_g μ u v 0 = 0 := GleasonBridge.local_defect_g_zero_eq_zero μ u v
  linarith [hXY, h0', heven, hzero]

lemma local_A_func_eq_two_mul_hadamard_residual_one
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    local_A_func μ u v r = 2 * hadamard_residual_one μ u v r := by
  have hgap :
      defect_one_gap μ u v r = 2 * hadamard_bridge_error μ u v r := by
    exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv r
  have hgap' :
      local_quad2DDefect μ u v (1 + r) (1 - r) - local_defect_g μ u v r =
        2 * hadamard_bridge_error μ u v r := by
    simpa [defect_one_gap, local_defect_g] using hgap
  have hgap'' :
      local_quad2DDefect μ u v (1 + r) (1 - r) - local_defect_g μ u v r =
        2 * (hadamard_residual_one μ u v r - (1 / 2 : ℝ) * local_defect_g μ u v r) := by
    simpa [hadamard_bridge_error] using hgap'
  unfold local_A_func
  linarith [hgap'']

lemma hadamard_residual_one_swap_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    hadamard_residual_one μ v u r = - hadamard_residual_one μ u v r := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hAuv :
      local_A_func μ u v r = 2 * hadamard_residual_one μ u v r :=
    local_A_func_eq_two_mul_hadamard_residual_one hdim μ u v hu hv huv r
  have hAvu :
      local_A_func μ v u r = 2 * hadamard_residual_one μ v u r :=
    local_A_func_eq_two_mul_hadamard_residual_one hdim μ v u hv hu hvu r
  have hAswap :
      local_A_func μ v u r = - local_A_func μ u v r :=
    local_A_func_swap_neg hdim μ u v hu hv huv r
  linarith [hAuv, hAvu, hAswap]

lemma hadamard_bridge_error_swap_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    hadamard_bridge_error μ v u r = - hadamard_bridge_error μ u v r := by
  have hres :
      hadamard_residual_one μ v u r = - hadamard_residual_one μ u v r :=
    hadamard_residual_one_swap_neg hdim μ u v hu hv huv r
  have hgswap :
      local_defect_g μ v u r = - local_defect_g μ u v r := by
    have hsum := local_defect_g_swap_add_eq_zero hdim μ u v hu hv huv r
    linarith [hsum]
  unfold hadamard_bridge_error
  linarith [hres, hgswap]

lemma local_defect_g_second_diff_swap_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    local_defect_g μ v u (s + t) + local_defect_g μ v u (s - t) -
      2 * local_defect_g μ v u s
      =
    -(local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
      2 * local_defect_g μ u v s) := by
  have hst :
      local_defect_g μ v u (s + t) = - local_defect_g μ u v (s + t) := by
    have hsum := local_defect_g_swap_add_eq_zero hdim μ u v hu hv huv (s + t)
    linarith [hsum]
  have hsm :
      local_defect_g μ v u (s - t) = - local_defect_g μ u v (s - t) := by
    have hsum := local_defect_g_swap_add_eq_zero hdim μ u v hu hv huv (s - t)
    linarith [hsum]
  have hs :
      local_defect_g μ v u s = - local_defect_g μ u v s := by
    have hsum := local_defect_g_swap_add_eq_zero hdim μ u v hu hv huv s
    linarith [hsum]
  linarith [hst, hsm, hs]

lemma local_A_func_second_diff_swap_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    local_A_func μ v u (s + t) + local_A_func μ v u (s - t) -
      2 * local_A_func μ v u s
      =
    -(local_A_func μ u v (s + t) + local_A_func μ u v (s - t) -
      2 * local_A_func μ u v s) := by
  have hst : local_A_func μ v u (s + t) = - local_A_func μ u v (s + t) :=
    local_A_func_swap_neg hdim μ u v hu hv huv (s + t)
  have hsm : local_A_func μ v u (s - t) = - local_A_func μ u v (s - t) :=
    local_A_func_swap_neg hdim μ u v hu hv huv (s - t)
  have hs : local_A_func μ v u s = - local_A_func μ u v s :=
    local_A_func_swap_neg hdim μ u v hu hv huv s
  linarith [hst, hsm, hs]

lemma hadamard_bridge_error_second_diff_eq_half_bridge_gap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    hadamard_bridge_error μ u v (s + t) + hadamard_bridge_error μ u v (s - t) -
      2 * hadamard_bridge_error μ u v s
      =
    (local_quad2DDefect μ (u + v + (s : ℂ) • (u - v)) (u - v) 1 t +
      local_quad2DDefect μ (u - v + (s : ℂ) • (u + v)) (u + v) 1 t
      - (local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
          2 * local_defect_g μ u v s)) / 2 := by
  have hA := local_A_func_second_diff hdim μ u v hu hv huv s t
  have hAp : local_A_func μ u v (s + t) = 2 * hadamard_residual_one μ u v (s + t) :=
    local_A_func_eq_two_mul_hadamard_residual_one hdim μ u v hu hv huv (s + t)
  have hAm : local_A_func μ u v (s - t) = 2 * hadamard_residual_one μ u v (s - t) :=
    local_A_func_eq_two_mul_hadamard_residual_one hdim μ u v hu hv huv (s - t)
  have hAs : local_A_func μ u v s = 2 * hadamard_residual_one μ u v s :=
    local_A_func_eq_two_mul_hadamard_residual_one hdim μ u v hu hv huv s
  have hE :
      hadamard_bridge_error μ u v (s + t) + hadamard_bridge_error μ u v (s - t) -
        2 * hadamard_bridge_error μ u v s
      =
      (hadamard_residual_one μ u v (s + t) + hadamard_residual_one μ u v (s - t) -
        2 * hadamard_residual_one μ u v s)
      -
      (1 / 2 : ℝ) *
        (local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
          2 * local_defect_g μ u v s) := by
    unfold hadamard_bridge_error
    ring
  have hF :
      hadamard_residual_one μ u v (s + t) + hadamard_residual_one μ u v (s - t) -
        2 * hadamard_residual_one μ u v s
      =
      (local_quad2DDefect μ (u + v + (s : ℂ) • (u - v)) (u - v) 1 t +
        local_quad2DDefect μ (u - v + (s : ℂ) • (u + v)) (u + v) 1 t) / 2 := by
    have hA' :
        local_A_func μ u v (s + t) + local_A_func μ u v (s - t) - 2 * local_A_func μ u v s
          =
        local_quad2DDefect μ (u + v + (s : ℂ) • (u - v)) (u - v) 1 t +
          local_quad2DDefect μ (u - v + (s : ℂ) • (u + v)) (u + v) 1 t := hA
    rw [hAp, hAm, hAs] at hA'
    linarith [hA']
  linarith [hE, hF]

lemma defect_one_gap_midpoint_iff_hadamard_bridge_error_midpoint
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∀ s t : ℝ,
      defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) =
        2 * defect_one_gap μ u v s)
      ↔
    (∀ s t : ℝ,
      hadamard_bridge_error μ u v (s + t) + hadamard_bridge_error μ u v (s - t) =
        2 * hadamard_bridge_error μ u v s) := by
  constructor
  · intro hmid s t
    have hst : defect_one_gap μ u v (s + t) = 2 * hadamard_bridge_error μ u v (s + t) := by
      exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv (s + t)
    have hsd : defect_one_gap μ u v (s - t) = 2 * hadamard_bridge_error μ u v (s - t) := by
      exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv (s - t)
    have hs : defect_one_gap μ u v s = 2 * hadamard_bridge_error μ u v s := by
      exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv s
    linarith [hmid s t, hst, hsd, hs]
  · intro hmid s t
    have hst : defect_one_gap μ u v (s + t) = 2 * hadamard_bridge_error μ u v (s + t) := by
      exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv (s + t)
    have hsd : defect_one_gap μ u v (s - t) = 2 * hadamard_bridge_error μ u v (s - t) := by
      exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv (s - t)
    have hs : defect_one_gap μ u v s = 2 * hadamard_bridge_error μ u v s := by
      exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv s
    linarith [hmid s t, hst, hsd, hs]

lemma hadamard_bridge_error_midpoint_iff_local_A_bridge
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∀ s t : ℝ,
      hadamard_bridge_error μ u v (s + t) + hadamard_bridge_error μ u v (s - t) =
        2 * hadamard_bridge_error μ u v s)
      ↔
    (∀ s t : ℝ,
      local_quad2DDefect μ (u + v + (s : ℂ) • (u - v)) (u - v) 1 t +
        local_quad2DDefect μ (u - v + (s : ℂ) • (u + v)) (u + v) 1 t
        =
      local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
        2 * local_defect_g μ u v s) := by
  exact
    (defect_one_gap_midpoint_iff_hadamard_bridge_error_midpoint
      hdim μ u v hu hv huv).symm.trans
      (defect_one_gap_midpoint_iff_local_A_bridge hdim μ u v hu hv huv)

lemma hadamard_bridge_error_mobius_symm_antisymm_struct
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let φ : ℝ := (1 - r) / (1 + r)
    let S : ℝ := hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)
    let A : ℝ := hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)
    let Sφ : ℝ := hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)
    let Aφ : ℝ := hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ)
    (1 + r) ^ 2 * Sφ = -A ∧ (1 + r) ^ 2 * Aφ = -4 * S := by
  intro φ S A Sφ Aφ
  rcases hadamard_bridge_error_mobius_linearized hdim μ u v hu hv huv r h1pr with
    ⟨hEφ, hEnegφ⟩
  constructor
  · have hsum : 2 * (1 + r) ^ 2 *
      (hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)) =
      (-5 * hadamard_bridge_error μ u v r - 3 * hadamard_bridge_error μ u v (-r)) +
      (3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r)) := by
      linarith [hEφ, hEnegφ]
    dsimp [S, A, Sφ]
    linarith [hsum]
  · have hdiff : 2 * (1 + r) ^ 2 *
      (hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ)) =
      (-5 * hadamard_bridge_error μ u v r - 3 * hadamard_bridge_error μ u v (-r)) -
      (3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r)) := by
      linarith [hEφ, hEnegφ]
    dsimp [S, A, Aφ]
    linarith [hdiff]

lemma hadamard_bridge_error_inversion_symm_antisymm
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    {r : ℝ} (hr : r ≠ 0) :
    let S : ℝ := hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)
    let A : ℝ := hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)
    let Sinv : ℝ := hadamard_bridge_error μ u v (1 / r) + hadamard_bridge_error μ u v (-(1 / r))
    let Ainv : ℝ := hadamard_bridge_error μ u v (1 / r) - hadamard_bridge_error μ u v (-(1 / r))
    S = -r ^ 2 * Sinv ∧ A = r ^ 2 * Ainv := by
  intro S A Sinv Ainv
  have h1 : hadamard_bridge_error μ u v r = -r ^ 2 * hadamard_bridge_error μ u v (-(1 / r)) := by
    exact hadamard_bridge_error_inversion hdim μ u v hu hv huv hr
  have h2 : hadamard_bridge_error μ u v (-r) = -r ^ 2 * hadamard_bridge_error μ u v (1 / r) := by
    have h := hadamard_bridge_error_inversion hdim μ u v hu hv huv (neg_ne_zero.mpr hr)
    simpa [neg_sq] using h
  constructor
  · dsimp [S, Sinv]
    linarith [h1, h2]
  · dsimp [A, Ainv]
    linarith [h1, h2]

lemma hadamard_bridge_error_mobius_normalized
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let φ : ℝ := (1 - r) / (1 + r)
    N φ = -(5 * N r + 3 * N (-r)) / 4
      ∧
    N (-φ) = (3 * N r + 5 * N (-r)) / 4 := by
  intro N φ
  rcases hadamard_bridge_error_mobius_linearized hdim μ u v hu hv huv r h1pr with
    ⟨hEφ, hEnegφ⟩
  have h1pr_sq_ne : (1 + r) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 h1pr
  have hphi_den : 1 + φ ^ 2 = 2 * (1 + r ^ 2) / (1 + r) ^ 2 := by
    dsimp [φ]
    field_simp [h1pr]
    ring
  have h1r2_ne : (1 + r ^ 2) ≠ 0 := by positivity
  have hEφ' :
      hadamard_bridge_error μ u v φ =
        -(5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r))
          / (2 * (1 + r) ^ 2) := by
    have h2mul_ne : (2 * (1 + r) ^ 2) ≠ 0 := by
      exact mul_ne_zero (by norm_num) h1pr_sq_ne
    apply (eq_div_iff h2mul_ne).2
    have hEφ0 :
        2 * (1 + r) ^ 2 * hadamard_bridge_error μ u v φ =
          -(5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r)) := by
      simpa [φ] using hEφ
    linarith [hEφ0]
  have hEnegφ' :
      hadamard_bridge_error μ u v (-φ) =
        (3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r))
          / (2 * (1 + r) ^ 2) := by
    have h2mul_ne : (2 * (1 + r) ^ 2) ≠ 0 := by
      exact mul_ne_zero (by norm_num) h1pr_sq_ne
    apply (eq_div_iff h2mul_ne).2
    have hEnegφ0 :
        2 * (1 + r) ^ 2 * hadamard_bridge_error μ u v (-φ) =
          3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r) := by
      simpa [φ] using hEnegφ
    linarith [hEnegφ0]
  have hNφ_core :
      hadamard_bridge_error μ u v φ / (1 + φ ^ 2) =
        -(5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r))
          / (4 * (1 + r ^ 2)) := by
    rw [hEφ', hphi_den]
    field_simp [h1pr, h1r2_ne]
    ring
  have hNnegφ_core :
      hadamard_bridge_error μ u v (-φ) / (1 + (-φ) ^ 2) =
        (3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r))
          / (4 * (1 + r ^ 2)) := by
    have hphi_den_neg : 1 + (-φ) ^ 2 = 2 * (1 + r ^ 2) / (1 + r) ^ 2 := by
      simpa [neg_sq] using hphi_den
    rw [hEnegφ', hphi_den_neg]
    field_simp [h1pr, h1r2_ne]
    ring
  constructor
  · dsimp [N]
    rw [hNφ_core]
    field_simp [h1r2_ne]
  · dsimp [N]
    rw [hNnegφ_core]
    field_simp [h1r2_ne]


end
