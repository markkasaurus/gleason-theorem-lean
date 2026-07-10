import Gleason.Continuity.Defect.SecondDifference

noncomputable section

open GleasonBridge RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

def local_defect_g_normalized_gap
    (μ : FrameFunction H) (u v : H) (r : ℝ) : ℝ :=
  |(|local_defect_g μ u v r| / (1 + r ^ 2)) -
    (|local_defect_g μ u v ((1 - r) / (1 + r))| /
      (1 + ((1 - r) / (1 + r)) ^ 2))|

lemma local_defect_g_normalized_gap_nonneg
    (μ : FrameFunction H) (u v : H) (r : ℝ) :
    0 ≤ local_defect_g_normalized_gap μ u v r := by
  dsimp [local_defect_g_normalized_gap]
  exact abs_nonneg _

lemma local_defect_g_normalized_gap_eq_zero_of_infimum_pair
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (huM : frame_quadratic μ u = sInf (Q_sphere_set μ))
    (hvM : frame_quadratic μ v = sInf (Q_sphere_set μ))
    (r : ℝ) :
    local_defect_g_normalized_gap μ u v r = 0 := by
  have hr : local_defect_g μ u v r = 0 :=
    local_defect_g_eq_zero_of_infimum_pair hdim μ u v hu hv huv huM hvM r
  have hphi : local_defect_g μ u v ((1 - r) / (1 + r)) = 0 :=
    local_defect_g_eq_zero_of_infimum_pair hdim μ u v hu hv huv huM hvM ((1 - r) / (1 + r))
  unfold local_defect_g_normalized_gap
  simp [hr, hphi]

lemma local_defect_g_normalized_gap_bound_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    local_defect_g_normalized_gap μ u v r
      ≤
    4 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
      4 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) := by
  simpa [local_defect_g_normalized_gap] using
    local_defect_g_normalized_gap_bound_infimum_pre hdim μ u v hu hv huv r

lemma local_defect_g_normalized_gap_pos_iff
    (μ : FrameFunction H) (u v : H) (r : ℝ) :
    0 < local_defect_g_normalized_gap μ u v r
      ↔
    (|local_defect_g μ u v r| / (1 + r ^ 2))
      ≠
    (|local_defect_g μ u v ((1 - r) / (1 + r))| /
      (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  constructor
  · intro hpos
    exact sub_ne_zero.mp (abs_pos.mp (by simpa [local_defect_g_normalized_gap] using hpos))
  · intro hne
    exact abs_pos.mpr (by simpa [local_defect_g_normalized_gap] using (sub_ne_zero.mpr hne))

lemma local_defect_g_normalized_abs_eq_bridge_symm_norm
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    |local_defect_g μ u v r| / (1 + r ^ 2)
      =
    |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)| / (1 + r ^ 2) := by
  have hsym :=
    local_defect_g_eq_bridge_error_symm hdim μ u v hu hv huv r
  have hneg :
      -(hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r))
        =
      -hadamard_bridge_error μ u v (-r) + -hadamard_bridge_error μ u v r := by
    ring
  rw [hsym, hneg]
  have habs :
      |(-hadamard_bridge_error μ u v (-r) + -hadamard_bridge_error μ u v r)|
        =
      |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)| := by
    calc
      |(-hadamard_bridge_error μ u v (-r) + -hadamard_bridge_error μ u v r)|
          =
        |-(hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r))| := by
            ring_nf
      _ =
        |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)| := by
            rw [abs_neg]
  simpa [habs]

lemma local_defect_g_normalized_abs_mobius_eq_bridge_antisymm_norm
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let φ : ℝ := (1 - r) / (1 + r)
    |local_defect_g μ u v φ| / (1 + φ ^ 2)
      =
    |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| /
      (2 * (1 + r ^ 2)) := by
  intro φ
  rcases hadamard_bridge_error_mobius_symm_antisymm hdim μ u v hu hv huv r h1pr with
    ⟨hS, hA⟩
  have hgφ :
      local_defect_g μ u v φ =
        -(hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)) := by
    simpa [φ] using local_defect_g_eq_bridge_error_symm hdim μ u v hu hv huv φ
  have hmul :
      (1 + r) ^ 2 * local_defect_g μ u v φ =
        hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r) := by
    calc
      (1 + r) ^ 2 * local_defect_g μ u v φ
          = -((1 + r) ^ 2 *
              (hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ))) := by
              rw [hgφ]
              ring
      _ = hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r) := by
            linarith [hS]
  have hmul_abs :
      (1 + r) ^ 2 * |local_defect_g μ u v φ| =
        |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| := by
    have habs := congrArg abs hmul
    have hsq_abs : |(1 + r) ^ 2| = (1 + r) ^ 2 := by
      exact abs_of_nonneg (sq_nonneg (1 + r))
    simpa [abs_mul, hsq_abs] using habs
  have hden :
      1 + φ ^ 2 = (2 * (1 + r ^ 2)) / (1 + r) ^ 2 := by
    dsimp [φ]
    field_simp [h1pr]
    ring
  have h1pr_sq : (1 + r) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 h1pr
  calc
    |local_defect_g μ u v φ| / (1 + φ ^ 2)
        = |local_defect_g μ u v φ| / ((2 * (1 + r ^ 2)) / (1 + r) ^ 2) := by
            rw [hden]
    _ = ((1 + r) ^ 2 * |local_defect_g μ u v φ|) / (2 * (1 + r ^ 2)) := by
          field_simp [h1pr_sq]
    _ =
      |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| /
        (2 * (1 + r ^ 2)) := by
          rw [hmul_abs]

lemma local_defect_g_transport_s0_iff_bridge_antisymm_dominates_symm
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∀ r : ℝ, 0 < r → r < 1 →
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        ≤
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)))
      ↔
    (∀ r : ℝ, 0 < r → r < 1 →
      2 * |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)|
        ≤
      |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)|) := by
  constructor
  · intro htransport r hr0 hr1
    have h1pr : 1 + r ≠ 0 := by linarith
    have htr := htransport r hr0 hr1
    have hleft :
        |local_defect_g μ u v r| / (1 + r ^ 2)
          =
        |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)| / (1 + r ^ 2) := by
      exact local_defect_g_normalized_abs_eq_bridge_symm_norm hdim μ u v hu hv huv r
    have hright :
        |local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)
          =
        |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| /
          (2 * (1 + r ^ 2)) := by
      simpa using
        local_defect_g_normalized_abs_mobius_eq_bridge_antisymm_norm
          hdim μ u v hu hv huv r h1pr
    rw [hleft, hright] at htr
    have hden_pos : 0 < 1 + r ^ 2 := by positivity
    have htr' : 2 * |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)|
          ≤
        |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| := by
      have h := htr
      field_simp [hden_pos.ne'] at h
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    exact htr'
  · intro hdom r hr0 hr1
    have h1pr : 1 + r ≠ 0 := by linarith
    have hdom_r := hdom r hr0 hr1
    have hleft :
        |local_defect_g μ u v r| / (1 + r ^ 2)
          =
        |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)| / (1 + r ^ 2) := by
      exact local_defect_g_normalized_abs_eq_bridge_symm_norm hdim μ u v hu hv huv r
    have hright :
        |local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)
          =
        |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| /
          (2 * (1 + r ^ 2)) := by
      simpa using
        local_defect_g_normalized_abs_mobius_eq_bridge_antisymm_norm
          hdim μ u v hu hv huv r h1pr
    rw [hleft, hright]
    have hden_pos : 0 < 1 + r ^ 2 := by positivity
    have hdom_div :
        |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)|
          ≤
        |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| / 2 := by
      nlinarith [hdom_r]
    have hdiv :
        |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)| / (1 + r ^ 2)
          ≤
        (|hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| / 2) / (1 + r ^ 2) :=
      div_le_div_of_nonneg_right hdom_div (le_of_lt hden_pos)
    have hrhs :
        (|hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| / 2) / (1 + r ^ 2)
          =
        |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| / (2 * (1 + r ^ 2)) := by
      field_simp [hden_pos.ne']
    exact hdiv.trans (by simpa [hrhs])

lemma local_defect_g_normalized_abs_mobius_companion_pre
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) (h1mr : 1 - r ≠ 0) :
    (|local_defect_g μ u v ((1 + r) / (1 - r))| /
        (1 + ((1 + r) / (1 - r)) ^ 2))
      =
    (|local_defect_g μ u v ((1 - r) / (1 + r))| /
      (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  have hφ :
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))
        =
      |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| /
        (2 * (1 + r ^ 2)) := by
    simpa using
      local_defect_g_normalized_abs_mobius_eq_bridge_antisymm_norm
        hdim μ u v hu hv huv r h1pr
  have hψ :
      (|local_defect_g μ u v ((1 + r) / (1 - r))| /
          (1 + ((1 + r) / (1 - r)) ^ 2))
        =
      |hadamard_bridge_error μ u v (-r) - hadamard_bridge_error μ u v (-(-r))| /
        (2 * (1 + (-r) ^ 2)) := by
    have h1m : 1 + (-r) ≠ 0 := by simpa using h1mr
    simpa [sub_eq_add_neg] using
      local_defect_g_normalized_abs_mobius_eq_bridge_antisymm_norm
        hdim μ u v hu hv huv (-r) h1m
  calc
    (|local_defect_g μ u v ((1 + r) / (1 - r))| /
        (1 + ((1 + r) / (1 - r)) ^ 2))
        =
      |hadamard_bridge_error μ u v (-r) - hadamard_bridge_error μ u v r| /
        (2 * (1 + r ^ 2)) := by
          simpa [neg_sq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hψ
    _ =
      |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| /
        (2 * (1 + r ^ 2)) := by
          rw [abs_sub_comm]
    _ =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := hφ.symm

lemma local_defect_g_no_neq_witness_eq_on_unit_interval
    (μ : FrameFunction H) (u v : H)
    (hno :
      ¬ ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ r : ℝ, 0 < r → r < 1 →
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro r hr0 hr1
  by_contra hne
  exact hno ⟨r, hr0, hr1, hne⟩

lemma local_defect_g_normalized_abs_lift_eq_of_no_neq_witness
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hno :
      ¬ ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ r : ℝ, 0 < r → r < 1 →
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 + r) / (1 - r))| /
        (1 + ((1 + r) / (1 - r)) ^ 2)) := by
  intro r hr0 hr1
  have hEq_unit :
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) :=
    local_defect_g_no_neq_witness_eq_on_unit_interval μ u v hno r hr0 hr1
  have h1pr : 1 + r ≠ 0 := by linarith
  have h1mr : 1 - r ≠ 0 := by linarith
  have hcomp :
      (|local_defect_g μ u v ((1 + r) / (1 - r))| /
          (1 + ((1 + r) / (1 - r)) ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    simpa using
      (local_defect_g_normalized_abs_mobius_companion_pre
        hdim μ u v hu hv huv r h1pr h1mr)
  calc
    (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := hEq_unit
    _ =
      (|local_defect_g μ u v ((1 + r) / (1 - r))| /
        (1 + ((1 + r) / (1 - r)) ^ 2)) := by
          simpa using hcomp.symm

lemma local_defect_g_normalized_abs_has_unit_interval_representative_of_no_neq_witness
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hno :
      ¬ ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≠ 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (|local_defect_g μ u v t| / (1 + t ^ 2))
        =
      (|local_defect_g μ u v r| / (1 + r ^ 2)) := by
  rcases lt_or_gt_of_ne ht1 with ht_lt | ht_gt
  · refine ⟨t, ht0, ht_lt, ?_⟩
    rfl
  · let r : ℝ := (t - 1) / (t + 1)
    have ht1_pos : 0 < t - 1 := by linarith
    have ht1p_pos : 0 < t + 1 := by linarith
    have hr0 : 0 < r := by
      dsimp [r]
      exact div_pos ht1_pos ht1p_pos
    have hr1 : r < 1 := by
      dsimp [r]
      exact (div_lt_iff₀ ht1p_pos).2 (by linarith)
    have hrepr : (1 + r) / (1 - r) = t := by
      dsimp [r]
      field_simp
      ring
    have hlift :
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          =
        (|local_defect_g μ u v ((1 + r) / (1 - r))| /
          (1 + ((1 + r) / (1 - r)) ^ 2)) :=
      local_defect_g_normalized_abs_lift_eq_of_no_neq_witness
        hdim μ u v hu hv huv hno r hr0 hr1
    refine ⟨r, hr0, hr1, ?_⟩
    simpa [hrepr] using hlift.symm

lemma local_defect_g_transport_eq_on_unit_interval
    (μ : FrameFunction H) (u v : H)
    (htransport :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ r : ℝ, 0 < r → r < 1 →
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  exact
    hadamard_mobius_transport_eq_on_unit_interval
      (G := fun x =>
        |local_defect_g μ u v x| / (1 + x ^ 2))
      htransport

lemma local_defect_g_normalized_abs_lift_eq_of_transport
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ r : ℝ, 0 < r → r < 1 →
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 + r) / (1 - r))| /
        (1 + ((1 + r) / (1 - r)) ^ 2)) := by
  intro r hr0 hr1
  have hEq_unit :
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) :=
    local_defect_g_transport_eq_on_unit_interval μ u v htransport r hr0 hr1
  have h1pr : 1 + r ≠ 0 := by linarith
  have h1mr : 1 - r ≠ 0 := by linarith
  have hcomp :
      (|local_defect_g μ u v ((1 + r) / (1 - r))| /
          (1 + ((1 + r) / (1 - r)) ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    simpa using
      (local_defect_g_normalized_abs_mobius_companion_pre
        hdim μ u v hu hv huv r h1pr h1mr)
  calc
    (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := hEq_unit
    _ =
      (|local_defect_g μ u v ((1 + r) / (1 - r))| /
        (1 + ((1 + r) / (1 - r)) ^ 2)) := by
          simpa using hcomp.symm

lemma local_defect_g_normalized_abs_has_unit_interval_representative_of_transport
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≠ 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (|local_defect_g μ u v t| / (1 + t ^ 2))
        =
      (|local_defect_g μ u v r| / (1 + r ^ 2)) := by
  rcases lt_or_gt_of_ne ht1 with ht_lt | ht_gt
  · refine ⟨t, ht0, ht_lt, ?_⟩
    rfl
  · let r : ℝ := (t - 1) / (t + 1)
    have ht1_pos : 0 < t - 1 := by linarith
    have ht1p_pos : 0 < t + 1 := by linarith
    have hr0 : 0 < r := by
      dsimp [r]
      exact div_pos ht1_pos ht1p_pos
    have hr1 : r < 1 := by
      dsimp [r]
      exact (div_lt_iff₀ ht1p_pos).2 (by linarith)
    have hrepr : (1 + r) / (1 - r) = t := by
      dsimp [r]
      field_simp
      ring
    have hlift :
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          =
        (|local_defect_g μ u v ((1 + r) / (1 - r))| /
          (1 + ((1 + r) / (1 - r)) ^ 2)) :=
      local_defect_g_normalized_abs_lift_eq_of_transport
        hdim μ u v hu hv huv htransport r hr0 hr1
    refine ⟨r, hr0, hr1, ?_⟩
    simpa [hrepr] using hlift.symm

lemma exists_local_defect_g_ne_zero_in_unit_interval_pre
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

lemma exists_local_defect_g_normalized_abs_ne_zero_in_unit_interval_pre
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2)) ≠ 0 := by
  intro hg_nz
  rcases exists_local_defect_g_ne_zero_in_unit_interval_pre hdim μ u v hu hv huv hg_nz with
    ⟨r, hr0, hr1, hr_nz⟩
  refine ⟨r, hr0, hr1, ?_⟩
  exact div_ne_zero (abs_ne_zero.mpr hr_nz) (by positivity)

lemma local_defect_g_positive_equal_pair_of_no_neq_witness
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hno :
      ¬ ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hg_nz : ∃ t : ℝ, local_defect_g μ u v t ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2))
      ∧
      0 < (|local_defect_g μ u v r| / (1 + r ^ 2)) := by
  rcases
    exists_local_defect_g_normalized_abs_ne_zero_in_unit_interval_pre
      hdim μ u v hu hv huv hg_nz with
    ⟨r, hr0, hr1, hr_nz⟩
  have hEq :
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) :=
    local_defect_g_no_neq_witness_eq_on_unit_interval μ u v hno r hr0 hr1
  have hnonneg : 0 ≤ (|local_defect_g μ u v r| / (1 + r ^ 2)) := by
    positivity
  have hpos : 0 < (|local_defect_g μ u v r| / (1 + r ^ 2)) := by
    exact lt_of_le_of_ne hnonneg (Ne.symm hr_nz)
  exact ⟨r, hr0, hr1, hEq, hpos⟩

lemma local_defect_g_normalized_gap_eq_zero_of_no_neq_witness
    (μ : FrameFunction H) (u v : H)
    (hno :
      ¬ ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ r : ℝ, 0 < r → r < 1 →
      local_defect_g_normalized_gap μ u v r = 0 := by
  intro r hr0 hr1
  have hEq :
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        =
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) :=
    local_defect_g_no_neq_witness_eq_on_unit_interval μ u v hno r hr0 hr1
  dsimp [local_defect_g_normalized_gap]
  exact abs_eq_zero.mpr (sub_eq_zero.mpr hEq)

lemma local_defect_g_positive_zero_gap_pair_of_no_neq_witness
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hno :
      ¬ ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hg_nz : ∃ t : ℝ, local_defect_g μ u v t ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      0 < (|local_defect_g μ u v r| / (1 + r ^ 2)) ∧
      local_defect_g_normalized_gap μ u v r = 0 := by
  rcases
    local_defect_g_positive_equal_pair_of_no_neq_witness
      hdim μ u v hu hv huv hno hg_nz with
    ⟨r, hr0, hr1, hEq, hpos⟩
  refine ⟨r, hr0, hr1, hpos, ?_⟩
  dsimp [local_defect_g_normalized_gap]
  exact abs_eq_zero.mpr (sub_eq_zero.mpr hEq)

lemma local_defect_g_no_neq_witness_false_of_shift_gap_dominance_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (C : ℝ) (hCzero : C = 0)
    (hgap :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          C * (1 + s ^ 2) < local_defect_g_normalized_gap μ u v r)
    (hg_nz : ∃ t : ℝ, local_defect_g μ u v t ≠ 0)
    (hno :
      ¬ ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    False := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  rcases hg_nz with ⟨t0, ht0⟩
  have hker_nz :
      ∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0 := by
    refine ⟨t0, ?_⟩
    intro hk0
    have hrepr :
        swapped_bridge_kernel μ v u 0 t0 =
          -2 * local_defect_g μ u v t0 := by
      simpa using swapped_bridge_kernel_zero_s hdim μ v u hv hu hvu t0
    rw [hrepr] at hk0
    have h2 : (-2 : ℝ) ≠ 0 := by norm_num
    have hg0 : local_defect_g μ u v t0 = 0 := (mul_eq_zero.mp hk0).resolve_left h2
    exact ht0 hg0
  rcases hgap 0 hker_nz with ⟨r, hr0, hr1, hstrict⟩
  have hgap0 :
      local_defect_g_normalized_gap μ u v r = 0 :=
    local_defect_g_normalized_gap_eq_zero_of_no_neq_witness μ u v hno r hr0 hr1
  have hstrict0 : 0 < local_defect_g_normalized_gap μ u v r := by
    simpa [hCzero] using hstrict
  linarith [hstrict0, hgap0]

lemma local_defect_g_no_neq_witness_false_of_shift_gap_dominance_zero_s0
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hgap0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          0 < local_defect_g_normalized_gap μ u v r)
    (hg_nz : ∃ t : ℝ, local_defect_g μ u v t ≠ 0)
    (hno :
      ¬ ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    False := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  rcases hg_nz with ⟨t0, ht0⟩
  have hker_nz :
      ∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0 := by
    refine ⟨t0, ?_⟩
    intro hk0
    have hrepr :
        swapped_bridge_kernel μ v u 0 t0 =
          -2 * local_defect_g μ u v t0 := by
      simpa using swapped_bridge_kernel_zero_s hdim μ v u hv hu hvu t0
    rw [hrepr] at hk0
    have h2 : (-2 : ℝ) ≠ 0 := by norm_num
    have hg0 : local_defect_g μ u v t0 = 0 := (mul_eq_zero.mp hk0).resolve_left h2
    exact ht0 hg0
  rcases hgap0 hker_nz with ⟨r, hr0, hr1, hstrict0⟩
  have hgap0_eq :
      local_defect_g_normalized_gap μ u v r = 0 :=
    local_defect_g_normalized_gap_eq_zero_of_no_neq_witness μ u v hno r hr0 hr1
  linarith [hstrict0, hgap0_eq]

lemma local_defect_g_neq_witness_of_shift_gap_dominance_zero_s0
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hgap0 :
      (∃ t : ℝ, swapped_bridge_kernel μ v u 0 t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          0 < local_defect_g_normalized_gap μ u v r) :
    (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro hg_nz
  by_contra hno
  exact
    local_defect_g_no_neq_witness_false_of_shift_gap_dominance_zero_s0
      hdim μ u v hu hv huv hgap0 hg_nz hno

lemma hadamard_bridge_error_second_diff_noninvariance_of_local_defect_g_margin_pre
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s r : ℝ)
    (hmargin :
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
    (|hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2))
      ≠
    (|hadamard_bridge_error_second_diff μ u v s ((1 - r) / (1 + r))| /
      (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  set φ : ℝ := (1 - r) / (1 + r)
  set A_r : ℝ := |hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2)
  set A_φ : ℝ := |hadamard_bridge_error_second_diff μ u v s φ| / (1 + φ ^ 2)
  set G_r : ℝ := |local_defect_g μ u v r| / (1 + r ^ 2)
  set G_φ : ℝ := |local_defect_g μ u v φ| / (1 + φ ^ 2)
  set E_r : ℝ :=
    (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
      |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
      2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2)
  set E_φ : ℝ :=
    (|hadamard_bridge_error μ u v (s + φ) - hadamard_bridge_error μ u v φ| +
      |hadamard_bridge_error μ u v (s - φ) - hadamard_bridge_error μ u v (-φ)| +
      2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + φ ^ 2)
  have hgap_r : |A_r - G_r| ≤ E_r := by
    simpa [A_r, G_r, E_r] using
      hadamard_bridge_error_second_diff_local_defect_g_normalized_gap_bound
        hdim μ u v hu hv huv s r
  have hgap_φ : |A_φ - G_φ| ≤ E_φ := by
    simpa [A_φ, G_φ, E_φ] using
      hadamard_bridge_error_second_diff_local_defect_g_normalized_gap_bound
        hdim μ u v hu hv huv s φ
  have hmargin' : E_r + E_φ < |G_r - G_φ| := by
    simpa [φ, G_r, G_φ, E_r, E_φ] using hmargin
  intro hEq
  have hA0 : A_r - A_φ = 0 := by
    linarith [hEq]
  have hGG : |G_r - G_φ| ≤ E_r + E_φ := by
    have hrepr : G_r - G_φ = (G_r - A_r) - (G_φ - A_φ) := by
      linarith [hA0]
    rw [hrepr]
    calc
      |(G_r - A_r) - (G_φ - A_φ)|
          ≤ |G_r - A_r| + |G_φ - A_φ| := by
              exact abs_sub (G_r - A_r) (G_φ - A_φ)
      _ = |A_r - G_r| + |A_φ - G_φ| := by
            rw [abs_sub_comm G_r A_r, abs_sub_comm G_φ A_φ]
      _ ≤ E_r + E_φ := add_le_add hgap_r hgap_φ
  linarith [hGG, hmargin']

lemma hadamard_bridge_error_second_diff_noninvariance_of_shift_oscillation_gap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s r : ℝ)
    (hgap :
      hadamard_bridge_error_shift_oscillation_pair μ u v s r <
        local_defect_g_normalized_gap μ u v r) :
    (|hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2))
      ≠
    (|hadamard_bridge_error_second_diff μ u v s ((1 - r) / (1 + r))| /
      (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  simpa [hadamard_bridge_error_shift_oscillation_pair, local_defect_g_normalized_gap] using
    (hadamard_bridge_error_second_diff_noninvariance_of_local_defect_g_margin_pre
      hdim μ u v hu hv huv s r hgap)

lemma hadamard_bridge_error_second_diff_noninvariance_of_shift_oscillation_amplified
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s r κ : ℝ)
    (hκ : κ < 1)
    (hgap_pos : 0 < local_defect_g_normalized_gap μ u v r)
    (hamp :
      hadamard_bridge_error_shift_oscillation_pair μ u v s r ≤
        κ * local_defect_g_normalized_gap μ u v r) :
    (|hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2))
      ≠
    (|hadamard_bridge_error_second_diff μ u v s ((1 - r) / (1 + r))| /
      (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  have hgap_lt :
      hadamard_bridge_error_shift_oscillation_pair μ u v s r <
        local_defect_g_normalized_gap μ u v r := by
    nlinarith [hamp, hκ, hgap_pos]
  exact
    hadamard_bridge_error_second_diff_noninvariance_of_shift_oscillation_gap
      hdim μ u v hu hv huv s r hgap_lt

lemma hadamard_bridge_error_second_diff_noninvariance_witness_of_shift_oscillation_amplified
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (κ : ℝ) (hκ : κ < 1)
    (hamp :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          0 < local_defect_g_normalized_gap μ u v r ∧
          hadamard_bridge_error_shift_oscillation_pair μ u v s r ≤
            κ * local_defect_g_normalized_gap μ u v r) :
    ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2))
          ≠
        (|hadamard_bridge_error_second_diff μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro s hker
  rcases hamp s hker with ⟨r, hr0, hr1, hgap_pos, hamp_r⟩
  refine ⟨r, hr0, hr1, ?_⟩
  exact
    hadamard_bridge_error_second_diff_noninvariance_of_shift_oscillation_amplified
      hdim μ u v hu hv huv s r κ hκ hgap_pos hamp_r

lemma hadamard_bridge_error_second_diff_noninvariance_of_local_defect_g_margin
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s r : ℝ)
    (hmargin :
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
    (|hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2))
      ≠
    (|hadamard_bridge_error_second_diff μ u v s ((1 - r) / (1 + r))| /
      (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  set φ : ℝ := (1 - r) / (1 + r)
  set A_r : ℝ := |hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2)
  set A_φ : ℝ := |hadamard_bridge_error_second_diff μ u v s φ| / (1 + φ ^ 2)
  set G_r : ℝ := |local_defect_g μ u v r| / (1 + r ^ 2)
  set G_φ : ℝ := |local_defect_g μ u v φ| / (1 + φ ^ 2)
  set E_r : ℝ :=
    (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
      |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
      2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2)
  set E_φ : ℝ :=
    (|hadamard_bridge_error μ u v (s + φ) - hadamard_bridge_error μ u v φ| +
      |hadamard_bridge_error μ u v (s - φ) - hadamard_bridge_error μ u v (-φ)| +
      2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + φ ^ 2)
  have hgap_r : |A_r - G_r| ≤ E_r := by
    simpa [A_r, G_r, E_r] using
      hadamard_bridge_error_second_diff_local_defect_g_normalized_gap_bound
        hdim μ u v hu hv huv s r
  have hgap_φ : |A_φ - G_φ| ≤ E_φ := by
    simpa [A_φ, G_φ, E_φ] using
      hadamard_bridge_error_second_diff_local_defect_g_normalized_gap_bound
        hdim μ u v hu hv huv s φ
  have hmargin' : E_r + E_φ < |G_r - G_φ| := by
    simpa [φ, G_r, G_φ, E_r, E_φ] using hmargin
  intro hEq
  have hA0 : A_r - A_φ = 0 := by
    linarith [hEq]
  have hGG : |G_r - G_φ| ≤ E_r + E_φ := by
    have hrepr : G_r - G_φ = (G_r - A_r) - (G_φ - A_φ) := by
      linarith [hA0]
    rw [hrepr]
    calc
      |(G_r - A_r) - (G_φ - A_φ)|
          ≤ |G_r - A_r| + |G_φ - A_φ| := by
              exact abs_sub (G_r - A_r) (G_φ - A_φ)
      _ = |A_r - G_r| + |A_φ - G_φ| := by
            rw [abs_sub_comm G_r A_r, abs_sub_comm G_φ A_φ]
      _ ≤ E_r + E_φ := add_le_add hgap_r hgap_φ
  linarith [hGG, hmargin']

lemma local_shift_oscillation_amplification_factor_of_uniform_margin
    (μ : FrameFunction H) (u v : H) (C s r : ℝ)
    (herr :
      hadamard_bridge_error_shift_oscillation_pair μ u v s r ≤ C * (1 + s ^ 2))
    (hdom :
      C * (1 + s ^ 2) < local_defect_g_normalized_gap μ u v r) :
    ∃ κ : ℝ, κ < 1 ∧
      hadamard_bridge_error_shift_oscillation_pair μ u v s r ≤
        κ * local_defect_g_normalized_gap μ u v r := by
  set G : ℝ := local_defect_g_normalized_gap μ u v r
  have hshift_nonneg : 0 ≤ hadamard_bridge_error_shift_oscillation_pair μ u v s r := by
    dsimp [hadamard_bridge_error_shift_oscillation_pair]
    positivity
  have hCterm_nonneg : 0 ≤ C * (1 + s ^ 2) := by
    exact le_trans hshift_nonneg herr
  have hGpos : 0 < G := by
    have hdom' : C * (1 + s ^ 2) < G := by
      simpa [G] using hdom
    exact lt_of_le_of_lt hCterm_nonneg hdom'
  refine ⟨(C * (1 + s ^ 2)) / G, ?_, ?_⟩
  · have hlt : C * (1 + s ^ 2) < G := by
      simpa [G] using hdom
    exact (div_lt_iff₀ hGpos).2 (by linarith [hlt])
  · have hkappa :
        ((C * (1 + s ^ 2)) / G) * local_defect_g_normalized_gap μ u v r =
          C * (1 + s ^ 2) := by
      calc
        ((C * (1 + s ^ 2)) / G) * local_defect_g_normalized_gap μ u v r
            = ((C * (1 + s ^ 2)) / G) * G := by simp [G]
        _ = C * (1 + s ^ 2) := by
              field_simp [hGpos.ne']
    calc
      hadamard_bridge_error_shift_oscillation_pair μ u v s r
          ≤ C * (1 + s ^ 2) := herr
      _ = ((C * (1 + s ^ 2)) / G) * local_defect_g_normalized_gap μ u v r := by
            symm
            exact hkappa

lemma hadamard_bridge_error_second_diff_noninvariance_witness_of_uniform_shift_margin
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (C : ℝ)
    (herr :
      ∀ s r : ℝ,
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
          ≤ C * (1 + s ^ 2))
    (hgap :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          C * (1 + s ^ 2) <
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
  rcases hgap s hker with ⟨r, hr0, hr1, hdom⟩
  have herr_sr :
      hadamard_bridge_error_shift_oscillation_pair μ u v s r ≤ C * (1 + s ^ 2) := by
    simpa [hadamard_bridge_error_shift_oscillation_pair] using herr s r
  rcases
    local_shift_oscillation_amplification_factor_of_uniform_margin
      μ u v C s r herr_sr (by simpa [local_defect_g_normalized_gap] using hdom) with
    ⟨κ, hκ, hamp⟩
  have hshift_nonneg : 0 ≤ hadamard_bridge_error_shift_oscillation_pair μ u v s r := by
    dsimp [hadamard_bridge_error_shift_oscillation_pair]
    positivity
  have hCterm_nonneg : 0 ≤ C * (1 + s ^ 2) := by
    exact le_trans hshift_nonneg herr_sr
  have hgap_pos :
      0 < local_defect_g_normalized_gap μ u v r := by
    exact lt_of_le_of_lt hCterm_nonneg (by simpa [local_defect_g_normalized_gap] using hdom)
  refine ⟨r, hr0, hr1, ?_⟩
  exact
    hadamard_bridge_error_second_diff_noninvariance_of_shift_oscillation_amplified
      hdim μ u v hu hv huv s r κ hκ hgap_pos hamp

lemma hadamard_bridge_error_second_diff_transport_of_uniform_shift_margin
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (C : ℝ)
    (herr :
      ∀ s r : ℝ,
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
          ≤ C * (1 + s ^ 2))
    (htransport_gap :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ s r : ℝ, 0 < r → r < 1 →
      (|hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2))
        ≤
      (|hadamard_bridge_error_second_diff μ u v s ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro s r hr0 hr1
  have herr_sr :
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
        ≤ C * (1 + s ^ 2) := herr s r
  have hdom :
      (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
        ≤
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := htransport_gap s r hr0 hr1
  have hmargin :
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        +
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
        ≤
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    linarith [herr_sr, hdom]
  set φ : ℝ := (1 - r) / (1 + r)
  set A_r : ℝ := |hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2)
  set A_φ : ℝ := |hadamard_bridge_error_second_diff μ u v s φ| / (1 + φ ^ 2)
  set G_r : ℝ := |local_defect_g μ u v r| / (1 + r ^ 2)
  set G_φ : ℝ := |local_defect_g μ u v φ| / (1 + φ ^ 2)
  set E_r : ℝ :=
    (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
      |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
      2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2)
  set E_φ : ℝ :=
    (|hadamard_bridge_error μ u v (s + φ) - hadamard_bridge_error μ u v φ| +
      |hadamard_bridge_error μ u v (s - φ) - hadamard_bridge_error μ u v (-φ)| +
      2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + φ ^ 2)
  have hA_r : A_r ≤ G_r + E_r := by
    simpa [A_r, G_r, E_r] using
      hadamard_bridge_error_second_diff_normalized_from_local_defect_g_bound
        hdim μ u v hu hv huv s r
  have hG_φ : G_φ ≤ A_φ + E_φ := by
    simpa [G_φ, A_φ, E_φ] using
      local_defect_g_normalized_abs_from_hadamard_second_diff_bound
        hdim μ u v hu hv huv s φ
  have hmargin' : G_r + E_r + E_φ ≤ G_φ := by
    simpa [φ, G_r, G_φ, E_r, E_φ] using hmargin
  have hE_φ_nonneg : 0 ≤ E_φ := by
    dsimp [E_φ]
    positivity
  have hA : A_r ≤ A_φ := by
    have hmid : G_r + E_r ≤ A_φ := by
      have haux : G_r + E_r + E_φ ≤ A_φ + E_φ := le_trans hmargin' hG_φ
      nlinarith [haux, hE_φ_nonneg]
    exact le_trans hA_r hmid
  simpa [A_r, A_φ, φ] using hA

lemma hadamard_bridge_error_zero_all_of_local_defect_g_uniform_shift_margin
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (C : ℝ)
    (herr :
      ∀ s r : ℝ,
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
          ≤ C * (1 + s ^ 2))
    (htransport_gap :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hgap :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          C * (1 + s ^ 2) <
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
      (hadamard_bridge_error_second_diff_transport_of_uniform_shift_margin
        hdim μ u v hu hv huv C herr htransport_gap s r hr0 hr1)
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
      (hadamard_bridge_error_second_diff_noninvariance_witness_of_uniform_shift_margin
        hdim μ u v hu hv huv C herr hgap s hker) with
      ⟨r, hr0, hr1, hne⟩
    refine ⟨r, hr0, hr1, ?_⟩
    simpa [hadamard_bridge_error_second_diff] using hne
  exact
    hadamard_bridge_error_zero_all_of_second_diff_transport_neq
      hdim μ u v hu hv huv htransportE hneqE

lemma hadamard_bridge_error_zero_all_of_local_defect_g_shift_bound_dominance
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
    (hgap :
      let C : ℝ := Classical.choose
        (hadamard_bridge_error_shift_error_double_bundle_uniform_bound
          hdim μ u v hu hv huv)
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          C * (1 + s ^ 2) <
            |(|local_defect_g μ u v r| / (1 + r ^ 2)) -
              (|local_defect_g μ u v ((1 - r) / (1 + r))| /
                (1 + ((1 - r) / (1 + r)) ^ 2))|) :
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
  have herr :
      ∀ s r : ℝ,
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
          ≤ C * (1 + s ^ 2) := hCspec.2
  have htransport_gap' :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    simpa [C] using htransport_gap
  have hgap' :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          C * (1 + s ^ 2) <
            |(|local_defect_g μ u v r| / (1 + r ^ 2)) -
              (|local_defect_g μ u v ((1 - r) / (1 + r))| /
                (1 + ((1 - r) / (1 + r)) ^ 2))| := by
    simpa [C] using hgap
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_uniform_shift_margin
      hdim μ u v hu hv huv C herr htransport_gap' hgap'

lemma local_defect_g_strict_gap_of_transport_neq
    (μ : FrameFunction H) (u v : H) (C s r : ℝ)
    (htransport :
      (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
        ≤
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hneq :
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        ≠
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2))) :
    C * (1 + s ^ 2) ≤
      |(|local_defect_g μ u v r| / (1 + r ^ 2)) -
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))| := by
  clear hneq
  set G_r : ℝ := |local_defect_g μ u v r| / (1 + r ^ 2)
  set G_φ : ℝ :=
    |local_defect_g μ u v ((1 - r) / (1 + r))| /
      (1 + ((1 - r) / (1 + r)) ^ 2)
  have hle : C * (1 + s ^ 2) ≤ G_φ - G_r := by
    linarith [htransport]
  have hdiff_le_abs : G_φ - G_r ≤ |G_r - G_φ| := by
    have h1 : G_φ - G_r ≤ |G_φ - G_r| := le_abs_self (G_φ - G_r)
    have h2 : |G_φ - G_r| = |G_r - G_φ| := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (abs_sub_comm G_φ G_r)
    linarith
  have hfinal : C * (1 + s ^ 2) ≤ |G_r - G_φ| := le_trans hle hdiff_le_abs
  simpa [G_r, G_φ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hfinal

lemma local_defect_g_shift_bound_transport_forces_C_nonpos
    (μ : FrameFunction H) (u v : H) (C : ℝ)
    (htransport_gap :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    C ≤ 0 := by
  by_contra hC_nonpos
  have hCpos : 0 < C := lt_of_not_ge hC_nonpos
  set r0 : ℝ := (1 / 2 : ℝ)
  have hr0 : 0 < r0 := by
    dsimp [r0]
    norm_num
  have hr1 : r0 < 1 := by
    dsimp [r0]
    norm_num
  set G : ℝ := |local_defect_g μ u v r0| / (1 + r0 ^ 2)
  set H : ℝ :=
    |local_defect_g μ u v ((1 - r0) / (1 + r0))| /
      (1 + ((1 - r0) / (1 + r0)) ^ 2)
  have hbound : ∀ s : ℝ, G + C * (1 + s ^ 2) ≤ H := by
    intro s
    simpa [G, H] using htransport_gap s r0 hr0 hr1
  set s0 : ℝ := (|H - G| + 1) / C
  have hs0_nonneg : 0 ≤ s0 := by
    dsimp [s0]
    exact div_nonneg (by positivity) (le_of_lt hCpos)
  have hs0_le : s0 ≤ 1 + s0 ^ 2 := by
    nlinarith [hs0_nonneg]
  have hCs_le : C * s0 ≤ C * (1 + s0 ^ 2) := by
    exact mul_le_mul_of_nonneg_left hs0_le (le_of_lt hCpos)
  have hCs_eq : C * s0 = |H - G| + 1 := by
    dsimp [s0]
    field_simp [hCpos.ne']
  have hlower :
      H - G + 1 ≤ C * (1 + s0 ^ 2) := by
    have hHG_le_abs : H - G ≤ |H - G| := by exact le_abs_self (H - G)
    have h1 : H - G + 1 ≤ |H - G| + 1 := by linarith
    have h2 : |H - G| + 1 ≤ C * (1 + s0 ^ 2) := by
      calc
        |H - G| + 1 = C * s0 := by exact hCs_eq.symm
        _ ≤ C * (1 + s0 ^ 2) := hCs_le
    linarith
  have hs0_bound : G + C * (1 + s0 ^ 2) ≤ H := hbound s0
  have hcontra : H + 1 ≤ H := by
    linarith [hlower, hs0_bound]
  linarith [hcontra]

lemma local_defect_g_shift_bound_transport_forces_C_zero
    (μ : FrameFunction H) (u v : H) (C : ℝ)
    (hCnn : 0 ≤ C)
    (htransport_gap :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    C = 0 := by
  have hCnonpos :
      C ≤ 0 :=
    local_defect_g_shift_bound_transport_forces_C_nonpos
      μ u v C htransport_gap
  linarith

lemma local_defect_g_transport_of_shift_bound_transport
    (μ : FrameFunction H) (u v : H) (C : ℝ)
    (hCzero : C = 0)
    (htransport_gap :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ r : ℝ, 0 < r → r < 1 →
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        ≤
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro r hr0 hr1
  simpa [hCzero] using htransport_gap 0 r hr0 hr1

lemma local_defect_g_neq_witness_of_shift_gap_dominance_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (C : ℝ) (hCzero : C = 0)
    (hgap :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          C * (1 + s ^ 2) < local_defect_g_normalized_gap μ u v r) :
    (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro hg_nz
  by_contra hno
  exact
    local_defect_g_no_neq_witness_false_of_shift_gap_dominance_zero
      hdim μ u v hu hv huv C hCzero hgap hg_nz hno

lemma local_defect_g_neq_witness_of_shift_bound_dominance
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (C : ℝ) (hCzero : C = 0)
    (hgap :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          C * (1 + s ^ 2) <
            |(|local_defect_g μ u v r| / (1 + r ^ 2)) -
              (|local_defect_g μ u v ((1 - r) / (1 + r))| /
                (1 + ((1 - r) / (1 + r)) ^ 2))|) :
    (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  have hgap' :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          C * (1 + s ^ 2) < local_defect_g_normalized_gap μ u v r := by
    intro s hker
    rcases hgap s hker with ⟨r, hr0, hr1, hstrict⟩
    refine ⟨r, hr0, hr1, ?_⟩
    simpa [local_defect_g_normalized_gap] using hstrict
  exact
    local_defect_g_neq_witness_of_shift_gap_dominance_zero
      hdim μ u v hu hv huv C hCzero hgap'

lemma local_defect_g_transport_neq_witness_of_shift_bound_dominance
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (C : ℝ) (hCnn : 0 ≤ C)
    (htransport_gap :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2)) + C * (1 + s ^ 2)
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hgap :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          C * (1 + s ^ 2) <
            |(|local_defect_g μ u v r| / (1 + r ^ 2)) -
              (|local_defect_g μ u v ((1 - r) / (1 + r))| /
                (1 + ((1 - r) / (1 + r)) ^ 2))|) :
    (∀ r : ℝ, 0 < r → r < 1 →
      (|local_defect_g μ u v r| / (1 + r ^ 2))
        ≤
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)))
    ∧
    ((∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≠
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) := by
  have hCzero : C = 0 :=
    local_defect_g_shift_bound_transport_forces_C_zero
      μ u v C hCnn htransport_gap
  constructor
  · exact local_defect_g_transport_of_shift_bound_transport μ u v C hCzero htransport_gap
  · exact
      local_defect_g_neq_witness_of_shift_bound_dominance
        hdim μ u v hu hv huv C hCzero hgap

lemma hadamard_bridge_error_zero_all_of_local_defect_g_shift_bound_transport_neq
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
  have hgap' :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          C * (1 + s ^ 2) <
            |(|local_defect_g μ u v r| / (1 + r ^ 2)) -
              (|local_defect_g μ u v ((1 - r) / (1 + r))| /
                (1 + ((1 - r) / (1 + r)) ^ 2))| := by
    intro s hker
    rcases hneq_gap s hker with ⟨r, hr0, hr1, hneq⟩
    refine ⟨r, hr0, hr1, ?_⟩
    have hpos :
        0 <
          |(|local_defect_g μ u v r| / (1 + r ^ 2)) -
            (|local_defect_g μ u v ((1 - r) / (1 + r))| /
              (1 + ((1 - r) / (1 + r)) ^ 2))| := by
      exact abs_pos.mpr (sub_ne_zero.mpr hneq)
    simpa [hCzero] using hpos
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_shift_bound_dominance
      hdim μ u v hu hv huv
      (by simpa [C] using htransport_gap')
      (by simpa [C] using hgap')

lemma exists_local_defect_g_ne_zero_of_swapped_kernel_ne_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s : ℝ)
    (hker_nz : ∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) :
    ∃ t : ℝ, local_defect_g μ u v t ≠ 0 := by
  by_contra hg_all_zero
  push_neg at hg_all_zero
  have hE0 :
      ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
    intro x
    by_cases h1px : 1 + x ≠ 0
    · have hres :
          hadamard_residual_one μ u v x = 0 := by
        have hmob :=
          hadamard_residual_one_eq_mobius_scaled_local_defect
            hdim μ u v hu hv huv x h1px
        rw [hg_all_zero ((1 - x) / (1 + x)), mul_zero] at hmob
        exact hmob
      unfold hadamard_bridge_error
      rw [hres, hg_all_zero x]
      ring
    · have hx0 : 1 + x = 0 := by
        by_contra hx0
        exact h1px hx0
      have hx : x = -1 := by linarith [hx0]
      simpa [hx] using hadamard_bridge_error_neg_one hdim μ u v hu hv huv
  rcases hker_nz with ⟨t, ht⟩
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hker_repr :
      swapped_bridge_kernel μ v u s t =
        2 * hadamard_bridge_error_second_diff μ u v s t := by
    unfold hadamard_bridge_error_second_diff
    simpa [add_assoc, add_left_comm, add_comm] using
      swapped_bridge_kernel_eq_two_hadamard_bridge_error_second_diff
        hdim μ v u hv hu hvu s t
  have hE2_zero : hadamard_bridge_error_second_diff μ u v s t = 0 := by
    unfold hadamard_bridge_error_second_diff
    rw [hE0 (s + t), hE0 (s - t), hE0 s]
    ring
  have hk0 : swapped_bridge_kernel μ v u s t = 0 := by
    rw [hker_repr, hE2_zero]
    ring
  exact ht hk0

lemma hadamard_bridge_error_zero_all_of_local_defect_g_shift_bound_transport_global_neq
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
    (hneq_g :
      (∃ t : ℝ, local_defect_g μ u v t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have hneq_gap :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|local_defect_g μ u v r| / (1 + r ^ 2))
            ≠
          (|local_defect_g μ u v ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    intro s hker
    have hg_nz :
        ∃ t : ℝ, local_defect_g μ u v t ≠ 0 :=
      exists_local_defect_g_ne_zero_of_swapped_kernel_ne_zero
        hdim μ u v hu hv huv s hker
    exact hneq_g hg_nz
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_shift_bound_transport_neq
      hdim μ u v hu hv huv htransport_gap hneq_gap

lemma hadamard_bridge_error_second_diff_transport_of_local_defect_g_transport_margin
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_margin :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          +
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
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ s r : ℝ, 0 < r → r < 1 →
      (|hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2))
        ≤
      (|hadamard_bridge_error_second_diff μ u v s ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro s r hr0 hr1
  set φ : ℝ := (1 - r) / (1 + r)
  set A_r : ℝ := |hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2)
  set A_φ : ℝ := |hadamard_bridge_error_second_diff μ u v s φ| / (1 + φ ^ 2)
  set G_r : ℝ := |local_defect_g μ u v r| / (1 + r ^ 2)
  set G_φ : ℝ := |local_defect_g μ u v φ| / (1 + φ ^ 2)
  set E_r : ℝ :=
    (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
      |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
      2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2)
  set E_φ : ℝ :=
    (|hadamard_bridge_error μ u v (s + φ) - hadamard_bridge_error μ u v φ| +
      |hadamard_bridge_error μ u v (s - φ) - hadamard_bridge_error μ u v (-φ)| +
      2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + φ ^ 2)
  have hA_r : A_r ≤ G_r + E_r := by
    simpa [A_r, G_r, E_r] using
      hadamard_bridge_error_second_diff_normalized_from_local_defect_g_bound
        hdim μ u v hu hv huv s r
  have hG_φ : G_φ ≤ A_φ + E_φ := by
    simpa [A_φ, G_φ, E_φ] using
      local_defect_g_normalized_abs_from_hadamard_second_diff_bound
        hdim μ u v hu hv huv s φ
  have hmargin : G_r + E_r + E_φ ≤ G_φ := by
    simpa [φ, G_r, G_φ, E_r, E_φ] using htransport_margin s r hr0 hr1
  have hmid : G_r + E_r ≤ G_φ - E_φ := by
    linarith [hmargin]
  have hA_φ : G_φ - E_φ ≤ A_φ := by
    linarith [hG_φ]
  have hA : A_r ≤ A_φ := by
    linarith [hA_r, hmid, hA_φ]
  simpa [A_r, A_φ, φ] using hA

lemma hadamard_bridge_error_zero_all_of_local_defect_g_transport_margin_neq
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_margin :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          +
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
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hneqE :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|hadamard_bridge_error μ u v (s + r) +
              hadamard_bridge_error μ u v (s - r) -
              2 * hadamard_bridge_error μ u v s| / (1 + r ^ 2))
            ≠
          (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) +
              hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
              2 * hadamard_bridge_error μ u v s| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
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
      (hadamard_bridge_error_second_diff_transport_of_local_defect_g_transport_margin
        hdim μ u v hu hv huv htransport_margin s r hr0 hr1)
  exact
    hadamard_bridge_error_zero_all_of_second_diff_transport_neq
      hdim μ u v hu hv huv htransportE hneqE

lemma hadamard_bridge_error_zero_all_of_local_defect_g_transport_margin
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_margin :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          +
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
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
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
    rcases hmargin s hker with ⟨r, hr0, hr1, hmr⟩
    refine ⟨r, hr0, hr1, ?_⟩
    have hne :
        (|hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2))
          ≠
        (|hadamard_bridge_error_second_diff μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
      exact
        hadamard_bridge_error_second_diff_noninvariance_of_local_defect_g_margin
          hdim μ u v hu hv huv s r hmr
    simpa [hadamard_bridge_error_second_diff] using hne
  exact
    hadamard_bridge_error_zero_all_of_local_defect_g_transport_margin_neq
      hdim μ u v hu hv huv htransport_margin hneqE


end
