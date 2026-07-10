import Gleason.Continuity.Defect.KernelTransport

noncomputable section

open GleasonBridge RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

lemma hadamard_bridge_error_inversion_normalized
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    {r : ℝ} (hr : r ≠ 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    N r = - N (-(1 / r)) ∧ N (-r) = -N (1 / r) := by
  intro N
  have h1 : hadamard_bridge_error μ u v r = -r ^ 2 * hadamard_bridge_error μ u v (-(1 / r)) := by
    exact hadamard_bridge_error_inversion hdim μ u v hu hv huv hr
  have h2 : hadamard_bridge_error μ u v (-r) = -r ^ 2 * hadamard_bridge_error μ u v (1 / r) := by
    have h := hadamard_bridge_error_inversion hdim μ u v hu hv huv (neg_ne_zero.mpr hr)
    simpa [neg_sq] using h
  have hden1 : 1 + (-(1 / r) : ℝ) ^ 2 = (1 + r ^ 2) / r ^ 2 := by
    field_simp [hr]
    ring
  have hden2 : 1 + (1 / r : ℝ) ^ 2 = (1 + r ^ 2) / r ^ 2 := by
    field_simp [hr]
    ring
  have hr2_ne : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  constructor
  · dsimp [N]
    rw [hden1]
    field_simp [hr2_ne]
    linarith [h1]
  · dsimp [N]
    rw [hden2]
    field_simp [hr2_ne]
    linarith [h2]

lemma hadamard_bridge_error_max_abs_inversion
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    {r : ℝ} (hr : r ≠ 0) :
    max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| =
      r ^ 2 * max
        |hadamard_bridge_error μ u v (1 / r)|
        |hadamard_bridge_error μ u v (-(1 / r))| := by
  have h1 : hadamard_bridge_error μ u v r = -r ^ 2 * hadamard_bridge_error μ u v (-(1 / r)) := by
    exact hadamard_bridge_error_inversion hdim μ u v hu hv huv hr
  have h2 : hadamard_bridge_error μ u v (-r) = -r ^ 2 * hadamard_bridge_error μ u v (1 / r) := by
    have h := hadamard_bridge_error_inversion hdim μ u v hu hv huv (neg_ne_zero.mpr hr)
    simpa [neg_sq] using h
  have hr2_nn : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have habs1 :
      |hadamard_bridge_error μ u v r| =
        r ^ 2 * |hadamard_bridge_error μ u v (-(1 / r))| := by
    rw [h1, abs_mul, abs_neg, abs_of_nonneg hr2_nn]
  have habs2 :
      |hadamard_bridge_error μ u v (-r)| =
        r ^ 2 * |hadamard_bridge_error μ u v (1 / r)| := by
    rw [h2, abs_mul, abs_neg, abs_of_nonneg hr2_nn]
  calc
    max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)|
        =
      max
        (r ^ 2 * |hadamard_bridge_error μ u v (-(1 / r))|)
        (r ^ 2 * |hadamard_bridge_error μ u v (1 / r)|) := by
          rw [habs1, habs2]
    _ =
      r ^ 2 * max
        |hadamard_bridge_error μ u v (-(1 / r))|
        |hadamard_bridge_error μ u v (1 / r)| := by
          simpa using (mul_max_of_nonneg
            |hadamard_bridge_error μ u v (-(1 / r))|
            |hadamard_bridge_error μ u v (1 / r)| hr2_nn).symm
    _ =
      r ^ 2 * max
        |hadamard_bridge_error μ u v (1 / r)|
        |hadamard_bridge_error μ u v (-(1 / r))| := by
          rw [max_comm]

lemma hadamard_bridge_error_normalized_gauge_inversion_invariant
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    {r : ℝ} (hr : r ≠ 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let G : ℝ → ℝ := fun x => max |N x + N (-x)| |(N x - N (-x)) / 2|
    G (1 / r) = G r := by
  intro N G
  rcases hadamard_bridge_error_inversion_normalized hdim μ u v hu hv huv hr with
    ⟨hNr, hNneg⟩
  have hNr' : N (-(1 / r)) = -N r := by linarith [hNr]
  have hNneg' : N (1 / r) = -N (-r) := by linarith [hNneg]
  have hsum :
      |N (1 / r) + N (-(1 / r))| = |N r + N (-r)| := by
    have hsum0 : N (1 / r) + N (-(1 / r)) = -(N r + N (-r)) := by
      rw [hNneg', hNr']
      ring_nf
    rw [hsum0, abs_neg]
  have hdiff :
      |(N (1 / r) - N (-(1 / r))) / 2| = |(N r - N (-r)) / 2| := by
    have hdiff0 : (N (1 / r) - N (-(1 / r))) / 2 = (N r - N (-r)) / 2 := by
      rw [hNneg', hNr']
      ring
    exact congrArg abs hdiff0
  dsimp [G]
  rw [hsum, hdiff]

lemma hadamard_bridge_error_mobius_normalized_symm_antisymm
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let φ : ℝ := (1 - r) / (1 + r)
    let S : ℝ := N r + N (-r)
    let A : ℝ := N r - N (-r)
    let Sφ : ℝ := N φ + N (-φ)
    let Aφ : ℝ := N φ - N (-φ)
    Sφ = -A / 2 ∧ Aφ = -2 * S := by
  intro N φ S A Sφ Aφ
  rcases hadamard_bridge_error_mobius_normalized hdim μ u v hu hv huv r h1pr with
    ⟨hNφ, hNnegφ⟩
  constructor
  · dsimp [S, A, Sφ]
    linarith [hNφ, hNnegφ]
  · dsimp [S, A, Aφ]
    linarith [hNφ, hNnegφ]

lemma hadamard_bridge_error_mobius_normalized_invariant
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let φ : ℝ := (1 - r) / (1 + r)
    let G : ℝ → ℝ := fun x => max |N x + N (-x)| |(N x - N (-x)) / 2|
    G φ = G r := by
  intro N φ G
  rcases hadamard_bridge_error_mobius_normalized_symm_antisymm hdim μ u v hu hv huv r h1pr with
    ⟨hSφ, hAφ⟩
  have hSφ' : N φ + N (-φ) = -(N r - N (-r)) / 2 := by
    simpa [N, φ] using hSφ
  have hAφ' : N φ - N (-φ) = -2 * (N r + N (-r)) := by
    simpa [N, φ] using hAφ
  have h1 : |N φ + N (-φ)| = |(N r - N (-r)) / 2| := by
    have h1' : |N φ + N (-φ)| = |(N (-r) - N r) / 2| := by
      simpa [abs_neg] using congrArg abs hSφ'
    have hrhs : |(N (-r) - N r) / 2| = |(N r - N (-r)) / 2| := by
      have : (N (-r) - N r) / 2 = -((N r - N (-r)) / 2) := by ring
      rw [this, abs_neg]
    exact h1'.trans hrhs
  have h2 : |(N φ - N (-φ)) / 2| = |N r + N (-r)| := by
    have hAhalf : (N φ - N (-φ)) / 2 = -(N r + N (-r)) := by
      linarith [hAφ']
    have h2' : |(N φ - N (-φ)) / 2| = |-N (-r) + -N r| := by
      simpa using congrArg abs hAhalf
    have hrhs : |-N (-r) + -N r| = |N r + N (-r)| := by
      have : -N (-r) + -N r = -(N r + N (-r)) := by ring
      rw [this, abs_neg]
    exact h2'.trans hrhs
  dsimp [G]
  rw [h1, h2]
  exact max_comm _ _

lemma hadamard_bridge_error_normalized_gauge_even
    (μ : FrameFunction H) (u v : H) (x : ℝ) :
    let N : ℝ → ℝ := fun t => hadamard_bridge_error μ u v t / (1 + t ^ 2)
    let G : ℝ → ℝ := fun t => max |N t + N (-t)| |(N t - N (-t)) / 2|
    G (-x) = G x := by
  intro N G
  dsimp [G]
  have hsum :
      |N (-x) + N (-(-x))| = |N x + N (-x)| := by
    simpa [add_comm, add_left_comm, add_assoc]
  have hdiff :
      |(N (-x) - N (-(-x))) / 2| = |(N x - N (-x)) / 2| := by
    have hneg : (N (-x) - N (-(-x))) / 2 = -((N x - N (-x)) / 2) := by
      ring_nf
    rw [hneg, abs_neg]
  rw [hsum, hdiff]

lemma hadamard_bridge_error_mobius_normalized_invariant_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let N : ℝ → ℝ := fun t => hadamard_bridge_error μ u v t / (1 + t ^ 2)
    let φ : ℝ := (1 - r) / (1 + r)
    let G : ℝ → ℝ := fun t => max |N t + N (-t)| |(N t - N (-t)) / 2|
    G (-φ) = G r := by
  intro N φ G
  have hφ :
      G φ = G r := by
    simpa [N, φ, G] using
      hadamard_bridge_error_mobius_normalized_invariant hdim μ u v hu hv huv r h1pr
  have heven :
      G (-φ) = G φ := by
    simpa [N, G] using hadamard_bridge_error_normalized_gauge_even μ u v φ
  exact heven.trans hφ

lemma hadamard_bridge_error_normalized_gauge_uniform_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
      let G : ℝ → ℝ := fun x => max |N x + N (-x)| |(N x - N (-x)) / 2|
      ∀ r : ℝ, G r ≤ C := by
  rcases hadamard_bridge_error_growth_bound hdim μ u v hu hv huv with ⟨C0, hC0nn, hC0⟩
  refine ⟨2 * C0, by nlinarith, ?_⟩
  intro N G r
  have hden_pos : 0 < 1 + r ^ 2 := by positivity
  have hNr : |N r| ≤ C0 := by
    have hdiv : |hadamard_bridge_error μ u v r| / (1 + r ^ 2) ≤ C0 := by
      exact (div_le_iff₀ hden_pos).2
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hC0 r)
    have habs : |N r| = |hadamard_bridge_error μ u v r| / (1 + r ^ 2) := by
      dsimp [N]
      rw [abs_div, abs_of_pos hden_pos]
    rw [habs]
    exact hdiv
  have hden_neg_pos : 0 < 1 + (-r) ^ 2 := by positivity
  have hNneg : |N (-r)| ≤ C0 := by
    have hdiv' : |hadamard_bridge_error μ u v (-r)| / (1 + (-r) ^ 2) ≤ C0 := by
      exact (div_le_iff₀ hden_neg_pos).2
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using hC0 (-r))
    have hdiv : |hadamard_bridge_error μ u v (-r)| / (1 + r ^ 2) ≤ C0 := by
      simpa [neg_sq] using hdiv'
    have habs : |N (-r)| = |hadamard_bridge_error μ u v (-r)| / (1 + r ^ 2) := by
      dsimp [N]
      rw [neg_sq, abs_div, abs_of_pos hden_pos]
    rw [habs]
    exact hdiv
  have hsum :
      |N r + N (-r)| ≤ 2 * C0 := by
    calc
      |N r + N (-r)| ≤ |N r| + |N (-r)| := abs_add_le _ _
      _ ≤ C0 + C0 := by linarith [hNr, hNneg]
      _ = 2 * C0 := by ring
  have hdiffC0 :
      |(N r - N (-r)) / 2| ≤ C0 := by
    calc
      |(N r - N (-r)) / 2| = |N r - N (-r)| / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (|N r| + |N (-r)|) / 2 := by
        gcongr
        exact abs_sub (N r) (N (-r))
      _ ≤ (C0 + C0) / 2 := by
        gcongr
      _ = C0 := by ring
  have hdiff :
      |(N r - N (-r)) / 2| ≤ 2 * C0 := by
    nlinarith [hdiffC0, hC0nn]
  dsimp [G]
  exact max_le hsum hdiff

lemma hadamard_mobius_neg_iter_two
    (r : ℝ) (h1pr : 1 + r ≠ 0) (hr : r ≠ 0) :
    let T : ℝ → ℝ := fun x => -((1 - x) / (1 + x))
    T (T r) = -(1 / r) := by
  intro T
  dsimp [T]
  field_simp [h1pr, hr]
  have hnum : 1 + r - -(1 - r) = (2 : ℝ) := by ring
  rw [hnum]
  have hden : 1 + r + -(1 - r) = 2 * r := by ring
  rw [hden]
  field_simp [hr]

lemma hadamard_bridge_error_pair_zero_iff_max_zero
    (μ : FrameFunction H) (u v : H) (r : ℝ) :
    (hadamard_bridge_error μ u v r = 0 ∧ hadamard_bridge_error μ u v (-r) = 0)
      ↔
    max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| = 0 := by
  constructor
  · intro h
    rw [h.1, h.2]
    simp
  · intro hm
    have hEr_abs : |hadamard_bridge_error μ u v r| = 0 := by
      have hle : |hadamard_bridge_error μ u v r|
          ≤ max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| :=
        le_max_left _ _
      linarith [hm, hle, abs_nonneg (hadamard_bridge_error μ u v r)]
    have hEneg_abs : |hadamard_bridge_error μ u v (-r)| = 0 := by
      have hle : |hadamard_bridge_error μ u v (-r)|
          ≤ max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| :=
        le_max_right _ _
      linarith [hm, hle, abs_nonneg (hadamard_bridge_error μ u v (-r))]
    exact ⟨abs_eq_zero.mp hEr_abs, abs_eq_zero.mp hEneg_abs⟩

lemma hadamard_bridge_error_pair_zero_iff_normalized_gauge_zero
    (μ : FrameFunction H) (u v : H) (r : ℝ) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let G : ℝ → ℝ := fun x => max |N x + N (-x)| |(N x - N (-x)) / 2|
    (hadamard_bridge_error μ u v r = 0 ∧ hadamard_bridge_error μ u v (-r) = 0)
      ↔
    G r = 0 := by
  intro N G
  constructor
  · intro hpair
    have hNr : N r = 0 := by
      simp [N, hpair.1]
    have hNneg : N (-r) = 0 := by
      simp [N, hpair.2]
    dsimp [G]
    simp [hNr, hNneg]
  · intro hG
    have hmax0 : max |N r + N (-r)| |(N r - N (-r)) / 2| = 0 := by
      simpa [G] using hG
    have hsum_abs : |N r + N (-r)| = 0 := by
      have hle : |N r + N (-r)| ≤ max |N r + N (-r)| |(N r - N (-r)) / 2| := le_max_left _ _
      linarith [hmax0, hle, abs_nonneg (N r + N (-r))]
    have hdiff_abs : |(N r - N (-r)) / 2| = 0 := by
      have hle : |(N r - N (-r)) / 2| ≤ max |N r + N (-r)| |(N r - N (-r)) / 2| := le_max_right _ _
      linarith [hmax0, hle, abs_nonneg ((N r - N (-r)) / 2)]
    have hsum0 : N r + N (-r) = 0 := abs_eq_zero.mp hsum_abs
    have hdiff0 : (N r - N (-r)) / 2 = 0 := abs_eq_zero.mp hdiff_abs
    have hNr0 : N r = 0 := by linarith [hsum0, hdiff0]
    have hNneg0 : N (-r) = 0 := by linarith [hsum0, hdiff0]
    have h1r2_ne : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
    have hEr_div : hadamard_bridge_error μ u v r / (1 + r ^ 2) = 0 := by
      simpa [N] using hNr0
    have hEneg_div : hadamard_bridge_error μ u v (-r) / (1 + r ^ 2) = 0 := by
      simpa [N, neg_sq] using hNneg0
    have hEr : hadamard_bridge_error μ u v r = 0 :=
      (div_eq_zero_iff.mp hEr_div).resolve_right h1r2_ne
    have hEneg : hadamard_bridge_error μ u v (-r) = 0 :=
      (div_eq_zero_iff.mp hEneg_div).resolve_right h1r2_ne
    exact ⟨hEr, hEneg⟩

lemma hadamard_bridge_error_normalized_gauge_one_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let G : ℝ → ℝ := fun x => max |N x + N (-x)| |(N x - N (-x)) / 2|
    G 1 = 0 := by
  intro N G
  have hpair : hadamard_bridge_error μ u v 1 = 0 ∧ hadamard_bridge_error μ u v (-1) = 0 := by
    exact
      ⟨hadamard_bridge_error_one hdim μ u v hu hv huv,
        hadamard_bridge_error_neg_one hdim μ u v hu hv huv⟩
  exact (hadamard_bridge_error_pair_zero_iff_normalized_gauge_zero μ u v 1).1 hpair

lemma hadamard_bridge_error_max_zero_iff_normalized_gauge_zero
    (μ : FrameFunction H) (u v : H) (r : ℝ) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let G : ℝ → ℝ := fun x => max |N x + N (-x)| |(N x - N (-x)) / 2|
    max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| = 0
      ↔
    G r = 0 := by
  intro N G
  constructor
  · intro hm
    have hpair :
        hadamard_bridge_error μ u v r = 0 ∧ hadamard_bridge_error μ u v (-r) = 0 :=
      (hadamard_bridge_error_pair_zero_iff_max_zero μ u v r).2 hm
    exact (hadamard_bridge_error_pair_zero_iff_normalized_gauge_zero μ u v r).1 hpair
  · intro hG
    have hpair :
        hadamard_bridge_error μ u v r = 0 ∧ hadamard_bridge_error μ u v (-r) = 0 :=
      (hadamard_bridge_error_pair_zero_iff_normalized_gauge_zero μ u v r).2 hG
    exact (hadamard_bridge_error_pair_zero_iff_max_zero μ u v r).1 hpair

lemma hadamard_residual_one_normalized_eq_local_defect_g_normalized_mobius
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let φ : ℝ := (1 - r) / (1 + r)
    hadamard_residual_one μ u v r / (1 + r ^ 2)
      =
    local_defect_g μ u v φ / (1 + φ ^ 2) := by
  intro φ
  have hF :
      hadamard_residual_one μ u v r =
        ((1 + r) ^ 2 / 2) * local_defect_g μ u v φ := by
    simpa [φ] using
      hadamard_residual_one_eq_mobius_scaled_local_defect hdim μ u v hu hv huv r h1pr
  have hphi_den : 1 + φ ^ 2 = 2 * (1 + r ^ 2) / (1 + r) ^ 2 := by
    dsimp [φ]
    field_simp [h1pr]
    ring
  have h1r2_ne : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
  have hcoef_ne : ((1 + r) ^ 2 : ℝ) ≠ 0 := by exact pow_ne_zero 2 h1pr
  calc
    hadamard_residual_one μ u v r / (1 + r ^ 2)
        = (((1 + r) ^ 2 / 2) * local_defect_g μ u v φ) / (1 + r ^ 2) := by rw [hF]
    _ = local_defect_g μ u v φ * ((1 + r) ^ 2 / (2 * (1 + r ^ 2))) := by
          field_simp [h1r2_ne]
    _ = local_defect_g μ u v φ / (1 + φ ^ 2) := by
          rw [hphi_den]
          field_simp [hcoef_ne]

lemma hadamard_bridge_error_normalized_sum_eq_neg_local_defect_g_normalized
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    N r + N (-r) = -(local_defect_g μ u v r) / (1 + r ^ 2) := by
  intro N
  have hsym_r :
      local_defect_g μ u v r =
        -(hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)) := by
    simpa using local_defect_g_eq_bridge_error_symm hdim μ u v hu hv huv r
  dsimp [N]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hlin :
      hadamard_bridge_error μ u v r * (1 + r ^ 2)⁻¹ +
        hadamard_bridge_error μ u v (-r) * (1 + (-r) ^ 2)⁻¹
        =
      (hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)) * (1 + r ^ 2)⁻¹ := by
    simp [add_mul]
  have hsym_r' :
      hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r) =
        -local_defect_g μ u v r := by
    linarith [hsym_r]
  rw [hlin, ← div_eq_mul_inv]
  rw [hsym_r']

lemma hadamard_bridge_error_normalized_diff_eq_hadamard_residual_one_normalized
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    (N r - N (-r)) / 2 = hadamard_residual_one μ u v r / (1 + r ^ 2) := by
  intro N
  have hanti_r :
      hadamard_residual_one μ u v r =
        (hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)) / 2 := by
    simpa using hadamard_residual_one_eq_bridge_error_antisymm hdim μ u v hu hv huv r
  dsimp [N]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  simp
  rw [hanti_r]
  ring

lemma hadamard_bridge_error_normalized_diff_eq_local_defect_g_normalized_mobius
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let φ : ℝ := (1 - r) / (1 + r)
    (N r - N (-r)) / 2 = local_defect_g μ u v φ / (1 + φ ^ 2) := by
  intro N φ
  calc
    (N r - N (-r)) / 2 = hadamard_residual_one μ u v r / (1 + r ^ 2) := by
      simpa [N] using
        hadamard_bridge_error_normalized_diff_eq_hadamard_residual_one_normalized
          hdim μ u v hu hv huv r
    _ = local_defect_g μ u v φ / (1 + φ ^ 2) := by
      simpa [φ] using
        hadamard_residual_one_normalized_eq_local_defect_g_normalized_mobius
          hdim μ u v hu hv huv r h1pr

lemma hadamard_residual_one_normalized_abs_eq_local_defect_g_normalized_abs_mobius
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let φ : ℝ := (1 - r) / (1 + r)
    |hadamard_residual_one μ u v r| / (1 + r ^ 2)
      =
    |local_defect_g μ u v φ| / (1 + φ ^ 2) := by
  intro φ
  have hF :
      hadamard_residual_one μ u v r =
        ((1 + r) ^ 2 / 2) * local_defect_g μ u v φ := by
    simpa [φ] using
      hadamard_residual_one_eq_mobius_scaled_local_defect hdim μ u v hu hv huv r h1pr
  have hFabs : |hadamard_residual_one μ u v r| =
      ((1 + r) ^ 2 / 2) * |local_defect_g μ u v φ| := by
    have h := congrArg abs hF
    have hcoef : (0 : ℝ) ≤ ((1 + r) ^ 2 / 2) := by positivity
    simpa [abs_mul, abs_of_nonneg hcoef] using h
  have hphi_den : 1 + φ ^ 2 = 2 * (1 + r ^ 2) / (1 + r) ^ 2 := by
    dsimp [φ]
    field_simp [h1pr]
    ring
  have h1r2_ne : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
  have hcoef_ne : ((1 + r) ^ 2 : ℝ) ≠ 0 := by exact pow_ne_zero 2 h1pr
  calc
    |hadamard_residual_one μ u v r| / (1 + r ^ 2)
        = (((1 + r) ^ 2 / 2) * |local_defect_g μ u v φ|) / (1 + r ^ 2) := by rw [hFabs]
    _ = |local_defect_g μ u v φ| * ((1 + r) ^ 2 / (2 * (1 + r ^ 2))) := by
          field_simp [h1r2_ne]
    _ = |local_defect_g μ u v φ| / (1 + φ ^ 2) := by
          rw [hphi_den]
          field_simp [hcoef_ne]

lemma hadamard_bridge_error_normalized_gauge_eq_max_local_defect_g_normalized_pair
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let G : ℝ → ℝ := fun x => max |N x + N (-x)| |(N x - N (-x)) / 2|
    let φ : ℝ := (1 - r) / (1 + r)
    G r
      =
    max
      (|local_defect_g μ u v r| / (1 + r ^ 2))
      (|local_defect_g μ u v φ| / (1 + φ ^ 2)) := by
  intro N G φ
  have hsym_r :
      local_defect_g μ u v r =
        -(hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)) := by
    simpa using local_defect_g_eq_bridge_error_symm hdim μ u v hu hv huv r
  have hsum_norm :
      |N r + N (-r)| = |local_defect_g μ u v r| / (1 + r ^ 2) := by
    have h1r2_ne : (1 + r ^ 2 : ℝ) ≠ 0 := by positivity
    have hsum :
        N r + N (-r) =
          -(local_defect_g μ u v r) / (1 + r ^ 2) := by
      dsimp [N]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hlin :
          hadamard_bridge_error μ u v r * (1 + r ^ 2)⁻¹ +
            hadamard_bridge_error μ u v (-r) * (1 + (-r) ^ 2)⁻¹
            =
          (hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)) * (1 + r ^ 2)⁻¹ := by
        simp [neg_sq, add_mul]
      have hsym_r' :
          hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r) =
            -local_defect_g μ u v r := by
        linarith [hsym_r]
      rw [hlin, ← div_eq_mul_inv]
      rw [hsym_r']
    rw [hsum, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (1 + r ^ 2))]
  have hanti_r :
      hadamard_residual_one μ u v r =
        (hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)) / 2 := by
    simpa using hadamard_residual_one_eq_bridge_error_antisymm hdim μ u v hu hv huv r
  have hdiff_norm :
      |(N r - N (-r)) / 2| = |hadamard_residual_one μ u v r| / (1 + r ^ 2) := by
    have hdiff :
        (N r - N (-r)) / 2 = hadamard_residual_one μ u v r / (1 + r ^ 2) := by
      dsimp [N]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      simp [neg_sq]
      rw [hanti_r]
      ring
    rw [hdiff, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (1 + r ^ 2))]
  have hres_norm :
      |hadamard_residual_one μ u v r| / (1 + r ^ 2)
        =
      |local_defect_g μ u v φ| / (1 + φ ^ 2) := by
    simpa [φ] using
      hadamard_residual_one_normalized_abs_eq_local_defect_g_normalized_abs_mobius
        hdim μ u v hu hv huv r h1pr
  dsimp [G]
  rw [hsum_norm, hdiff_norm, hres_norm]

lemma hadamard_bridge_error_normalized_gauge_inversion
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    {r : ℝ} (hr : r ≠ 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let G : ℝ → ℝ := fun x => max |N x + N (-x)| |(N x - N (-x)) / 2|
    G (1 / r) = G r := by
  intro N G
  rcases hadamard_bridge_error_inversion_normalized hdim μ u v hu hv huv hr with
    ⟨hNr, hNneg⟩
  have hsum : |N (1 / r) + N (-(1 / r))| = |N r + N (-r)| := by
    have : N (1 / r) + N (-(1 / r)) = -(N r + N (-r)) := by
      linarith [hNr, hNneg]
    rw [this, abs_neg]
  have hdiff : |(N (1 / r) - N (-(1 / r))) / 2| = |(N r - N (-r)) / 2| := by
    have : (N (1 / r) - N (-(1 / r))) / 2 = (N r - N (-r)) / 2 := by
      linarith [hNr, hNneg]
    rw [this]
  dsimp [G]
  rw [hsum, hdiff]

lemma hadamard_bridge_error_lift_linearized
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) (h1mr : 1 - r ≠ 0) :
    let R : ℝ := (1 + r) / (1 - r)
    2 * (1 - r) ^ 2 * hadamard_bridge_error μ u v (-R)
      = 5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r)
      ∧
    2 * (1 - r) ^ 2 * hadamard_bridge_error μ u v R
      = -(3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r)) := by
  intro R
  set φ : ℝ := (1 - r) / (1 + r)
  have hphi_ne : φ ≠ 0 := by
    dsimp [φ]
    exact div_ne_zero h1mr h1pr
  rcases hadamard_bridge_error_mobius_linearized hdim μ u v hu hv huv r h1pr with
    ⟨hEφ, hEnegφ⟩
  have hinvφ :
      hadamard_bridge_error μ u v φ = -φ ^ 2 * hadamard_bridge_error μ u v (-(1 / φ)) := by
    exact hadamard_bridge_error_inversion hdim μ u v hu hv huv hphi_ne
  have hinvnegφ :
      hadamard_bridge_error μ u v (-φ) = -φ ^ 2 * hadamard_bridge_error μ u v (1 / φ) := by
    have h := hadamard_bridge_error_inversion hdim μ u v hu hv huv (neg_ne_zero.mpr hphi_ne)
    simpa [neg_sq] using h
  have hR1 : -(1 / φ) = -R := by
    dsimp [φ, R]
    field_simp [h1pr, h1mr]
  have hR2 : (1 / φ) = R := by
    dsimp [φ, R]
    field_simp [h1pr, h1mr]
  have hfac : (1 + r) ^ 2 * φ ^ 2 = (1 - r) ^ 2 := by
    dsimp [φ]
    field_simp [h1pr]
  constructor
  · rw [hinvφ, hR1] at hEφ
    have htmp :
        -(2 * (1 - r) ^ 2 * hadamard_bridge_error μ u v (-R)) =
          -(5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r)) := by
      calc
        -(2 * (1 - r) ^ 2 * hadamard_bridge_error μ u v (-R))
            = -(2 * ((1 + r) ^ 2 * φ ^ 2) * hadamard_bridge_error μ u v (-R)) := by rw [hfac]
        _ = 2 * (1 + r) ^ 2 * (-φ ^ 2 * hadamard_bridge_error μ u v (-R)) := by ring
        _ = -(5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r)) := hEφ
    linarith [htmp]
  · rw [hinvnegφ, hR2] at hEnegφ
    have htmp :
        -(2 * (1 - r) ^ 2 * hadamard_bridge_error μ u v R) =
          3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r) := by
      calc
        -(2 * (1 - r) ^ 2 * hadamard_bridge_error μ u v R)
            = -(2 * ((1 + r) ^ 2 * φ ^ 2) * hadamard_bridge_error μ u v R) := by rw [hfac]
        _ = 2 * (1 + r) ^ 2 * (-φ ^ 2 * hadamard_bridge_error μ u v R) := by ring
        _ = 3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r) := hEnegφ
    linarith [htmp]

lemma hadamard_bridge_error_lift_normalized
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) (h1mr : 1 - r ≠ 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let R : ℝ := (1 + r) / (1 - r)
    N (-R) = (5 * N r + 3 * N (-r)) / 4
      ∧
    N R = -(3 * N r + 5 * N (-r)) / 4 := by
  intro N R
  rcases hadamard_bridge_error_lift_linearized hdim μ u v hu hv huv r h1pr h1mr with
    ⟨hnegR, hR⟩
  have hRden : 1 + R ^ 2 = 2 * (1 + r ^ 2) / (1 - r) ^ 2 := by
    dsimp [R]
    field_simp [h1mr]
    ring
  have hRdenNeg : 1 + (-R) ^ 2 = 2 * (1 + r ^ 2) / (1 - r) ^ 2 := by
    simpa [neg_sq] using hRden
  have h1r2_ne : (1 + r ^ 2) ≠ 0 := by positivity
  constructor
  · have hnegR' :
        hadamard_bridge_error μ u v (-R) / (1 + (-R) ^ 2) =
          (5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r))
            / (4 * (1 + r ^ 2)) := by
      rw [hRdenNeg]
      field_simp [h1mr, h1r2_ne]
      linarith [hnegR]
    dsimp [N]
    rw [hnegR']
    field_simp [h1r2_ne]
  · have hR' :
        hadamard_bridge_error μ u v R / (1 + R ^ 2) =
          -(3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r))
            / (4 * (1 + r ^ 2)) := by
      rw [hRden]
      field_simp [h1mr, h1r2_ne]
      linarith [hR]
    dsimp [N]
    rw [hR']
    field_simp [h1r2_ne]

lemma hadamard_bridge_error_lift_normalized_symm_antisymm
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) (h1mr : 1 - r ≠ 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let R : ℝ := (1 + r) / (1 - r)
    let S : ℝ := N r + N (-r)
    let A : ℝ := N r - N (-r)
    let SR : ℝ := N R + N (-R)
    let AR : ℝ := N R - N (-R)
    SR = A / 2 ∧ AR = -2 * S := by
  intro N R S A SR AR
  rcases hadamard_bridge_error_lift_normalized hdim μ u v hu hv huv r h1pr h1mr with
    ⟨hNRneg, hNR⟩
  constructor
  · dsimp [SR, S, A]
    linarith [hNRneg, hNR]
  · dsimp [AR, S, A]
    linarith [hNRneg, hNR]

lemma hadamard_bridge_error_lift_normalized_invariant
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) (h1mr : 1 - r ≠ 0) :
    let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
    let R : ℝ := (1 + r) / (1 - r)
    let G : ℝ → ℝ := fun x => max |N x + N (-x)| |(N x - N (-x)) / 2|
    G R = G r := by
  intro N R G
  rcases hadamard_bridge_error_lift_normalized_symm_antisymm hdim μ u v hu hv huv r h1pr h1mr with
    ⟨hSR, hAR⟩
  have hSR' : N R + N (-R) = (N r - N (-r)) / 2 := by
    simpa [N, R] using hSR
  have hAR' : N R - N (-R) = -2 * (N r + N (-r)) := by
    simpa [N, R] using hAR
  have h1 : |N R + N (-R)| = |(N r - N (-r)) / 2| := by
    exact congrArg abs hSR'
  have h2 : |(N R - N (-R)) / 2| = |N r + N (-r)| := by
    have hARhalf : (N R - N (-R)) / 2 = -(N r + N (-r)) := by
      linarith [hAR']
    have h2' : |(N R - N (-R)) / 2| = |-N (-r) + -N r| := by
      simpa using congrArg abs hARhalf
    have hrhs : |-N (-r) + -N r| = |N r + N (-r)| := by
      have : -N (-r) + -N r = -(N r + N (-r)) := by ring
      rw [this, abs_neg]
    exact h2'.trans hrhs
  dsimp [G]
  rw [h1, h2]
  exact max_comm _ _

lemma hadamard_bridge_error_pair_zero_of_g_zero_at_r_and_mobius
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0)
    (hgr : local_defect_g μ u v r = 0)
    (hgφ : local_defect_g μ u v ((1 - r) / (1 + r)) = 0) :
    hadamard_bridge_error μ u v r = 0 ∧
      hadamard_bridge_error μ u v ((1 - r) / (1 + r)) = 0 := by
  set E : ℝ → ℝ := hadamard_bridge_error μ u v
  set F : ℝ → ℝ := hadamard_residual_one μ u v
  set g : ℝ → ℝ := local_defect_g μ u v
  set φ : ℝ := (1 - r) / (1 + r)
  have hsym_r : g r = -(E r + E (-r)) := by
    dsimp [E, g]
    simpa using local_defect_g_eq_bridge_error_symm hdim μ u v hu hv huv r
  have hsym_φ : g φ = -(E φ + E (-φ)) := by
    dsimp [E, g, φ]
    simpa using local_defect_g_eq_bridge_error_symm hdim μ u v hu hv huv φ
  have hEr_neg : E (-r) = -E r := by
    rw [hgr] at hsym_r
    linarith [hsym_r]
  have hEφ_neg : E (-φ) = -E φ := by
    rw [hgφ] at hsym_φ
    linarith [hsym_φ]
  have hF_r : F r = E r := by
    have hanti_r :
        F r = (E r - E (-r)) / 2 := by
      dsimp [E, F]
      simpa using hadamard_residual_one_eq_bridge_error_antisymm hdim μ u v hu hv huv r
    rw [hEr_neg] at hanti_r
    linarith [hanti_r]
  have hF_φ : F φ = E φ := by
    have hanti_φ :
        F φ = (E φ - E (-φ)) / 2 := by
      dsimp [E, F, φ]
      simpa using hadamard_residual_one_eq_bridge_error_antisymm hdim μ u v hu hv huv φ
    rw [hEφ_neg] at hanti_φ
    linarith [hanti_φ]
  have hhalf :
      ((1 + r) ^ 2 / 4) * F φ = (1 / 2 : ℝ) * g r := by
    dsimp [F, g, φ]
    simpa using hadamard_residual_half_step_eq_half_local_defect hdim μ u v hu hv huv r h1pr
  have hEφ0 : E φ = 0 := by
    have hFφ0 : F φ = 0 := by
      rw [hgr] at hhalf
      have hcoeff_ne : ((1 + r) ^ 2 / 4 : ℝ) ≠ 0 := by
        have hsq_ne : (1 + r) ^ 2 ≠ 0 := by exact pow_ne_zero 2 h1pr
        exact div_ne_zero hsq_ne (by norm_num)
      have hmul : ((1 + r) ^ 2 / 4 : ℝ) * F φ = 0 := by
        simpa using hhalf
      exact (mul_eq_zero.mp hmul).resolve_left hcoeff_ne
    rw [← hF_φ]
    exact hFφ0
  rcases hadamard_bridge_error_mobius_linearized hdim μ u v hu hv huv r h1pr with
    ⟨hlin1, _⟩
  have hEr0 : E r = 0 := by
    have hlin1' :
        2 * (1 + r) ^ 2 * E φ = -(5 * E r + 3 * E (-r)) := by
      simpa [E, φ] using hlin1
    rw [hEφ0, hEr_neg] at hlin1'
    nlinarith [hlin1']
  constructor
  · dsimp [E]
    exact hEr0
  · dsimp [E, φ]
    exact hEφ0

lemma hadamard_bridge_error_zero_of_g_zero_at_r_and_mobius
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0)
    (hgr : local_defect_g μ u v r = 0)
    (hgφ : local_defect_g μ u v ((1 - r) / (1 + r)) = 0) :
    hadamard_bridge_error μ u v r = 0 := by
  exact
    (hadamard_bridge_error_pair_zero_of_g_zero_at_r_and_mobius
      hdim μ u v hu hv huv r h1pr hgr hgφ).1

lemma local_defect_g_pair_zero_of_hadamard_bridge_error_pair_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0)
    (hEr : hadamard_bridge_error μ u v r = 0)
    (hEφ : hadamard_bridge_error μ u v ((1 - r) / (1 + r)) = 0) :
    local_defect_g μ u v r = 0 ∧
      local_defect_g μ u v ((1 - r) / (1 + r)) = 0 := by
  set E : ℝ → ℝ := hadamard_bridge_error μ u v
  set g : ℝ → ℝ := local_defect_g μ u v
  set φ : ℝ := (1 - r) / (1 + r)
  have hlin := hadamard_bridge_error_mobius_linearized hdim μ u v hu hv huv r h1pr
  rcases hlin with ⟨hlin1, hlin2⟩
  have h1pr_sq_ne : (1 + r) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 h1pr
  have hEneg_r : E (-r) = 0 := by
    have hlin1' :
        2 * (1 + r) ^ 2 * E φ = -(5 * E r + 3 * E (-r)) := by
      simpa [E, φ] using hlin1
    rw [hEr, hEφ] at hlin1'
    have : 3 * E (-r) = 0 := by linarith [hlin1']
    nlinarith [this]
  have hEneg_φ : E (-φ) = 0 := by
    have hlin2' :
        2 * (1 + r) ^ 2 * E (-φ) = 3 * E r + 5 * E (-r) := by
      simpa [E, φ] using hlin2
    rw [hEr, hEneg_r] at hlin2'
    have : 2 * (1 + r) ^ 2 * E (-φ) = 0 := by simpa using hlin2'
    have hcoef_ne : (2 * (1 + r) ^ 2 : ℝ) ≠ 0 := by
      exact mul_ne_zero (by norm_num) h1pr_sq_ne
    exact (mul_eq_zero.mp this).resolve_left hcoef_ne
  have hgr : g r = 0 := by
    have hsym_r : g r = -(E r + E (-r)) := by
      dsimp [E, g]
      simpa using local_defect_g_eq_bridge_error_symm hdim μ u v hu hv huv r
    rw [hEr, hEneg_r] at hsym_r
    simpa using hsym_r
  have hgφ : g φ = 0 := by
    have hsym_φ : g φ = -(E φ + E (-φ)) := by
      dsimp [E, g, φ]
      simpa using local_defect_g_eq_bridge_error_symm hdim μ u v hu hv huv φ
    rw [hEφ, hEneg_φ] at hsym_φ
    simpa using hsym_φ
  constructor
  · simpa [g] using hgr
  · simpa [g, φ] using hgφ

lemma local_defect_g_mobius_pair_zero_iff_hadamard_bridge_error_pair_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    (local_defect_g μ u v r = 0 ∧
      local_defect_g μ u v ((1 - r) / (1 + r)) = 0)
      ↔
    (hadamard_bridge_error μ u v r = 0 ∧
      hadamard_bridge_error μ u v ((1 - r) / (1 + r)) = 0) := by
  constructor
  · intro h
    exact
      hadamard_bridge_error_pair_zero_of_g_zero_at_r_and_mobius
        hdim μ u v hu hv huv r h1pr h.1 h.2
  · intro h
    exact
      local_defect_g_pair_zero_of_hadamard_bridge_error_pair_zero
        hdim μ u v hu hv huv r h1pr h.1 h.2

lemma hadamard_bridge_error_pair_zero_of_max_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0)
    (hm : max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| = 0) :
    hadamard_bridge_error μ u v r = 0 ∧
      hadamard_bridge_error μ u v ((1 - r) / (1 + r)) = 0 := by
  have hEr0 : hadamard_bridge_error μ u v r = 0 := by
    have hle : |hadamard_bridge_error μ u v r| ≤
        max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := le_max_left _ _
    have : |hadamard_bridge_error μ u v r| = 0 := by
      linarith [hm, hle, abs_nonneg (hadamard_bridge_error μ u v r)]
    exact abs_eq_zero.mp this
  have hEneg_r0 : hadamard_bridge_error μ u v (-r) = 0 := by
    have hle : |hadamard_bridge_error μ u v (-r)| ≤
        max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := le_max_right _ _
    have : |hadamard_bridge_error μ u v (-r)| = 0 := by
      linarith [hm, hle, abs_nonneg (hadamard_bridge_error μ u v (-r))]
    exact abs_eq_zero.mp this
  rcases hadamard_bridge_error_mobius_linearized hdim μ u v hu hv huv r h1pr with
    ⟨hlin1, _⟩
  have hEphi0 : hadamard_bridge_error μ u v ((1 - r) / (1 + r)) = 0 := by
    have hlin1' :
        2 * (1 + r) ^ 2 * hadamard_bridge_error μ u v ((1 - r) / (1 + r))
          = -(5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r)) := by
      simpa using hlin1
    rw [hEr0, hEneg_r0] at hlin1'
    have hcoef_ne : (2 * (1 + r) ^ 2 : ℝ) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 h1pr)
    have hlin1'' :
        2 * (1 + r) ^ 2 * hadamard_bridge_error μ u v ((1 - r) / (1 + r)) = 0 := by
      simpa using hlin1'
    exact (mul_eq_zero.mp hlin1'').resolve_left hcoef_ne
  exact ⟨hEr0, hEphi0⟩

lemma max_abs_add_sub_eq_abs_add_abs (x y : ℝ) :
    max |x + y| |x - y| = |x| + |y| := by
  have hupper1 : |x + y| ≤ |x| + |y| := abs_add_le _ _
  have hupper2 : |x - y| ≤ |x| + |y| := abs_sub _ _
  have hupper : max |x + y| |x - y| ≤ |x| + |y| := max_le hupper1 hupper2
  have hlower : |x| + |y| ≤ max |x + y| |x - y| := by
    by_cases hx : 0 ≤ x
    · by_cases hy : 0 ≤ y
      · have hxy : |x| + |y| = |x + y| := by
          rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (add_nonneg hx hy)]
        calc
          |x| + |y| = |x + y| := hxy
          _ ≤ max |x + y| |x - y| := le_max_left _ _
      · have hy' : y ≤ 0 := le_of_not_ge hy
        have hxy : |x| + |y| = |x - y| := by
          rw [abs_of_nonneg hx, abs_of_nonpos hy']
          have hsub : 0 ≤ x - y := by linarith
          rw [abs_of_nonneg hsub]
          ring
        calc
          |x| + |y| = |x - y| := hxy
          _ ≤ max |x + y| |x - y| := le_max_right _ _
    · have hx' : x ≤ 0 := le_of_not_ge hx
      by_cases hy : 0 ≤ y
      · have hxy : |x| + |y| = |x - y| := by
          rw [abs_of_nonpos hx', abs_of_nonneg hy]
          have hsub : x - y ≤ 0 := by linarith
          rw [abs_of_nonpos hsub]
          ring
        calc
          |x| + |y| = |x - y| := hxy
          _ ≤ max |x + y| |x - y| := le_max_right _ _
      · have hy' : y ≤ 0 := le_of_not_ge hy
        have hxy : |x| + |y| = |x + y| := by
          rw [abs_of_nonpos hx', abs_of_nonpos hy']
          have hadd : x + y ≤ 0 := by linarith
          rw [abs_of_nonpos hadd]
          ring
        calc
          |x| + |y| = |x + y| := hxy
          _ ≤ max |x + y| |x - y| := le_max_left _ _
  exact le_antisymm hupper hlower

lemma hadamard_bridge_error_max_abs_eq
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| =
      |hadamard_residual_one μ u v r| + (1 / 2 : ℝ) * |local_defect_g μ u v r| := by
  have hodd : hadamard_residual_one μ u v (-r) = -hadamard_residual_one μ u v r := by
    simpa using hadamard_residual_one_odd hdim μ u v hu hv huv r
  have heven : local_defect_g μ u v (-r) = local_defect_g μ u v r := by
    simpa using GleasonBridge.local_defect_g_even μ u v r
  have hEneg :
      hadamard_bridge_error μ u v (-r) =
        -(hadamard_residual_one μ u v r + (1 / 2 : ℝ) * local_defect_g μ u v r) := by
    unfold hadamard_bridge_error
    rw [hodd, heven]
    ring
  have hEpos :
      hadamard_bridge_error μ u v r =
        hadamard_residual_one μ u v r - (1 / 2 : ℝ) * local_defect_g μ u v r := by
    rfl
  rw [hEpos, hEneg, abs_neg]
  have hmax :=
    max_abs_add_sub_eq_abs_add_abs
      (hadamard_residual_one μ u v r)
      ((1 / 2 : ℝ) * local_defect_g μ u v r)
  have hmax' :
      max
          |hadamard_residual_one μ u v r - (1 / 2 : ℝ) * local_defect_g μ u v r|
          |hadamard_residual_one μ u v r + (1 / 2 : ℝ) * local_defect_g μ u v r|
        =
      |hadamard_residual_one μ u v r| + |(1 / 2 : ℝ) * local_defect_g μ u v r| := by
    simpa [max_comm] using hmax
  rw [hmax', abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)]

lemma hadamard_bridge_error_max_abs_eq_symm_antisymm
    (μ : FrameFunction H) (u v : H) (r : ℝ) :
    let S : ℝ := hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)
    let A : ℝ := hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)
    max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| =
      (|S| + |A|) / 2 := by
  intro S A
  set E : ℝ → ℝ := hadamard_bridge_error μ u v
  have hSA :
      max |S + A| |S - A| = |S| + |A| := max_abs_add_sub_eq_abs_add_abs S A
  have hSA' :
      max |2 * E r| |2 * E (-r)| = |S| + |A| := by
    simpa [S, A, E, two_mul, add_assoc, add_left_comm, add_comm] using hSA
  have hmul :
      max |2 * E r| |2 * E (-r)| = 2 * max |E r| |E (-r)| := by
    have habs_r : |2 * E r| = 2 * |E r| := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    have habs_nr : |2 * E (-r)| = 2 * |E (-r)| := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [habs_r, habs_nr]
    have hmax2 :
        2 * max |E r| |E (-r)| = max (2 * |E r|) (2 * |E (-r)|) := by
      exact mul_max_of_nonneg |E r| |E (-r)| (by norm_num)
    exact hmax2.symm
  have htwo :
      2 * max |E r| |E (-r)| = |S| + |A| := by
    rw [← hmul]
    exact hSA'
  have htwo' : (2 : ℝ) ≠ 0 := by norm_num
  apply (eq_div_iff htwo').2
  simpa [E, mul_comm, mul_left_comm, mul_assoc] using htwo

lemma hadamard_bridge_error_max_abs_eq_mobius_g
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| =
      ((1 + r) ^ 2 / 2) * |local_defect_g μ u v ((1 - r) / (1 + r))| +
        (1 / 2 : ℝ) * |local_defect_g μ u v r| := by
  have hmax := hadamard_bridge_error_max_abs_eq hdim μ u v hu hv huv r
  have hF :
      hadamard_residual_one μ u v r =
        ((1 + r) ^ 2 / 2) * local_defect_g μ u v ((1 - r) / (1 + r)) := by
    simpa using
      hadamard_residual_one_eq_mobius_scaled_local_defect
        hdim μ u v hu hv huv r h1pr
  rw [hF] at hmax
  have hcoef : (0 : ℝ) ≤ ((1 + r) ^ 2 / 2) := by positivity
  rw [abs_mul, abs_of_nonneg hcoef] at hmax
  exact hmax

lemma hadamard_bridge_error_mobius_max_abs_exact
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    (1 + r) ^ 2 *
        max
          |hadamard_bridge_error μ u v ((1 - r) / (1 + r))|
          |hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))|
      =
    2 * |local_defect_g μ u v r| +
      ((1 + r) ^ 2 / 2) * |local_defect_g μ u v ((1 - r) / (1 + r))| := by
  set φ : ℝ := (1 - r) / (1 + r)
  have h1pφ : 1 + φ ≠ 0 := by
    have hnum : 1 + φ = 2 / (1 + r) := by
      dsimp [φ]
      field_simp [h1pr]
      ring
    rw [hnum]
    exact div_ne_zero (by norm_num) h1pr
  have hmaxφ :=
    hadamard_bridge_error_max_abs_eq_mobius_g hdim μ u v hu hv huv φ h1pφ
  have hmob : (1 - φ) / (1 + φ) = r := by
    simpa [φ] using hadamard_mobius_involutive r h1pr
  rw [hmob] at hmaxφ
  have hprod : (1 + r) ^ 2 * (1 + φ) ^ 2 = 4 := by
    dsimp [φ]
    field_simp [h1pr]
    ring
  have hmul :
      (1 + r) ^ 2 * max |hadamard_bridge_error μ u v φ| |hadamard_bridge_error μ u v (-φ)| =
        (1 + r) ^ 2 *
          (((1 + φ) ^ 2 / 2) * |local_defect_g μ u v r| + (1 / 2 : ℝ) * |local_defect_g μ u v φ|) := by
    exact congrArg (fun x : ℝ => (1 + r) ^ 2 * x) hmaxφ
  have hmain :
      (1 + r) ^ 2 * max |hadamard_bridge_error μ u v φ| |hadamard_bridge_error μ u v (-φ)| =
        2 * |local_defect_g μ u v r| +
          ((1 + r) ^ 2 / 2) * |local_defect_g μ u v φ| := by
    calc
      (1 + r) ^ 2 * max |hadamard_bridge_error μ u v φ| |hadamard_bridge_error μ u v (-φ)|
          =
        (1 + r) ^ 2 *
          (((1 + φ) ^ 2 / 2) * |local_defect_g μ u v r| + (1 / 2 : ℝ) * |local_defect_g μ u v φ|) := hmul
      _ = (((1 + r) ^ 2 * (1 + φ) ^ 2) / 2) * |local_defect_g μ u v r| +
            ((1 + r) ^ 2 / 2) * |local_defect_g μ u v φ| := by ring
      _ = 2 * |local_defect_g μ u v r| +
            ((1 + r) ^ 2 / 2) * |local_defect_g μ u v φ| := by
            rw [hprod]
            ring_nf
  calc
    (1 + r) ^ 2 *
        max |hadamard_bridge_error μ u v ((1 - r) / (1 + r))|
          |hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))|
        = 2 * |local_defect_g μ u v r| +
            ((1 + r) ^ 2 / 2) * |local_defect_g μ u v ((1 - r) / (1 + r))| := by
          simpa [φ] using hmain

lemma local_defect_g_normalized_abs_inversion
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    {t : ℝ} (ht : t ≠ 0) :
    |local_defect_g μ u v (1 / t)| / (1 + (1 / t) ^ 2) =
      |local_defect_g μ u v t| / (1 + t ^ 2) := by
  have hInv := GleasonBridge.local_defect_g_inversion hdim μ u v hu hv huv ht
  have habs_mul :
      |local_defect_g μ u v t| = t ^ 2 * |local_defect_g μ u v (1 / t)| := by
    rw [hInv, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg t)]
  have ht2_ne : t ^ 2 ≠ 0 := by exact pow_ne_zero 2 ht
  have habs :
      |local_defect_g μ u v (1 / t)| = |local_defect_g μ u v t| / t ^ 2 := by
    apply (eq_div_iff ht2_ne).2
    nlinarith [habs_mul]
  have hden : 1 + (1 / t) ^ 2 = (1 + t ^ 2) / t ^ 2 := by
    field_simp [ht]
    ring
  rw [habs, hden]
  field_simp [ht]

lemma local_defect_g_normalized_abs_mobius_companion
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) (h1mr : 1 - r ≠ 0) :
    let φ : ℝ := (1 - r) / (1 + r)
    let R : ℝ := (1 + r) / (1 - r)
    |local_defect_g μ u v R| / (1 + R ^ 2) =
      |local_defect_g μ u v φ| / (1 + φ ^ 2) := by
  intro φ R
  have hphi_ne : φ ≠ 0 := by
    dsimp [φ]
    exact div_ne_zero h1mr h1pr
  have hR_eq : R = 1 / φ := by
    dsimp [R, φ]
    field_simp [h1pr, h1mr]
  rw [hR_eq]
  exact local_defect_g_normalized_abs_inversion hdim μ u v hu hv huv hphi_ne

lemma local_defect_g_normalized_pair_max_zero_iff_hadamard_bridge_error_max_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    max
      (|local_defect_g μ u v r| / (1 + r ^ 2))
      (|local_defect_g μ u v ((1 - r) / (1 + r))| / (1 + ((1 - r) / (1 + r)) ^ 2)) = 0
      ↔
    max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| = 0 := by
  let N : ℝ → ℝ := fun x => hadamard_bridge_error μ u v x / (1 + x ^ 2)
  let G : ℝ → ℝ := fun x => max |N x + N (-x)| |(N x - N (-x)) / 2|
  have hG_eq :
      G r =
        max
          (|local_defect_g μ u v r| / (1 + r ^ 2))
          (|local_defect_g μ u v ((1 - r) / (1 + r))| / (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    simpa [N, G] using
      hadamard_bridge_error_normalized_gauge_eq_max_local_defect_g_normalized_pair
        hdim μ u v hu hv huv r h1pr
  have hmax_eq :
      max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| = 0
        ↔
      G r = 0 := by
    simpa [N, G] using
      (hadamard_bridge_error_max_zero_iff_normalized_gauge_zero μ u v r)
  constructor
  · intro hg
    have hG0 : G r = 0 := by simpa [hG_eq] using hg
    exact hmax_eq.mpr hG0
  · intro hm
    have hG0 : G r = 0 := hmax_eq.mp hm
    simpa [hG_eq] using hG0

lemma local_defect_g_normalized_pair_max_zero_of_defect_one_gap_midpoint
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0)
    (hmid : ∀ s t : ℝ,
      defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) =
        2 * defect_one_gap μ u v s) :
    max
      (|local_defect_g μ u v r| / (1 + r ^ 2))
      (|local_defect_g μ u v ((1 - r) / (1 + r))| / (1 + ((1 - r) / (1 + r)) ^ 2)) = 0 := by
  have hEzero :
      ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 :=
    hadamard_bridge_error_zero_of_defect_one_gap_midpoint
      hdim μ u v hu hv huv hmid
  have hpair0 :
      hadamard_bridge_error μ u v r = 0 ∧
        hadamard_bridge_error μ u v (-r) = 0 := ⟨hEzero r, hEzero (-r)⟩
  have hm0 :
      max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| = 0 :=
    (hadamard_bridge_error_pair_zero_iff_max_zero μ u v r).1 hpair0
  exact
    (local_defect_g_normalized_pair_max_zero_iff_hadamard_bridge_error_max_zero
      hdim μ u v hu hv huv r h1pr).2 hm0

lemma local_defect_g_second_diff_eq_shifted_base_pair
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
      2 * local_defect_g μ u v s
      =
    local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t +
      local_quad2DDefect μ (u - (s : ℂ) • v) v 1 t := by
  have hpair := shifted_base_pair_sum_eq_residual μ u v s t
  have hpair' :
      local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t +
          local_quad2DDefect μ (u - (s : ℂ) • v) v 1 t
        =
      local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
          2 * local_defect_g μ u v s := by
    simpa [local_defect_residual, local_defect_g] using hpair
  linarith [hpair']

lemma local_A_bridge_lhs_as_hadamard_shifted_pair
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    local_quad2DDefect μ (u + v + (s : ℂ) • (u - v)) (u - v) 1 t +
      local_quad2DDefect μ (u - v + (s : ℂ) • (u + v)) (u + v) 1 t
      =
    s2 ^ 2 *
      (local_quad2DDefect μ (p + (s : ℂ) • q) q 1 t +
        local_quad2DDefect μ (q + (s : ℂ) • p) p 1 t) := by
  intro s2 p q
  have hs2_ne : (s2 : ℝ) ≠ 0 := by
    dsimp [s2]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2_mul_inv : s2 * s2⁻¹ = (1 : ℝ) := by
    field_simp [hs2_ne]
  have hXr : (s2 : ℝ) • p = u + v := by
    dsimp [p]
    rw [smul_smul, hs2_mul_inv, one_smul]
  have hYr : (s2 : ℝ) • q = u - v := by
    dsimp [q]
    rw [smul_smul, hs2_mul_inv, one_smul]
  have hX : u + v = (s2 : ℂ) • p := by
    change u + v = (s2 : ℝ) • p
    exact hXr.symm
  have hY : u - v = (s2 : ℂ) • q := by
    change u - v = (s2 : ℝ) • q
    exact hYr.symm
  have hplus :
      u + v + (s : ℂ) • (u - v) = (s2 : ℂ) • (p + (s : ℂ) • q) := by
    rw [hX, hY]
    simp [smul_add, smul_smul, mul_comm]
  rw [hplus, hY, hX]
  have hminus_base2 :
      (s2 : ℂ) • q + (s : ℂ) • ((s2 : ℂ) • p) = (s2 : ℂ) • (q + (s : ℂ) • p) := by
    simp [smul_add, smul_smul, mul_comm]
  rw [hminus_base2]
  have hd1 := local_quad2DDefect_real_scale μ (p + (s : ℂ) • q) q s2 1 t
  have hd2 := local_quad2DDefect_real_scale μ (q + (s : ℂ) • p) p s2 1 t
  linarith [hd1, hd2]

lemma hadamard_twice_vectors
    (u v : H) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    ((s2⁻¹ : ℝ) • (p + q) = u) ∧
      ((s2⁻¹ : ℝ) • (p - q) = v) := by
  intro s2 p q
  have hs2_sq : s2 ^ 2 = 2 := by
    dsimp [s2]
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs2_ne : (s2 : ℝ) ≠ 0 := by
    dsimp [s2]
    positivity
  have hs2inv_sq : (s2⁻¹ : ℝ) ^ 2 = (1 / 2 : ℝ) := by
    calc
      (s2⁻¹ : ℝ) ^ 2 = (s2 ^ 2)⁻¹ := by simpa using (inv_pow s2 2)
      _ = (2 : ℝ)⁻¹ := by rw [hs2_sq]
      _ = (1 / 2 : ℝ) := by norm_num
  constructor
  · calc
      (s2⁻¹ : ℝ) • (p + q)
          = (s2⁻¹ : ℝ) • ((s2⁻¹ : ℝ) • (u + v) + (s2⁻¹ : ℝ) • (u - v)) := by
              simp [p, q]
      _ = (s2⁻¹ : ℝ) • ((2 * s2⁻¹ : ℝ) • u) := by
              module
      _ = (((s2⁻¹ : ℝ) * (2 * s2⁻¹ : ℝ)) • u) := by
              simp [smul_smul]
      _ = ((2 : ℝ) * (s2⁻¹ : ℝ) ^ 2) • u := by
              ring_nf
      _ = (1 : ℝ) • u := by
              rw [hs2inv_sq]
              ring_nf
      _ = u := by simp
  · calc
      (s2⁻¹ : ℝ) • (p - q)
          = (s2⁻¹ : ℝ) • ((s2⁻¹ : ℝ) • (u + v) - (s2⁻¹ : ℝ) • (u - v)) := by
              simp [p, q]
      _ = (s2⁻¹ : ℝ) • ((2 * s2⁻¹ : ℝ) • v) := by
              module
      _ = (((s2⁻¹ : ℝ) * (2 * s2⁻¹ : ℝ)) • v) := by
              simp [smul_smul]
      _ = ((2 : ℝ) * (s2⁻¹ : ℝ) ^ 2) • v := by
              ring_nf
      _ = (1 : ℝ) • v := by
              rw [hs2inv_sq]
              ring_nf
      _ = v := by simp

lemma hadamard_lhs_reexpand_to_uv
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    local_quad2DDefect μ
        ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • q))
        (p - q) 1 t
      +
      local_quad2DDefect μ
        ((((1 + s : ℝ) : ℂ) • p) + (((s - 1 : ℝ) : ℂ) • q))
        (p + q) 1 t
      =
    2 * (local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t +
      local_quad2DDefect μ (v + (s : ℂ) • u) u 1 t) := by
  intro s2 p q
  have hs2_sq : s2 ^ 2 = 2 := by
    dsimp [s2]
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hraw := local_A_bridge_lhs_as_hadamard_shifted_pair μ p q s t
  have htwice := hadamard_twice_vectors u v
  have hpu : (s2⁻¹ : ℝ) • (p + q) = u := by simpa [s2, p, q] using htwice.1
  have hqv : (s2⁻¹ : ℝ) • (p - q) = v := by simpa [s2, p, q] using htwice.2
  have hs2inv_sq : (s2⁻¹ : ℝ) ^ 2 = (1 / 2 : ℝ) := by
    calc
      (s2⁻¹ : ℝ) ^ 2 = (s2 ^ 2)⁻¹ := by simpa using (inv_pow s2 2)
      _ = (2 : ℝ)⁻¹ := by rw [hs2_sq]
      _ = (1 / 2 : ℝ) := by norm_num
  have hmain :
      local_quad2DDefect μ
          ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • q))
          (p - q) 1 t
        +
        local_quad2DDefect μ
          ((((1 + s : ℝ) : ℂ) • p) + (((s - 1 : ℝ) : ℂ) • q))
          (p + q) 1 t
        =
      s2 ^ 2 *
        (local_quad2DDefect μ ((s2⁻¹ : ℝ) • (p + q) + (s : ℂ) • ((s2⁻¹ : ℝ) • (p - q)))
            ((s2⁻¹ : ℝ) • (p - q)) 1 t
          +
          local_quad2DDefect μ ((s2⁻¹ : ℝ) • (p - q) + (s : ℂ) • ((s2⁻¹ : ℝ) • (p + q)))
            ((s2⁻¹ : ℝ) • (p + q)) 1 t) := by
    have hraw' := hraw
    have hL1 :
        p + q + (s : ℂ) • (p - q) =
          ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • q)) := by
      module
    have hL2 :
        p - q + (s : ℂ) • (p + q) =
          ((((1 + s : ℝ) : ℂ) • p) + (((s - 1 : ℝ) : ℂ) • q)) := by
      module
    rw [hL1, hL2] at hraw'
    simpa [s2] using hraw'
  rw [hmain, hpu, hqv]
  rw [hs2_sq]

lemma local_A_bridge_rhs_as_hadamard_shifted_pair
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t +
      local_quad2DDefect μ (u - (s : ℂ) • v) v 1 t
      =
    (s2 ^ 2 / 4) *
      (local_quad2DDefect μ
          ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • q))
          (p - q) 1 t
        +
        local_quad2DDefect μ
          ((((1 - s : ℝ) : ℂ) • p) + (((1 + s : ℝ) : ℂ) • q))
          (p - q) 1 t) := by
  intro s2 p q
  have hs2_ne : (s2 : ℝ) ≠ 0 := by
    dsimp [s2]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2_mul_inv : s2 * s2⁻¹ = (1 : ℝ) := by
    field_simp [hs2_ne]
  have hXr : (s2 : ℝ) • p = u + v := by
    dsimp [p]
    rw [smul_smul, hs2_mul_inv, one_smul]
  have hYr : (s2 : ℝ) • q = u - v := by
    dsimp [q]
    rw [smul_smul, hs2_mul_inv, one_smul]
  have hX : u + v = (s2 : ℂ) • p := by
    change u + v = (s2 : ℝ) • p
    exact hXr.symm
  have hY : u - v = (s2 : ℂ) • q := by
    change u - v = (s2 : ℝ) • q
    exact hYr.symm
  set c : ℝ := s2 / 2
  have h_v :
      v = (c : ℂ) • (p - q) := by
    have hsum : (u + v) - (u - v) = (s2 : ℂ) • p - (s2 : ℂ) • q := by
      simpa [hX, hY]
    have hsum' : (2 : ℂ) • v = (s2 : ℂ) • (p - q) := by
      simpa [two_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_sub] using hsum
    have hhalf := congrArg (fun z : H => ((1 / 2 : ℂ)) • z) hsum'
    have hvc : v = ((2⁻¹ : ℂ) • ((s2 : ℂ) • (p - q))) := by
      simpa [smul_smul] using hhalf
    have hvc' : v = (((2⁻¹ : ℂ) * (s2 : ℂ)) • (p - q)) := by
      calc
        v = (2⁻¹ : ℂ) • ((s2 : ℂ) • (p - q)) := hvc
        _ = (((2⁻¹ : ℂ) * (s2 : ℂ)) • (p - q)) := by
              rw [smul_smul]
    have hs2_half : ((2⁻¹ : ℂ) * (s2 : ℂ)) = (c : ℂ) := by
      dsimp [c]
      norm_num [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    simpa [hs2_half] using hvc'
  have h_plus :
      u + (s : ℂ) • v
        =
      (c : ℂ) •
        ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • q)) := by
    have huv_id :
        u + (s : ℂ) • v
          =
        ((((1 + s : ℝ) / 2 : ℝ) : ℂ) • (u + v))
          +
        ((((1 - s : ℝ) / 2 : ℝ) : ℂ) • (u - v)) := by
      have hcoeff_u_real : ((1 + s : ℝ) / 2) + ((1 - s : ℝ) / 2) = 1 := by
        ring
      have hcoeff_v_real : ((1 + s : ℝ) / 2) - ((1 - s : ℝ) / 2) = s := by
        ring
      have hcoeff_u :
          ((((1 + s : ℝ) / 2 : ℝ) : ℂ) + (((1 - s : ℝ) / 2 : ℝ) : ℂ)) = (1 : ℂ) := by
        exact_mod_cast hcoeff_u_real
      have hcoeff_v :
          ((((1 + s : ℝ) / 2 : ℝ) : ℂ) - (((1 - s : ℝ) / 2 : ℝ) : ℂ)) = (s : ℂ) := by
        exact_mod_cast hcoeff_v_real
      have htmp :
          ((((1 + s : ℝ) / 2 : ℝ) : ℂ) • (u + v))
            +
          ((((1 - s : ℝ) / 2 : ℝ) : ℂ) • (u - v))
            =
          u + (s : ℂ) • v := by
        calc
          ((((1 + s : ℝ) / 2 : ℝ) : ℂ) • (u + v))
              +
            ((((1 - s : ℝ) / 2 : ℝ) : ℂ) • (u - v))
              =
            ((((1 + s : ℝ) / 2 : ℝ) : ℂ) + (((1 - s : ℝ) / 2 : ℝ) : ℂ)) • u
              +
            ((((1 + s : ℝ) / 2 : ℝ) : ℂ) - (((1 - s : ℝ) / 2 : ℝ) : ℂ)) • v := by
                module
          _ = (1 : ℂ) • u + (s : ℂ) • v := by rw [hcoeff_u, hcoeff_v]
          _ = u + (s : ℂ) • v := by simp
      exact htmp.symm
    calc
      u + (s : ℂ) • v
          =
        ((((1 + s : ℝ) / 2 : ℝ) : ℂ) • (u + v))
          +
        ((((1 - s : ℝ) / 2 : ℝ) : ℂ) • (u - v)) := huv_id
      _ =
        ((((1 + s : ℝ) / 2 : ℝ) : ℂ) • ((s2 : ℂ) • p))
          +
        ((((1 - s : ℝ) / 2 : ℝ) : ℂ) • ((s2 : ℂ) • q)) := by rw [hX, hY]
      _ =
        (c : ℂ) •
          ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • q)) := by
            dsimp [c]
            simp [smul_add, smul_smul]
            ring_nf
  have h_minus :
      u - (s : ℂ) • v
        =
      (c : ℂ) •
        ((((1 - s : ℝ) : ℂ) • p) + (((1 + s : ℝ) : ℂ) • q)) := by
    have huv_id :
        u - (s : ℂ) • v
          =
        ((((1 - s : ℝ) / 2 : ℝ) : ℂ) • (u + v))
          +
        ((((1 + s : ℝ) / 2 : ℝ) : ℂ) • (u - v)) := by
      have hcoeff_u_real : ((1 - s : ℝ) / 2) + ((1 + s : ℝ) / 2) = 1 := by
        ring
      have hcoeff_v_real : ((1 - s : ℝ) / 2) - ((1 + s : ℝ) / 2) = -s := by
        ring
      have hcoeff_u :
          ((((1 - s : ℝ) / 2 : ℝ) : ℂ) + (((1 + s : ℝ) / 2 : ℝ) : ℂ)) = (1 : ℂ) := by
        exact_mod_cast hcoeff_u_real
      have hcoeff_v :
          ((((1 - s : ℝ) / 2 : ℝ) : ℂ) - (((1 + s : ℝ) / 2 : ℝ) : ℂ)) = (-s : ℂ) := by
        exact_mod_cast hcoeff_v_real
      have htmp :
          ((((1 - s : ℝ) / 2 : ℝ) : ℂ) • (u + v))
            +
          ((((1 + s : ℝ) / 2 : ℝ) : ℂ) • (u - v))
            =
          u - (s : ℂ) • v := by
        calc
          ((((1 - s : ℝ) / 2 : ℝ) : ℂ) • (u + v))
              +
            ((((1 + s : ℝ) / 2 : ℝ) : ℂ) • (u - v))
              =
            ((((1 - s : ℝ) / 2 : ℝ) : ℂ) + (((1 + s : ℝ) / 2 : ℝ) : ℂ)) • u
              +
            ((((1 - s : ℝ) / 2 : ℝ) : ℂ) - (((1 + s : ℝ) / 2 : ℝ) : ℂ)) • v := by
                module
          _ = (1 : ℂ) • u + ((-s : ℂ) • v) := by rw [hcoeff_u, hcoeff_v]
          _ = u - (s : ℂ) • v := by simp [sub_eq_add_neg]
      exact htmp.symm
    calc
      u - (s : ℂ) • v
          =
        ((((1 - s : ℝ) / 2 : ℝ) : ℂ) • (u + v))
          +
        ((((1 + s : ℝ) / 2 : ℝ) : ℂ) • (u - v)) := huv_id
      _ =
        ((((1 - s : ℝ) / 2 : ℝ) : ℂ) • ((s2 : ℂ) • p))
          +
        ((((1 + s : ℝ) / 2 : ℝ) : ℂ) • ((s2 : ℂ) • q)) := by rw [hX, hY]
      _ =
        (c : ℂ) •
          ((((1 - s : ℝ) : ℂ) • p) + (((1 + s : ℝ) : ℂ) • q)) := by
            dsimp [c]
            simp [smul_add, smul_smul]
            ring_nf
  rw [h_plus, h_minus, h_v]
  have hd1 := local_quad2DDefect_real_scale μ
    ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • q))
    (p - q) c 1 t
  have hd2 := local_quad2DDefect_real_scale μ
    ((((1 - s : ℝ) : ℂ) • p) + (((1 + s : ℝ) : ℂ) • q))
    (p - q) c 1 t
  have hc_sq : c ^ 2 = s2 ^ 2 / 4 := by
    dsimp [c]
    ring
  rw [hc_sq] at hd1 hd2
  linarith [hd1, hd2]

lemma local_A_bridge_rhs_as_hadamard_shifted_pair_swap
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    local_quad2DDefect μ (v + (s : ℂ) • u) u 1 t +
      local_quad2DDefect μ (v - (s : ℂ) • u) u 1 t
      =
    (s2 ^ 2 / 4) *
      (local_quad2DDefect μ
          ((((1 + s : ℝ) : ℂ) • p) + (((s - 1 : ℝ) : ℂ) • q))
          (p + q) 1 t
        +
        local_quad2DDefect μ
          ((((1 - s : ℝ) : ℂ) • p) + (((-1 - s : ℝ) : ℂ) • q))
          (p + q) 1 t) := by
  intro s2 p q
  have hswap :=
    local_A_bridge_rhs_as_hadamard_shifted_pair μ v u s t
  have hp : (s2⁻¹ : ℝ) • (v + u) = p := by
    dsimp [p]
    module
  have hq : (s2⁻¹ : ℝ) • (v - u) = -q := by
    dsimp [q]
    module
  calc
    local_quad2DDefect μ (v + (s : ℂ) • u) u 1 t +
        local_quad2DDefect μ (v - (s : ℂ) • u) u 1 t
        =
      (s2 ^ 2 / 4) *
        (local_quad2DDefect μ
            ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • (-q)))
            (p - (-q)) 1 t
          +
          local_quad2DDefect μ
            ((((1 - s : ℝ) : ℂ) • p) + (((1 + s : ℝ) : ℂ) • (-q)))
            (p - (-q)) 1 t) := by
              simpa [s2, p, q, sub_eq_add_neg, smul_add, add_smul, smul_sub, sub_smul,
                add_assoc, add_left_comm, add_comm] using hswap
    _ =
      (s2 ^ 2 / 4) *
        (local_quad2DDefect μ
            ((((1 + s : ℝ) : ℂ) • p) + (((s - 1 : ℝ) : ℂ) • q))
            (p + q) 1 t
          +
          local_quad2DDefect μ
            ((((1 - s : ℝ) : ℂ) • p) + (((-1 - s : ℝ) : ℂ) • q))
            (p + q) 1 t) := by
              have harg1 :
                  ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • (-q))) =
                    ((((1 + s : ℝ) : ℂ) • p) + (((s - 1 : ℝ) : ℂ) • q)) := by
                module
              have harg2 :
                  ((((1 - s : ℝ) : ℂ) • p) + (((1 + s : ℝ) : ℂ) • (-q))) =
                    ((((1 - s : ℝ) : ℂ) • p) + (((-1 - s : ℝ) : ℂ) • q)) := by
                module
              have hbase : p - (-q) = p + q := by
                module
              rw [harg1, harg2, hbase]

lemma local_A_bridge_lhs_as_hadamard_shifted_pair_swap
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    local_quad2DDefect μ (v + u + (s : ℂ) • (v - u)) (v - u) 1 t +
      local_quad2DDefect μ (v - u + (s : ℂ) • (v + u)) (v + u) 1 t
      =
    s2 ^ 2 *
      (local_quad2DDefect μ (p - (s : ℂ) • q) q 1 t +
        local_quad2DDefect μ (q - (s : ℂ) • p) p 1 t) := by
  intro s2 p q
  have hswap :=
    local_A_bridge_lhs_as_hadamard_shifted_pair μ v u s t
  have hp : (s2⁻¹ : ℝ) • (v + u) = p := by
    dsimp [p]
    module
  have hq : (s2⁻¹ : ℝ) • (v - u) = -q := by
    dsimp [q]
    module
  calc
    local_quad2DDefect μ (v + u + (s : ℂ) • (v - u)) (v - u) 1 t +
        local_quad2DDefect μ (v - u + (s : ℂ) • (v + u)) (v + u) 1 t
        =
      s2 ^ 2 *
        (local_quad2DDefect μ (p + (s : ℂ) • (-q)) (-q) 1 t +
          local_quad2DDefect μ ((-q) + (s : ℂ) • p) p 1 t) := by
            simpa [s2, p, q, sub_eq_add_neg, smul_add, add_smul, smul_sub, sub_smul,
              add_assoc, add_left_comm, add_comm] using hswap
    _ =
      s2 ^ 2 *
        (local_quad2DDefect μ (p - (s : ℂ) • q) q 1 t +
          local_quad2DDefect μ (q - (s : ℂ) • p) p 1 t) := by
            have harg1 : p + (s : ℂ) • (-q) = p - (s : ℂ) • q := by
              module
            have harg2 : (-q) + (s : ℂ) • p = -(q - (s : ℂ) • p) := by
              module
            rw [harg1, harg2]
            rw [local_quad2DDefect_neg_right μ (p - (s : ℂ) • q) q 1 t]
            rw [local_quad2DDefect_neg_left μ (q - (s : ℂ) • p) p 1 t]

lemma hadamard_core_identity_reduce_to_Bsum
    (μ : FrameFunction H) (p q X Y : H) (s t : ℝ)
    (hRsum :
      local_quad2DDefect μ
          ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • q))
          Y 1 t
        +
        local_quad2DDefect μ
          ((((1 - s : ℝ) : ℂ) • p) + (((1 + s : ℝ) : ℂ) • q))
          Y 1 t
        =
      local_defect_residual_mix μ X Y Y s t + 2 * local_quad2DDefect μ X Y 1 t)
    (hYsum :
      local_quad2DDefect μ
          ((((1 + s : ℝ) : ℂ) • p) + (((s - 1 : ℝ) : ℂ) • q))
          X 1 t
        +
        local_quad2DDefect μ
          ((((1 - s : ℝ) : ℂ) • p) + (((-1 - s : ℝ) : ℂ) • q))
          X 1 t
        =
      local_defect_residual_mix μ Y X X s t + 2 * local_quad2DDefect μ Y X 1 t)
    (hmix0 :
      local_defect_residual_mix μ X Y Y s t +
        local_defect_residual_mix μ Y X X s t = 0)
    (hD0 :
      local_quad2DDefect μ X Y 1 t + local_quad2DDefect μ Y X 1 t = 0)
    (hsum_pairs :
      local_quad2DDefect μ (p + (s : ℂ) • q) q 1 t +
          local_quad2DDefect μ (p - (s : ℂ) • q) q 1 t
        +
        (local_quad2DDefect μ (q + (s : ℂ) • p) p 1 t +
          local_quad2DDefect μ (q - (s : ℂ) • p) p 1 t)
        = 0) :
    (2 * (local_quad2DDefect μ (p + (s : ℂ) • q) q 1 t +
          local_quad2DDefect μ (q + (s : ℂ) • p) p 1 t) =
        (2 / 4) *
          (local_quad2DDefect μ
              ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • q))
              Y 1 t
            +
            local_quad2DDefect μ
              ((((1 - s : ℝ) : ℂ) • p) + (((1 + s : ℝ) : ℂ) • q))
              Y 1 t))
      ↔
    (local_quad2DDefect μ
        ((((1 + s : ℝ) : ℂ) • p) + (((s - 1 : ℝ) : ℂ) • q))
        X 1 t
      +
      local_quad2DDefect μ
        ((((1 - s : ℝ) : ℂ) • p) + (((-1 - s : ℝ) : ℂ) • q))
        X 1 t
      =
    4 * (local_quad2DDefect μ (p - (s : ℂ) • q) q 1 t +
      local_quad2DDefect μ (q - (s : ℂ) • p) p 1 t)) := by
  let Cplus : ℝ :=
    local_quad2DDefect μ (p + (s : ℂ) • q) q 1 t +
      local_quad2DDefect μ (q + (s : ℂ) • p) p 1 t
  let Cminus : ℝ :=
    local_quad2DDefect μ (p - (s : ℂ) • q) q 1 t +
      local_quad2DDefect μ (q - (s : ℂ) • p) p 1 t
  let Asum : ℝ :=
    local_quad2DDefect μ
        ((((1 + s : ℝ) : ℂ) • p) + (((1 - s : ℝ) : ℂ) • q))
        Y 1 t
      +
      local_quad2DDefect μ
        ((((1 - s : ℝ) : ℂ) • p) + (((1 + s : ℝ) : ℂ) • q))
        Y 1 t
  let Bsum : ℝ :=
    local_quad2DDefect μ
        ((((1 + s : ℝ) : ℂ) • p) + (((s - 1 : ℝ) : ℂ) • q))
        X 1 t
      +
      local_quad2DDefect μ
        ((((1 - s : ℝ) : ℂ) • p) + (((-1 - s : ℝ) : ℂ) • q))
        X 1 t
  change (2 * Cplus = (2 / 4) * Asum) ↔ (Bsum = 4 * Cminus)
  have hAeq :
      Asum =
        local_defect_residual_mix μ X Y Y s t + 2 * local_quad2DDefect μ X Y 1 t := by
    dsimp [Asum]
    convert hRsum using 1 <;> ring
  have hBeq :
      Bsum =
        local_defect_residual_mix μ Y X X s t + 2 * local_quad2DDefect μ Y X 1 t := by
    dsimp [Bsum]
    convert hYsum using 1 <;> ring
  have hAB : Asum + Bsum = 0 := by
    linarith [hAeq, hBeq, hmix0, hD0]
  have hCC : Cplus + Cminus = 0 := by
    dsimp [Cplus, Cminus]
    simpa [add_assoc, add_left_comm, add_comm] using hsum_pairs
  constructor
  · intro hmain
    have hA : Asum = 4 * Cplus := by
      have hmain' : 2 * Cplus = (1 / 2 : ℝ) * Asum := by
        have hhalf : (2 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
        simpa [hhalf] using hmain
      nlinarith [hmain']
    have hB : Bsum = 4 * Cminus := by
      linarith [hAB, hCC, hA]
    exact hB
  · intro hmain
    have hB : Bsum = 4 * Cminus := hmain
    have hA : Asum = 4 * Cplus := by
      linarith [hAB, hCC, hB]
    have hmain' : 2 * Cplus = (1 / 2 : ℝ) * Asum := by
      nlinarith [hA]
    have hhalf : (2 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
    simpa [hhalf] using hmain'


end
