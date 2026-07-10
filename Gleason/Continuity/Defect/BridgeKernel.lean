import Gleason.Continuity.Defect.HadamardTransform

noncomputable section

open GleasonBridge RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

lemma hadamard_bridge_error_add_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r) =
      -GleasonBridge.local_defect_g μ u v r := by
  have hodd : hadamard_residual_one μ u v (-r) = -hadamard_residual_one μ u v r := by
    simpa using hadamard_residual_one_odd hdim μ u v hu hv huv r
  have heven : GleasonBridge.local_defect_g μ u v (-r) = GleasonBridge.local_defect_g μ u v r := by
    simpa using GleasonBridge.local_defect_g_even μ u v r
  unfold hadamard_bridge_error
  rw [hodd, heven]
  ring

lemma hadamard_bridge_error_neg_one
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    hadamard_bridge_error μ u v (-1) = 0 := by
  have hadd :=
    hadamard_bridge_error_add_neg hdim μ u v hu hv huv 1
  have h1 : hadamard_bridge_error μ u v 1 = 0 :=
    hadamard_bridge_error_one hdim μ u v hu hv huv
  have hg1 : GleasonBridge.local_defect_g μ u v 1 = 0 :=
    GleasonBridge.local_defect_g_one_eq_zero hdim μ u v hu hv huv
  linarith [hadd, h1, hg1]

lemma hadamard_bridge_error_sq_one
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (hr : r ^ 2 = 1) :
    hadamard_bridge_error μ u v r = 0 := by
  have hsq : r ^ 2 = (1 : ℝ) ^ 2 := by simpa using hr
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hr1 | hr1
  · simpa [hr1] using hadamard_bridge_error_one hdim μ u v hu hv huv
  · simpa [hr1] using hadamard_bridge_error_neg_one hdim μ u v hu hv huv

lemma hadamard_bridge_error_sub_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r) =
      2 * hadamard_residual_one μ u v r := by
  have hodd : hadamard_residual_one μ u v (-r) = -hadamard_residual_one μ u v r := by
    simpa using hadamard_residual_one_odd hdim μ u v hu hv huv r
  have heven : GleasonBridge.local_defect_g μ u v (-r) = GleasonBridge.local_defect_g μ u v r := by
    simpa using GleasonBridge.local_defect_g_even μ u v r
  unfold hadamard_bridge_error
  rw [hodd, heven]
  ring

lemma local_defect_g_eq_bridge_error_symm
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    GleasonBridge.local_defect_g μ u v r =
      -(hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)) := by
  have hsum := hadamard_bridge_error_add_neg hdim μ u v hu hv huv r
  linarith [hsum]

lemma hadamard_residual_one_eq_bridge_error_antisymm
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    hadamard_residual_one μ u v r =
      (hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)) / 2 := by
  have hdiff := hadamard_bridge_error_sub_neg hdim μ u v hu hv huv r
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hscaled :
      (2 : ℝ) * hadamard_residual_one μ u v r =
        hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r) := by
    linarith [hdiff]
  have hdiv := congrArg (fun x : ℝ => x / 2) hscaled
  simpa [h2, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

lemma hadamard_bridge_error_as_scaled_defect_gap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    let s2 : ℝ := Real.sqrt 2
    hadamard_bridge_error μ u v r =
      local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) -
        local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) := by
  intro s2
  have hres :
      hadamard_residual_one μ u v r =
        local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) := by
    unfold hadamard_residual_one
    simpa [s2] using
      (local_quad2DCross_residual_hadamard_step hdim μ u v hu hv huv (1 : ℝ) r)
  have hhom := GleasonBridge.local_quad2DDefect_hom μ u v (s2⁻¹) (1 : ℝ) r
  have hs2_sq : (s2⁻¹ : ℝ) ^ 2 = (1 / 2 : ℝ) := by
    have hs2_nonneg : (0 : ℝ) ≤ 2 := by norm_num
    have hs2_def : s2 ^ 2 = 2 := by
      dsimp [s2]
      exact Real.sq_sqrt hs2_nonneg
    calc
      (s2⁻¹ : ℝ) ^ 2 = (s2 ^ 2)⁻¹ := by simpa using (inv_pow s2 2)
      _ = (2 : ℝ)⁻¹ := by rw [hs2_def]
      _ = (1 / 2 : ℝ) := by norm_num
  have hhalf :
      local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) =
        (1 / 2 : ℝ) * local_defect_g μ u v r := by
    calc
      local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹)
          = (s2⁻¹ : ℝ) ^ 2 * local_quad2DDefect μ u v 1 r := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hhom
      _ = (1 / 2 : ℝ) * local_quad2DDefect μ u v 1 r := by rw [hs2_sq]
      _ = (1 / 2 : ℝ) * local_defect_g μ u v r := by rfl
  unfold hadamard_bridge_error
  linarith [hres, hhalf]

lemma local_quad2DDefect_dyadic_gap_eq_scaled_bridge_error
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) (hab : a + b ≠ 0) :
    local_quad2DDefect μ u v a b -
        local_quad2DDefect μ u v ((a + b) / 2) ((a - b) / 2)
      =
    (((a + b) / (Real.sqrt 2)) ^ 2) *
      hadamard_bridge_error μ u v ((a - b) / (a + b)) := by
  set s2 : ℝ := Real.sqrt 2
  set r : ℝ := (a - b) / (a + b)
  set lam : ℝ := (a + b) / s2
  have hs2_sq : s2 ^ 2 = 2 := by
    dsimp [s2]
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs2_inv_sq : (s2⁻¹ : ℝ) ^ 2 = (1 / 2 : ℝ) := by
    calc
      (s2⁻¹ : ℝ) ^ 2 = (s2 ^ 2)⁻¹ := by simpa using (inv_pow s2 2)
      _ = (2 : ℝ)⁻¹ := by rw [hs2_sq]
      _ = (1 / 2 : ℝ) := by norm_num
  have hE :
      hadamard_bridge_error μ u v r =
        local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) -
          local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) := by
    simpa [s2, r] using
      (hadamard_bridge_error_as_scaled_defect_gap hdim μ u v hu hv huv r)
  have hhom_plus :=
    GleasonBridge.local_quad2DDefect_hom μ u v lam ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹)
  have hhom_mid :=
    GleasonBridge.local_quad2DDefect_hom μ u v lam (1 * s2⁻¹) (r * s2⁻¹)
  have hplus_a : lam * ((1 + r) * s2⁻¹) = a := by
    calc
      lam * ((1 + r) * s2⁻¹) = (a + b) * (1 + r) * ((s2⁻¹ : ℝ) ^ 2) := by
        dsimp [lam]
        ring
      _ = (a + b) * (1 + r) * (1 / 2 : ℝ) := by rw [hs2_inv_sq]
      _ = a := by
        dsimp [r]
        field_simp [hab]
        ring
  have hplus_b : lam * ((1 - r) * s2⁻¹) = b := by
    calc
      lam * ((1 - r) * s2⁻¹) = (a + b) * (1 - r) * ((s2⁻¹ : ℝ) ^ 2) := by
        dsimp [lam]
        ring
      _ = (a + b) * (1 - r) * (1 / 2 : ℝ) := by rw [hs2_inv_sq]
      _ = b := by
        dsimp [r]
        field_simp [hab]
        ring
  have hmid_a : lam * (1 * s2⁻¹) = (a + b) / 2 := by
    calc
      lam * (1 * s2⁻¹) = (a + b) * ((s2⁻¹ : ℝ) ^ 2) := by
        dsimp [lam]
        ring
      _ = (a + b) * (1 / 2 : ℝ) := by rw [hs2_inv_sq]
      _ = (a + b) / 2 := by ring
  have hmid_b : lam * (r * s2⁻¹) = (a - b) / 2 := by
    calc
      lam * (r * s2⁻¹) = (a + b) * r * ((s2⁻¹ : ℝ) ^ 2) := by
        dsimp [lam]
        ring
      _ = (a + b) * r * (1 / 2 : ℝ) := by rw [hs2_inv_sq]
      _ = (a - b) / 2 := by
        dsimp [r]
        field_simp [hab]
  have hscale_plus :
      local_quad2DDefect μ u v a b =
        lam ^ 2 * local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) := by
    calc
      local_quad2DDefect μ u v a b
          = local_quad2DDefect μ u v (lam * ((1 + r) * s2⁻¹)) (lam * ((1 - r) * s2⁻¹)) := by
              rw [hplus_a, hplus_b]
      _ = lam ^ 2 * local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hhom_plus
  have hscale_mid :
      local_quad2DDefect μ u v ((a + b) / 2) ((a - b) / 2) =
        lam ^ 2 * local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) := by
    calc
      local_quad2DDefect μ u v ((a + b) / 2) ((a - b) / 2)
          = local_quad2DDefect μ u v (lam * (1 * s2⁻¹)) (lam * (r * s2⁻¹)) := by
              rw [hmid_a, hmid_b]
      _ = lam ^ 2 * local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hhom_mid
  calc
    local_quad2DDefect μ u v a b -
        local_quad2DDefect μ u v ((a + b) / 2) ((a - b) / 2)
        =
      lam ^ 2 * local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) -
        lam ^ 2 * local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) := by
          rw [hscale_plus, hscale_mid]
    _ =
      lam ^ 2 *
        (local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) -
          local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹)) := by
            ring
    _ = lam ^ 2 * hadamard_bridge_error μ u v r := by rw [← hE]
    _ =
      (((a + b) / (Real.sqrt 2)) ^ 2) *
        hadamard_bridge_error μ u v ((a - b) / (a + b)) := by
          simp [lam, r, s2]

lemma local_quad2DDefect_dyadic_of_bridge_error_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hE : ∀ r : ℝ, hadamard_bridge_error μ u v r = 0)
    (a b : ℝ) :
    local_quad2DDefect μ u v a b =
      local_quad2DDefect μ u v ((a + b) / 2) ((a - b) / 2) := by
  by_cases hab : a + b = 0
  · have hb : b = -a := by linarith
    subst hb
    have h11 : local_quad2DDefect μ u v 1 1 = 0 := by
      simpa [local_defect_g] using
        GleasonBridge.local_defect_g_one_eq_zero hdim μ u v hu hv huv
    have hdiag : ∀ t : ℝ, local_quad2DDefect μ u v t t = 0 := by
      intro t
      have hhom := GleasonBridge.local_quad2DDefect_hom μ u v t 1 1
      have : local_quad2DDefect μ u v (t * 1) (t * 1) =
          t ^ 2 * local_quad2DDefect μ u v 1 1 := by
        simpa using hhom
      simpa [h11] using this
    have hanti : ∀ t : ℝ, local_quad2DDefect μ u v t (-t) = 0 := by
      intro t
      have heven :
          local_quad2DDefect μ u v t (-t) = local_quad2DDefect μ u v t t := by
        simpa using GleasonBridge.local_quad2DDefect_even_b μ u v t t
      rw [heven, hdiag t]
    have hzero : local_quad2DDefect μ u v 0 a = 0 := by
      simpa using GleasonBridge.local_quad2DDefect_zero_left μ u v a
    have hmain : local_quad2DDefect μ u v a (-a) = local_quad2DDefect μ u v 0 a :=
      (hanti a).trans hzero.symm
    have hA0 : (a + (-a)) / 2 = 0 := by ring
    have hA1 : (a - (-a)) / 2 = a := by ring
    simpa [hA0, hA1] using hmain
  · have hgap :=
      local_quad2DDefect_dyadic_gap_eq_scaled_bridge_error
        hdim μ u v hu hv huv a b hab
    have hsub :
        local_quad2DDefect μ u v a b -
          local_quad2DDefect μ u v ((a + b) / 2) ((a - b) / 2) = 0 := by
      simpa [hE ((a - b) / (a + b))] using hgap
    exact sub_eq_zero.mp hsub

lemma hadamard_bridge_error_eq_zero_iff_scaled_defect
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    hadamard_bridge_error μ u v r = 0
      ↔
    local_quad2DDefect μ u v ((1 + r) * (Real.sqrt 2)⁻¹) ((1 - r) * (Real.sqrt 2)⁻¹) =
      local_quad2DDefect μ u v (1 * (Real.sqrt 2)⁻¹) (r * (Real.sqrt 2)⁻¹) := by
  constructor <;> intro h
  · let s2 : ℝ := Real.sqrt 2
    have hrepr :
        hadamard_bridge_error μ u v r =
          local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) -
            local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) := by
      simpa [s2] using
        (hadamard_bridge_error_as_scaled_defect_gap hdim μ u v hu hv huv r)
    have hscaled :
        local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) =
          local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) := by
      linarith [h, hrepr]
    simpa [s2] using hscaled
  · let s2 : ℝ := Real.sqrt 2
    have hscaled :
        local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) =
          local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) := by
      simpa [s2] using h
    have hrepr :
        hadamard_bridge_error μ u v r =
          local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) -
            local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) := by
      simpa [s2] using
        (hadamard_bridge_error_as_scaled_defect_gap hdim μ u v hu hv huv r)
    linarith [hscaled, hrepr]

lemma hadamard_bridge_error_mobius_sum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r) =
      -(1 + r) ^ 2 *
        (hadamard_bridge_error μ u v ((1 - r) / (1 + r)) +
          hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))) := by
  set φ : ℝ := (1 - r) / (1 + r)
  have hres_mob :
      hadamard_residual_one μ u v r =
        ((1 + r) ^ 2 / 2) * GleasonBridge.local_defect_g μ u v φ := by
    simpa [φ] using
      hadamard_residual_one_eq_mobius_scaled_local_defect hdim μ u v hu hv huv r h1pr
  have hleft :
      hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r) =
        2 * hadamard_residual_one μ u v r := by
    simpa using hadamard_bridge_error_sub_neg hdim μ u v hu hv huv r
  have hsym_φ :
      GleasonBridge.local_defect_g μ u v φ =
        -(hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)) := by
    simpa [φ] using local_defect_g_eq_bridge_error_symm hdim μ u v hu hv huv φ
  calc
    hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)
        = 2 * hadamard_residual_one μ u v r := hleft
    _ = (1 + r) ^ 2 * GleasonBridge.local_defect_g μ u v φ := by
          linarith [hres_mob]
    _ = -(1 + r) ^ 2 *
          (hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)) := by
          rw [hsym_φ]
          ring
    _ = -(1 + r) ^ 2 *
          (hadamard_bridge_error μ u v ((1 - r) / (1 + r)) +
            hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))) := by
          simp [φ]

lemma hadamard_bridge_error_mobius_diff
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    (1 + r) ^ 2 *
      (hadamard_bridge_error μ u v ((1 - r) / (1 + r)) -
        hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))) =
      -4 * (hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)) := by
  set φ : ℝ := (1 - r) / (1 + r)
  have hhalf :
      ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v φ =
        (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by
    simpa [φ] using
      (hadamard_residual_half_step_eq_half_local_defect hdim μ u v hu hv huv r h1pr)
  have hres_φ :
      hadamard_residual_one μ u v φ =
        (hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ)) / 2 := by
    simpa [φ] using
      hadamard_residual_one_eq_bridge_error_antisymm hdim μ u v hu hv huv φ
  have hsym_r :
      GleasonBridge.local_defect_g μ u v r =
        -(hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)) := by
    simpa using local_defect_g_eq_bridge_error_symm hdim μ u v hu hv huv r
  have hmain :
      ((1 + r) ^ 2 / 8) *
          (hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ))
        =
      -(1 / 2 : ℝ) *
          (hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)) := by
    have hhalf' :
        ((1 + r) ^ 2 / 8) *
            (hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ))
          =
        (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by
      rw [hres_φ] at hhalf
      linarith [hhalf]
    rw [hsym_r] at hhalf'
    linarith [hhalf']
  have hmul := congrArg (fun x : ℝ => 8 * x) hmain
  calc
    (1 + r) ^ 2 *
        (hadamard_bridge_error μ u v ((1 - r) / (1 + r)) -
          hadamard_bridge_error μ u v (-( (1 - r) / (1 + r))))
        =
      (1 + r) ^ 2 * (hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ)) := by
          simp [φ]
    _ = -4 * (hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)) := by
          linarith [hmul]

lemma hadamard_bridge_error_mobius_linearized
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    2 * (1 + r) ^ 2 * hadamard_bridge_error μ u v ((1 - r) / (1 + r)) =
      -(5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r))
      ∧
    2 * (1 + r) ^ 2 * hadamard_bridge_error μ u v (-( (1 - r) / (1 + r))) =
      3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r) := by
  set φ : ℝ := (1 - r) / (1 + r)
  have hsum := hadamard_bridge_error_mobius_sum hdim μ u v hu hv huv r h1pr
  have hdiff := hadamard_bridge_error_mobius_diff hdim μ u v hu hv huv r h1pr
  have hsum' :
      hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r) =
        -(1 + r) ^ 2 * (hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)) := by
    simpa [φ] using hsum
  have hdiff' :
      (1 + r) ^ 2 * (hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ)) =
        -4 * (hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)) := by
    simpa [φ] using hdiff
  have hEφ :
      2 * (1 + r) ^ 2 * hadamard_bridge_error μ u v φ =
        -(5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r)) := by
    linarith [hsum', hdiff']
  have hEnegφ :
      2 * (1 + r) ^ 2 * hadamard_bridge_error μ u v (-φ) =
        3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r) := by
    linarith [hsum', hdiff']
  constructor
  · simpa [φ] using hEφ
  · simpa [φ] using hEnegφ

lemma hadamard_bridge_error_mobius_symm_antisymm
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let φ : ℝ := (1 - r) / (1 + r)
    (1 + r) ^ 2 *
        (hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ))
      =
    -(hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r))
    ∧
    (1 + r) ^ 2 *
        (hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ))
      =
    -4 * (hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)) := by
  intro φ
  rcases hadamard_bridge_error_mobius_linearized hdim μ u v hu hv huv r h1pr with
    ⟨hEφ, hEnegφ⟩
  constructor
  · linarith [hEφ, hEnegφ]
  · linarith [hEφ, hEnegφ]

lemma hadamard_bridge_error_mobius_symm_antisymm_abs
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let φ : ℝ := (1 - r) / (1 + r)
    (1 + r) ^ 2 *
        |hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)|
      =
    |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)|
    ∧
    (1 + r) ^ 2 *
        |hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ)|
      =
    4 * |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)| := by
  intro φ
  rcases hadamard_bridge_error_mobius_symm_antisymm hdim μ u v hu hv huv r h1pr with
    ⟨hsym, hanti⟩
  have hfac_nonneg : 0 ≤ (1 + r) ^ 2 := sq_nonneg (1 + r)
  constructor
  · simpa [abs_mul, abs_of_nonneg hfac_nonneg, abs_neg, abs_sub_comm] using congrArg abs hsym
  · have h := congrArg abs hanti
    simpa [abs_mul, abs_of_nonneg hfac_nonneg, abs_neg] using h

lemma hadamard_bridge_error_bridge_form_mobius_duality
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let φ : ℝ := (1 - r) / (1 + r)
    (2 * |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)|
        ≤
      |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)|)
      ↔
    (|hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ)|
        ≤
      2 * |hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)|) := by
  intro φ
  rcases hadamard_bridge_error_mobius_symm_antisymm_abs hdim μ u v hu hv huv r h1pr with
    ⟨hsym_abs, hanti_abs⟩
  have hfac_pos : 0 < (1 + r) ^ 2 := by
    exact sq_pos_of_ne_zero h1pr
  constructor
  · intro hdom
    have hscaled :
        (1 + r) ^ 2 *
            |hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ)|
          ≤
        (1 + r) ^ 2 *
            (2 * |hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)|) := by
      calc
        (1 + r) ^ 2 * |hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ)|
            = 4 * |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)| := hanti_abs
        _ ≤ 2 * |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| := by
              nlinarith [hdom]
        _ = (1 + r) ^ 2 *
              (2 * |hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)|) := by
              calc
                2 * |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)|
                    = 2 * ((1 + r) ^ 2 *
                        |hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)|) := by
                          rw [hsym_abs]
                _ = (1 + r) ^ 2 *
                      (2 * |hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)|) := by
                      ring
    nlinarith [hscaled, hfac_pos]
  · intro hdom
    have hscaled :
        (1 + r) ^ 2 *
            |hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ)|
          ≤
        (1 + r) ^ 2 *
            (2 * |hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)|) := by
      exact mul_le_mul_of_nonneg_left hdom (sq_nonneg (1 + r))
    have hineq :
        4 * |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)|
          ≤
        2 * |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| := by
      calc
        4 * |hadamard_bridge_error μ u v r + hadamard_bridge_error μ u v (-r)|
            =
          (1 + r) ^ 2 *
            |hadamard_bridge_error μ u v φ - hadamard_bridge_error μ u v (-φ)| := by
              simpa using hanti_abs.symm
        _ ≤
          (1 + r) ^ 2 *
            (2 * |hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)|) := hscaled
        _ = 2 * |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| := by
              calc
                (1 + r) ^ 2 *
                    (2 * |hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)|)
                    =
                  2 * ((1 + r) ^ 2 *
                    |hadamard_bridge_error μ u v φ + hadamard_bridge_error μ u v (-φ)|) := by
                      ring
                _ = 2 * |hadamard_bridge_error μ u v r - hadamard_bridge_error μ u v (-r)| := by
                      rw [hsym_abs]
    nlinarith [hineq]

lemma hadamard_bridge_error_mobius_fixedpoint_sqrt2_sub_one
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    let r0 : ℝ := Real.sqrt 2 - 1
    hadamard_bridge_error μ u v (-r0) = -3 * hadamard_bridge_error μ u v r0 := by
  intro r0
  have h1pr : 1 + r0 ≠ 0 := by
    dsimp [r0]
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    linarith
  have hphi : (1 - r0) / (1 + r0) = r0 := by
    dsimp [r0]
    have hsqrt2_ne : (Real.sqrt 2) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    have hsqrt2_sq : (Real.sqrt 2) ^ 2 = 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    calc
      (1 - (Real.sqrt 2 - 1)) / (1 + (Real.sqrt 2 - 1))
          = (2 - Real.sqrt 2) / Real.sqrt 2 := by ring
      _ = Real.sqrt 2 - 1 := by
            field_simp [hsqrt2_ne]
            nlinarith [hsqrt2_sq]
  have hsq : (1 + r0) ^ 2 = 2 := by
    dsimp [r0]
    have hsq2 : (Real.sqrt 2) ^ 2 = 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    nlinarith [hsq2]
  rcases hadamard_bridge_error_mobius_linearized hdim μ u v hu hv huv r0 h1pr with
    ⟨hlin, _⟩
  rw [hphi, hsq] at hlin
  linarith

lemma hadamard_bridge_error_mobius_abs_linearized
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    2 * (1 + r) ^ 2 * |hadamard_bridge_error μ u v ((1 - r) / (1 + r))|
      ≤ 5 * |hadamard_bridge_error μ u v r| + 3 * |hadamard_bridge_error μ u v (-r)|
      ∧
    2 * (1 + r) ^ 2 * |hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))|
      ≤ 3 * |hadamard_bridge_error μ u v r| + 5 * |hadamard_bridge_error μ u v (-r)| := by
  rcases hadamard_bridge_error_mobius_linearized hdim μ u v hu hv huv r h1pr with
    ⟨hEφ, hEnegφ⟩
  have hEφ_abs : 2 * (1 + r) ^ 2 * |hadamard_bridge_error μ u v ((1 - r) / (1 + r))|
      = |5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r)| := by
    have h := congrArg abs hEφ
    rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
      abs_of_nonneg (sq_nonneg (1 + r)), abs_neg] at h
    exact h
  have hEnegφ_abs : 2 * (1 + r) ^ 2 * |hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))|
      = |3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r)| := by
    have h := congrArg abs hEnegφ
    rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
      abs_of_nonneg (sq_nonneg (1 + r))] at h
    exact h
  constructor
  · rw [hEφ_abs]
    calc
      |5 * hadamard_bridge_error μ u v r + 3 * hadamard_bridge_error μ u v (-r)|
          ≤ |5 * hadamard_bridge_error μ u v r| + |3 * hadamard_bridge_error μ u v (-r)| := by
              exact abs_add_le _ _
      _ = 5 * |hadamard_bridge_error μ u v r| + 3 * |hadamard_bridge_error μ u v (-r)| := by
            rw [abs_mul, abs_mul]
            norm_num
  · rw [hEnegφ_abs]
    calc
      |3 * hadamard_bridge_error μ u v r + 5 * hadamard_bridge_error μ u v (-r)|
          ≤ |3 * hadamard_bridge_error μ u v r| + |5 * hadamard_bridge_error μ u v (-r)| := by
              exact abs_add_le _ _
      _ = 3 * |hadamard_bridge_error μ u v r| + 5 * |hadamard_bridge_error μ u v (-r)| := by
            rw [abs_mul, abs_mul]
            norm_num

lemma hadamard_bridge_error_mobius_max_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    (1 + r) ^ 2 *
      max
        |hadamard_bridge_error μ u v ((1 - r) / (1 + r))|
        |hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))|
      ≤
    4 *
      max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
  rcases hadamard_bridge_error_mobius_abs_linearized hdim μ u v hu hv huv r h1pr with
    ⟨hφ, hnegφ⟩
  have hsq_nn : 0 ≤ (1 + r) ^ 2 := sq_nonneg (1 + r)
  have hφ' :
      (1 + r) ^ 2 * |hadamard_bridge_error μ u v ((1 - r) / (1 + r))|
        ≤
      4 * max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
    have h5 :
        5 * |hadamard_bridge_error μ u v r|
          ≤ 5 * max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
      gcongr
      exact le_max_left _ _
    have h3 :
        3 * |hadamard_bridge_error μ u v (-r)|
          ≤ 3 * max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
      gcongr
      exact le_max_right _ _
    have hsum :
        5 * |hadamard_bridge_error μ u v r| + 3 * |hadamard_bridge_error μ u v (-r)|
          ≤ 8 * max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
      linarith [h5, h3]
    have htmp : 2 * (1 + r) ^ 2 * |hadamard_bridge_error μ u v ((1 - r) / (1 + r))|
        ≤ 8 * max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
      exact le_trans hφ hsum
    nlinarith [htmp]
  have hnegφ' :
      (1 + r) ^ 2 * |hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))|
        ≤
      4 * max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
    have h3 :
        3 * |hadamard_bridge_error μ u v r|
          ≤ 3 * max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
      gcongr
      exact le_max_left _ _
    have h5 :
        5 * |hadamard_bridge_error μ u v (-r)|
          ≤ 5 * max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
      gcongr
      exact le_max_right _ _
    have hsum :
        3 * |hadamard_bridge_error μ u v r| + 5 * |hadamard_bridge_error μ u v (-r)|
          ≤ 8 * max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
      linarith [h3, h5]
    have htmp : 2 * (1 + r) ^ 2 * |hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))|
        ≤ 8 * max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
      exact le_trans hnegφ hsum
    nlinarith [htmp]
  have hmax :
      max
          ((1 + r) ^ 2 * |hadamard_bridge_error μ u v ((1 - r) / (1 + r))|)
          ((1 + r) ^ 2 * |hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))|)
        ≤
      4 * max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)| := by
    exact max_le hφ' hnegφ'
  have hfactor :
      let A := |hadamard_bridge_error μ u v ((1 - r) / (1 + r))|
      let B := |hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))|
      (1 + r) ^ 2 *
          max A B
        =
      max
        ((1 + r) ^ 2 * A)
        ((1 + r) ^ 2 * B) := by
    intro A B
    exact mul_max_of_nonneg A B hsq_nn
  simpa [hfactor] using hmax

lemma max_abs_lincomb_53_lower (x y : ℝ) :
    2 * max |x| |y| ≤ max |5 * x + 3 * y| |3 * x + 5 * y| := by
  set u : ℝ := 5 * x + 3 * y
  set v : ℝ := 3 * x + 5 * y
  have hx : x = (5 * u - 3 * v) / 16 := by
    dsimp [u, v]
    ring
  have hy : y = (-3 * u + 5 * v) / 16 := by
    dsimp [u, v]
    ring
  have hx_le : |x| ≤ (1 / 2 : ℝ) * max |u| |v| := by
    rw [hx]
    calc
      |(5 * u - 3 * v) / 16| = |5 * u - 3 * v| / 16 := by
        rw [abs_div]
        norm_num
      _ ≤ (|5 * u| + |3 * v|) / 16 := by
        gcongr
        exact abs_sub (5 * u) (3 * v)
      _ = (5 * |u| + 3 * |v|) / 16 := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ (5 * max |u| |v| + 3 * max |u| |v|) / 16 := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
      _ = (1 / 2 : ℝ) * max |u| |v| := by ring
  have hy_le : |y| ≤ (1 / 2 : ℝ) * max |u| |v| := by
    rw [hy]
    calc
      |(-3 * u + 5 * v) / 16| = |(5 * v - 3 * u) / 16| := by
        congr 1
        ring
      _ = |5 * v - 3 * u| / 16 := by
        rw [abs_div]
        norm_num
      _ ≤ (|5 * v| + |3 * u|) / 16 := by
        gcongr
        exact abs_sub (5 * v) (3 * u)
      _ = (5 * |v| + 3 * |u|) / 16 := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ (5 * max |u| |v| + 3 * max |u| |v|) / 16 := by
        gcongr
        · exact le_max_right _ _
        · exact le_max_left _ _
      _ = (1 / 2 : ℝ) * max |u| |v| := by ring
  have hmax_le : max |x| |y| ≤ (1 / 2 : ℝ) * max |u| |v| := max_le hx_le hy_le
  have hmul :
      2 * max |x| |y| ≤ 2 * ((1 / 2 : ℝ) * max |u| |v|) := by
    gcongr
  calc
    2 * max |x| |y| ≤ 2 * ((1 / 2 : ℝ) * max |u| |v|) := hmul
    _ = max |u| |v| := by ring
    _ = max |5 * x + 3 * y| |3 * x + 5 * y| := by simp [u, v]

lemma hadamard_bridge_error_mobius_max_lower_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    max |hadamard_bridge_error μ u v r| |hadamard_bridge_error μ u v (-r)|
      ≤
    (1 + r) ^ 2 *
      max
        |hadamard_bridge_error μ u v ((1 - r) / (1 + r))|
        |hadamard_bridge_error μ u v (-( (1 - r) / (1 + r)))| := by
  set E : ℝ → ℝ := hadamard_bridge_error μ u v
  set φ : ℝ := (1 - r) / (1 + r)
  rcases hadamard_bridge_error_mobius_linearized hdim μ u v hu hv huv r h1pr with
    ⟨hEφ, hEnegφ⟩
  have hlin :
      2 * max |E r| |E (-r)| ≤
        max |-(2 * (1 + r) ^ 2 * E φ)| |2 * (1 + r) ^ 2 * E (-φ)| := by
    have h53 : 2 * max |E r| |E (-r)| ≤ max |5 * E r + 3 * E (-r)| |3 * E r + 5 * E (-r)| :=
      max_abs_lincomb_53_lower (E r) (E (-r))
    have hcomb1 : 5 * E r + 3 * E (-r) = -(2 * (1 + r) ^ 2 * E φ) := by
      linarith [hEφ]
    have hcomb2 : 3 * E r + 5 * E (-r) = 2 * (1 + r) ^ 2 * E (-φ) := by
      linarith [hEnegφ]
    calc
      2 * max |E r| |E (-r)| ≤ max |5 * E r + 3 * E (-r)| |3 * E r + 5 * E (-r)| := h53
      _ = max |-(2 * (1 + r) ^ 2 * E φ)| |2 * (1 + r) ^ 2 * E (-φ)| := by
            rw [hcomb1, hcomb2]
  have hsq_nn : 0 ≤ (2 * (1 + r) ^ 2 : ℝ) := by positivity
  have hfactor :
      max |-(2 * (1 + r) ^ 2 * E φ)| |2 * (1 + r) ^ 2 * E (-φ)|
        =
      (2 * (1 + r) ^ 2) * max |E φ| |E (-φ)| := by
    rw [abs_neg]
    have habs1 : |2 * (1 + r) ^ 2 * E φ| = (2 * (1 + r) ^ 2) * |E φ| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg (sq_nonneg (1 + r))]
    have habs2 : |2 * (1 + r) ^ 2 * E (-φ)| = (2 * (1 + r) ^ 2) * |E (-φ)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg (sq_nonneg (1 + r))]
    rw [habs1, habs2]
    simpa using (mul_max_of_nonneg |E φ| |E (-φ)| hsq_nn).symm
  have hlin' :
      2 * max |E r| |E (-r)|
        ≤
      (2 * (1 + r) ^ 2) * max |E φ| |E (-φ)| := by
    calc
      2 * max |E r| |E (-r)|
          ≤ max |-(2 * (1 + r) ^ 2 * E φ)| |2 * (1 + r) ^ 2 * E (-φ)| := hlin
      _ = (2 * (1 + r) ^ 2) * max |E φ| |E (-φ)| := hfactor
  have hhalf :
      (1 / 2 : ℝ) * (2 * max |E r| |E (-r)|)
        ≤
      (1 / 2 : ℝ) * ((2 * (1 + r) ^ 2) * max |E φ| |E (-φ)|) := by
    exact mul_le_mul_of_nonneg_left hlin' (by norm_num)
  have hmain :
      max |E r| |E (-r)| ≤ (1 + r) ^ 2 * max |E φ| |E (-φ)| := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hhalf
  simpa [E, φ] using hmain

/-- Defect-one gap: the difference between the Möbius-shifted defect and the base defect. -/
def defect_one_gap
    (μ : FrameFunction H) (u v : H) (r : ℝ) : ℝ :=
  local_quad2DDefect μ u v (1 + r) (1 - r) - local_quad2DDefect μ u v 1 r

lemma defect_one_gap_eq_two_mul_bridge_error
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    defect_one_gap μ u v r = 2 * hadamard_bridge_error μ u v r := by
  let s2 : ℝ := Real.sqrt 2
  have hrepr :
      hadamard_bridge_error μ u v r =
        local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) -
          local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) := by
    simpa [s2] using
      (hadamard_bridge_error_as_scaled_defect_gap hdim μ u v hu hv huv r)
  have hhom1 := GleasonBridge.local_quad2DDefect_hom μ u v (s2⁻¹) (1 + r) (1 - r)
  have hhom2 := GleasonBridge.local_quad2DDefect_hom μ u v (s2⁻¹) (1 : ℝ) r
  have hs2_sq : (s2⁻¹ : ℝ) ^ 2 = (1 / 2 : ℝ) := by
    have hs2_nonneg : (0 : ℝ) ≤ 2 := by norm_num
    have hs2_def : s2 ^ 2 = 2 := by
      dsimp [s2]
      exact Real.sq_sqrt hs2_nonneg
    calc
      (s2⁻¹ : ℝ) ^ 2 = (s2 ^ 2)⁻¹ := by simpa using (inv_pow s2 2)
      _ = (2 : ℝ)⁻¹ := by rw [hs2_def]
      _ = (1 / 2 : ℝ) := by norm_num
  have hscaled :
      local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) -
          local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹)
        =
      (1 / 2 : ℝ) * defect_one_gap μ u v r := by
    have h1 :
        local_quad2DDefect μ u v ((1 + r) * s2⁻¹) ((1 - r) * s2⁻¹) =
          (s2⁻¹ : ℝ) ^ 2 * local_quad2DDefect μ u v (1 + r) (1 - r) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hhom1
    have h2 :
        local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) =
          (s2⁻¹ : ℝ) ^ 2 * local_quad2DDefect μ u v 1 r := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hhom2
    unfold defect_one_gap
    rw [h1, h2, hs2_sq]
    ring
  have hhalf :
      hadamard_bridge_error μ u v r = (1 / 2 : ℝ) * defect_one_gap μ u v r := by
    linarith [hrepr, hscaled]
  linarith [hhalf]

lemma defect_one_gap_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    defect_one_gap μ u v 0 = 0 := by
  unfold defect_one_gap
  have h11 : local_quad2DDefect μ u v 1 1 = 0 := by
    simpa [GleasonBridge.local_defect_g] using
      GleasonBridge.local_defect_g_one_eq_zero hdim μ u v hu hv huv
  have h10 : local_quad2DDefect μ u v 1 0 = 0 := by
    simpa using GleasonBridge.local_quad2DDefect_one_zero_eq_zero μ u v
  simpa using sub_eq_zero.mpr (h11.trans h10.symm)

lemma defect_one_gap_one
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    defect_one_gap μ u v 1 = 0 := by
  unfold defect_one_gap
  have h20 : local_quad2DDefect μ u v 2 0 = 0 := by
    simpa using GleasonBridge.local_quad2DDefect_zero_right μ u v 2
  have h11 : local_quad2DDefect μ u v 1 1 = 0 := by
    simpa [GleasonBridge.local_defect_g] using
      GleasonBridge.local_defect_g_one_eq_zero hdim μ u v hu hv huv
  have hrew :
      local_quad2DDefect μ u v (1 + 1) (1 - 1) - local_quad2DDefect μ u v 1 1 =
        local_quad2DDefect μ u v 2 0 - local_quad2DDefect μ u v 1 1 := by
    norm_num
  rw [hrew]
  simpa using sub_eq_zero.mpr (h20.trans h11.symm)

lemma defect_one_gap_growth_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |defect_one_gap μ u v r| ≤ C * (1 + r ^ 2) := by
  rcases hadamard_bridge_error_growth_bound hdim μ u v hu hv huv with ⟨C, hCnn, hC⟩
  refine ⟨2 * C, by nlinarith, ?_⟩
  intro r
  have hgap : defect_one_gap μ u v r = 2 * hadamard_bridge_error μ u v r := by
    exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv r
  rw [hgap, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have hCr : |hadamard_bridge_error μ u v r| ≤ C * (1 + r ^ 2) := hC r
  nlinarith [hCr]

lemma defect_one_gap_second_diff_growth_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      |defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) -
          2 * defect_one_gap μ u v s|
        ≤ C * (1 + t ^ 2) := by
  rcases defect_one_gap_growth_bound hdim μ u v hu hv huv with ⟨C0, hC0nn, hC0⟩
  refine ⟨C0 * (10 + 6 * s ^ 2), ?_, ?_⟩
  · nlinarith [hC0nn, sq_nonneg s]
  · intro t
    have hspt_sq : (s + t) ^ 2 ≤ 2 * (s ^ 2 + t ^ 2) := by
      nlinarith [sq_nonneg (s - t)]
    have hsmt_sq : (s - t) ^ 2 ≤ 2 * (s ^ 2 + t ^ 2) := by
      nlinarith [sq_nonneg (s + t)]
    have hspt :
        |defect_one_gap μ u v (s + t)| ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) := by
      have haux : 1 + (s + t) ^ 2 ≤ 2 + 2 * s ^ 2 + 2 * t ^ 2 := by
        nlinarith [hspt_sq]
      have hmul :
          C0 * (1 + (s + t) ^ 2) ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) :=
        mul_le_mul_of_nonneg_left haux hC0nn
      exact le_trans (hC0 (s + t)) hmul
    have hsmt :
        |defect_one_gap μ u v (s - t)| ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) := by
      have haux : 1 + (s - t) ^ 2 ≤ 2 + 2 * s ^ 2 + 2 * t ^ 2 := by
        nlinarith [hsmt_sq]
      have hmul :
          C0 * (1 + (s - t) ^ 2) ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) :=
        mul_le_mul_of_nonneg_left haux hC0nn
      exact le_trans (hC0 (s - t)) hmul
    have hs0 : |defect_one_gap μ u v s| ≤ C0 * (1 + s ^ 2) := hC0 s
    set dpt : ℝ := defect_one_gap μ u v (s + t)
    set dmt : ℝ := defect_one_gap μ u v (s - t)
    set ds : ℝ := defect_one_gap μ u v s
    have htri1 : |dpt + dmt - 2 * ds| ≤ |dpt + dmt| + |2 * ds| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (dpt + dmt) (-(2 * ds))
    have htri2 : |dpt + dmt| ≤ |dpt| + |dmt| := abs_add_le dpt dmt
    have htri3 : |2 * ds| = 2 * |ds| := by
      rw [abs_mul]
      norm_num
    have habs :
        |dpt + dmt - 2 * ds| ≤ |dpt| + |dmt| + 2 * |ds| := by
      calc
        |dpt + dmt - 2 * ds| ≤ |dpt + dmt| + |2 * ds| := htri1
        _ ≤ (|dpt| + |dmt|) + |2 * ds| := by
              gcongr
        _ = |dpt| + |dmt| + 2 * |ds| := by
              simpa [htri3, add_assoc, add_left_comm, add_comm]
    have hspt' : |dpt| ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) := by simpa [dpt] using hspt
    have hsmt' : |dmt| ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) := by simpa [dmt] using hsmt
    have hs0' : |ds| ≤ C0 * (1 + s ^ 2) := by simpa [ds] using hs0
    have hpoly1 :
        |dpt + dmt - 2 * ds| ≤ C0 * (6 + 6 * s ^ 2 + 4 * t ^ 2) := by
      linarith [habs, hspt', hsmt', hs0']
    have hpoly2 :
        C0 * (6 + 6 * s ^ 2 + 4 * t ^ 2) ≤
          (C0 * (10 + 6 * s ^ 2)) * (1 + t ^ 2) := by
      have hbase : 6 + 6 * s ^ 2 + 4 * t ^ 2 ≤ (10 + 6 * s ^ 2) * (1 + t ^ 2) := by
        nlinarith [sq_nonneg s, sq_nonneg t]
      have hmul :
          C0 * (6 + 6 * s ^ 2 + 4 * t ^ 2) ≤ C0 * ((10 + 6 * s ^ 2) * (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hbase hC0nn
      calc
        C0 * (6 + 6 * s ^ 2 + 4 * t ^ 2) ≤ C0 * ((10 + 6 * s ^ 2) * (1 + t ^ 2)) := hmul
        _ = (C0 * (10 + 6 * s ^ 2)) * (1 + t ^ 2) := by ring
    exact le_trans hpoly1 hpoly2

lemma defect_one_gap_eq_zero_iff_bridge_error_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    defect_one_gap μ u v r = 0 ↔ hadamard_bridge_error μ u v r = 0 := by
  have hgap : defect_one_gap μ u v r = 2 * hadamard_bridge_error μ u v r := by
    exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv r
  constructor <;> intro h
  · rw [hgap] at h
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp h).resolve_left h2
  · rw [hgap]
    simpa [h]

lemma hadamard_bridge_error_zero_of_defect_one_gap_midpoint
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hmid : ∀ s t : ℝ,
      defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) = 2 * defect_one_gap μ u v s) :
    ∀ r : ℝ, hadamard_bridge_error μ u v r = 0 := by
  intro r
  have h0 : defect_one_gap μ u v 0 = 0 := defect_one_gap_zero hdim μ u v hu hv huv
  have h1 : defect_one_gap μ u v 1 = 0 := defect_one_gap_one hdim μ u v hu hv huv
  rcases defect_one_gap_growth_bound hdim μ u v hu hv huv with ⟨C, hCnn, hC⟩
  have hgap0 : defect_one_gap μ u v r = 0 := by
    exact midpoint_additive_bounded_zero (defect_one_gap μ u v) hmid h0 h1 C hCnn hC r
  exact (defect_one_gap_eq_zero_iff_bridge_error_eq_zero hdim μ u v hu hv huv r).1 hgap0

lemma defect_one_gap_midpoint_iff_hadamard_bridge_error_zero_all
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∀ s t : ℝ,
      defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) =
        2 * defect_one_gap μ u v s)
      ↔
    (∀ r : ℝ, hadamard_bridge_error μ u v r = 0) := by
  constructor
  · intro hmid
    exact hadamard_bridge_error_zero_of_defect_one_gap_midpoint
      hdim μ u v hu hv huv hmid
  · intro hEzero s t
    have hgap0 : ∀ x : ℝ, defect_one_gap μ u v x = 0 := by
      intro x
      have hgap :
          defect_one_gap μ u v x = 2 * hadamard_bridge_error μ u v x := by
        exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv x
      rw [hgap, hEzero x]
      ring
    rw [hgap0 (s + t), hgap0 (s - t), hgap0 s]
    ring

lemma vec_id1 (u v : H) (s t : ℝ) :
    (((1 + (s + t) : ℝ) : ℂ) • u + ((1 - (s + t) : ℝ) : ℂ) • v)
      = (u + v + (s : ℂ) • (u - v)) + (t : ℂ) • (u - v) := by
  have hs1 : (((1 + (s + t) : ℝ) : ℂ)) = (((1 + s : ℝ) : ℂ) + (t : ℂ)) := by
    push_cast
    ring
  have hs2 : (((1 - (s + t) : ℝ) : ℂ)) = (((1 - s : ℝ) : ℂ) + (-(t : ℂ))) := by
    push_cast
    ring
  rw [hs1, hs2]
  simp [sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm]

lemma vec_id2 (u v : H) (s t : ℝ) :
    (((1 + (s + t) : ℝ) : ℂ) • u - ((1 - (s + t) : ℝ) : ℂ) • v)
      = (u - v + (s : ℂ) • (u + v)) + (t : ℂ) • (u + v) := by
  have hs1 : (((1 + (s + t) : ℝ) : ℂ)) = (((1 + s : ℝ) : ℂ) + (t : ℂ)) := by
    push_cast
    ring
  have hs2 : (((1 - (s + t) : ℝ) : ℂ)) = (((1 - s : ℝ) : ℂ) + (-(t : ℂ))) := by
    push_cast
    ring
  rw [hs1, hs2]
  simp [sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm]

lemma vec_id3 (u v : H) (s t : ℝ) :
    (((1 + (s - t) : ℝ) : ℂ) • u + ((1 - (s - t) : ℝ) : ℂ) • v)
      = (u + v + (s : ℂ) • (u - v)) - (t : ℂ) • (u - v) := by
  have hs1 : (((1 + (s - t) : ℝ) : ℂ)) = (((1 + s : ℝ) : ℂ) + (-(t : ℂ))) := by
    push_cast
    ring
  have hs2 : (((1 - (s - t) : ℝ) : ℂ)) = (((1 - s : ℝ) : ℂ) + (t : ℂ)) := by
    push_cast
    ring
  rw [hs1, hs2]
  simp [sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm]

lemma vec_id4 (u v : H) (s t : ℝ) :
    (((1 + (s - t) : ℝ) : ℂ) • u - ((1 - (s - t) : ℝ) : ℂ) • v)
      = (u - v + (s : ℂ) • (u + v)) - (t : ℂ) • (u + v) := by
  have hs1 : (((1 + (s - t) : ℝ) : ℂ)) = (((1 + s : ℝ) : ℂ) + (-(t : ℂ))) := by
    push_cast
    ring
  have hs2 : (((1 - (s - t) : ℝ) : ℂ)) = (((1 - s : ℝ) : ℂ) + (t : ℂ)) := by
    push_cast
    ring
  rw [hs1, hs2]
  simp [sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm]

def local_A_func (μ : FrameFunction H) (u v : H) (r : ℝ) : ℝ :=
  local_quad2DDefect μ u v (1 + r) (1 - r)

lemma local_A_func_second_diff
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    local_A_func μ u v (s + t) + local_A_func μ u v (s - t) - 2 * local_A_func μ u v s =
      local_quad2DDefect μ (u + v + (s : ℂ) • (u - v)) (u - v) 1 t +
      local_quad2DDefect μ (u - v + (s : ℂ) • (u + v)) (u + v) 1 t := by
  have hRP : frame_quadratic μ (u + v) + frame_quadratic μ (u - v) =
      2 * frame_quadratic μ u + 2 * frame_quadratic μ v := by
    simpa [sub_eq_add_neg] using parallelogram_orthogonal_eq_norm hdim μ u v huv (by simpa [hu, hv])
  unfold local_A_func
  unfold local_quad2DDefect local_quad2DExpr
  rw [vec_id1 u v s t, vec_id2 u v s t, vec_id3 u v s t, vec_id4 u v s t]
  have hsum : frame_quadratic μ (u - v) + frame_quadratic μ (u + v) =
      2 * frame_quadratic μ u + 2 * frame_quadratic μ v := by
    linarith [hRP]
  have htail :
      2 * t ^ 2 * frame_quadratic μ (u - v) + 2 * t ^ 2 * frame_quadratic μ (u + v)
        = 4 * t ^ 2 * frame_quadratic μ u + 4 * t ^ 2 * frame_quadratic μ v := by
    calc
      2 * t ^ 2 * frame_quadratic μ (u - v) + 2 * t ^ 2 * frame_quadratic μ (u + v)
          = 2 * t ^ 2 * (frame_quadratic μ (u - v) + frame_quadratic μ (u + v)) := by ring
      _ = 2 * t ^ 2 * (2 * frame_quadratic μ u + 2 * frame_quadratic μ v) := by rw [hsum]
      _ = 4 * t ^ 2 * frame_quadratic μ u + 4 * t ^ 2 * frame_quadratic μ v := by ring
  have hxs : u + v + (s : ℂ) • (u - v) = ((1 + s : ℝ) : ℂ) • u + ((1 - s : ℝ) : ℂ) • v := by
    have hs1 : (((1 + s : ℝ) : ℂ)) = (1 : ℂ) + (s : ℂ) := by
      push_cast
      ring
    have hs2 : (((1 - s : ℝ) : ℂ)) = (1 : ℂ) + (-(s : ℂ)) := by
      push_cast
      ring
    rw [hs1, hs2]
    simp [sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm]
  have hys : u - v + (s : ℂ) • (u + v) = ((1 + s : ℝ) : ℂ) • u - ((1 - s : ℝ) : ℂ) • v := by
    have hs1 : (((1 + s : ℝ) : ℂ)) = (1 : ℂ) + (s : ℂ) := by
      push_cast
      ring
    have hs2 : (((1 - s : ℝ) : ℂ)) = (1 : ℂ) + (-(s : ℂ)) := by
      push_cast
      ring
    rw [hs1, hs2]
    simp [sub_eq_add_neg, add_smul, smul_add, add_assoc, add_left_comm, add_comm]
  rw [hxs, hys]
  simp [one_smul]
  have hsq1 : (1 + (s + t)) ^ 2 + (1 + (s - t)) ^ 2 - 2 * (1 + s) ^ 2 = 2 * t ^ 2 := by ring
  have hsq2 : (1 - (s + t)) ^ 2 + (1 - (s - t)) ^ 2 - 2 * (1 - s) ^ 2 = 2 * t ^ 2 := by ring
  linarith [htail, hsq1, hsq2]

lemma local_quad2DDefect_neg_right
    (μ : FrameFunction H) (x y : H) (a b : ℝ) :
    local_quad2DDefect μ x (-y) a b = local_quad2DDefect μ x y a b := by
  unfold local_quad2DDefect local_quad2DExpr
  have h1 : (a : ℂ) • x + (b : ℂ) • (-y) = (a : ℂ) • x - (b : ℂ) • y := by
    module
  have h2 : (a : ℂ) • x - (b : ℂ) • (-y) = (a : ℂ) • x + (b : ℂ) • y := by
    module
  rw [h1, h2]
  rw [frame_quadratic_neg μ y]
  ring

lemma local_quad2DDefect_neg_left
    (μ : FrameFunction H) (x y : H) (a b : ℝ) :
    local_quad2DDefect μ (-x) y a b = local_quad2DDefect μ x y a b := by
  calc
    local_quad2DDefect μ (-x) y a b = local_quad2DDefect μ y (-x) b a := by
      simpa using (local_quad2DDefect_swap_vectors μ (-x) y a b).symm
    _ = local_quad2DDefect μ y x b a := by
      simpa using (local_quad2DDefect_neg_right μ y x b a)
    _ = local_quad2DDefect μ x y a b := by
      simpa using (local_quad2DDefect_swap_vectors μ x y a b)

lemma local_defect_residual_mix_real_scale
    (μ : FrameFunction H) (x y z : H) (c s t : ℝ) :
    local_defect_residual_mix μ ((c : ℂ) • x) ((c : ℂ) • y) ((c : ℂ) • z) s t =
      c ^ 2 * local_defect_residual_mix μ x y z s t := by
  have hscale :
      ∀ A B : H,
        local_quad2DDefect μ ((c : ℂ) • A) ((c : ℂ) • B) 1 t =
          c ^ 2 * local_quad2DDefect μ A B 1 t := by
    intro A B
    unfold local_quad2DDefect local_quad2DExpr
    have h1 :
        (((1 : ℝ) : ℂ) • ((c : ℂ) • A) + (t : ℂ) • ((c : ℂ) • B)) =
          (c : ℂ) • ((((1 : ℝ) : ℂ) • A) + (t : ℂ) • B) := by
      simp [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    have h2 :
        (((1 : ℝ) : ℂ) • ((c : ℂ) • A) - (t : ℂ) • ((c : ℂ) • B)) =
          (c : ℂ) • ((((1 : ℝ) : ℂ) • A) - (t : ℂ) • B) := by
      simp [smul_sub, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    rw [h1, h2]
    rw [frame_quadratic_sq_hom μ (c : ℂ) ((((1 : ℝ) : ℂ) • A) + (t : ℂ) • B)]
    rw [frame_quadratic_sq_hom μ (c : ℂ) ((((1 : ℝ) : ℂ) • A) - (t : ℂ) • B)]
    rw [frame_quadratic_sq_hom μ (c : ℂ) A]
    rw [frame_quadratic_sq_hom μ (c : ℂ) B]
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  unfold local_defect_residual_mix
  have hplus :
      (c : ℂ) • x + (s : ℝ) • ((c : ℂ) • y) = (c : ℂ) • (x + (s : ℝ) • y) := by
    simp [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  have hminus :
      (c : ℂ) • x - (s : ℝ) • ((c : ℂ) • y) = (c : ℂ) • (x - (s : ℝ) • y) := by
    simp [smul_sub, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  rw [hplus, hminus]
  rw [hscale (x + (s : ℝ) • y) z, hscale (x - (s : ℝ) • y) z, hscale x z]
  ring

lemma local_defect_residual_mix_sum_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    let X := u + v
    let Y := u - v
    local_defect_residual_mix μ X Y Y s t + local_defect_residual_mix μ Y X X s t = 0 := by
  intro X Y
  let s2 : ℝ := Real.sqrt 2
  let p : H := (s2⁻¹ : ℝ) • X
  let q : H := (s2⁻¹ : ℝ) • Y
  have hpq : ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ inner (𝕜 := ℂ) p q = 0 := by
    simpa [s2, p, q, X, Y, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      GleasonBridge.hadamard_orthonormal_vw_local u v hu hv huv
  rcases hpq with ⟨hp, hq, hpq0⟩
  have hs2_ne : (s2 : ℝ) ≠ 0 := by
    dsimp [s2]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2_mul_inv : s2 * s2⁻¹ = (1 : ℝ) := by
    field_simp [hs2_ne]
  have hXr : (s2 : ℝ) • p = X := by
    dsimp [p]
    rw [smul_smul, hs2_mul_inv, one_smul]
  have hYr : (s2 : ℝ) • q = Y := by
    dsimp [q]
    rw [smul_smul, hs2_mul_inv, one_smul]
  have hX : X = (s2 : ℂ) • p := by
    change X = (s2 : ℝ) • p
    exact hXr.symm
  have hY : Y = (s2 : ℂ) • q := by
    change Y = (s2 : ℝ) • q
    exact hYr.symm
  have hm1 := local_defect_residual_mix_real_scale μ p q q s2 s t
  have hm2 := local_defect_residual_mix_real_scale μ q p p s2 s t
  rw [← hX, ← hY] at hm1 hm2
  have hzero :=
    local_defect_residual_mix_self_swap_add_eq_zero hdim μ p q hp hq hpq0 s t
  calc
    local_defect_residual_mix μ X Y Y s t + local_defect_residual_mix μ Y X X s t
        = s2 ^ 2 *
            (local_defect_residual_mix μ p q q s t + local_defect_residual_mix μ q p p s t) := by
              linarith [hm1, hm2]
    _ = 0 := by rw [hzero, mul_zero]

lemma frame_quadratic_real_hom
    (μ : FrameFunction H) (c : ℝ) (x : H) :
    frame_quadratic μ ((c : ℂ) • x) = c ^ 2 * frame_quadratic μ x := by
  have h := frame_quadratic_sq_hom μ (c : ℂ) x
  simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

lemma local_quad2DDefect_real_scale
    (μ : FrameFunction H) (x y : H) (c a b : ℝ) :
    local_quad2DDefect μ ((c : ℂ) • x) ((c : ℂ) • y) a b =
      c ^ 2 * local_quad2DDefect μ x y a b := by
  unfold local_quad2DDefect local_quad2DExpr
  have h1 : (a : ℂ) • ((c : ℂ) • x) + (b : ℂ) • ((c : ℂ) • y) =
      (c : ℂ) • ((a : ℂ) • x + (b : ℂ) • y) := by
    simp [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  have h2 : (a : ℂ) • ((c : ℂ) • x) - (b : ℂ) • ((c : ℂ) • y) =
      (c : ℂ) • ((a : ℂ) • x - (b : ℂ) • y) := by
    simp [smul_sub, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  rw [h1, h2]
  rw [frame_quadratic_real_hom μ c ((a : ℂ) • x + (b : ℂ) • y)]
  rw [frame_quadratic_real_hom μ c ((a : ℂ) • x - (b : ℂ) • y)]
  rw [frame_quadratic_real_hom μ c x]
  rw [frame_quadratic_real_hom μ c y]
  ring

lemma local_quad2DDefect_X_Y_sum_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    let X := u + v
    let Y := u - v
    local_quad2DDefect μ X Y 1 t + local_quad2DDefect μ Y X 1 t = 0 := by
  intro X Y
  let s2 : ℝ := Real.sqrt 2
  let p : H := (s2⁻¹ : ℝ) • X
  let q : H := (s2⁻¹ : ℝ) • Y
  have hpq : ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ inner (𝕜 := ℂ) p q = 0 := by
    simpa [s2, p, q, X, Y, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      GleasonBridge.hadamard_orthonormal_vw_local u v hu hv huv
  rcases hpq with ⟨hp, hq, hpq0⟩
  have hs2_ne : (s2 : ℝ) ≠ 0 := by
    dsimp [s2]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs2_mul_inv : s2 * s2⁻¹ = (1 : ℝ) := by
    field_simp [hs2_ne]
  have hXr : (s2 : ℝ) • p = X := by
    dsimp [p]
    rw [smul_smul, hs2_mul_inv, one_smul]
  have hYr : (s2 : ℝ) • q = Y := by
    dsimp [q]
    rw [smul_smul, hs2_mul_inv, one_smul]
  have hX : X = (s2 : ℂ) • p := by
    change X = (s2 : ℝ) • p
    exact hXr.symm
  have hY : Y = (s2 : ℂ) • q := by
    change Y = (s2 : ℝ) • q
    exact hYr.symm
  have hd1 := local_quad2DDefect_real_scale μ p q s2 1 t
  have hd2 := local_quad2DDefect_real_scale μ q p s2 1 t
  rw [← hX, ← hY] at hd1 hd2
  have hg : local_quad2DDefect μ p q 1 t + local_quad2DDefect μ q p 1 t = 0 := by
    simpa [local_defect_g] using local_defect_g_swap_add_eq_zero hdim μ p q hp hq hpq0 t
  calc
    local_quad2DDefect μ X Y 1 t + local_quad2DDefect μ Y X 1 t
        = s2 ^ 2 * (local_quad2DDefect μ p q 1 t + local_quad2DDefect μ q p 1 t) := by
            linarith [hd1, hd2]
    _ = s2 ^ 2 * 0 := by rw [hg]
    _ = 0 := by ring

lemma local_quad2DDefect_mix_identity_x
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    let X := u + v
    let Y := u - v
    let xs := X + (s : ℂ) • Y
    let xms := X - (s : ℂ) • Y
    local_quad2DDefect μ xs Y 1 t + local_quad2DDefect μ xms Y 1 t =
      local_defect_residual_mix μ X Y Y s t + 2 * local_quad2DDefect μ X Y 1 t := by
  intro X Y xs xms
  unfold local_defect_residual_mix
  have h1 : X + (s : ℝ) • Y = xs := rfl
  have h2 : X - (s : ℝ) • Y = xms := rfl
  rw [h1, h2]
  ring

lemma local_quad2DDefect_mix_identity_y
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    let X := u + v
    let Y := u - v
    let ys := Y + (s : ℂ) • X
    let yms := Y - (s : ℂ) • X
    local_quad2DDefect μ ys X 1 t + local_quad2DDefect μ yms X 1 t =
      local_defect_residual_mix μ Y X X s t + 2 * local_quad2DDefect μ Y X 1 t := by
  intro X Y ys yms
  unfold local_defect_residual_mix
  have h1 : Y + (s : ℝ) • X = ys := rfl
  have h2 : Y - (s : ℝ) • X = yms := rfl
  rw [h1, h2]
  ring

lemma hadamard_shifted_pair_sum_swap_params_x
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    let X := u + v
    let Y := u - v
    (local_quad2DDefect μ (X + (s : ℂ) • Y) Y 1 t +
      local_quad2DDefect μ (X - (s : ℂ) • Y) Y 1 t)
      -
    (local_quad2DDefect μ (X + (t : ℂ) • Y) Y 1 s +
      local_quad2DDefect μ (X - (t : ℂ) • Y) Y 1 s)
      =
    2 * (local_quad2DDefect μ X Y 1 t - local_quad2DDefect μ X Y 1 s) := by
  intro X Y
  have hst := local_quad2DDefect_mix_identity_x μ u v s t
  have hts := local_quad2DDefect_mix_identity_x μ u v t s
  have hsym := local_defect_residual_mix_selfarg_symm μ X Y s t
  linarith [hst, hts, hsym]

lemma hadamard_shifted_pair_sum_swap_params_y
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    let X := u + v
    let Y := u - v
    (local_quad2DDefect μ (Y + (s : ℂ) • X) X 1 t +
      local_quad2DDefect μ (Y - (s : ℂ) • X) X 1 t)
      -
    (local_quad2DDefect μ (Y + (t : ℂ) • X) X 1 s +
      local_quad2DDefect μ (Y - (t : ℂ) • X) X 1 s)
      =
    2 * (local_quad2DDefect μ Y X 1 t - local_quad2DDefect μ Y X 1 s) := by
  intro X Y
  have hst := local_quad2DDefect_mix_identity_y μ u v s t
  have hts := local_quad2DDefect_mix_identity_y μ u v t s
  have hsym := local_defect_residual_mix_selfarg_symm μ Y X s t
  linarith [hst, hts, hsym]

lemma local_A_func_second_diff_pair_cancel
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    (local_A_func μ u v (s + t) + local_A_func μ u v (s - t) - 2 * local_A_func μ u v s) +
      (local_A_func μ u v (-s + t) + local_A_func μ u v (-s - t) - 2 * local_A_func μ u v (-s))
      = 0 := by
  have hs := local_A_func_second_diff hdim μ u v hu hv huv s t
  have hms := local_A_func_second_diff hdim μ u v hu hv huv (-s) t
  set X : H := u + v
  set Y : H := u - v
  set xs : H := X + (s : ℂ) • Y
  set xms : H := X - (s : ℂ) • Y
  set ys : H := Y + (s : ℂ) • X
  set yms : H := Y - (s : ℂ) • X
  have hs' :
      local_A_func μ u v (s + t) + local_A_func μ u v (s - t) - 2 * local_A_func μ u v s =
        local_quad2DDefect μ xs Y 1 t + local_quad2DDefect μ ys X 1 t := by
    simpa [xs, ys] using hs
  have hms' :
      local_A_func μ u v (-s + t) + local_A_func μ u v (-s - t) - 2 * local_A_func μ u v (-s) =
        local_quad2DDefect μ xms Y 1 t + local_quad2DDefect μ yms X 1 t := by
    simpa [xms, yms, sub_eq_add_neg, neg_smul] using hms
  have hmixX := local_quad2DDefect_mix_identity_x μ u v s t
  have hmixY := local_quad2DDefect_mix_identity_y μ u v s t
  have hmix0 := local_defect_residual_mix_sum_zero hdim μ u v hu hv huv s t
  have hD0 := local_quad2DDefect_X_Y_sum_zero hdim μ u v hu hv huv t
  linarith [hs', hms', hmixX, hmixY, hmix0, hD0]

lemma local_A_func_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    local_A_func μ u v (-r) = - local_A_func μ u v r := by
  unfold local_A_func
  have hswap :=
    GleasonBridge.local_quad2DDefect_swap_of_orthonormal (H := H) hdim μ u v hu hv huv (1 - r) (1 + r)
  have hneg :
      local_quad2DDefect μ u v (1 - r) (1 + r) =
        - local_quad2DDefect μ u v (1 + r) (1 - r) := by
    simpa [add_comm] using hswap
  have hleft : local_quad2DDefect μ u v (1 + (-r)) (1 - (-r)) =
      local_quad2DDefect μ u v (1 - r) (1 + r) := by ring_nf
  rw [hleft, hneg]

lemma local_A_func_swap_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    local_A_func μ v u r = - local_A_func μ u v r := by
  unfold local_A_func
  have hswapVec :
      local_quad2DDefect μ v u (1 + r) (1 - r) =
        local_quad2DDefect μ u v (1 - r) (1 + r) := by
    simpa [sub_eq_add_neg] using
      (local_quad2DDefect_swap_vectors μ u v (1 - r) (1 + r))
  have hanti :
      local_quad2DDefect μ u v (1 - r) (1 + r) =
        - local_quad2DDefect μ u v (1 + r) (1 - r) := by
    have h :=
      GleasonBridge.local_quad2DDefect_swap_of_orthonormal
        (H := H) hdim μ u v hu hv huv (1 - r) (1 + r)
    simpa [add_comm] using h
  linarith [hswapVec, hanti]

lemma defect_one_gap_swap_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    defect_one_gap μ v u r = -defect_one_gap μ u v r := by
  have hA :
      local_A_func μ v u r = -local_A_func μ u v r :=
    local_A_func_swap_neg hdim μ u v hu hv huv r
  have hg :
      local_defect_g μ v u r = -local_defect_g μ u v r := by
    have hsum := local_defect_g_swap_add_eq_zero hdim μ u v hu hv huv r
    linarith [hsum]
  have hA' :
      local_quad2DDefect μ v u (1 + r) (1 - r) =
        -local_quad2DDefect μ u v (1 + r) (1 - r) := by
    simpa [local_A_func] using hA
  have hg' :
      local_quad2DDefect μ v u 1 r =
        -local_quad2DDefect μ u v 1 r := by
    simpa [local_defect_g] using hg
  unfold defect_one_gap
  linarith [hA', hg']

lemma defect_one_gap_second_diff_swap_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    defect_one_gap μ v u (s + t) + defect_one_gap μ v u (s - t) -
      2 * defect_one_gap μ v u s
      =
    -(defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) -
      2 * defect_one_gap μ u v s) := by
  have hst :
      defect_one_gap μ v u (s + t) = -defect_one_gap μ u v (s + t) :=
    defect_one_gap_swap_neg hdim μ u v hu hv huv (s + t)
  have hsm :
      defect_one_gap μ v u (s - t) = -defect_one_gap μ u v (s - t) :=
    defect_one_gap_swap_neg hdim μ u v hu hv huv (s - t)
  have hs :
      defect_one_gap μ v u s = -defect_one_gap μ u v s :=
    defect_one_gap_swap_neg hdim μ u v hu hv huv s
  linarith [hst, hsm, hs]

lemma defect_one_gap_add_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    defect_one_gap μ u v r + defect_one_gap μ u v (-r) =
      -2 * local_defect_g μ u v r := by
  unfold defect_one_gap
  have hAneg := local_A_func_neg hdim μ u v hu hv huv r
  have hgEven : local_defect_g μ u v (-r) = local_defect_g μ u v r := by
    simpa using GleasonBridge.local_defect_g_even μ u v r
  have hA :
      local_quad2DDefect μ u v (1 + (-r)) (1 - (-r)) =
        - local_quad2DDefect μ u v (1 + r) (1 - r) := by
    simpa [local_A_func] using hAneg
  have hG :
      local_quad2DDefect μ u v 1 (-r) = local_quad2DDefect μ u v 1 r := by
    simpa [local_defect_g] using hgEven
  have hgr : local_quad2DDefect μ u v 1 r = local_defect_g μ u v r := rfl
  rw [hA, hG]
  rw [hgr]
  ring

lemma defect_one_gap_second_diff_pair
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    (defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) - 2 * defect_one_gap μ u v s) +
      (defect_one_gap μ u v (-s + t) + defect_one_gap μ u v (-s - t) - 2 * defect_one_gap μ u v (-s))
      =
    -2 * (local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) - 2 * local_defect_g μ u v s) := by
  have hA := local_A_func_second_diff_pair_cancel hdim μ u v hu hv huv s t
  have he1 : local_defect_g μ u v (-s + t) = local_defect_g μ u v (s - t) := by
    have : -s + t = -(s - t) := by ring
    rw [this, GleasonBridge.local_defect_g_even]
  have he2 : local_defect_g μ u v (-s - t) = local_defect_g μ u v (s + t) := by
    have : -s - t = -(s + t) := by ring
    rw [this, GleasonBridge.local_defect_g_even]
  have he3 : local_defect_g μ u v (-s) = local_defect_g μ u v s := by
    simpa using GleasonBridge.local_defect_g_even μ u v s
  have hdef : ∀ x : ℝ, defect_one_gap μ u v x = local_A_func μ u v x - local_defect_g μ u v x := by
    intro x
    rfl
  rw [hdef (s + t), hdef (s - t), hdef s, hdef (-s + t), hdef (-s - t), hdef (-s)]
  rw [he1, he2, he3]
  linarith [hA]

lemma defect_one_gap_second_diff_eq_local_A_minus_g
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) -
      2 * defect_one_gap μ u v s
      =
    (local_quad2DDefect μ (u + v + (s : ℂ) • (u - v)) (u - v) 1 t +
      local_quad2DDefect μ (u - v + (s : ℂ) • (u + v)) (u + v) 1 t)
      -
    (local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t +
      local_quad2DDefect μ (u - (s : ℂ) • v) v 1 t) := by
  have hA := local_A_func_second_diff hdim μ u v hu hv huv s t
  have hg := shifted_base_pair_sum_eq_second_difference μ u v s t
  calc
    defect_one_gap μ u v (s + t) + defect_one_gap μ u v (s - t) -
        2 * defect_one_gap μ u v s
        =
      (local_A_func μ u v (s + t) + local_A_func μ u v (s - t) -
        2 * local_A_func μ u v s)
      -
      (local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
        2 * local_defect_g μ u v s) := by
          set A1 : ℝ := local_A_func μ u v (s + t)
          set A2 : ℝ := local_A_func μ u v (s - t)
          set A3 : ℝ := local_A_func μ u v s
          set G1 : ℝ := local_defect_g μ u v (s + t)
          set G2 : ℝ := local_defect_g μ u v (s - t)
          set G3 : ℝ := local_defect_g μ u v s
          change (A1 - G1) + (A2 - G2) - 2 * (A3 - G3) =
            (A1 + A2 - 2 * A3) - (G1 + G2 - 2 * G3)
          nlinarith
    _ =
      (local_quad2DDefect μ (u + v + (s : ℂ) • (u - v)) (u - v) 1 t +
        local_quad2DDefect μ (u - v + (s : ℂ) • (u + v)) (u + v) 1 t)
      -
      (local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t +
        local_quad2DDefect μ (u - (s : ℂ) • v) v 1 t) := by
          rw [hA, hg]

lemma defect_one_gap_second_diff_eq_swapped_bridge_gap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    defect_one_gap μ v u (s + t) + defect_one_gap μ v u (s - t) -
      2 * defect_one_gap μ v u s
      =
    (local_quad2DDefect μ (v + u + (s : ℂ) • (v - u)) (v - u) 1 t +
      local_quad2DDefect μ (v - u + (s : ℂ) • (v + u)) (v + u) 1 t)
      -
    (local_quad2DDefect μ (v + (s : ℂ) • u) u 1 t +
      local_quad2DDefect μ (v - (s : ℂ) • u) u 1 t) := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  simpa [add_comm, add_left_comm, add_assoc] using
    (defect_one_gap_second_diff_eq_local_A_minus_g hdim μ v u hv hu hvu s t)

def swapped_bridge_kernel
    (μ : FrameFunction H) (u v : H) (s t : ℝ) : ℝ :=
  defect_one_gap μ v u (s + t) + defect_one_gap μ v u (s - t) -
    2 * defect_one_gap μ v u s

lemma swapped_bridge_kernel_eq_gap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    swapped_bridge_kernel μ u v s t =
      (local_quad2DDefect μ (v + u + (s : ℂ) • (v - u)) (v - u) 1 t +
        local_quad2DDefect μ (v - u + (s : ℂ) • (v + u)) (v + u) 1 t)
      -
      (local_quad2DDefect μ (v + (s : ℂ) • u) u 1 t +
        local_quad2DDefect μ (v - (s : ℂ) • u) u 1 t) := by
  simpa [swapped_bridge_kernel] using
    defect_one_gap_second_diff_eq_swapped_bridge_gap hdim μ u v hu hv huv s t

lemma swapped_bridge_kernel_swap_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    swapped_bridge_kernel μ u v s t = -swapped_bridge_kernel μ v u s t := by
  simpa [swapped_bridge_kernel] using
    defect_one_gap_second_diff_swap_neg hdim μ u v hu hv huv s t

lemma swapped_bridge_kernel_eq_zero_of_pair_nonneg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ)
    (huv_nonneg : 0 ≤ swapped_bridge_kernel μ u v s t)
    (hvu_nonneg : 0 ≤ swapped_bridge_kernel μ v u s t) :
    swapped_bridge_kernel μ u v s t = 0 := by
  have hswap := swapped_bridge_kernel_swap_neg hdim μ u v hu hv huv s t
  linarith [hvu_nonneg, hswap, huv_nonneg]

lemma swapped_bridge_kernel_eq_zero_of_global_nonneg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hnonneg :
      ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
        ∀ s t : ℝ, 0 ≤ swapped_bridge_kernel μ a b s t)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∀ s t : ℝ, swapped_bridge_kernel μ u v s t = 0 := by
  intro s t
  have huv_nonneg : 0 ≤ swapped_bridge_kernel μ u v s t := hnonneg u v hu hv huv s t
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hvu_nonneg : 0 ≤ swapped_bridge_kernel μ v u s t := hnonneg v u hv hu hvu s t
  exact
    swapped_bridge_kernel_eq_zero_of_pair_nonneg
      hdim μ u v hu hv huv s t huv_nonneg hvu_nonneg

lemma shifted_bridge_eq_of_pair_nonneg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ)
    (huv_nonneg : 0 ≤ swapped_bridge_kernel μ u v s t)
    (hvu_nonneg : 0 ≤ swapped_bridge_kernel μ v u s t) :
    local_quad2DDefect μ (v + u + (s : ℂ) • (v - u)) (v - u) 1 t +
      local_quad2DDefect μ (v - u + (s : ℂ) • (v + u)) (v + u) 1 t
      =
    local_quad2DDefect μ (v + (s : ℂ) • u) u 1 t +
      local_quad2DDefect μ (v - (s : ℂ) • u) u 1 t := by
  have hk0 :
      swapped_bridge_kernel μ u v s t = 0 :=
    swapped_bridge_kernel_eq_zero_of_pair_nonneg
      hdim μ u v hu hv huv s t huv_nonneg hvu_nonneg
  have hgap :=
    swapped_bridge_kernel_eq_gap hdim μ u v hu hv huv s t
  linarith [hgap, hk0]

lemma swapped_bridge_kernel_zero_t0
    (μ : FrameFunction H) (u v : H) (s : ℝ) :
    swapped_bridge_kernel μ u v s 0 = 0 := by
  unfold swapped_bridge_kernel
  ring_nf

lemma swapped_bridge_kernel_even_t
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    swapped_bridge_kernel μ u v s (-t) = swapped_bridge_kernel μ u v s t := by
  unfold swapped_bridge_kernel
  ring_nf

lemma swapped_bridge_kernel_growth_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      |swapped_bridge_kernel μ u v s t| ≤ C * (1 + t ^ 2) := by
  rcases defect_one_gap_second_diff_growth_bound hdim μ v u hv hu
      (by simpa [inner_eq_zero_symm] using huv) s with ⟨C, hCnn, hC⟩
  refine ⟨C, hCnn, ?_⟩
  intro t
  simpa [swapped_bridge_kernel] using hC t

lemma swapped_bridge_kernel_growth_bound_two_vars
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ,
      |swapped_bridge_kernel μ u v s t| ≤ C * (1 + s ^ 2 + t ^ 2) := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  rcases defect_one_gap_growth_bound hdim μ v u hv hu hvu with ⟨C0, hC0nn, hC0⟩
  refine ⟨12 * C0, by nlinarith, ?_⟩
  intro s t
  have hspt_sq : (s + t) ^ 2 ≤ 2 * (s ^ 2 + t ^ 2) := by
    nlinarith [sq_nonneg (s - t)]
  have hsmt_sq : (s - t) ^ 2 ≤ 2 * (s ^ 2 + t ^ 2) := by
    nlinarith [sq_nonneg (s + t)]
  have hspt :
      |defect_one_gap μ v u (s + t)| ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) := by
    have haux : 1 + (s + t) ^ 2 ≤ 2 + 2 * s ^ 2 + 2 * t ^ 2 := by
      nlinarith [hspt_sq]
    have hmul :
        C0 * (1 + (s + t) ^ 2) ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left haux hC0nn
    exact le_trans (hC0 (s + t)) hmul
  have hsmt :
      |defect_one_gap μ v u (s - t)| ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) := by
    have haux : 1 + (s - t) ^ 2 ≤ 2 + 2 * s ^ 2 + 2 * t ^ 2 := by
      nlinarith [hsmt_sq]
    have hmul :
        C0 * (1 + (s - t) ^ 2) ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left haux hC0nn
    exact le_trans (hC0 (s - t)) hmul
  have hs0 : |defect_one_gap μ v u s| ≤ C0 * (1 + s ^ 2) := hC0 s
  set dpt : ℝ := defect_one_gap μ v u (s + t)
  set dmt : ℝ := defect_one_gap μ v u (s - t)
  set ds : ℝ := defect_one_gap μ v u s
  have htri1 : |dpt + dmt - 2 * ds| ≤ |dpt + dmt| + |2 * ds| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le (dpt + dmt) (-(2 * ds))
  have htri2 : |dpt + dmt| ≤ |dpt| + |dmt| := abs_add_le dpt dmt
  have htri3 : |2 * ds| = 2 * |ds| := by
    rw [abs_mul]
    norm_num
  have habs :
      |dpt + dmt - 2 * ds| ≤ |dpt| + |dmt| + 2 * |ds| := by
    calc
      |dpt + dmt - 2 * ds| ≤ |dpt + dmt| + |2 * ds| := htri1
      _ ≤ (|dpt| + |dmt|) + |2 * ds| := by
            gcongr
      _ = |dpt| + |dmt| + 2 * |ds| := by
            simpa [htri3, add_assoc, add_left_comm, add_comm]
  have hspt' : |dpt| ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) := by
    simpa [dpt] using hspt
  have hsmt' : |dmt| ≤ C0 * (2 + 2 * s ^ 2 + 2 * t ^ 2) := by
    simpa [dmt] using hsmt
  have hs0' : |ds| ≤ C0 * (1 + s ^ 2) := by
    simpa [ds] using hs0
  have hpoly1 :
      |dpt + dmt - 2 * ds| ≤ C0 * (6 + 6 * s ^ 2 + 4 * t ^ 2) := by
    linarith [habs, hspt', hsmt', hs0']
  have hpoly2 :
      C0 * (6 + 6 * s ^ 2 + 4 * t ^ 2) ≤
        (12 * C0) * (1 + s ^ 2 + t ^ 2) := by
    have hbase : 6 + 6 * s ^ 2 + 4 * t ^ 2 ≤ 12 * (1 + s ^ 2 + t ^ 2) := by
      nlinarith [sq_nonneg s, sq_nonneg t]
    have hmul :
        C0 * (6 + 6 * s ^ 2 + 4 * t ^ 2) ≤ C0 * (12 * (1 + s ^ 2 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left hbase hC0nn
    calc
      C0 * (6 + 6 * s ^ 2 + 4 * t ^ 2) ≤ C0 * (12 * (1 + s ^ 2 + t ^ 2)) := hmul
      _ = (12 * C0) * (1 + s ^ 2 + t ^ 2) := by ring
  have hmain :
      |dpt + dmt - 2 * ds| ≤ (12 * C0) * (1 + s ^ 2 + t ^ 2) := by
    exact le_trans hpoly1 hpoly2
  unfold swapped_bridge_kernel
  simpa [dpt, dmt, ds] using hmain


end
