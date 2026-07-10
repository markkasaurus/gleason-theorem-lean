import Gleason.Continuity.Defect.BridgeKernel

noncomputable section

open GleasonBridge RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

lemma shifted_base_pair_sum_swap_params
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    (local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t +
      local_quad2DDefect μ (u - (s : ℂ) • v) v 1 t)
      -
    (local_quad2DDefect μ (u + (t : ℂ) • v) v 1 s +
      local_quad2DDefect μ (u - (t : ℂ) • v) v 1 s)
      =
    2 * (local_defect_g μ u v t - local_defect_g μ u v s) := by
  have hs := shifted_base_pair_sum_eq_residual μ u v s t
  have ht := shifted_base_pair_sum_eq_residual μ u v t s
  have hsym := local_defect_residual_symm μ u v s t
  linarith [hs, ht, hsym]

lemma local_defect_g_second_diff_swap_params_formula
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    (local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
        2 * local_defect_g μ u v s)
      -
    (local_defect_g μ u v (t + s) + local_defect_g μ u v (t - s) -
        2 * local_defect_g μ u v t)
      =
    2 * (local_defect_g μ u v t - local_defect_g μ u v s) := by
  have heven : local_defect_g μ u v (t - s) = local_defect_g μ u v (s - t) := by
    have h := GleasonBridge.local_defect_g_even μ u v (s - t)
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  rw [add_comm t s, heven]
  ring

lemma local_A_func_second_diff_swap_params_formula
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    (local_A_func μ u v (s + t) + local_A_func μ u v (s - t) -
        2 * local_A_func μ u v s)
      -
    (local_A_func μ u v (t + s) + local_A_func μ u v (t - s) -
        2 * local_A_func μ u v t)
      =
    2 * local_A_func μ u v (s - t) + 2 * (local_A_func μ u v t - local_A_func μ u v s) := by
  have hneg : local_A_func μ u v (t - s) = - local_A_func μ u v (s - t) := by
    have h := local_A_func_neg hdim μ u v hu hv huv (s - t)
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  rw [add_comm t s, hneg]
  ring

lemma local_defect_g_second_diff_even_s
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    local_defect_g μ u v ((-s) + t) + local_defect_g μ u v ((-s) - t) -
      2 * local_defect_g μ u v (-s)
      =
    local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) -
      2 * local_defect_g μ u v s := by
  have he1 : local_defect_g μ u v ((-s) + t) = local_defect_g μ u v (s - t) := by
    have h := GleasonBridge.local_defect_g_even μ u v (s - t)
    have hneg : ((-s) + t) = -(s - t) := by ring
    simpa [hneg] using h
  have he2 : local_defect_g μ u v ((-s) - t) = local_defect_g μ u v (s + t) := by
    have h := GleasonBridge.local_defect_g_even μ u v (s + t)
    have hneg : ((-s) - t) = -(s + t) := by ring
    simpa [hneg] using h
  have he3 : local_defect_g μ u v (-s) = local_defect_g μ u v s := by
    simpa using GleasonBridge.local_defect_g_even μ u v s
  rw [he1, he2, he3]
  ring

lemma local_A_func_second_diff_reflect_s
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    local_A_func μ u v ((-s) + t) + local_A_func μ u v ((-s) - t) -
      2 * local_A_func μ u v (-s)
      =
    -(local_A_func μ u v (s + t) + local_A_func μ u v (s - t) -
      2 * local_A_func μ u v s) := by
  have h1 : local_A_func μ u v ((-s) + t) = -local_A_func μ u v (s - t) := by
    have h := local_A_func_neg hdim μ u v hu hv huv (s - t)
    have hneg : ((-s) + t) = -(s - t) := by ring
    simpa [hneg] using h
  have h2 : local_A_func μ u v ((-s) - t) = -local_A_func μ u v (s + t) := by
    have h := local_A_func_neg hdim μ u v hu hv huv (s + t)
    have hneg : ((-s) - t) = -(s + t) := by ring
    simpa [hneg] using h
  have h3 : local_A_func μ u v (-s) = -local_A_func μ u v s := by
    simpa using local_A_func_neg hdim μ u v hu hv huv s
  rw [h1, h2, h3]
  ring

lemma swapped_bridge_kernel_pair_sum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    swapped_bridge_kernel μ u v s t + swapped_bridge_kernel μ u v (-s) t
      =
    -2 * (local_defect_g μ v u (s + t) + local_defect_g μ v u (s - t) -
      2 * local_defect_g μ v u s) := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  simpa [swapped_bridge_kernel] using
    defect_one_gap_second_diff_pair hdim μ v u hv hu hvu s t

lemma swapped_bridge_kernel_swap_params_explicit
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    swapped_bridge_kernel μ u v s t - swapped_bridge_kernel μ u v t s =
      defect_one_gap μ v u (s - t) - defect_one_gap μ v u (t - s) +
        2 * (defect_one_gap μ v u t - defect_one_gap μ v u s) := by
  unfold swapped_bridge_kernel
  ring_nf

lemma swapped_bridge_kernel_swap_params_via_add_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    swapped_bridge_kernel μ u v s t - swapped_bridge_kernel μ u v t s =
      2 * (defect_one_gap μ v u (s - t) + local_defect_g μ v u (s - t) +
        defect_one_gap μ v u t - defect_one_gap μ v u s) := by
  have h0 :=
    swapped_bridge_kernel_swap_params_explicit
      (μ := μ) (u := u) (v := v) (s := s) (t := t)
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hadd :
      defect_one_gap μ v u (s - t) + defect_one_gap μ v u (t - s) =
        -2 * local_defect_g μ v u (s - t) := by
    have h :=
      defect_one_gap_add_neg hdim μ v u hv hu hvu (s - t)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  have hts :
      defect_one_gap μ v u (t - s) =
        -2 * local_defect_g μ v u (s - t) - defect_one_gap μ v u (s - t) := by
    linarith [hadd]
  linarith [h0, hts]

lemma sr_eq_sl_iff_swapped_bridge_kernel_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    let SR : ℝ :=
      local_quad2DDefect μ (v + (s : ℂ) • u) u 1 t +
        local_quad2DDefect μ (v - (s : ℂ) • u) u 1 t
    let SL : ℝ :=
      local_quad2DDefect μ (v + u + (s : ℂ) • (v - u)) (v - u) 1 t +
        local_quad2DDefect μ (v - u + (s : ℂ) • (v + u)) (v + u) 1 t
    (SR = SL) ↔ swapped_bridge_kernel μ u v s t = 0 := by
  intro SR SL
  have hgap : swapped_bridge_kernel μ u v s t = SL - SR := by
    unfold swapped_bridge_kernel SR SL
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (defect_one_gap_second_diff_eq_swapped_bridge_gap hdim μ u v hu hv huv s t)
  constructor
  · intro hSRSL
    rw [hgap, hSRSL]
    ring
  · intro hK0
    rw [hgap] at hK0
    linarith

lemma defect_one_gap_second_diff_swap_params_formula
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    (defect_one_gap μ v u (s + t) + defect_one_gap μ v u (s - t) -
        2 * defect_one_gap μ v u s)
      -
    (defect_one_gap μ v u (t + s) + defect_one_gap μ v u (t - s) -
        2 * defect_one_gap μ v u t)
      =
    2 * (defect_one_gap μ v u (s - t) + local_defect_g μ v u (s - t) +
      defect_one_gap μ v u t - defect_one_gap μ v u s) := by
  have hcomm :=
    swapped_bridge_kernel_swap_params_via_add_neg
      hdim μ u v hu hv huv s t
  simpa [swapped_bridge_kernel, add_comm t s] using hcomm

lemma local_defect_g_zero_of_swapped_kernel_symmetry
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hsym : ∀ s t : ℝ, swapped_bridge_kernel μ u v s t = swapped_bridge_kernel μ u v t s) :
    ∀ t : ℝ, local_defect_g μ v u t = 0 := by
  intro t
  have hswap := hsym 0 t
  have h0t :
      swapped_bridge_kernel μ u v 0 t = -2 * local_defect_g μ v u t := by
    have hvu : inner (𝕜 := ℂ) v u = 0 := by
      simpa [inner_eq_zero_symm] using huv
    have hsum :
        defect_one_gap μ v u t + defect_one_gap μ v u (-t) =
          -2 * local_defect_g μ v u t := by
      simpa using defect_one_gap_add_neg hdim μ v u hv hu hvu t
    have h0 : defect_one_gap μ v u 0 = 0 :=
      defect_one_gap_zero hdim μ v u hv hu hvu
    unfold swapped_bridge_kernel
    rw [zero_add, zero_sub]
    linarith
  have ht0 :
      swapped_bridge_kernel μ u v t 0 = 0 := swapped_bridge_kernel_zero_t0 μ u v t
  rw [h0t, ht0] at hswap
  linarith [hswap]

lemma frame_quadratic_full_parallelogram_of_swapped_kernel_nonneg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hnonneg :
      ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
        ∀ s t : ℝ, 0 ≤ swapped_bridge_kernel μ a b s t)
    (x y : H) :
    frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
      2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by
  have hg0 :
      ∀ (u v : H), ‖u‖ = 1 → ‖v‖ = 1 → inner (𝕜 := ℂ) u v = 0 →
        ∀ t : ℝ, local_defect_g μ u v t = 0 := by
    intro u v hu hv huv t
    have hvu : inner (𝕜 := ℂ) v u = 0 := by
      simpa [inner_eq_zero_symm] using huv
    have hker0 :
        ∀ s t : ℝ, swapped_bridge_kernel μ v u s t = 0 := by
      intro s t
      exact
        swapped_bridge_kernel_eq_zero_of_global_nonneg
          hdim μ hnonneg v u hv hu hvu s t
    have hsym :
        ∀ s t : ℝ, swapped_bridge_kernel μ v u s t = swapped_bridge_kernel μ v u t s := by
      intro s t
      rw [hker0 s t, hker0 t s]
    exact
      local_defect_g_zero_of_swapped_kernel_symmetry
        hdim μ v u hv hu hvu hsym t
  have horth :
      ∀ (a b : H), inner (𝕜 := ℂ) a b = 0 →
        frame_quadratic (H := H) μ (a + b) + frame_quadratic (H := H) μ (a - b) =
          2 * frame_quadratic (H := H) μ a + 2 * frame_quadratic (H := H) μ b := by
    intro a b hab
    exact orthogonal_pi_of_g_zero hdim μ hg0 a b hab
  exact full_pi_of_orthogonal_pi hdim μ horth x y

def hadamard_bridge_error_second_diff
    (μ : FrameFunction H) (u v : H) (s t : ℝ) : ℝ :=
  hadamard_bridge_error μ u v (s + t) +
    hadamard_bridge_error μ u v (s - t) -
    2 * hadamard_bridge_error μ u v s

lemma local_quad2DDefect_eq_zero_of_full_pi_mod
    (μ : FrameFunction H)
    (hPI : ∀ x y : H,
      frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
        2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y)
    (u v : H) (a b : ℝ) :
    local_quad2DDefect μ u v a b = 0 := by
  have hfp := hPI ((a : ℂ) • u) ((b : ℂ) • v)
  have hQua : frame_quadratic (H := H) μ ((a : ℂ) • u) =
      a ^ 2 * frame_quadratic (H := H) μ u := by
    have h := frame_quadratic_sq_hom (H := H) μ (a : ℂ) u
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    exact h
  have hQvb : frame_quadratic (H := H) μ ((b : ℂ) • v) =
      b ^ 2 * frame_quadratic (H := H) μ v := by
    have h := frame_quadratic_sq_hom (H := H) μ (b : ℂ) v
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    exact h
  unfold local_quad2DDefect local_quad2DExpr
  linarith [hfp, hQua, hQvb]

lemma hadamard_bridge_error_zero_all_of_full_pi_mod
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hPI : ∀ x y : H,
      frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
        2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∀ r : ℝ, hadamard_bridge_error μ u v r = 0 := by
  intro r
  have hDzero : ∀ a b : ℝ, local_quad2DDefect μ u v a b = 0 :=
    fun a b => local_quad2DDefect_eq_zero_of_full_pi_mod μ hPI u v a b
  have hgap0 : defect_one_gap μ u v r = 0 := by
    unfold defect_one_gap
    rw [hDzero (1 + r) (1 - r), hDzero 1 r]
    ring
  have hgap : defect_one_gap μ u v r = 2 * hadamard_bridge_error μ u v r :=
    defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv r
  linarith [hgap, hgap0]

lemma hadamard_bridge_error_second_diff_nonneg_of_full_pi_mod
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hPI : ∀ x y : H,
      frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
        2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∀ s t : ℝ, 0 ≤ hadamard_bridge_error_second_diff μ u v s t := by
  intro s t
  have hE0 := hadamard_bridge_error_zero_all_of_full_pi_mod hdim μ hPI u v hu hv huv
  unfold hadamard_bridge_error_second_diff
  rw [hE0 (s + t), hE0 (s - t), hE0 s]
  norm_num


lemma swapped_bridge_kernel_nonneg_of_hadamard_bridge_error_second_diff_nonneg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hE2_nonneg : ∀ s t : ℝ, 0 ≤ hadamard_bridge_error_second_diff μ v u s t) :
    ∀ s t : ℝ, 0 ≤ swapped_bridge_kernel μ u v s t := by
  intro s t
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hker :
      swapped_bridge_kernel μ u v s t =
        2 * hadamard_bridge_error_second_diff μ v u s t := by
    have hst :
        defect_one_gap μ v u (s + t) =
          2 * hadamard_bridge_error μ v u (s + t) := by
      exact defect_one_gap_eq_two_mul_bridge_error hdim μ v u hv hu hvu (s + t)
    have hsm :
        defect_one_gap μ v u (s - t) =
          2 * hadamard_bridge_error μ v u (s - t) := by
      exact defect_one_gap_eq_two_mul_bridge_error hdim μ v u hv hu hvu (s - t)
    have hs0 :
        defect_one_gap μ v u s =
          2 * hadamard_bridge_error μ v u s := by
      exact defect_one_gap_eq_two_mul_bridge_error hdim μ v u hv hu hvu s
    unfold swapped_bridge_kernel hadamard_bridge_error_second_diff
    rw [hst, hsm, hs0]
    ring
  rw [hker]
  nlinarith [hE2_nonneg s t]

lemma frame_quadratic_full_parallelogram_of_hadamard_bridge_error_second_diff_nonneg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hE2_nonneg :
      ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
        ∀ s t : ℝ, 0 ≤ hadamard_bridge_error_second_diff μ b a s t)
    (x y : H) :
    frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
      2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by
  have hker_nonneg :
      ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
        ∀ s t : ℝ, 0 ≤ swapped_bridge_kernel μ a b s t := by
    intro a b ha hb hab s t
    exact
      swapped_bridge_kernel_nonneg_of_hadamard_bridge_error_second_diff_nonneg
        hdim μ a b ha hb hab (hE2_nonneg a b ha hb hab) s t
  exact
    frame_quadratic_full_parallelogram_of_swapped_kernel_nonneg
      hdim μ hker_nonneg x y

lemma hadamard_bridge_error_zero_all_of_second_diff_global_nonneg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hE2_nonneg :
      ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
        ∀ s t : ℝ, 0 ≤ hadamard_bridge_error_second_diff μ a b s t)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hE2_zero :
      ∀ s t : ℝ, hadamard_bridge_error_second_diff μ u v s t = 0 := by
    intro s t
    have hnn_uv : 0 ≤ hadamard_bridge_error_second_diff μ u v s t :=
      hE2_nonneg u v hu hv huv s t
    have hnn_vu : 0 ≤ hadamard_bridge_error_second_diff μ v u s t :=
      hE2_nonneg v u hv hu hvu s t
    have hswap :
        hadamard_bridge_error_second_diff μ v u s t =
          -hadamard_bridge_error_second_diff μ u v s t := by
      have hker_uv :
          swapped_bridge_kernel μ u v s t =
            2 * hadamard_bridge_error_second_diff μ v u s t := by
        have hst :
            defect_one_gap μ v u (s + t) =
              2 * hadamard_bridge_error μ v u (s + t) := by
          exact defect_one_gap_eq_two_mul_bridge_error hdim μ v u hv hu hvu (s + t)
        have hsm :
            defect_one_gap μ v u (s - t) =
              2 * hadamard_bridge_error μ v u (s - t) := by
          exact defect_one_gap_eq_two_mul_bridge_error hdim μ v u hv hu hvu (s - t)
        have hs0 :
            defect_one_gap μ v u s =
              2 * hadamard_bridge_error μ v u s := by
          exact defect_one_gap_eq_two_mul_bridge_error hdim μ v u hv hu hvu s
        unfold swapped_bridge_kernel hadamard_bridge_error_second_diff
        rw [hst, hsm, hs0]
        ring
      have hker_vu :
          swapped_bridge_kernel μ v u s t =
            2 * hadamard_bridge_error_second_diff μ u v s t := by
        have hst :
            defect_one_gap μ u v (s + t) =
              2 * hadamard_bridge_error μ u v (s + t) := by
          exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv (s + t)
        have hsm :
            defect_one_gap μ u v (s - t) =
              2 * hadamard_bridge_error μ u v (s - t) := by
          exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv (s - t)
        have hs0 :
            defect_one_gap μ u v s =
              2 * hadamard_bridge_error μ u v s := by
          exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv s
        unfold swapped_bridge_kernel hadamard_bridge_error_second_diff
        rw [hst, hsm, hs0]
        ring
      have hswapK :
          swapped_bridge_kernel μ u v s t = -swapped_bridge_kernel μ v u s t :=
        swapped_bridge_kernel_swap_neg hdim μ u v hu hv huv s t
      have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
      apply (mul_right_inj' h2_ne).1
      calc
        2 * hadamard_bridge_error_second_diff μ v u s t
            = swapped_bridge_kernel μ u v s t := hker_uv.symm
        _ = -swapped_bridge_kernel μ v u s t := hswapK
        _ = 2 * (-hadamard_bridge_error_second_diff μ u v s t) := by
              rw [hker_vu]
              ring
    linarith
  have hker0 : ∀ s t : ℝ, swapped_bridge_kernel μ v u s t = 0 := by
    intro s t
    have hker :
        swapped_bridge_kernel μ v u s t =
          2 * hadamard_bridge_error_second_diff μ u v s t := by
      have hst :
          defect_one_gap μ u v (s + t) =
            2 * hadamard_bridge_error μ u v (s + t) := by
        exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv (s + t)
      have hsm :
          defect_one_gap μ u v (s - t) =
            2 * hadamard_bridge_error μ u v (s - t) := by
        exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv (s - t)
      have hs0 :
          defect_one_gap μ u v s =
            2 * hadamard_bridge_error μ u v s := by
        exact defect_one_gap_eq_two_mul_bridge_error hdim μ u v hu hv huv s
      unfold swapped_bridge_kernel hadamard_bridge_error_second_diff
      rw [hst, hsm, hs0]
      ring
    rw [hker, hE2_zero s t]
    ring
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

lemma hadamard_bridge_error_zero_all_of_swapped_kernel_global_nonneg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hnonneg :
      ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
        ∀ s t : ℝ, 0 ≤ swapped_bridge_kernel μ a b s t)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have hker0 :
      ∀ s t : ℝ, swapped_bridge_kernel μ v u s t = 0 :=
    swapped_bridge_kernel_eq_zero_of_global_nonneg hdim μ hnonneg v u hv hu
      (by simpa [inner_eq_zero_symm] using huv)
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

lemma frame_quadratic_full_parallelogram_of_second_diff_global_nonneg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hE2_nonneg :
      ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
        ∀ s t : ℝ, 0 ≤ hadamard_bridge_error_second_diff μ a b s t)
    (x y : H) :
    frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
      2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by
  have hE2_nonneg_rev :
      ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
        ∀ s t : ℝ, 0 ≤ hadamard_bridge_error_second_diff μ b a s t := by
    intro a b ha hb hab s t
    have hba : inner (𝕜 := ℂ) b a = 0 := by
      simpa [inner_eq_zero_symm] using hab
    exact hE2_nonneg b a hb ha hba s t
  exact
    frame_quadratic_full_parallelogram_of_hadamard_bridge_error_second_diff_nonneg
      hdim μ hE2_nonneg_rev x y

lemma swapped_bridge_kernel_zero_s
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    swapped_bridge_kernel μ u v 0 t = -2 * local_defect_g μ v u t := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hsum :
      defect_one_gap μ v u t + defect_one_gap μ v u (-t) =
        -2 * local_defect_g μ v u t := by
    simpa using defect_one_gap_add_neg hdim μ v u hv hu hvu t
  have h0 : defect_one_gap μ v u 0 = 0 :=
    defect_one_gap_zero hdim μ v u hv hu hvu
  unfold swapped_bridge_kernel
  rw [zero_add, zero_sub]
  linarith

/-- Normalized two-point gauge for the swapped bridge kernel in the `t` variable. -/
def swapped_bridge_kernel_normalized_gauge
    (μ : FrameFunction H) (u v : H) (s r : ℝ) : ℝ :=
  max
    (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
    (|swapped_bridge_kernel μ u v s (-r)| / (1 + r ^ 2))

lemma swapped_bridge_kernel_normalized_gauge_nonneg
    (μ : FrameFunction H) (u v : H) (s r : ℝ) :
    0 ≤ swapped_bridge_kernel_normalized_gauge μ u v s r := by
  unfold swapped_bridge_kernel_normalized_gauge
  have h1 : 0 ≤ |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2) := by
    refine div_nonneg (abs_nonneg _) ?_
    nlinarith [sq_nonneg r]
  exact le_trans h1 (le_max_left _ _)

lemma swapped_bridge_kernel_normalized_gauge_eq_single
    (μ : FrameFunction H) (u v : H) (s r : ℝ) :
    swapped_bridge_kernel_normalized_gauge μ u v s r =
      |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2) := by
  unfold swapped_bridge_kernel_normalized_gauge
  rw [swapped_bridge_kernel_even_t μ u v s r]
  simp

lemma swapped_bridge_kernel_normalized_gauge_even_r
    (μ : FrameFunction H) (u v : H) (s r : ℝ) :
    swapped_bridge_kernel_normalized_gauge μ u v s (-r) =
      swapped_bridge_kernel_normalized_gauge μ u v s r := by
  rw [swapped_bridge_kernel_normalized_gauge_eq_single]
  rw [swapped_bridge_kernel_normalized_gauge_eq_single]
  rw [swapped_bridge_kernel_even_t μ u v s r]
  ring_nf

lemma swapped_bridge_kernel_zero_of_normalized_gauge_zero
    (μ : FrameFunction H) (u v : H) (s r : ℝ)
    (hG : swapped_bridge_kernel_normalized_gauge μ u v s r = 0) :
    swapped_bridge_kernel μ u v s r = 0 := by
  have hsingle :
      |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2) = 0 := by
    have hle :
        |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2)
          ≤ swapped_bridge_kernel_normalized_gauge μ u v s r := by
      unfold swapped_bridge_kernel_normalized_gauge
      exact le_max_left _ _
    have hle0 :
        |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2) ≤ 0 := by
      simpa [hG] using hle
    have hnonneg :
        0 ≤ |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2) := by
      refine div_nonneg (abs_nonneg _) ?_
      nlinarith [sq_nonneg r]
    exact le_antisymm hle0 hnonneg
  have habs0 : |swapped_bridge_kernel μ u v s r| = 0 := by
    rcases (div_eq_zero_iff).1 hsingle with habs0 | hden0
    · exact habs0
    · exfalso
      nlinarith [sq_nonneg r, hden0]
  exact abs_eq_zero.mp habs0

lemma hadamard_mobius_abs_lt_one_of_pos_lt_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    |(1 - r) / (1 + r)| < 1 := by
  have h1pr_pos : 0 < 1 + r := by linarith
  have hnum_pos : 0 < 1 - r := by linarith
  have hfrac_nonneg : 0 ≤ (1 - r) / (1 + r) := by
    exact div_nonneg (le_of_lt hnum_pos) (le_of_lt h1pr_pos)
  have hfrac_lt_one : (1 - r) / (1 + r) < 1 := by
    exact (div_lt_iff₀ h1pr_pos).2 (by linarith)
  rw [abs_of_nonneg hfrac_nonneg]
  exact hfrac_lt_one

lemma hadamard_mobius_pos_lt_one_of_pos_lt_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < (1 - r) / (1 + r) ∧ (1 - r) / (1 + r) < 1 := by
  have h1pr_pos : 0 < 1 + r := by linarith
  constructor
  · exact div_pos (by linarith) h1pr_pos
  · exact (div_lt_iff₀ h1pr_pos).2 (by linarith)

lemma hadamard_mobius_transport_eq_on_unit_interval
    (G : ℝ → ℝ)
    (htransport :
      ∀ r : ℝ, 0 < r → r < 1 → G r ≤ G ((1 - r) / (1 + r))) :
    ∀ r : ℝ, 0 < r → r < 1 → G r = G ((1 - r) / (1 + r)) := by
  intro r hr0 hr1
  let φ : ℝ := (1 - r) / (1 + r)
  have h1pr : 1 + r ≠ 0 := by linarith
  have hφ : 0 < φ ∧ φ < 1 := by
    simpa [φ] using hadamard_mobius_pos_lt_one_of_pos_lt_one (r := r) hr0 hr1
  have hA : G r ≤ G φ := by
    simpa [φ] using htransport r hr0 hr1
  have hB : G φ ≤ G ((1 - φ) / (1 + φ)) := by
    exact htransport φ hφ.1 hφ.2
  have hφφ : (1 - φ) / (1 + φ) = r := by
    simpa [φ] using hadamard_mobius_involutive r h1pr
  rw [hφφ] at hB
  exact le_antisymm hA hB

lemma swapped_bridge_kernel_zero_all_of_transport_strict
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport :
      ∀ s r : ℝ, 0 < r → r < 1 →
        swapped_bridge_kernel_normalized_gauge μ v u s r ≤
          swapped_bridge_kernel_normalized_gauge μ v u s ((1 - r) / (1 + r)))
    (hstrict :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          swapped_bridge_kernel_normalized_gauge μ v u s r <
            swapped_bridge_kernel_normalized_gauge μ v u s ((1 - r) / (1 + r))) :
    ∀ s t : ℝ, swapped_bridge_kernel μ v u s t = 0 := by
  intro s t
  by_contra hne
  have hnz : ∃ z : ℝ, swapped_bridge_kernel μ v u s z ≠ 0 := ⟨t, hne⟩
  rcases hstrict s hnz with ⟨r, hr0, hr1, hslt⟩
  have heq :
      swapped_bridge_kernel_normalized_gauge μ v u s r =
        swapped_bridge_kernel_normalized_gauge μ v u s ((1 - r) / (1 + r)) := by
    exact
      hadamard_mobius_transport_eq_on_unit_interval
        (G := fun x => swapped_bridge_kernel_normalized_gauge μ v u s x)
        (htransport := fun x hx0 hx1 => htransport s x hx0 hx1)
        r hr0 hr1
  linarith [hslt, heq]

lemma hadamard_bridge_error_zero_all_of_transport_strict
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport :
      ∀ s r : ℝ, 0 < r → r < 1 →
        swapped_bridge_kernel_normalized_gauge μ v u s r ≤
          swapped_bridge_kernel_normalized_gauge μ v u s ((1 - r) / (1 + r)))
    (hstrict :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          swapped_bridge_kernel_normalized_gauge μ v u s r <
            swapped_bridge_kernel_normalized_gauge μ v u s ((1 - r) / (1 + r))) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have hker0 : ∀ s t : ℝ, swapped_bridge_kernel μ v u s t = 0 := by
    exact swapped_bridge_kernel_zero_all_of_transport_strict hdim μ u v hu hv huv htransport hstrict
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

lemma hadamard_bridge_error_zero_all_of_transport_strict_single
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport1 :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|swapped_bridge_kernel μ v u s r| / (1 + r ^ 2))
          ≤
        (|swapped_bridge_kernel μ v u s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hstrict1 :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|swapped_bridge_kernel μ v u s r| / (1 + r ^ 2))
            <
          (|swapped_bridge_kernel μ v u s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have htransport :
      ∀ s r : ℝ, 0 < r → r < 1 →
        swapped_bridge_kernel_normalized_gauge μ v u s r
          ≤
        swapped_bridge_kernel_normalized_gauge μ v u s ((1 - r) / (1 + r)) := by
    intro s r hr0 hr1
    rw [swapped_bridge_kernel_normalized_gauge_eq_single]
    rw [swapped_bridge_kernel_normalized_gauge_eq_single]
    exact htransport1 s r hr0 hr1
  have hstrict :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          swapped_bridge_kernel_normalized_gauge μ v u s r
            <
          swapped_bridge_kernel_normalized_gauge μ v u s ((1 - r) / (1 + r)) := by
    intro s hnz
    rcases hstrict1 s hnz with ⟨r, hr0, hr1, hlt⟩
    refine ⟨r, hr0, hr1, ?_⟩
    rw [swapped_bridge_kernel_normalized_gauge_eq_single]
    rw [swapped_bridge_kernel_normalized_gauge_eq_single]
    exact hlt
  exact hadamard_bridge_error_zero_all_of_transport_strict hdim μ u v hu hv huv htransport hstrict

lemma swapped_bridge_kernel_transport_pair_of_single
    (μ : FrameFunction H) (u v : H)
    (htransport1 :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
          ≤
        (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ s r : ℝ, 0 < r → r < 1 →
      swapped_bridge_kernel_normalized_gauge μ u v s r
        ≤
      swapped_bridge_kernel_normalized_gauge μ u v s ((1 - r) / (1 + r)) := by
  intro s r hr0 hr1
  rw [swapped_bridge_kernel_normalized_gauge_eq_single]
  rw [swapped_bridge_kernel_normalized_gauge_eq_single]
  exact htransport1 s r hr0 hr1

lemma swapped_bridge_kernel_transport_single_of_pair
    (μ : FrameFunction H) (u v : H)
    (htransport :
      ∀ s r : ℝ, 0 < r → r < 1 →
        swapped_bridge_kernel_normalized_gauge μ u v s r
          ≤
        swapped_bridge_kernel_normalized_gauge μ u v s ((1 - r) / (1 + r))) :
    ∀ s r : ℝ, 0 < r → r < 1 →
      (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
        ≤
      (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro s r hr0 hr1
  have h := htransport s r hr0 hr1
  rw [swapped_bridge_kernel_normalized_gauge_eq_single] at h
  rw [swapped_bridge_kernel_normalized_gauge_eq_single] at h
  exact h

lemma swapped_bridge_kernel_transport_strict_pair_of_single
    (μ : FrameFunction H) (u v : H)
    (hstrict1 :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
            <
          (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        swapped_bridge_kernel_normalized_gauge μ u v s r
          <
        swapped_bridge_kernel_normalized_gauge μ u v s ((1 - r) / (1 + r)) := by
  intro s hnz
  rcases hstrict1 s hnz with ⟨r, hr0, hr1, hlt⟩
  refine ⟨r, hr0, hr1, ?_⟩
  rw [swapped_bridge_kernel_normalized_gauge_eq_single]
  rw [swapped_bridge_kernel_normalized_gauge_eq_single]
  exact hlt

lemma swapped_bridge_kernel_transport_strict_single_of_pair
    (μ : FrameFunction H) (u v : H)
    (hstrict :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          swapped_bridge_kernel_normalized_gauge μ u v s r
            <
          swapped_bridge_kernel_normalized_gauge μ u v s ((1 - r) / (1 + r))) :
    ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
          <
        (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro s hnz
  rcases hstrict s hnz with ⟨r, hr0, hr1, hlt⟩
  refine ⟨r, hr0, hr1, ?_⟩
  rw [swapped_bridge_kernel_normalized_gauge_eq_single] at hlt
  rw [swapped_bridge_kernel_normalized_gauge_eq_single] at hlt
  exact hlt

lemma swapped_bridge_kernel_transport_strict_single_of_neq_witness
    (μ : FrameFunction H) (u v : H)
    (hneq :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
            ≠
          (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
          <
        (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
  intro s hnz
  rcases hneq s hnz with ⟨r, hr0, hr1, hne⟩
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

lemma swapped_bridge_kernel_normalized_gauge_uniform_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s r : ℝ,
      swapped_bridge_kernel_normalized_gauge μ u v s r ≤ C * (1 + s ^ 2) := by
  rcases swapped_bridge_kernel_growth_bound_two_vars hdim μ u v hu hv huv with
    ⟨C0, hC0nn, hC0⟩
  refine ⟨C0, hC0nn, ?_⟩
  intro s r
  have hden_pos : 0 < (1 + r ^ 2 : ℝ) := by
    nlinarith [sq_nonneg r]
  have hden_nonneg : 0 ≤ (1 + r ^ 2 : ℝ) := le_of_lt hden_pos
  have hratio :
      (1 + s ^ 2 + r ^ 2) / (1 + r ^ 2) ≤ 1 + s ^ 2 := by
    have hmul : 1 + s ^ 2 + r ^ 2 ≤ (1 + s ^ 2) * (1 + r ^ 2) := by
      nlinarith [sq_nonneg s, sq_nonneg r]
    exact (div_le_iff₀ hden_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hsr_raw : |swapped_bridge_kernel μ u v s r| ≤ C0 * (1 + s ^ 2 + r ^ 2) := hC0 s r
  have hsr_div :
      |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2)
        ≤ (C0 * (1 + s ^ 2 + r ^ 2)) / (1 + r ^ 2) := by
    exact div_le_div_of_nonneg_right hsr_raw hden_nonneg
  have hsr_main :
      |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2) ≤ C0 * (1 + s ^ 2) := by
    have hmulratio :
        (C0 * (1 + s ^ 2 + r ^ 2)) / (1 + r ^ 2) ≤ C0 * (1 + s ^ 2) := by
      have hrew :
          (C0 * (1 + s ^ 2 + r ^ 2)) / (1 + r ^ 2)
            = C0 * ((1 + s ^ 2 + r ^ 2) / (1 + r ^ 2)) := by
        ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_left hratio hC0nn
    exact le_trans hsr_div hmulratio
  have hsnr_raw : |swapped_bridge_kernel μ u v s (-r)| ≤ C0 * (1 + s ^ 2 + (-r) ^ 2) := hC0 s (-r)
  have hsnr_div :
      |swapped_bridge_kernel μ u v s (-r)| / (1 + r ^ 2)
        ≤ (C0 * (1 + s ^ 2 + (-r) ^ 2)) / (1 + r ^ 2) := by
    have hsnr_div' :
        |swapped_bridge_kernel μ u v s (-r)| / (1 + (-r) ^ 2)
          ≤ (C0 * (1 + s ^ 2 + (-r) ^ 2)) / (1 + (-r) ^ 2) := by
      exact div_le_div_of_nonneg_right hsnr_raw (by nlinarith [sq_nonneg r])
    simpa using hsnr_div'
  have hratio_neg :
      (1 + s ^ 2 + (-r) ^ 2) / (1 + r ^ 2) ≤ 1 + s ^ 2 := by
    simpa using hratio
  have hsnr_main :
      |swapped_bridge_kernel μ u v s (-r)| / (1 + r ^ 2) ≤ C0 * (1 + s ^ 2) := by
    have hmulratio :
        (C0 * (1 + s ^ 2 + (-r) ^ 2)) / (1 + r ^ 2) ≤ C0 * (1 + s ^ 2) := by
      have hrew :
          (C0 * (1 + s ^ 2 + (-r) ^ 2)) / (1 + r ^ 2)
            = C0 * ((1 + s ^ 2 + (-r) ^ 2) / (1 + r ^ 2)) := by
        ring
      rw [hrew]
      exact mul_le_mul_of_nonneg_left hratio_neg hC0nn
    exact le_trans hsnr_div hmulratio
  unfold swapped_bridge_kernel_normalized_gauge
  exact max_le_iff.mpr ⟨hsr_main, hsnr_main⟩

lemma swapped_bridge_kernel_eq_zero_of_zero_all_normalized_gauge
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hG0 : ∀ s r : ℝ, swapped_bridge_kernel_normalized_gauge μ u v s r = 0) :
    ∀ s t : ℝ, swapped_bridge_kernel μ u v s t = 0 := by
  intro s t
  exact swapped_bridge_kernel_zero_of_normalized_gauge_zero μ u v s t (hG0 s t)

lemma swapped_bridge_kernel_gap_closure
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    (swapped_bridge_kernel μ u v s t = 0)
      ↔
    (local_quad2DDefect μ (v + u + (s : ℂ) • (v - u)) (v - u) 1 t +
      local_quad2DDefect μ (v - u + (s : ℂ) • (v + u)) (v + u) 1 t
      =
    local_quad2DDefect μ (v + (s : ℂ) • u) u 1 t +
      local_quad2DDefect μ (v - (s : ℂ) • u) u 1 t) := by
  have hgap := swapped_bridge_kernel_eq_gap hdim μ u v hu hv huv s t
  constructor
  · intro hk
    linarith [hgap, hk]
  · intro hEq
    linarith [hgap, hEq]

lemma swapped_bridge_kernel_eq_two_hadamard_bridge_error_second_diff
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    swapped_bridge_kernel μ u v s t
      =
    2 *
      (hadamard_bridge_error μ v u (s + t) +
        hadamard_bridge_error μ v u (s - t) -
        2 * hadamard_bridge_error μ v u s) := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hst :
      defect_one_gap μ v u (s + t) =
        2 * hadamard_bridge_error μ v u (s + t) := by
    exact defect_one_gap_eq_two_mul_bridge_error hdim μ v u hv hu hvu (s + t)
  have hsm :
      defect_one_gap μ v u (s - t) =
        2 * hadamard_bridge_error μ v u (s - t) := by
    exact defect_one_gap_eq_two_mul_bridge_error hdim μ v u hv hu hvu (s - t)
  have hs0 :
      defect_one_gap μ v u s =
        2 * hadamard_bridge_error μ v u s := by
    exact defect_one_gap_eq_two_mul_bridge_error hdim μ v u hv hu hvu s
  unfold swapped_bridge_kernel
  rw [hst, hsm, hs0]
  ring

lemma swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    |swapped_bridge_kernel μ u v s t| / (1 + t ^ 2)
      =
    2 *
      (|hadamard_bridge_error μ v u (s + t) +
          hadamard_bridge_error μ v u (s - t) -
          2 * hadamard_bridge_error μ v u s| / (1 + t ^ 2)) := by
  have hker :=
    swapped_bridge_kernel_eq_two_hadamard_bridge_error_second_diff
      hdim μ u v hu hv huv s t
  have h2nn : (0 : ℝ) ≤ 2 := by norm_num
  rw [hker]
  rw [abs_mul, abs_of_nonneg h2nn]
  ring

lemma swapped_bridge_kernel_transport_single_iff_hadamard_second_diff_transport
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∀ s r : ℝ, 0 < r → r < 1 →
      (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
        ≤
      (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2)))
      ↔
    (∀ s r : ℝ, 0 < r → r < 1 →
      (|hadamard_bridge_error μ v u (s + r) +
          hadamard_bridge_error μ v u (s - r) -
          2 * hadamard_bridge_error μ v u s| / (1 + r ^ 2))
        ≤
      (|hadamard_bridge_error μ v u (s + ((1 - r) / (1 + r))) +
          hadamard_bridge_error μ v u (s - ((1 - r) / (1 + r))) -
          2 * hadamard_bridge_error μ v u s| /
        (1 + ((1 - r) / (1 + r)) ^ 2))) := by
  constructor
  · intro htransport s r hr0 hr1
    have hker_r :
        |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + r) +
              hadamard_bridge_error μ v u (s - r) -
              2 * hadamard_bridge_error μ v u s| / (1 + r ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s r
    have hker_phi :
        |swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + ((1 - r) / (1 + r))) +
              hadamard_bridge_error μ v u (s - ((1 - r) / (1 + r))) -
              2 * hadamard_bridge_error μ v u s| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s ((1 - r) / (1 + r))
    have h := htransport s r hr0 hr1
    rw [hker_r, hker_phi] at h
    nlinarith
  · intro htransport s r hr0 hr1
    have hker_r :
        |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + r) +
              hadamard_bridge_error μ v u (s - r) -
              2 * hadamard_bridge_error μ v u s| / (1 + r ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s r
    have hker_phi :
        |swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + ((1 - r) / (1 + r))) +
              hadamard_bridge_error μ v u (s - ((1 - r) / (1 + r))) -
              2 * hadamard_bridge_error μ v u s| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s ((1 - r) / (1 + r))
    have h := htransport s r hr0 hr1
    nlinarith [hker_r, hker_phi, h]

lemma swapped_bridge_kernel_transport_strict_single_iff_hadamard_second_diff_transport
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
          <
        (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
      ↔
    (∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|hadamard_bridge_error μ v u (s + r) +
            hadamard_bridge_error μ v u (s - r) -
            2 * hadamard_bridge_error μ v u s| / (1 + r ^ 2))
          <
        (|hadamard_bridge_error μ v u (s + ((1 - r) / (1 + r))) +
            hadamard_bridge_error μ v u (s - ((1 - r) / (1 + r))) -
            2 * hadamard_bridge_error μ v u s| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) := by
  constructor
  · intro hstrict s hnz
    rcases hstrict s hnz with ⟨r, hr0, hr1, hlt⟩
    refine ⟨r, hr0, hr1, ?_⟩
    have hker_r :
        |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + r) +
              hadamard_bridge_error μ v u (s - r) -
              2 * hadamard_bridge_error μ v u s| / (1 + r ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s r
    have hker_phi :
        |swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + ((1 - r) / (1 + r))) +
              hadamard_bridge_error μ v u (s - ((1 - r) / (1 + r))) -
              2 * hadamard_bridge_error μ v u s| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s ((1 - r) / (1 + r))
    rw [hker_r, hker_phi] at hlt
    nlinarith
  · intro hstrict s hnz
    rcases hstrict s hnz with ⟨r, hr0, hr1, hlt⟩
    refine ⟨r, hr0, hr1, ?_⟩
    have hker_r :
        |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + r) +
              hadamard_bridge_error μ v u (s - r) -
              2 * hadamard_bridge_error μ v u s| / (1 + r ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s r
    have hker_phi :
        |swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + ((1 - r) / (1 + r))) +
              hadamard_bridge_error μ v u (s - ((1 - r) / (1 + r))) -
              2 * hadamard_bridge_error μ v u s| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s ((1 - r) / (1 + r))
    nlinarith [hker_r, hker_phi, hlt]

lemma swapped_bridge_kernel_transport_neq_single_iff_hadamard_second_diff_neq
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    (∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|swapped_bridge_kernel μ u v s r| / (1 + r ^ 2))
          ≠
        (|swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
      ↔
    (∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ u v s t ≠ 0) →
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        (|hadamard_bridge_error μ v u (s + r) +
            hadamard_bridge_error μ v u (s - r) -
            2 * hadamard_bridge_error μ v u s| / (1 + r ^ 2))
          ≠
        (|hadamard_bridge_error μ v u (s + ((1 - r) / (1 + r))) +
            hadamard_bridge_error μ v u (s - ((1 - r) / (1 + r))) -
            2 * hadamard_bridge_error μ v u s| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) := by
  constructor
  · intro hneq s hnz
    rcases hneq s hnz with ⟨r, hr0, hr1, hne⟩
    refine ⟨r, hr0, hr1, ?_⟩
    have hker_r :
        |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + r) +
              hadamard_bridge_error μ v u (s - r) -
              2 * hadamard_bridge_error μ v u s| / (1 + r ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s r
    have hker_phi :
        |swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + ((1 - r) / (1 + r))) +
              hadamard_bridge_error μ v u (s - ((1 - r) / (1 + r))) -
              2 * hadamard_bridge_error μ v u s| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s ((1 - r) / (1 + r))
    intro hEq
    apply hne
    rw [hker_r, hker_phi]
    nlinarith [hEq]
  · intro hneq s hnz
    rcases hneq s hnz with ⟨r, hr0, hr1, hne⟩
    refine ⟨r, hr0, hr1, ?_⟩
    have hker_r :
        |swapped_bridge_kernel μ u v s r| / (1 + r ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + r) +
              hadamard_bridge_error μ v u (s - r) -
              2 * hadamard_bridge_error μ v u s| / (1 + r ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s r
    have hker_phi :
        |swapped_bridge_kernel μ u v s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)
          =
        2 *
          (|hadamard_bridge_error μ v u (s + ((1 - r) / (1 + r))) +
              hadamard_bridge_error μ v u (s - ((1 - r) / (1 + r))) -
              2 * hadamard_bridge_error μ v u s| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        swapped_bridge_kernel_normalized_single_eq_hadamard_second_diff
          hdim μ u v hu hv huv s ((1 - r) / (1 + r))
    intro hEq
    apply hne
    have hEq' :
        (|hadamard_bridge_error μ v u (s + r) +
            hadamard_bridge_error μ v u (s - r) -
            2 * hadamard_bridge_error μ v u s| / (1 + r ^ 2))
          =
        (|hadamard_bridge_error μ v u (s + ((1 - r) / (1 + r))) +
            hadamard_bridge_error μ v u (s - ((1 - r) / (1 + r))) -
            2 * hadamard_bridge_error μ v u s| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
      nlinarith [hker_r, hker_phi, hEq]
    exact hEq'

lemma hadamard_bridge_error_zero_all_of_second_diff_transport_strict
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransportE :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|hadamard_bridge_error μ u v (s + r) +
            hadamard_bridge_error μ u v (s - r) -
            2 * hadamard_bridge_error μ u v s| / (1 + r ^ 2))
          ≤
        (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) +
            hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
            2 * hadamard_bridge_error μ u v s| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))
    (hstrictE :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|hadamard_bridge_error μ u v (s + r) +
              hadamard_bridge_error μ u v (s - r) -
              2 * hadamard_bridge_error μ u v s| / (1 + r ^ 2))
            <
          (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) +
              hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
              2 * hadamard_bridge_error μ u v s| /
            (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have htransportK :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|swapped_bridge_kernel μ v u s r| / (1 + r ^ 2))
          ≤
        (|swapped_bridge_kernel μ v u s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    exact
      (swapped_bridge_kernel_transport_single_iff_hadamard_second_diff_transport
        hdim μ v u hv hu (by simpa [inner_eq_zero_symm] using huv)).2 htransportE
  have hstrictK :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|swapped_bridge_kernel μ v u s r| / (1 + r ^ 2))
            <
          (|swapped_bridge_kernel μ v u s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    exact
      (swapped_bridge_kernel_transport_strict_single_iff_hadamard_second_diff_transport
        hdim μ v u hv hu (by simpa [inner_eq_zero_symm] using huv)).2 hstrictE
  exact
    hadamard_bridge_error_zero_all_of_transport_strict_single
      hdim μ u v hu hv huv htransportK hstrictK

lemma hadamard_bridge_error_zero_all_of_second_diff_transport_neq
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransportE :
      ∀ s r : ℝ, 0 < r → r < 1 →
        (|hadamard_bridge_error μ u v (s + r) +
            hadamard_bridge_error μ u v (s - r) -
            2 * hadamard_bridge_error μ u v s| / (1 + r ^ 2))
          ≤
        (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) +
            hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
            2 * hadamard_bridge_error μ u v s| /
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
  have hneqK :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|swapped_bridge_kernel μ v u s r| / (1 + r ^ 2))
            ≠
          (|swapped_bridge_kernel μ v u s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    exact
      (swapped_bridge_kernel_transport_neq_single_iff_hadamard_second_diff_neq
        hdim μ v u hv hu (by simpa [inner_eq_zero_symm] using huv)).2 hneqE
  have hstrictK :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|swapped_bridge_kernel μ v u s r| / (1 + r ^ 2))
            <
          (|swapped_bridge_kernel μ v u s ((1 - r) / (1 + r))| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    exact
      swapped_bridge_kernel_transport_strict_single_of_neq_witness
        (μ := μ) (u := v) (v := u) hneqK
  have hstrictE :
      ∀ s : ℝ, (∃ t : ℝ, swapped_bridge_kernel μ v u s t ≠ 0) →
        ∃ r : ℝ, 0 < r ∧ r < 1 ∧
          (|hadamard_bridge_error μ u v (s + r) +
              hadamard_bridge_error μ u v (s - r) -
              2 * hadamard_bridge_error μ u v s| / (1 + r ^ 2))
            <
          (|hadamard_bridge_error μ u v (s + ((1 - r) / (1 + r))) +
              hadamard_bridge_error μ u v (s - ((1 - r) / (1 + r))) -
              2 * hadamard_bridge_error μ u v s| /
            (1 + ((1 - r) / (1 + r)) ^ 2)) := by
    exact
      (swapped_bridge_kernel_transport_strict_single_iff_hadamard_second_diff_transport
        hdim μ v u hv hu (by simpa [inner_eq_zero_symm] using huv)).1 hstrictK
  exact
    hadamard_bridge_error_zero_all_of_second_diff_transport_strict
      hdim μ u v hu hv huv htransportE hstrictE

lemma hadamard_bridge_error_second_diff_growth_bound_two_vars
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ,
      |hadamard_bridge_error μ u v (s + t) +
          hadamard_bridge_error μ u v (s - t) -
          2 * hadamard_bridge_error μ u v s|
        ≤ C * (1 + s ^ 2 + t ^ 2) := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  rcases swapped_bridge_kernel_growth_bound_two_vars hdim μ v u hv hu hvu with
    ⟨C0, hC0nn, hC0⟩
  refine ⟨C0, hC0nn, ?_⟩
  intro s t
  have hK :=
    hC0 s t
  have hrepr :
      swapped_bridge_kernel μ v u s t
        =
      2 * (hadamard_bridge_error μ u v (s + t) +
            hadamard_bridge_error μ u v (s - t) -
            2 * hadamard_bridge_error μ u v s) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      swapped_bridge_kernel_eq_two_hadamard_bridge_error_second_diff
        hdim μ v u hv hu hvu s t
  have hmain :
      2 *
          |hadamard_bridge_error μ u v (s + t) +
              hadamard_bridge_error μ u v (s - t) -
              2 * hadamard_bridge_error μ u v s|
        ≤ C0 * (1 + s ^ 2 + t ^ 2) := by
    calc
      2 *
          |hadamard_bridge_error μ u v (s + t) +
              hadamard_bridge_error μ u v (s - t) -
              2 * hadamard_bridge_error μ u v s|
          =
        |swapped_bridge_kernel μ v u s t| := by
          rw [hrepr, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ C0 * (1 + s ^ 2 + t ^ 2) := hK
  have habs_nn :
      0 ≤
        |hadamard_bridge_error μ u v (s + t) +
            hadamard_bridge_error μ u v (s - t) -
            2 * hadamard_bridge_error μ u v s| := by
    exact abs_nonneg _
  nlinarith [hmain, habs_nn]

lemma hadamard_bridge_error_second_diff_even_t
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    hadamard_bridge_error_second_diff μ u v s (-t) =
      hadamard_bridge_error_second_diff μ u v s t := by
  unfold hadamard_bridge_error_second_diff
  ring_nf

lemma hadamard_bridge_error_second_diff_zero_t0
    (μ : FrameFunction H) (u v : H) (s : ℝ) :
    hadamard_bridge_error_second_diff μ u v s 0 = 0 := by
  unfold hadamard_bridge_error_second_diff
  ring_nf

lemma hadamard_bridge_error_second_diff_swap_params_explicit
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    hadamard_bridge_error_second_diff μ u v s t -
        hadamard_bridge_error_second_diff μ u v t s
      =
    hadamard_bridge_error μ u v (s - t) -
        hadamard_bridge_error μ u v (t - s) +
      2 * (hadamard_bridge_error μ u v t - hadamard_bridge_error μ u v s) := by
  unfold hadamard_bridge_error_second_diff
  ring_nf

lemma hadamard_bridge_error_second_diff_swap_params_via_sub_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    hadamard_bridge_error_second_diff μ u v s t -
        hadamard_bridge_error_second_diff μ u v t s
      =
    2 * (hadamard_residual_one μ u v (s - t) +
      hadamard_bridge_error μ u v t - hadamard_bridge_error μ u v s) := by
  have h0 :=
    hadamard_bridge_error_second_diff_swap_params_explicit
      (μ := μ) (u := u) (v := v) (s := s) (t := t)
  have hsub :
      hadamard_bridge_error μ u v (s - t) -
          hadamard_bridge_error μ u v (t - s)
        =
      2 * hadamard_residual_one μ u v (s - t) := by
    have h :=
      hadamard_bridge_error_sub_neg hdim μ u v hu hv huv (s - t)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  linarith [h0, hsub]

lemma hadamard_bridge_error_second_diff_s0_eq_neg_local_defect_g
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    hadamard_bridge_error_second_diff μ u v 0 t = -local_defect_g μ u v t := by
  unfold hadamard_bridge_error_second_diff
  have hsum := hadamard_bridge_error_add_neg hdim μ u v hu hv huv t
  have hE0 : hadamard_bridge_error μ u v 0 = 0 := hadamard_bridge_error_zero μ u v
  simpa [hE0] using hsum

lemma hadamard_bridge_error_second_diff_s0_normalized_abs_eq_local_defect_g_normalized_abs
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    |hadamard_bridge_error_second_diff μ u v 0 t| / (1 + t ^ 2) =
      |local_defect_g μ u v t| / (1 + t ^ 2) := by
  rw [hadamard_bridge_error_second_diff_s0_eq_neg_local_defect_g hdim μ u v hu hv huv t]
  rw [abs_neg]

lemma hadamard_bridge_error_second_diff_decompose_from_s0
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    hadamard_bridge_error_second_diff μ u v s t
      =
    hadamard_bridge_error_second_diff μ u v 0 t +
      (hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t) +
      (hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)) -
      2 * (hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0) := by
  unfold hadamard_bridge_error_second_diff
  ring_nf

lemma hadamard_bridge_error_second_diff_normalized_from_s0_bound
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    |hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2)
      ≤
    |hadamard_bridge_error_second_diff μ u v 0 t| / (1 + t ^ 2) +
      (|hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t| +
        |hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)| +
        2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + t ^ 2) := by
  set A : ℝ := hadamard_bridge_error_second_diff μ u v 0 t
  set B : ℝ := hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t
  set C : ℝ := hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)
  set D : ℝ := hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0
  have hdecomp :
      hadamard_bridge_error_second_diff μ u v s t = A + B + C - 2 * D := by
    simpa [A, B, C, D] using
      hadamard_bridge_error_second_diff_decompose_from_s0 μ u v s t
  have habs :
      |hadamard_bridge_error_second_diff μ u v s t|
        ≤ |A| + |B| + |C| + 2 * |D| := by
    rw [hdecomp]
    have h1 : |A + B + C - 2 * D| ≤ |A + B + C| + |2 * D| := by
      exact abs_sub (A + B + C) (2 * D)
    have h2 : |A + B + C| ≤ |A| + |B + C| := by
      simpa [add_assoc] using abs_add_le A (B + C)
    have h3 : |B + C| ≤ |B| + |C| := abs_add_le B C
    have h4 : |2 * D| = 2 * |D| := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith [h1, h2, h3, h4]
  have hden_pos : 0 < (1 + t ^ 2 : ℝ) := by
    nlinarith [sq_nonneg t]
  have hdiv :
      |hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2)
        ≤
      (|A| + |B| + |C| + 2 * |D|) / (1 + t ^ 2) := by
    exact div_le_div_of_nonneg_right habs (le_of_lt hden_pos)
  calc
    |hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2)
        ≤
      (|A| + |B| + |C| + 2 * |D|) / (1 + t ^ 2) := hdiv
    _ = |A| / (1 + t ^ 2) +
        (|B| + |C| + 2 * |D|) / (1 + t ^ 2) := by ring
    _ = |hadamard_bridge_error_second_diff μ u v 0 t| / (1 + t ^ 2) +
        (|hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t| +
          |hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + t ^ 2) := by
          simp [A, B, C, D]

lemma hadamard_bridge_error_second_diff_normalized_from_local_defect_g_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    |hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2)
      ≤
    |local_defect_g μ u v t| / (1 + t ^ 2) +
      (|hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t| +
        |hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)| +
        2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + t ^ 2) := by
  have hbase :=
    hadamard_bridge_error_second_diff_normalized_from_s0_bound μ u v s t
  have hs0 :
      |hadamard_bridge_error_second_diff μ u v 0 t| / (1 + t ^ 2) =
        |local_defect_g μ u v t| / (1 + t ^ 2) :=
    hadamard_bridge_error_second_diff_s0_normalized_abs_eq_local_defect_g_normalized_abs
      hdim μ u v hu hv huv t
  rw [hs0] at hbase
  exact hbase

lemma hadamard_bridge_error_second_diff_normalized_s0_from_general_bound
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    |hadamard_bridge_error_second_diff μ u v 0 t| / (1 + t ^ 2)
      ≤
    |hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2) +
      (|hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t| +
        |hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)| +
        2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + t ^ 2) := by
  set A0 : ℝ := hadamard_bridge_error_second_diff μ u v 0 t
  set As : ℝ := hadamard_bridge_error_second_diff μ u v s t
  set B : ℝ := hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t
  set C : ℝ := hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)
  set D : ℝ := hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0
  have hdecomp :
      As = A0 + B + C - 2 * D := by
    simpa [A0, As, B, C, D] using
      hadamard_bridge_error_second_diff_decompose_from_s0 μ u v s t
  have hA0 :
      A0 = As - B - C + 2 * D := by
    linarith [hdecomp]
  have h1 : |As - B| ≤ |As| + |B| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le As (-B)
  have h2 : |-C + 2 * D| ≤ |C| + 2 * |D| := by
    calc
      |-C + 2 * D| = |(-C) + (2 * D)| := by ring_nf
      _ ≤ |(-C)| + |2 * D| := abs_add_le _ _
      _ = |C| + 2 * |D| := by
            rw [abs_neg, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have h3 : |As - B - C + 2 * D| ≤ |As - B| + |-C + 2 * D| := by
    have hrew : As - B - C + 2 * D = (As - B) + (-C + 2 * D) := by ring
    rw [hrew]
    exact abs_add_le _ _
  have habs : |A0| ≤ |As| + |B| + |C| + 2 * |D| := by
    have htmp : |A0| = |As - B - C + 2 * D| := by rw [hA0]
    rw [htmp]
    linarith [h1, h2, h3]
  have hden_pos : 0 < (1 + t ^ 2 : ℝ) := by
    nlinarith [sq_nonneg t]
  have hdiv :
      |A0| / (1 + t ^ 2)
        ≤ (|As| + |B| + |C| + 2 * |D|) / (1 + t ^ 2) := by
    exact (div_le_div_iff_of_pos_right hden_pos).2 habs
  calc
    |hadamard_bridge_error_second_diff μ u v 0 t| / (1 + t ^ 2)
        = |A0| / (1 + t ^ 2) := by simp [A0]
    _ ≤ (|As| + |B| + |C| + 2 * |D|) / (1 + t ^ 2) := hdiv
    _ = |hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2) +
        (|hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t| +
          |hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + t ^ 2) := by
          simp [As, B, C, D]
          ring

lemma local_defect_g_normalized_abs_from_hadamard_second_diff_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    |local_defect_g μ u v t| / (1 + t ^ 2)
      ≤
    |hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2) +
      (|hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t| +
        |hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)| +
        2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + t ^ 2) := by
  have hs0 :
      |local_defect_g μ u v t| / (1 + t ^ 2)
        =
      |hadamard_bridge_error_second_diff μ u v 0 t| / (1 + t ^ 2) := by
    have hs0_eq :
        hadamard_bridge_error_second_diff μ u v 0 t = -local_defect_g μ u v t :=
      hadamard_bridge_error_second_diff_s0_eq_neg_local_defect_g hdim μ u v hu hv huv t
    calc
      |local_defect_g μ u v t| / (1 + t ^ 2)
          = |-local_defect_g μ u v t| / (1 + t ^ 2) := by simp [abs_neg]
      _ = |hadamard_bridge_error_second_diff μ u v 0 t| / (1 + t ^ 2) := by
            simpa [hs0_eq]
  have hbase :=
    hadamard_bridge_error_second_diff_normalized_s0_from_general_bound μ u v s t
  simpa [hs0] using hbase

lemma hadamard_bridge_error_shift_error_bundle_uniform_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ,
      (|hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t| +
        |hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)| +
        2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + t ^ 2)
        ≤ C * (1 + s ^ 2) := by
  set E : ℝ → ℝ := hadamard_bridge_error μ u v
  rcases hadamard_bridge_error_growth_bound hdim μ u v hu hv huv with
    ⟨C0, hC0nn, hC0⟩
  refine ⟨8 * C0, by nlinarith [hC0nn], ?_⟩
  intro s t
  have hterm1 :
      |E (s + t) - E t| ≤ C0 * (2 + (s + t) ^ 2 + t ^ 2) := by
    have hsub : |E (s + t) - E t| ≤ |E (s + t)| + |E t| := by
      simpa [sub_eq_add_neg] using abs_add_le (E (s + t)) (-(E t))
    have hsum :
        |E (s + t)| + |E t| ≤ C0 * (1 + (s + t) ^ 2) + C0 * (1 + t ^ 2) :=
      add_le_add (hC0 (s + t)) (hC0 t)
    have hcombine :
        C0 * (1 + (s + t) ^ 2) + C0 * (1 + t ^ 2) =
          C0 * (2 + (s + t) ^ 2 + t ^ 2) := by ring
    exact le_trans hsub (by simpa [hcombine] using hsum)
  have hterm2 :
      |E (s - t) - E (-t)| ≤ C0 * (2 + (s - t) ^ 2 + t ^ 2) := by
    have hsub : |E (s - t) - E (-t)| ≤ |E (s - t)| + |E (-t)| := by
      simpa [sub_eq_add_neg] using abs_add_le (E (s - t)) (-(E (-t)))
    have hsum :
        |E (s - t)| + |E (-t)| ≤ C0 * (1 + (s - t) ^ 2) + C0 * (1 + (-t) ^ 2) :=
      add_le_add (hC0 (s - t)) (hC0 (-t))
    have hcombine :
        C0 * (1 + (s - t) ^ 2) + C0 * (1 + (-t) ^ 2) =
          C0 * (2 + (s - t) ^ 2 + t ^ 2) := by
      ring_nf
    have hsum' : |E (s - t)| + |E (-t)| ≤ C0 * (2 + (s - t) ^ 2 + t ^ 2) := by
      calc
        |E (s - t)| + |E (-t)| ≤ C0 * (1 + (s - t) ^ 2) + C0 * (1 + (-t) ^ 2) := hsum
        _ = C0 * (2 + (s - t) ^ 2 + t ^ 2) := hcombine
    exact le_trans hsub hsum'
  have hterm3 :
      2 * |E s - E 0| ≤ C0 * (4 + 2 * s ^ 2) := by
    have hsub : |E s - E 0| ≤ |E s| + |E 0| := by
      simpa [sub_eq_add_neg] using abs_add_le (E s) (-(E 0))
    have hsum : |E s| + |E 0| ≤ C0 * (1 + s ^ 2) + C0 * (1 + 0 ^ 2) :=
      add_le_add (hC0 s) (hC0 0)
    have hsum' : |E s - E 0| ≤ C0 * (2 + s ^ 2) := by
      have hcombine :
          C0 * (1 + s ^ 2) + C0 * (1 + 0 ^ 2) = C0 * (2 + s ^ 2) := by
        ring
      have hsum'' : |E s| + |E 0| ≤ C0 * (2 + s ^ 2) := by
        calc
          |E s| + |E 0| ≤ C0 * (1 + s ^ 2) + C0 * (1 + 0 ^ 2) := hsum
          _ = C0 * (2 + s ^ 2) := hcombine
      exact le_trans hsub hsum''
    nlinarith [hsum', hC0nn]
  set N : ℝ :=
    |E (s + t) - E t| +
      |E (s - t) - E (-t)| +
      2 * |E s - E 0|
  have hN :
      N ≤ C0 * (8 + 4 * s ^ 2 + 4 * t ^ 2) := by
    have hsum_terms :
        |E (s + t) - E t| + |E (s - t) - E (-t)| + 2 * |E s - E 0|
          ≤
        C0 * (2 + (s + t) ^ 2 + t ^ 2) +
          C0 * (2 + (s - t) ^ 2 + t ^ 2) +
          C0 * (4 + 2 * s ^ 2) := by
      nlinarith [hterm1, hterm2, hterm3]
    have hpoly :
        C0 * (2 + (s + t) ^ 2 + t ^ 2) +
            C0 * (2 + (s - t) ^ 2 + t ^ 2) +
            C0 * (4 + 2 * s ^ 2)
          =
        C0 * (8 + 4 * s ^ 2 + 4 * t ^ 2) := by ring
    dsimp [N]
    calc
      |E (s + t) - E t| + |E (s - t) - E (-t)| + 2 * |E s - E 0|
          ≤
        C0 * (2 + (s + t) ^ 2 + t ^ 2) +
          C0 * (2 + (s - t) ^ 2 + t ^ 2) +
          C0 * (4 + 2 * s ^ 2) := hsum_terms
      _ = C0 * (8 + 4 * s ^ 2 + 4 * t ^ 2) := hpoly
  have hfac : 8 + 4 * s ^ 2 + 4 * t ^ 2 ≤ 8 * (1 + s ^ 2) * (1 + t ^ 2) := by
    nlinarith [sq_nonneg s, sq_nonneg t]
  have hN' :
      N ≤ C0 * (8 * (1 + s ^ 2) * (1 + t ^ 2)) := by
    exact le_trans hN (mul_le_mul_of_nonneg_left hfac hC0nn)
  have hden_pos : 0 < (1 + t ^ 2 : ℝ) := by positivity
  have hdiv :
      N / (1 + t ^ 2) ≤ (C0 * (8 * (1 + s ^ 2) * (1 + t ^ 2))) / (1 + t ^ 2) := by
    exact (div_le_div_iff_of_pos_right hden_pos).2 hN'
  have hcancel :
      (C0 * (8 * (1 + s ^ 2) * (1 + t ^ 2))) / (1 + t ^ 2) = (8 * C0) * (1 + s ^ 2) := by
    field_simp
  calc
    (|hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t| +
      |hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)| +
      2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + t ^ 2)
        = N / (1 + t ^ 2) := by rfl
    _ ≤ (C0 * (8 * (1 + s ^ 2) * (1 + t ^ 2))) / (1 + t ^ 2) := hdiv
    _ = (8 * C0) * (1 + s ^ 2) := hcancel

lemma hadamard_bridge_error_shift_error_double_bundle_uniform_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s r : ℝ,
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
  rcases hadamard_bridge_error_shift_error_bundle_uniform_bound hdim μ u v hu hv huv with
    ⟨C0, hC0nn, hC0⟩
  refine ⟨2 * C0, by nlinarith [hC0nn], ?_⟩
  intro s r
  have hr := hC0 s r
  have hφ := hC0 s ((1 - r) / (1 + r))
  linarith [hr, hφ]

lemma hadamard_bridge_error_second_diff_transport_with_shift_error
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (htransport_g :
      ∀ r : ℝ, 0 < r → r < 1 →
        (|local_defect_g μ u v r| / (1 + r ^ 2))
          ≤
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))) :
    ∀ s r : ℝ, 0 < r → r < 1 →
      (|hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2))
        ≤
      (|hadamard_bridge_error_second_diff μ u v s ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2))
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
        (1 + ((1 - r) / (1 + r)) ^ 2) := by
  intro s r hr0 hr1
  set φ : ℝ := (1 - r) / (1 + r)
  have hsr :
      |hadamard_bridge_error_second_diff μ u v s r| / (1 + r ^ 2)
        ≤
      |local_defect_g μ u v r| / (1 + r ^ 2) +
        (|hadamard_bridge_error μ u v (s + r) - hadamard_bridge_error μ u v r| +
          |hadamard_bridge_error μ u v (s - r) - hadamard_bridge_error μ u v (-r)| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + r ^ 2) :=
    hadamard_bridge_error_second_diff_normalized_from_local_defect_g_bound
      hdim μ u v hu hv huv s r
  have htr :
      |local_defect_g μ u v r| / (1 + r ^ 2)
        ≤
      |local_defect_g μ u v φ| / (1 + φ ^ 2) := by
    simpa [φ] using htransport_g r hr0 hr1
  have hφ :
      |local_defect_g μ u v φ| / (1 + φ ^ 2)
        ≤
      |hadamard_bridge_error_second_diff μ u v s φ| / (1 + φ ^ 2) +
        (|hadamard_bridge_error μ u v (s + φ) - hadamard_bridge_error μ u v φ| +
          |hadamard_bridge_error μ u v (s - φ) - hadamard_bridge_error μ u v (-φ)| +
          2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + φ ^ 2) :=
    local_defect_g_normalized_abs_from_hadamard_second_diff_bound
      hdim μ u v hu hv huv s φ
  linarith [hsr, htr, hφ]

lemma hadamard_bridge_error_second_diff_local_defect_g_normalized_gap_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    |(|hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2) -
        |local_defect_g μ u v t| / (1 + t ^ 2))|
      ≤
    (|hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t| +
      |hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)| +
      2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + t ^ 2) := by
  set A : ℝ := |hadamard_bridge_error_second_diff μ u v s t| / (1 + t ^ 2)
  set G : ℝ := |local_defect_g μ u v t| / (1 + t ^ 2)
  set E : ℝ :=
    (|hadamard_bridge_error μ u v (s + t) - hadamard_bridge_error μ u v t| +
      |hadamard_bridge_error μ u v (s - t) - hadamard_bridge_error μ u v (-t)| +
      2 * |hadamard_bridge_error μ u v s - hadamard_bridge_error μ u v 0|) / (1 + t ^ 2)
  have hA : A ≤ G + E := by
    simpa [A, G, E] using
      hadamard_bridge_error_second_diff_normalized_from_local_defect_g_bound
        hdim μ u v hu hv huv s t
  have hG : G ≤ A + E := by
    simpa [A, G, E] using
      local_defect_g_normalized_abs_from_hadamard_second_diff_bound
        hdim μ u v hu hv huv s t
  have hupper : A - G ≤ E := by
    linarith [hA]
  have hlower : -E ≤ A - G := by
    linarith [hG]
  have habs : |A - G| ≤ E := by
    exact abs_le.mpr ⟨hlower, hupper⟩
  simpa [A, G, E]
    using habs

def hadamard_bridge_error_shift_oscillation_pair
    (μ : FrameFunction H) (u v : H) (s r : ℝ) : ℝ :=
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


end
