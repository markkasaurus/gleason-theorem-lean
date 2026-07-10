import Gleason.Continuity.Defect.Basic

noncomputable section

open GleasonBridge RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

lemma shifted_defect_kill_of_hyperbolic_relation
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = s ^ 2 - 1) :
    local_quad2DDefect μ (u + (c : ℂ) • w) v 1 s = 0 ∧
      local_quad2DDefect μ (u - (c : ℂ) • w) v 1 s = 0 := by
  have hwv : inner (𝕜 := ℂ) w v = 0 := inner_eq_zero_symm.1 hvw
  set xplus : H := u + (c : ℂ) • w
  have hsq_plus : ‖xplus‖ ^ 2 = s ^ 2 := by
    calc
      ‖xplus‖ ^ 2 = 1 + c ^ 2 := by
        simpa [xplus] using norm_sq_add_smul_of_orthonormal u w hu hw huw c
      _ = s ^ 2 := by nlinarith [hc]
  have hxplus_ne : xplus ≠ 0 := by
    have hs_pos : 0 < s ^ 2 := by nlinarith [hc, sq_nonneg c]
    intro hx0
    have : ‖xplus‖ ^ 2 = 0 := by simp [hx0]
    linarith [hsq_plus, hs_pos]
  have hxplusv : inner (𝕜 := ℂ) xplus v = 0 := by
    simp [xplus, huv, hwv]
  have hplus_g0 : local_defect_g μ xplus v s = 0 :=
    local_defect_g_zero_of_orthogonal_norm_sq hdim μ xplus v s hxplus_ne hv hxplusv hsq_plus
  have hplus : local_quad2DDefect μ (u + (c : ℂ) • w) v 1 s = 0 := by
    simpa [xplus, local_defect_g] using hplus_g0

  set xminus : H := u - (c : ℂ) • w
  have hsq_minus : ‖xminus‖ ^ 2 = s ^ 2 := by
    calc
      ‖xminus‖ ^ 2 = 1 + c ^ 2 := by
        simpa [xminus] using norm_sq_sub_smul_of_orthonormal u w hu hw huw c
      _ = s ^ 2 := by nlinarith [hc]
  have hxminus_ne : xminus ≠ 0 := by
    have hs_pos : 0 < s ^ 2 := by nlinarith [hc, sq_nonneg c]
    intro hx0
    have : ‖xminus‖ ^ 2 = 0 := by simp [hx0]
    linarith [hsq_minus, hs_pos]
  have hxminusv : inner (𝕜 := ℂ) xminus v = 0 := by
    simp [xminus, huv, hwv]
  have hminus_g0 : local_defect_g μ xminus v s = 0 :=
    local_defect_g_zero_of_orthogonal_norm_sq hdim μ xminus v s hxminus_ne hv hxminusv hsq_minus
  have hminus : local_quad2DDefect μ (u - (c : ℂ) • w) v 1 s = 0 := by
    simpa [xminus, local_defect_g] using hminus_g0
  exact ⟨hplus, hminus⟩

lemma hyperbolic_transfer_g
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = s ^ 2 - 1) :
    2 * local_defect_g μ u v s +
      local_quad2DDefect μ (u + (s : ℂ) • v) w 1 c +
      local_quad2DDefect μ (u - (s : ℂ) • v) w 1 c
      =
    2 * local_defect_g μ u w c := by
  have hexch := GleasonBridge.gleason_defect_algebraic_identity μ u v w 1 s c
  rcases shifted_defect_kill_of_hyperbolic_relation hdim μ u v w hu hv hw huv huw hvw s c hc
    with ⟨hkill_plus, hkill_minus⟩
  have hkill_plus' : local_quad2DDefect μ (u + (c : ℝ) • w) v 1 s = 0 := by
    change local_quad2DDefect μ (u + (c : ℂ) • w) v 1 s = 0
    exact hkill_plus
  have hkill_minus' : local_quad2DDefect μ (u - (c : ℝ) • w) v 1 s = 0 := by
    change local_quad2DDefect μ (u - (c : ℂ) • w) v 1 s = 0
    exact hkill_minus
  simpa [one_smul, local_defect_g, hkill_plus', hkill_minus'] using hexch

lemma hyperbolic_transfer_g'
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = s ^ 2 - 1) :
    2 * local_defect_g μ u v s =
      2 * local_defect_g μ u w c
        - local_quad2DDefect μ (u + (s : ℂ) • v) w 1 c
        - local_quad2DDefect μ (u - (s : ℂ) • v) w 1 c := by
  have h := hyperbolic_transfer_g hdim μ u v w hu hv hw huv huw hvw s c hc
  linarith

def local_defect_residual_mix
    (μ : FrameFunction H) (u a b : H) (s t : ℝ) : ℝ :=
  local_quad2DDefect μ (u + (s : ℝ) • a) b 1 t +
    local_quad2DDefect μ (u - (s : ℝ) • a) b 1 t -
    2 * local_quad2DDefect μ u b 1 t

lemma local_defect_residual_mix_swap
    (μ : FrameFunction H) (u a b : H) (s t : ℝ) :
    local_defect_residual_mix μ u a b s t =
      local_defect_residual_mix μ u b a t s := by
  have hexch := GleasonBridge.gleason_defect_algebraic_identity μ u a b 1 s t
  simp [one_smul] at hexch
  unfold local_defect_residual_mix
  linarith [hexch]

lemma local_defect_residual_mix_selfarg_symm
    (μ : FrameFunction H) (u a : H) (s t : ℝ) :
    local_defect_residual_mix μ u a a s t =
      local_defect_residual_mix μ u a a t s := by
  simpa using local_defect_residual_mix_swap μ u a a s t

lemma local_defect_residual_eq_mix_self
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    local_defect_residual μ u v s t =
      local_defect_residual_mix μ u v v s t := by
  have hpair := shifted_base_pair_sum_eq_residual μ u v s t
  have hpair' :
      local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t +
        local_quad2DDefect μ (u - (s : ℂ) • v) v 1 t
        = local_defect_residual μ u v s t + 2 * local_quad2DDefect μ u v 1 t := by
    simpa [local_defect_g] using hpair
  have hreal_plus :
      local_quad2DDefect μ (u + (s : ℝ) • v) v 1 t =
        local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t := by
    rfl
  have hreal_minus :
      local_quad2DDefect μ (u - (s : ℝ) • v) v 1 t =
        local_quad2DDefect μ (u - (s : ℂ) • v) v 1 t := by
    rfl
  unfold local_defect_residual_mix
  rw [hreal_plus, hreal_minus]
  linarith [hpair']

lemma local_defect_residual_mix_hyperbolic
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = s ^ 2 - 1) :
    local_defect_residual_mix μ u v w s c = -2 * local_defect_g μ u v s := by
  have h := hyperbolic_transfer_g hdim μ u v w hu hv hw huv huw hvw s c hc
  have hplus_cast :
      local_quad2DDefect μ (u + (s : ℂ) • v) w 1 c =
        local_quad2DDefect μ (u + (s : ℝ) • v) w 1 c := rfl
  have hminus_cast :
      local_quad2DDefect μ (u - (s : ℂ) • v) w 1 c =
        local_quad2DDefect μ (u - (s : ℝ) • v) w 1 c := rfl
  have hwg : local_defect_g μ u w c = local_quad2DDefect μ u w 1 c := rfl
  rw [hplus_cast, hminus_cast] at h
  unfold local_defect_residual_mix
  linarith [h, hwg]

lemma local_defect_residual_mix_cross_plane
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = 1 + s ^ 2) :
    local_defect_residual_mix μ u w v c s = -2 * local_defect_g μ u w c := by
  have h := cross_plane_transfer_g hdim μ u v w hu hv hw huv huw hvw s c hc
  have hpair :
      2 * local_quad2DDefect μ u v 1 s =
        2 * local_defect_g μ u w c +
          local_quad2DDefect μ (u + (c : ℂ) • w) v 1 s +
          local_quad2DDefect μ (u - (c : ℂ) • w) v 1 s := by
    simpa [local_defect_g] using h
  have hplus_cast :
      local_quad2DDefect μ (u + (c : ℂ) • w) v 1 s =
        local_quad2DDefect μ (u + (c : ℝ) • w) v 1 s := rfl
  have hminus_cast :
      local_quad2DDefect μ (u - (c : ℂ) • w) v 1 s =
        local_quad2DDefect μ (u - (c : ℝ) • w) v 1 s := rfl
  rw [hplus_cast, hminus_cast] at hpair
  unfold local_defect_residual_mix
  linarith [hpair]

lemma local_defect_residual_mix_hyperbolic_swapped
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = s ^ 2 - 1) :
    local_defect_residual_mix μ u w v c s = -2 * local_defect_g μ u v s := by
  have hswap := local_defect_residual_mix_swap μ u v w s c
  have hleft := local_defect_residual_mix_hyperbolic hdim μ u v w hu hv hw huv huw hvw s c hc
  linarith [hswap, hleft]

lemma local_defect_residual_mix_cross_plane_swapped
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = 1 + s ^ 2) :
    local_defect_residual_mix μ u v w s c = -2 * local_defect_g μ u w c := by
  have hswap := local_defect_residual_mix_swap μ u v w s c
  have hright := local_defect_residual_mix_cross_plane hdim μ u v w hu hv hw huv huw hvw s c hc
  linarith [hswap, hright]

lemma local_quad2DDefect_swap_vectors
    (μ : FrameFunction H) (u v : H) (a b : ℝ) :
    local_quad2DDefect μ v u b a = local_quad2DDefect μ u v a b := by
  have hneg :
      frame_quadratic (H := H) μ (((b : ℂ) • v - (a : ℂ) • u)) =
        frame_quadratic (H := H) μ (((a : ℂ) • u - (b : ℂ) • v)) := by
    have hqneg := frame_quadratic_neg (H := H) μ (((a : ℂ) • u - (b : ℂ) • v))
    have hsub : (b : ℂ) • v - (a : ℂ) • u = -(((a : ℂ) • u - (b : ℂ) • v) ) := by
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    simpa [hsub] using hqneg
  unfold local_quad2DDefect local_quad2DExpr
  rw [add_comm ((b : ℂ) • v) ((a : ℂ) • u), hneg]
  ring

lemma local_quad2DDefect_vu_s1_eq_g
    (μ : FrameFunction H) (u v : H) (s : ℝ) :
    local_quad2DDefect μ v u s 1 = local_defect_g μ u v s := by
  simpa [local_defect_g] using local_quad2DDefect_swap_vectors μ u v 1 s

lemma local_defect_g_swap_of_orthonormal
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s : ℝ) :
    local_defect_g μ v u s = - local_defect_g μ u v s := by
  have hswap :=
    GleasonBridge.local_quad2DDefect_swap_of_orthonormal (H := H) hdim μ u v hu hv huv 1 s
  -- D_{u,v}(1,s) = -D_{u,v}(s,1), and D_{v,u}(s,1) = D_{u,v}(1,s)
  have hvu_s1 : local_quad2DDefect μ v u s 1 = local_defect_g μ u v s :=
    local_quad2DDefect_vu_s1_eq_g μ u v s
  have hvu_1s : local_defect_g μ v u s = local_quad2DDefect μ v u 1 s := rfl
  have huv_s1 : local_quad2DDefect μ u v s 1 = local_defect_g μ v u s := by
    simpa [local_defect_g] using local_quad2DDefect_swap_vectors μ v u 1 s
  -- Rewrite everything into g-language.
  have hswap' : local_defect_g μ u v s = - local_defect_g μ v u s := by
    simpa [local_defect_g, huv_s1] using hswap
  linarith [hswap']

lemma local_defect_g_swap_add_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s : ℝ) :
    local_defect_g μ u v s + local_defect_g μ v u s = 0 := by
  have hswap := local_defect_g_swap_of_orthonormal hdim μ u v hu hv huv s
  linarith [hswap]

lemma local_defect_g_lower_bound_infimum
    (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s : ℝ) :
    - (2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
      2 * s ^ 2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)))
      ≤ local_defect_g μ u v s := by
  have h_lb_plus :
      sInf (Q_sphere_set μ) * ‖u + (s : ℂ) • v‖ ^ 2 ≤ frame_quadratic μ (u + (s : ℂ) • v) :=
    frame_quadratic_ge_inf_mul_norm_sq μ (u + (s : ℂ) • v)
  have h_lb_minus :
      sInf (Q_sphere_set μ) * ‖u - (s : ℂ) • v‖ ^ 2 ≤ frame_quadratic μ (u - (s : ℂ) • v) :=
    frame_quadratic_ge_inf_mul_norm_sq μ (u - (s : ℂ) • v)
  have h_norm_plus : ‖u + (s : ℂ) • v‖ ^ 2 = 1 + s ^ 2 :=
    norm_sq_add_smul_of_orthonormal u v hu hv huv s
  have h_norm_minus : ‖u - (s : ℂ) • v‖ ^ 2 = 1 + s ^ 2 :=
    norm_sq_sub_smul_of_orthonormal u v hu hv huv s
  rw [h_norm_plus] at h_lb_plus
  rw [h_norm_minus] at h_lb_minus
  unfold local_defect_g local_quad2DDefect local_quad2DExpr
  simp only [Complex.ofReal_one, one_smul, one_pow, mul_one]
  linarith [h_lb_plus, h_lb_minus]

lemma local_defect_g_upper_bound_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s : ℝ) :
    local_defect_g μ u v s ≤
      2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) +
      2 * s ^ 2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have h_swap : local_defect_g μ u v s = - local_defect_g μ v u s := by
    linarith [local_defect_g_swap_of_orthonormal hdim μ u v hu hv huv s]
  have h_lb :
      - (2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) +
        2 * s ^ 2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)))
        ≤ local_defect_g μ v u s :=
    local_defect_g_lower_bound_infimum μ v u hv hu hvu s
  calc
    local_defect_g μ u v s = - local_defect_g μ v u s := h_swap
    _ ≤ 2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) +
          2 * s ^ 2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) := by
            linarith [h_lb]

lemma local_defect_g_abs_bound_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s : ℝ) :
    |local_defect_g μ u v s| ≤
      2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
      2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) +
      2 * s ^ 2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
      2 * s ^ 2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) := by
  have h_lb := local_defect_g_lower_bound_infimum μ u v hu hv huv s
  have h_ub := local_defect_g_upper_bound_infimum hdim μ u v hu hv huv s
  have huM : 0 ≤ frame_quadratic μ u - sInf (Q_sphere_set μ) :=
    sub_nonneg.mpr (Q_sphere_inf_le μ u hu)
  have hvM : 0 ≤ frame_quadratic μ v - sInf (Q_sphere_set μ) :=
    sub_nonneg.mpr (Q_sphere_inf_le μ v hv)
  have hs2_nn : 0 ≤ s ^ 2 := sq_nonneg s
  have h1 : 0 ≤ 2 * s ^ 2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hs2_nn) huM
  have h2 : 0 ≤ 2 * s ^ 2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) :=
    mul_nonneg (mul_nonneg (by norm_num) hs2_nn) hvM
  rw [abs_le]
  constructor
  · linarith [h_lb, huM, hvM, h1, h2]
  · linarith [h_ub, huM, hvM, h1, h2]

lemma local_defect_g_eq_zero_of_infimum_pair
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (huM : frame_quadratic μ u = sInf (Q_sphere_set μ))
    (hvM : frame_quadratic μ v = sInf (Q_sphere_set μ))
    (s : ℝ) :
    local_defect_g μ u v s = 0 := by
  have habs :
      |local_defect_g μ u v s| ≤
        2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
          2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) +
          2 * s ^ 2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
          2 * s ^ 2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) := by
    simpa using local_defect_g_abs_bound_infimum hdim μ u v hu hv huv s
  have hrhs0 :
      2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
          2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) +
          2 * s ^ 2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
          2 * s ^ 2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) = 0 := by
    rw [huM, hvM]
    ring
  have habs0 : |local_defect_g μ u v s| ≤ 0 := by
    linarith [habs, hrhs0]
  exact abs_eq_zero.mp (le_antisymm habs0 (abs_nonneg _))

lemma local_defect_g_normalized_abs_bound_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s : ℝ) :
    |local_defect_g μ u v s| / (1 + s ^ 2)
      ≤
    2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
      2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) := by
  set K : ℝ :=
    2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
      2 * (frame_quadratic μ v - sInf (Q_sphere_set μ))
  have habs :
      |local_defect_g μ u v s|
        ≤
      2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
        2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) +
        2 * s ^ 2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
        2 * s ^ 2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) :=
    local_defect_g_abs_bound_infimum hdim μ u v hu hv huv s
  have hnum : |local_defect_g μ u v s| ≤ K * (1 + s ^ 2) := by
    dsimp [K]
    nlinarith [habs]
  have hden_pos : 0 < (1 + s ^ 2 : ℝ) := by positivity
  exact (div_le_iff₀ hden_pos).2 (by simpa [K, mul_comm, mul_left_comm, mul_assoc] using hnum)

lemma local_defect_g_normalized_gap_bound_infimum_pre
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    |(|local_defect_g μ u v r| / (1 + r ^ 2)) -
      (|local_defect_g μ u v ((1 - r) / (1 + r))| /
        (1 + ((1 - r) / (1 + r)) ^ 2))|
      ≤
    4 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
      4 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) := by
  set A : ℝ := |local_defect_g μ u v r| / (1 + r ^ 2)
  set B : ℝ := |local_defect_g μ u v ((1 - r) / (1 + r))| / (1 + ((1 - r) / (1 + r)) ^ 2)
  set K : ℝ :=
    2 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
      2 * (frame_quadratic μ v - sInf (Q_sphere_set μ))
  have hA : A ≤ K := by
    simpa [A, K] using local_defect_g_normalized_abs_bound_infimum hdim μ u v hu hv huv r
  have hB : B ≤ K := by
    simpa [B, K] using
      local_defect_g_normalized_abs_bound_infimum hdim μ u v hu hv huv ((1 - r) / (1 + r))
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    refine div_nonneg (abs_nonneg _) ?_
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    refine div_nonneg (abs_nonneg _) ?_
    positivity
  have htri : |A - B| ≤ |A| + |B| := by
    calc
      |A - B| = |A + (-B)| := by ring_nf
      _ ≤ |A| + |-B| := abs_add_le A (-B)
      _ = |A| + |B| := by simp
  have hgap : |A - B| ≤ 2 * K := by
    calc
      |A - B| ≤ |A| + |B| := htri
      _ = A + B := by simp [abs_of_nonneg hA_nonneg, abs_of_nonneg hB_nonneg]
      _ ≤ K + K := add_le_add hA hB
      _ = 2 * K := by ring
  calc
    |(|local_defect_g μ u v r| / (1 + r ^ 2) -
        (|local_defect_g μ u v ((1 - r) / (1 + r))| /
          (1 + ((1 - r) / (1 + r)) ^ 2)))| = |A - B| := by
          simp [A, B]
    _ ≤ 2 * K := hgap
    _ =
      4 * (frame_quadratic μ u - sInf (Q_sphere_set μ)) +
        4 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) := by
          dsimp [K]
          ring

lemma local_quad2DDefect_self_zero
    (μ : FrameFunction H) (u : H) (a b : ℝ) :
    local_quad2DDefect μ u u a b = 0 := by
  unfold local_quad2DDefect local_quad2DExpr
  have hplus_sm : ((a : ℂ) • u + (b : ℂ) • u) = (((a + b : ℝ) : ℂ) • u) := by
    simp [add_smul]
  have hminus_sm : ((a : ℂ) • u - (b : ℂ) • u) = (((a - b : ℝ) : ℂ) • u) := by
    simp [sub_eq_add_neg, add_smul]
  rw [hplus_sm, hminus_sm]
  have hplus := frame_quadratic_sq_hom (H := H) μ (((a + b : ℝ) : ℂ)) u
  have hminus := frame_quadratic_sq_hom (H := H) μ (((a - b : ℝ) : ℂ)) u
  rw [hplus, hminus]
  have hnorm_plus : ‖(((a + b : ℝ) : ℂ))‖ ^ 2 = (a + b) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hnorm_minus : ‖(((a - b : ℝ) : ℂ))‖ ^ 2 = (a - b) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnorm_plus, hnorm_minus]
  ring

lemma local_defect_g_self_zero
    (μ : FrameFunction H) (u : H) (s : ℝ) :
    local_defect_g μ u u s = 0 := by
  simpa [local_defect_g] using local_quad2DDefect_self_zero μ u 1 s

lemma local_defect_residual_self_pair_zero
    (μ : FrameFunction H) (u : H) (s t : ℝ) :
    local_defect_residual μ u u s t = 0 := by
  unfold local_defect_residual
  have h1 : local_quad2DDefect μ u u 1 (s + t) = 0 :=
    local_quad2DDefect_self_zero μ u 1 (s + t)
  have h2 : local_quad2DDefect μ u u 1 (s - t) = 0 :=
    local_quad2DDefect_self_zero μ u 1 (s - t)
  have h3 : local_quad2DDefect μ u u 1 s = 0 :=
    local_quad2DDefect_self_zero μ u 1 s
  have h4 : local_quad2DDefect μ u u 1 t = 0 :=
    local_quad2DDefect_self_zero μ u 1 t
  rw [h1, h2, h3, h4]
  ring

lemma local_defect_residual_swap_of_orthonormal
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    local_defect_residual μ v u s t = - local_defect_residual μ u v s t := by
  have hswap_r :
      ∀ r : ℝ, local_quad2DDefect μ v u 1 r = - local_quad2DDefect μ u v 1 r := by
    intro r
    have h := local_defect_g_swap_of_orthonormal hdim μ u v hu hv huv r
    simpa [local_defect_g] using h
  unfold local_defect_residual
  rw [hswap_r (s + t), hswap_r (s - t), hswap_r s, hswap_r t]
  ring

lemma local_defect_residual_swap_add_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    local_defect_residual μ u v s t + local_defect_residual μ v u s t = 0 := by
  have hswap := local_defect_residual_swap_of_orthonormal hdim μ u v hu hv huv s t
  linarith [hswap]

lemma local_defect_residual_mix_self_self_zero
    (μ : FrameFunction H) (u : H) (s t : ℝ) :
    local_defect_residual_mix μ u u u s t = 0 := by
  have hres : local_defect_residual μ u u s t = 0 :=
    local_defect_residual_self_pair_zero μ u s t
  simpa [local_defect_residual_eq_mix_self] using hres

lemma local_defect_residual_mix_self_swap_add_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    local_defect_residual_mix μ u v v s t +
      local_defect_residual_mix μ v u u s t = 0 := by
  have hres :=
    local_defect_residual_swap_add_eq_zero hdim μ u v hu hv huv s t
  simpa [local_defect_residual_eq_mix_self] using hres

lemma local_defect_residual_growth_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ,
      |local_defect_residual μ u v s t| ≤ C * (1 + s ^ 2 + t ^ 2) := by
  rcases GleasonBridge.local_defect_g_growth_bound μ u v hu hv huv with ⟨Cg, hCg⟩
  have hCg_nn : 0 ≤ Cg := by
    have h0 := hCg 0
    have hg0 : local_defect_g μ u v 0 = 0 := GleasonBridge.local_defect_g_zero_eq_zero μ u v
    have : 0 ≤ Cg * (1 + (0 : ℝ) ^ 2) := by simpa [hg0] using h0
    simpa using this
  refine ⟨8 * Cg, by nlinarith, ?_⟩
  intro s t
  set B : ℝ := 1 + s ^ 2 + t ^ 2
  have hB_nn : 0 ≤ B := by
    dsimp [B]
    nlinarith [sq_nonneg s, sq_nonneg t]
  have hsp : (s + t) ^ 2 ≤ 2 * (s ^ 2 + t ^ 2) := by
    nlinarith [sq_nonneg (s - t)]
  have hsm : (s - t) ^ 2 ≤ 2 * (s ^ 2 + t ^ 2) := by
    nlinarith [sq_nonneg (s + t)]
  have hBp : 1 + (s + t) ^ 2 ≤ 2 * B := by
    dsimp [B]
    nlinarith [hsp, sq_nonneg s, sq_nonneg t]
  have hBm : 1 + (s - t) ^ 2 ≤ 2 * B := by
    dsimp [B]
    nlinarith [hsm, sq_nonneg s, sq_nonneg t]
  have hBs : 1 + s ^ 2 ≤ B := by
    dsimp [B]
    nlinarith [sq_nonneg t]
  have hBt : 1 + t ^ 2 ≤ B := by
    dsimp [B]
    nlinarith [sq_nonneg s]
  have h1 : |local_defect_g μ u v (s + t)| ≤ 2 * Cg * B := by
    have h := hCg (s + t)
    have h' : |local_defect_g μ u v (s + t)| ≤ Cg * (2 * B) := by
      exact le_trans h (by gcongr)
    nlinarith [h']
  have h2 : |local_defect_g μ u v (s - t)| ≤ 2 * Cg * B := by
    have h := hCg (s - t)
    have h' : |local_defect_g μ u v (s - t)| ≤ Cg * (2 * B) := by
      exact le_trans h (by gcongr)
    nlinarith [h']
  have h3 : |local_defect_g μ u v s| ≤ Cg * B := by
    have h := hCg s
    exact le_trans h (by gcongr)
  have h4 : |local_defect_g μ u v t| ≤ Cg * B := by
    have h := hCg t
    exact le_trans h (by gcongr)
  have hform :
      local_defect_residual μ u v s t =
        local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t)
          - 2 * local_defect_g μ u v s - 2 * local_defect_g μ u v t := rfl
  rw [hform]
  calc
    |local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t)
        - 2 * local_defect_g μ u v s - 2 * local_defect_g μ u v t|
        = |(local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t)) -
            (2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t)| := by ring_nf
    _ ≤ |local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t)| +
          |2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t| := by
            have htri :
                |(local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t)) +
                    (-(2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t))|
                  ≤
                |local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t)| +
                  |-(2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t)| :=
              abs_add_le
                (local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t))
                (-(2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t))
            have hsum :
                (local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t)) +
                    (-(2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t))
                  =
                (local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t)) -
                  (2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t) := by
              ring
            have hnegArg :
                (-(2 * local_defect_g μ u v t) + -(2 * local_defect_g μ u v s))
                  = -(2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t) := by
              ring
            have hnegAbs :
                |-(2 * local_defect_g μ u v t) + -(2 * local_defect_g μ u v s)|
                  = |2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t| := by
              rw [hnegArg, abs_neg]
            rw [← hsum]
            simpa [hnegAbs] using htri
    _ ≤ (|local_defect_g μ u v (s + t)| + |local_defect_g μ u v (s - t)|) +
          (|2 * local_defect_g μ u v s| + |2 * local_defect_g μ u v t|) := by
            gcongr <;> exact abs_add_le _ _
    _ = |local_defect_g μ u v (s + t)| + |local_defect_g μ u v (s - t)|
          + |2 * local_defect_g μ u v s| + |2 * local_defect_g μ u v t| := by ring
    _ = |local_defect_g μ u v (s + t)| + |local_defect_g μ u v (s - t)|
          + 2 * |local_defect_g μ u v s| + 2 * |local_defect_g μ u v t| := by
            rw [abs_mul, abs_mul]
            norm_num
    _ ≤ 2 * Cg * B + 2 * Cg * B + 2 * (Cg * B) + 2 * (Cg * B) := by
          gcongr
    _ = (8 * Cg) * B := by ring

lemma local_quad2DCross_swap_of_orthonormal
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    local_quad2DCross μ u v a b = local_quad2DCross μ u v b a := by
  have hrot1 :=
    GleasonBridge.local_frame_quadratic_rotation (H := H) hdim μ u v hu hv huv a b
  have hrot2 :=
    GleasonBridge.local_frame_quadratic_rotation (H := H) hdim μ u v hu hv huv a (-b)
  have hneg :
      frame_quadratic (H := H) μ ((-(a : ℂ)) • v + (-(b : ℂ)) • u)
        =
      frame_quadratic (H := H) μ ((b : ℂ) • u + (a : ℂ) • v) := by
    have hq := frame_quadratic_neg (H := H) μ ((b : ℂ) • u + (a : ℂ) • v)
    simpa [sub_eq_add_neg, neg_smul, add_assoc, add_left_comm, add_comm] using hq
  have hrot2_raw :
      frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v) +
          frame_quadratic (H := H) μ ((-(a : ℂ)) • v + (-(b : ℂ)) • u)
        =
      (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by
    simpa [sub_eq_add_neg, neg_smul, pow_two, add_assoc, add_left_comm, add_comm] using hrot2
  have hrot2' :
      frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v) +
          frame_quadratic (H := H) μ ((b : ℂ) • u + (a : ℂ) • v)
        =
      (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by
    rw [hneg] at hrot2_raw
    simpa [add_assoc, add_left_comm, add_comm] using hrot2_raw
  have hcross :
      frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) -
          frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v)
        =
      frame_quadratic (H := H) μ ((b : ℂ) • u + (a : ℂ) • v) -
          frame_quadratic (H := H) μ ((b : ℂ) • u - (a : ℂ) • v) := by
    linarith [hrot1, hrot2']
  simpa [local_quad2DCross] using hcross

lemma local_quad2DCross_residual_as_hadamard_defect
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    let r : ℝ := Real.sqrt 2
    let p : H := (r⁻¹ : ℝ) • (u + v)
    let q : H := (r⁻¹ : ℝ) • (u - v)
    let α : ℝ := (a + b) * r⁻¹
    let β : ℝ := (a - b) * r⁻¹
    local_quad2DCross μ u v a b - (a * b) * local_quad2DCross μ u v 1 1 =
      local_quad2DDefect μ p q α β := by
  intro r p q α β
  have h :=
    GleasonBridge.quad2DDefect_hadamard (H := H) hdim μ u v hu hv huv a b
  simpa [r, p, q, α, β, quad2DCross, quad2DDefect, RCLike.real_smul_eq_coe_smul (K := ℂ),
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_assoc, mul_left_comm, mul_comm] using h.symm

def local_quad2DCross_residual
    (μ : FrameFunction H) (u v : H) (a b : ℝ) : ℝ :=
  local_quad2DCross μ u v a b - (a * b) * local_quad2DCross μ u v 1 1

lemma local_quad2DCross_residual_swap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    local_quad2DCross_residual μ u v a b = local_quad2DCross_residual μ u v b a := by
  unfold local_quad2DCross_residual
  rw [local_quad2DCross_swap_of_orthonormal hdim μ u v hu hv huv a b]
  ring

lemma local_quad2DCross_transfer
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = 1 + s ^ 2) :
    2 * local_quad2DCross μ u v 1 s =
      local_quad2DCross μ (u + (c : ℂ) • w) v 1 s +
        local_quad2DCross μ (u - (c : ℂ) • w) v 1 s := by
  have huw' : inner (𝕜 := ℂ) v u = 0 := inner_eq_zero_symm.1 huv
  have horth_plus : inner (𝕜 := ℂ) (u + (s : ℂ) • v) ((c : ℂ) • w) = 0 := by
    simp [huw, hvw]
  have horth_minus : inner (𝕜 := ℂ) (u - (s : ℂ) • v) ((c : ℂ) • w) = 0 := by
    simp [huw, hvw]
  have hnorm_plus_sq : ‖u + (s : ℂ) • v‖ ^ 2 = c ^ 2 := by
    have horth : inner (𝕜 := ℂ) u ((s : ℂ) • v) = 0 := by simp [huv]
    have hpyth :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u ((s : ℂ) • v) horth
    have hnorm_uv_mul : ‖u + (s : ℂ) • v‖ * ‖u + (s : ℂ) • v‖ = 1 + s * s := by
      simpa [hu, hv, norm_smul, Real.norm_eq_abs, sq_abs] using hpyth
    have hnorm_uv : ‖u + (s : ℂ) • v‖ ^ 2 = 1 + s ^ 2 := by
      simpa [pow_two] using hnorm_uv_mul
    linarith [hnorm_uv, hc]
  have hnorm_minus_sq : ‖u - (s : ℂ) • v‖ ^ 2 = c ^ 2 := by
    have horth : inner (𝕜 := ℂ) u (((-s : ℝ) : ℂ) • v) = 0 := by
      rw [inner_smul_right]
      simp [huv]
    have hpyth :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u (((-s : ℝ) : ℂ) • v) horth
    have hnorm_uv_mul : ‖u + (((-s : ℝ) : ℂ) • v)‖ * ‖u + (((-s : ℝ) : ℂ) • v)‖ = 1 + (-s) * (-s) := by
      simpa [hu, hv, norm_smul, Real.norm_eq_abs, sq_abs] using hpyth
    have hnorm_uv : ‖u + (((-s : ℝ) : ℂ) • v)‖ ^ 2 = 1 + s ^ 2 := by
      simpa [pow_two, neg_mul_neg] using hnorm_uv_mul
    have hminus : ‖u - (s : ℂ) • v‖ ^ 2 = 1 + s ^ 2 := by
      simpa [sub_eq_add_neg, neg_smul] using hnorm_uv
    linarith [hminus, hc]
  have hnorm_cw_sq : ‖(c : ℂ) • w‖ ^ 2 = c ^ 2 := by
    simp [hw, norm_smul, Real.norm_eq_abs, sq_abs]
  have hnorm_plus : ‖u + (s : ℂ) • v‖ = ‖(c : ℂ) • w‖ := by
    apply norm_eq_of_sq_eq
    nlinarith [hnorm_plus_sq, hnorm_cw_sq]
  have hnorm_minus : ‖u - (s : ℂ) • v‖ = ‖(c : ℂ) • w‖ := by
    apply norm_eq_of_sq_eq
    nlinarith [hnorm_minus_sq, hnorm_cw_sq]
  have hrp_plus :=
    frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ
      (u + (s : ℂ) • v) ((c : ℂ) • w) horth_plus hnorm_plus
  have hrp_minus :=
    frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ
      (u - (s : ℂ) • v) ((c : ℂ) • w) horth_minus hnorm_minus
  have hdiff :
      2 * (frame_quadratic (H := H) μ (u + (s : ℂ) • v) -
            frame_quadratic (H := H) μ (u - (s : ℂ) • v))
        =
      (frame_quadratic (H := H) μ (u + (s : ℂ) • v + (c : ℂ) • w) -
        frame_quadratic (H := H) μ (u - (s : ℂ) • v + (c : ℂ) • w))
        +
      (frame_quadratic (H := H) μ (u + (s : ℂ) • v - (c : ℂ) • w) -
        frame_quadratic (H := H) μ (u - (s : ℂ) • v - (c : ℂ) • w)) := by
    linarith [hrp_plus, hrp_minus]
  have hbase :
      local_quad2DCross μ u v 1 s =
        frame_quadratic (H := H) μ (u + (s : ℂ) • v) -
          frame_quadratic (H := H) μ (u - (s : ℂ) • v) := by
    simp [local_quad2DCross]
  have hplus :
      local_quad2DCross μ (u + (c : ℂ) • w) v 1 s =
        frame_quadratic (H := H) μ (u + (s : ℂ) • v + (c : ℂ) • w) -
          frame_quadratic (H := H) μ (u - (s : ℂ) • v + (c : ℂ) • w) := by
    simp [local_quad2DCross, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hminus :
      local_quad2DCross μ (u - (c : ℂ) • w) v 1 s =
        frame_quadratic (H := H) μ (u + (s : ℂ) • v - (c : ℂ) • w) -
          frame_quadratic (H := H) μ (u - (s : ℂ) • v - (c : ℂ) • w) := by
    simp [local_quad2DCross, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [hbase, hplus, hminus]
  linarith [hdiff]

lemma local_quad2DCross_residual_zero_right
    (μ : FrameFunction H) (u v : H) (a : ℝ) :
    local_quad2DCross_residual μ u v a 0 = 0 := by
  unfold local_quad2DCross_residual local_quad2DCross
  simp [sub_eq_add_neg]

lemma local_quad2DCross_residual_transfer
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = 1 + s ^ 2) :
    2 * local_quad2DCross_residual μ u v 1 s
      =
    local_quad2DCross_residual μ (u + (c : ℂ) • w) v 1 s +
      local_quad2DCross_residual μ (u - (c : ℂ) • w) v 1 s
      +
      s *
        (local_quad2DCross μ (u + (c : ℂ) • w) v 1 1 +
          local_quad2DCross μ (u - (c : ℂ) • w) v 1 1 -
          2 * local_quad2DCross μ u v 1 1) := by
  have hcross :=
    local_quad2DCross_transfer hdim μ u v w hu hv hw huv huw hvw s c hc
  unfold local_quad2DCross_residual
  linarith [hcross]

lemma local_quad2DCross_residual_zero_left
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (b : ℝ) :
    local_quad2DCross_residual μ u v 0 b = 0 := by
  rw [local_quad2DCross_residual_swap hdim μ u v hu hv huv 0 b]
  exact local_quad2DCross_residual_zero_right μ u v b

lemma local_quad2DCross_residual_diag
    (μ : FrameFunction H) (u v : H) :
    local_quad2DCross_residual μ u v 1 1 = 0 := by
  unfold local_quad2DCross_residual
  ring

lemma local_quad2DCross_residual_abs_le
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    |local_quad2DCross_residual μ u v a b| ≤ 4 * (a ^ 2 + b ^ 2) := by
  let r : ℝ := Real.sqrt 2
  let p : H := (r⁻¹ : ℝ) • (u + v)
  let q : H := (r⁻¹ : ℝ) • (u - v)
  let α : ℝ := (a + b) * r⁻¹
  let β : ℝ := (a - b) * r⁻¹
  have hpq :
      ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ inner (𝕜 := ℂ) p q = 0 := by
    simpa [r, p, q, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      GleasonBridge.hadamard_orthonormal_vw_local u v hu hv huv
  rcases hpq with ⟨hp, hq, hpq⟩
  have hdef :
      local_quad2DCross_residual μ u v a b = local_quad2DDefect μ p q α β := by
    simpa [r, p, q, α, β, local_quad2DCross_residual] using
      local_quad2DCross_residual_as_hadamard_defect hdim μ u v hu hv huv a b
  rw [hdef]
  have hbound := GleasonBridge.quad2DDefect_abs_le (H := H) μ p q hp hq hpq α β
  have hsq : α ^ 2 + β ^ 2 = a ^ 2 + b ^ 2 := by
    have hinv_sq : (r⁻¹ : ℝ) ^ 2 = (1 / 2 : ℝ) := by
      calc
        (r⁻¹ : ℝ) ^ 2 = (r ^ 2)⁻¹ := by
          simpa using (inv_pow r 2)
        _ = (2 : ℝ)⁻¹ := by
          dsimp [r]
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        _ = (1 / 2 : ℝ) := by norm_num
    calc
      α ^ 2 + β ^ 2
          = ((a + b) ^ 2 + (a - b) ^ 2) * (r⁻¹ : ℝ) ^ 2 := by
              dsimp [α, β]
              ring
      _ = ((a + b) ^ 2 + (a - b) ^ 2) * (1 / 2 : ℝ) := by rw [hinv_sq]
      _ = a ^ 2 + b ^ 2 := by ring
  simpa [hsq] using hbound

lemma local_quad2DCross_residual_hom
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (t a b : ℝ) :
    local_quad2DCross_residual μ u v (t * a) (t * b)
      = t ^ 2 * local_quad2DCross_residual μ u v a b := by
  let r : ℝ := Real.sqrt 2
  let p : H := (r⁻¹ : ℝ) • (u + v)
  let q : H := (r⁻¹ : ℝ) • (u - v)
  let A : ℝ := (a + b) * r⁻¹
  let B : ℝ := (a - b) * r⁻¹
  have hta :
      local_quad2DCross_residual μ u v (t * a) (t * b) =
        local_quad2DDefect μ p q (t * A) (t * B) := by
    have h :=
      local_quad2DCross_residual_as_hadamard_defect hdim μ u v hu hv huv (t * a) (t * b)
    simpa [local_quad2DCross_residual, r, p, q, A, B, mul_add, add_mul, sub_eq_add_neg,
      mul_assoc, mul_left_comm, mul_comm] using h
  have h0 :
      local_quad2DCross_residual μ u v a b =
        local_quad2DDefect μ p q A B := by
    simpa [local_quad2DCross_residual, r, p, q, A, B] using
      local_quad2DCross_residual_as_hadamard_defect hdim μ u v hu hv huv a b
  have hhom := GleasonBridge.local_quad2DDefect_hom μ p q t A B
  calc
    local_quad2DCross_residual μ u v (t * a) (t * b)
        = local_quad2DDefect μ p q (t * A) (t * B) := hta
    _ = t ^ 2 * local_quad2DDefect μ p q A B := hhom
    _ = t ^ 2 * local_quad2DCross_residual μ u v a b := by rw [h0]

lemma local_quad2DCross_residual_hadamard_step
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    let r : ℝ := Real.sqrt 2
    let p : H := (r⁻¹ : ℝ) • (u + v)
    let q : H := (r⁻¹ : ℝ) • (u - v)
    let A : ℝ := (a + b) * r⁻¹
    let B : ℝ := (a - b) * r⁻¹
    local_quad2DCross_residual μ p q a b = local_quad2DDefect μ u v A B := by
  intro r p q A B
  have hcross :=
    GleasonBridge.quad2DCross_hadamard_as_defect (H := H) hdim μ u v hu hv huv a b
  have h11 :=
    GleasonBridge.quad2DCross_hadamard_one_one (H := H) μ u v hu hv
  have hcross' :
      local_quad2DCross μ p q a b =
        local_quad2DDefect μ u v A B +
          (A ^ 2 - B ^ 2) * (frame_quadratic (H := H) μ u - frame_quadratic (H := H) μ v) := by
    simpa [r, p, q, A, B, quad2DCross, quad2DDefect, RCLike.real_smul_eq_coe_smul (K := ℂ)] using hcross
  have h11' :
      local_quad2DCross μ p q 1 1 =
        2 * frame_quadratic (H := H) μ u - 2 * frame_quadratic (H := H) μ v := by
    simpa [r, p, q, quad2DCross, RCLike.real_smul_eq_coe_smul (K := ℂ)] using h11
  have h11'' :
      local_quad2DCross μ p q 1 1 =
        2 * (frame_quadratic (H := H) μ u - frame_quadratic (H := H) μ v) := by
    linarith [h11']
  have hAB : A ^ 2 - B ^ 2 = 2 * a * b := by
    have hinv_sq : (r⁻¹ : ℝ) ^ 2 = (1 / 2 : ℝ) := by
      calc
        (r⁻¹ : ℝ) ^ 2 = (r ^ 2)⁻¹ := by simpa using (inv_pow r 2)
        _ = (2 : ℝ)⁻¹ := by
          dsimp [r]
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        _ = (1 / 2 : ℝ) := by norm_num
    calc
      A ^ 2 - B ^ 2
          = ((a + b) ^ 2 - (a - b) ^ 2) * (r⁻¹ : ℝ) ^ 2 := by
              dsimp [A, B]
              ring
      _ = ((a + b) ^ 2 - (a - b) ^ 2) * (1 / 2 : ℝ) := by rw [hinv_sq]
      _ = 2 * a * b := by ring
  unfold local_quad2DCross_residual
  calc
    local_quad2DCross μ p q a b - (a * b) * local_quad2DCross μ p q 1 1
        =
      local_quad2DDefect μ u v A B +
        (A ^ 2 - B ^ 2) * (frame_quadratic (H := H) μ u - frame_quadratic (H := H) μ v) -
          (a * b) * (2 * (frame_quadratic (H := H) μ u - frame_quadratic (H := H) μ v)) := by
            rw [hcross', h11'']
    _ = local_quad2DDefect μ u v A B +
          ((A ^ 2 - B ^ 2) - 2 * a * b) *
            (frame_quadratic (H := H) μ u - frame_quadratic (H := H) μ v) := by
            ring
    _ = local_quad2DDefect μ u v A B := by
          rw [hAB]
          ring

lemma local_defect_g_eq_hadamard_cross_residual
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    local_defect_g μ u v r =
      local_quad2DCross_residual μ p q ((1 + r) / s2) ((1 - r) / s2) := by
  intro s2 p q
  have hstep := local_quad2DCross_residual_hadamard_step hdim μ u v hu hv huv
    ((1 + r) / s2) ((1 - r) / s2)
  have hs2_sq : s2 ^ 2 = 2 := by
    dsimp [s2]
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hA : (((1 + r) / s2) + ((1 - r) / s2)) * s2⁻¹ = 1 := by
    have hs2_ne : s2 ≠ 0 := by
      dsimp [s2]
      exact by positivity
    have hA' : (((1 + r) / s2) + ((1 - r) / s2)) * s2⁻¹ = (2 : ℝ) / (s2 ^ 2) := by
      field_simp [hs2_ne]
      ring
    rw [hA', hs2_sq]
    norm_num
  have hB : (((1 + r) / s2) - ((1 - r) / s2)) * s2⁻¹ = r := by
    have hs2_ne : s2 ≠ 0 := by
      dsimp [s2]
      exact by positivity
    have hB' : (((1 + r) / s2) - ((1 - r) / s2)) * s2⁻¹ = (2 * r) / (s2 ^ 2) := by
      field_simp [hs2_ne]
      ring
    rw [hB', hs2_sq]
    ring
  simpa [local_defect_g, s2, p, q, hA, hB] using hstep.symm

lemma local_defect_residual_zero_of_hadamard_cross_residual_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hcross :
      let s2 : ℝ := Real.sqrt 2
      let p : H := (s2⁻¹ : ℝ) • (u + v)
      let q : H := (s2⁻¹ : ℝ) • (u - v)
      ∀ a b : ℝ, local_quad2DCross_residual μ p q a b = 0)
    (s t : ℝ) :
    local_defect_residual μ u v s t = 0 := by
  let s2 : ℝ := Real.sqrt 2
  let p : H := (s2⁻¹ : ℝ) • (u + v)
  let q : H := (s2⁻¹ : ℝ) • (u - v)
  have hcross' : ∀ a b : ℝ, local_quad2DCross_residual μ p q a b = 0 := by
    simpa [s2, p, q] using hcross
  have hg :
      ∀ r : ℝ, local_defect_g μ u v r = 0 := by
    intro r
    have hrepr :=
      local_defect_g_eq_hadamard_cross_residual hdim μ u v hu hv huv r
    rw [hrepr]
    exact hcross' ((1 + r) / s2) ((1 - r) / s2)
  have hgD : ∀ r : ℝ, local_quad2DDefect μ u v 1 r = 0 := by
    simpa [local_defect_g] using hg
  unfold local_defect_residual
  rw [hgD (s + t), hgD (s - t), hgD s, hgD t]
  ring

lemma defect_eq_zero_of_dyadic_squeeze
    (D : ℝ → ℝ → ℝ)
    (hbound : ∀ a b : ℝ, |D a b| ≤ 4 * (a ^ 2 + b ^ 2))
    (hdy : ∀ a b : ℝ, D a b = D ((a + b) / 2) ((a - b) / 2)) :
    ∀ a b : ℝ, D a b = 0 := by
  intro a b
  by_cases hab0 : a = 0 ∧ b = 0
  · rcases hab0 with ⟨ha0, hb0⟩
    subst ha0
    subst hb0
    have h0 := hbound 0 0
    have h0' : |D 0 0| ≤ 0 := by simpa using h0
    have : |D 0 0| = 0 := le_antisymm h0' (abs_nonneg _)
    exact abs_eq_zero.mp this
  let T : ℝ × ℝ → ℝ × ℝ := fun ab => ((ab.1 + ab.2) / 2, (ab.1 - ab.2) / 2)
  let ab0 : ℝ × ℝ := (a, b)
  let abn : ℕ → ℝ × ℝ := fun n => (T^[n]) ab0
  have hstep : ∀ n : ℕ, D (abn n).1 (abn n).2 = D (abn (n + 1)).1 (abn (n + 1)).2 := by
    intro n
    have : abn (n + 1) = T (abn n) := by simp [abn, Function.iterate_succ_apply', T]
    simpa [this, T] using hdy (abn n).1 (abn n).2
  have hconst : ∀ n : ℕ, D a b = D (abn n).1 (abn n).2 := by
    intro n
    induction n with
    | zero =>
        simp [abn, ab0]
    | succ n ih =>
        exact ih.trans (hstep n)
  have hnorm : ∀ x y : ℝ, ((x + y) / 2) ^ 2 + ((x - y) / 2) ^ 2 = (x ^ 2 + y ^ 2) / 2 := by
    intro x y
    ring
  have hnorm_iter : ∀ n : ℕ, (abn n).1 ^ 2 + (abn n).2 ^ 2 = (a ^ 2 + b ^ 2) / (2 ^ n) := by
    intro n
    induction n with
    | zero =>
        simp [abn, ab0]
    | succ n ih =>
        have hab : abn (n + 1) = T (abn n) := by simp [abn, Function.iterate_succ_apply', T]
        calc
          (abn (n + 1)).1 ^ 2 + (abn (n + 1)).2 ^ 2
              = (((abn n).1 + (abn n).2) / 2) ^ 2 + (((abn n).1 - (abn n).2) / 2) ^ 2 := by
                  simp [hab, T]
          _ = ((abn n).1 ^ 2 + (abn n).2 ^ 2) / 2 := by
                simpa using hnorm (abn n).1 (abn n).2
          _ = ((a ^ 2 + b ^ 2) / (2 ^ n)) / 2 := by simp [ih]
          _ = (a ^ 2 + b ^ 2) / (2 ^ (n + 1)) := by
                simp [div_div, pow_succ, mul_assoc]
  have hbound_iter : ∀ n : ℕ, |D a b| ≤ 4 * (a ^ 2 + b ^ 2) / (2 ^ n) := by
    intro n
    have hle_iter : |D (abn n).1 (abn n).2| ≤ 4 * ((abn n).1 ^ 2 + (abn n).2 ^ 2) := by
      exact hbound (abn n).1 (abn n).2
    have hrewrite : |D a b| = |D (abn n).1 (abn n).2| := by
      simpa using congrArg (fun t => |t|) (hconst n)
    calc
      |D a b| ≤ 4 * ((abn n).1 ^ 2 + (abn n).2 ^ 2) := by simpa [hrewrite] using hle_iter
      _ = 4 * ((a ^ 2 + b ^ 2) / (2 ^ n)) := by simp [hnorm_iter n]
      _ = 4 * (a ^ 2 + b ^ 2) / (2 ^ n) := by ring
  have hzero_abs : |D a b| = 0 := by
    by_contra hne
    have hpos : 0 < |D a b| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    have hab0' : a ^ 2 + b ^ 2 ≠ 0 := by
      intro h
      have : a = 0 ∧ b = 0 := by
        have ha : a ^ 2 = 0 := by nlinarith [h, sq_nonneg b]
        have hb : b ^ 2 = 0 := by nlinarith [h, sq_nonneg a]
        constructor <;> nlinarith
      exact hab0 (by simpa using this)
    have habpos : 0 < a ^ 2 + b ^ 2 := lt_of_le_of_ne (by nlinarith [sq_nonneg a, sq_nonneg b]) (Ne.symm hab0')
    have hεpos : 0 < |D a b| / (8 * (a ^ 2 + b ^ 2)) := by
      exact div_pos hpos (by nlinarith [habpos])
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < |D a b| / (8 * (a ^ 2 + b ^ 2)) :=
      exists_pow_lt_of_lt_one hεpos (by norm_num : (1 / 2 : ℝ) < 1)
    have hleN := hbound_iter N
    have hltN : (4 * (a ^ 2 + b ^ 2)) / (2 ^ N : ℝ) < |D a b| / 2 := by
      have hpow : (1 / (2 ^ N : ℝ)) = (1 / 2 : ℝ) ^ N := by simp [one_div, inv_pow]
      calc
        (4 * (a ^ 2 + b ^ 2)) / (2 ^ N : ℝ)
            = (4 * (a ^ 2 + b ^ 2)) * (1 / (2 ^ N : ℝ)) := by simp [div_eq_mul_inv]
        _ = (4 * (a ^ 2 + b ^ 2)) * ((1 / 2 : ℝ) ^ N) := by simp [hpow]
        _ < (4 * (a ^ 2 + b ^ 2)) * (|D a b| / (8 * (a ^ 2 + b ^ 2))) := by
              gcongr
        _ = |D a b| / 2 := by
              field_simp [hab0']
              ring
    have : |D a b| < |D a b| / 2 := lt_of_le_of_lt hleN hltN
    nlinarith [hpos, this]
  exact abs_eq_zero.mp hzero_abs

lemma local_quad2DCross_residual_zero_of_dyadic
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hdy : ∀ a b : ℝ,
      local_quad2DCross_residual μ u v a b =
        local_quad2DCross_residual μ u v ((a + b) / 2) ((a - b) / 2)) :
    ∀ a b : ℝ, local_quad2DCross_residual μ u v a b = 0 := by
  exact defect_eq_zero_of_dyadic_squeeze
    (D := local_quad2DCross_residual μ u v)
    (hbound := local_quad2DCross_residual_abs_le hdim μ u v hu hv huv)
    (hdy := hdy)

lemma hadamard_cross_residual_dyadic_iff_defect
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    local_quad2DCross_residual μ p q a b =
      local_quad2DCross_residual μ p q ((a + b) / 2) ((a - b) / 2)
      ↔
    local_quad2DDefect μ u v ((a + b) * s2⁻¹) ((a - b) * s2⁻¹) =
      local_quad2DDefect μ u v (a * s2⁻¹) (b * s2⁻¹) := by
  intro s2 p q
  have hpq :
      ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ inner (𝕜 := ℂ) p q = 0 := by
    simpa [s2, p, q, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      GleasonBridge.hadamard_orthonormal_vw_local u v hu hv huv
  rcases hpq with ⟨hp, hq, hpq0⟩
  have hleft :
      local_quad2DCross_residual μ p q a b =
        local_quad2DDefect μ u v ((a + b) * s2⁻¹) ((a - b) * s2⁻¹) := by
    simpa [s2, p, q] using
      local_quad2DCross_residual_hadamard_step hdim μ u v hu hv huv a b
  have hright :
      local_quad2DCross_residual μ p q ((a + b) / 2) ((a - b) / 2) =
        local_quad2DDefect μ u v (a * s2⁻¹) (b * s2⁻¹) := by
    have hstep :=
      local_quad2DCross_residual_hadamard_step hdim μ u v hu hv huv ((a + b) / 2) ((a - b) / 2)
    have hsimpA : ((((a + b) / 2) + ((a - b) / 2)) * s2⁻¹ : ℝ) = a * s2⁻¹ := by ring
    have hsimpB : ((((a + b) / 2) - ((a - b) / 2)) * s2⁻¹ : ℝ) = b * s2⁻¹ := by ring
    simpa [s2, p, q, hsimpA, hsimpB] using hstep
  constructor <;> intro h
  · rw [hleft, hright] at h
    exact h
  · rw [hleft, hright]
    exact h

lemma hadamard_cross_residual_dyadic_of_defect_contract
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hcontract :
      let s2 : ℝ := Real.sqrt 2
      ∀ a b : ℝ,
        local_quad2DDefect μ u v ((a + b) * s2⁻¹) ((a - b) * s2⁻¹) =
          local_quad2DDefect μ u v (a * s2⁻¹) (b * s2⁻¹)) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    ∀ a b : ℝ,
      local_quad2DCross_residual μ p q a b =
        local_quad2DCross_residual μ p q ((a + b) / 2) ((a - b) / 2) := by
  intro s2 p q a b
  have hcontract' :
      ∀ a b : ℝ,
        local_quad2DDefect μ u v ((a + b) * s2⁻¹) ((a - b) * s2⁻¹) =
          local_quad2DDefect μ u v (a * s2⁻¹) (b * s2⁻¹) := by
    simpa [s2] using hcontract
  have hiff :=
    hadamard_cross_residual_dyadic_iff_defect hdim μ u v hu hv huv a b
  exact hiff.mpr (hcontract' a b)

lemma hadamard_cross_residual_half_step
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    local_quad2DCross_residual μ p q ((1 + r) / 2) ((1 - r) / 2) =
      ((1 + r) ^ 2 / 4) *
        local_quad2DCross_residual μ p q 1 ((1 - r) / (1 + r)) := by
  intro s2 p q
  have hpq :
      ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ inner (𝕜 := ℂ) p q = 0 := by
    simpa [s2, p, q, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      GleasonBridge.hadamard_orthonormal_vw_local u v hu hv huv
  rcases hpq with ⟨hp, hq, hpq0⟩
  set phi : ℝ := (1 - r) / (1 + r)
  have hfac1 : ((1 + r) / 2) * (1 : ℝ) = (1 + r) / 2 := by ring
  have hfac2 : ((1 + r) / 2) * phi = (1 - r) / 2 := by
    dsimp [phi]
    field_simp [h1pr]
  have hhom :=
    local_quad2DCross_residual_hom hdim μ p q hp hq hpq0 ((1 + r) / 2) 1 phi
  calc
    local_quad2DCross_residual μ p q ((1 + r) / 2) ((1 - r) / 2)
        = local_quad2DCross_residual μ p q (((1 + r) / 2) * (1 : ℝ)) (((1 + r) / 2) * phi) := by
            rw [hfac1, hfac2]
    _ = ((1 + r) / 2) ^ 2 * local_quad2DCross_residual μ p q 1 phi := hhom
    _ = ((1 + r) ^ 2 / 4) * local_quad2DCross_residual μ p q 1 phi := by
          ring
    _ = ((1 + r) ^ 2 / 4) * local_quad2DCross_residual μ p q 1 ((1 - r) / (1 + r)) := by
          simp [phi]

lemma hadamard_cross_residual_dyadic_at_one_iff_recurrence
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    (let s2 : ℝ := Real.sqrt 2
      let p : H := (s2⁻¹ : ℝ) • (u + v)
      let q : H := (s2⁻¹ : ℝ) • (u - v)
      local_quad2DCross_residual μ p q 1 r =
        local_quad2DCross_residual μ p q ((1 + r) / 2) ((1 - r) / 2))
      ↔
    (let s2 : ℝ := Real.sqrt 2
      let p : H := (s2⁻¹ : ℝ) • (u + v)
      let q : H := (s2⁻¹ : ℝ) • (u - v)
      local_quad2DCross_residual μ p q 1 r =
        ((1 + r) ^ 2 / 4) *
          local_quad2DCross_residual μ p q 1 ((1 - r) / (1 + r))) := by
  let s2 : ℝ := Real.sqrt 2
  let p : H := (s2⁻¹ : ℝ) • (u + v)
  let q : H := (s2⁻¹ : ℝ) • (u - v)
  constructor <;> intro h
  · calc
      local_quad2DCross_residual μ p q 1 r
          = local_quad2DCross_residual μ p q ((1 + r) / 2) ((1 - r) / 2) := h
      _ = ((1 + r) ^ 2 / 4) *
            local_quad2DCross_residual μ p q 1 ((1 - r) / (1 + r)) := by
            simpa [s2, p, q] using
              (hadamard_cross_residual_half_step hdim μ u v hu hv huv r h1pr)
  · calc
      local_quad2DCross_residual μ p q 1 r
          = ((1 + r) ^ 2 / 4) *
              local_quad2DCross_residual μ p q 1 ((1 - r) / (1 + r)) := h
      _ = local_quad2DCross_residual μ p q ((1 + r) / 2) ((1 - r) / 2) := by
            simpa [s2, p, q] using
              (hadamard_cross_residual_half_step hdim μ u v hu hv huv r h1pr).symm

lemma hadamard_cross_residual_one_abs_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    |local_quad2DCross_residual μ p q 1 r| ≤ 4 * (1 + r ^ 2) := by
  intro s2 p q
  have hpq :
      ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ inner (𝕜 := ℂ) p q = 0 := by
    simpa [s2, p, q, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      GleasonBridge.hadamard_orthonormal_vw_local u v hu hv huv
  rcases hpq with ⟨hp, hq, hpq0⟩
  simpa [s2, p, q, one_pow] using
    (local_quad2DCross_residual_abs_le hdim μ p q hp hq hpq0 1 r)

lemma hadamard_cross_residual_one_odd
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    local_quad2DCross_residual μ p q 1 (-r) =
      - local_quad2DCross_residual μ p q 1 r := by
  intro s2 p q
  unfold local_quad2DCross_residual local_quad2DCross
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_comm, mul_left_comm, mul_assoc]

lemma hadamard_cross_residual_one_inversion
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    {r : ℝ} (hr : r ≠ 0) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    local_quad2DCross_residual μ p q 1 r =
      r ^ 2 * local_quad2DCross_residual μ p q 1 (1 / r) := by
  intro s2 p q
  have hpq :
      ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ inner (𝕜 := ℂ) p q = 0 := by
    simpa [s2, p, q, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      GleasonBridge.hadamard_orthonormal_vw_local u v hu hv huv
  rcases hpq with ⟨hp, hq, hpq0⟩
  have hswap :
      local_quad2DCross_residual μ p q 1 r =
        local_quad2DCross_residual μ p q r 1 := by
    exact local_quad2DCross_residual_swap hdim μ p q hp hq hpq0 1 r
  have hhom :=
    local_quad2DCross_residual_hom hdim μ p q hp hq hpq0 r 1 (1 / r)
  have hmul : r * (1 / r) = (1 : ℝ) := by field_simp [hr]
  calc
    local_quad2DCross_residual μ p q 1 r
        = local_quad2DCross_residual μ p q r 1 := hswap
    _ = local_quad2DCross_residual μ p q (r * 1) (r * (1 / r)) := by
          rw [hmul]
          simp
    _ = r ^ 2 * local_quad2DCross_residual μ p q 1 (1 / r) := hhom

def hadamard_residual_one
    (μ : FrameFunction H) (u v : H) (r : ℝ) : ℝ :=
  let s2 : ℝ := Real.sqrt 2
  let p : H := (s2⁻¹ : ℝ) • (u + v)
  let q : H := (s2⁻¹ : ℝ) • (u - v)
  local_quad2DCross_residual μ p q 1 r

lemma hadamard_residual_one_abs_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    |hadamard_residual_one μ u v r| ≤ 4 * (1 + r ^ 2) := by
  simpa [hadamard_residual_one] using
    (hadamard_cross_residual_one_abs_bound hdim μ u v hu hv huv r)

lemma hadamard_residual_one_odd
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) :
    hadamard_residual_one μ u v (-r) = -hadamard_residual_one μ u v r := by
  simpa [hadamard_residual_one] using
    (hadamard_cross_residual_one_odd hdim μ u v hu hv huv r)

lemma hadamard_residual_one_inversion
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    {r : ℝ} (hr : r ≠ 0) :
    hadamard_residual_one μ u v r =
      r ^ 2 * hadamard_residual_one μ u v (1 / r) := by
  simpa [hadamard_residual_one] using
    (hadamard_cross_residual_one_inversion hdim μ u v hu hv huv hr)

lemma hadamard_residual_half_step
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let s2 : ℝ := Real.sqrt 2
    let p : H := (s2⁻¹ : ℝ) • (u + v)
    let q : H := (s2⁻¹ : ℝ) • (u - v)
    local_quad2DCross_residual μ p q ((1 + r) / 2) ((1 - r) / 2) =
      ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r)) := by
  intro s2 p q
  unfold hadamard_residual_one
  simpa [s2, p, q, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (hadamard_cross_residual_half_step hdim μ u v hu hv huv r h1pr)

lemma hadamard_residual_half_step_eq_half_local_defect
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r))
      =
    (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by
  let s2 : ℝ := Real.sqrt 2
  let p : H := (s2⁻¹ : ℝ) • (u + v)
  let q : H := (s2⁻¹ : ℝ) • (u - v)
  have hhalf :
      local_quad2DCross_residual μ p q ((1 + r) / 2) ((1 - r) / 2) =
        ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r)) := by
    simpa [s2, p, q] using
      (hadamard_residual_half_step hdim μ u v hu hv huv r h1pr)
  have hstep :
      local_quad2DCross_residual μ p q ((1 + r) / 2) ((1 - r) / 2) =
        local_quad2DDefect μ u v (((((1 + r) / 2) + ((1 - r) / 2)) * s2⁻¹)) (((((1 + r) / 2) - ((1 - r) / 2)) * s2⁻¹)) := by
    simpa [s2, p, q] using
      (local_quad2DCross_residual_hadamard_step hdim μ u v hu hv huv ((1 + r) / 2) ((1 - r) / 2))
  have hstep' :
      local_quad2DCross_residual μ p q ((1 + r) / 2) ((1 - r) / 2) =
        local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) := by
    have hsimpA : (((((1 + r) / 2) + ((1 - r) / 2)) * s2⁻¹) : ℝ) = 1 * s2⁻¹ := by ring
    have hsimpB : (((((1 + r) / 2) - ((1 - r) / 2)) * s2⁻¹) : ℝ) = r * s2⁻¹ := by ring
    simpa [hsimpA, hsimpB] using hstep
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
  have hratio :
      local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹) =
        (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by
    calc
      local_quad2DDefect μ u v (1 * s2⁻¹) (r * s2⁻¹)
          = (s2⁻¹ : ℝ) ^ 2 * local_quad2DDefect μ u v 1 r := by
              simpa [mul_comm, mul_left_comm, mul_assoc] using hhom
      _ = (1 / 2 : ℝ) * local_quad2DDefect μ u v 1 r := by rw [hs2_sq]
      _ = (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by rfl
  linarith [hhalf, hstep', hratio]

lemma hadamard_residual_half_step_abs
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    (1 + r) ^ 2 * |hadamard_residual_one μ u v ((1 - r) / (1 + r))|
      =
    2 * |GleasonBridge.local_defect_g μ u v r| := by
  have hhalf :=
    hadamard_residual_half_step_eq_half_local_defect hdim μ u v hu hv huv r h1pr
  have habs :
      |((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r))|
        =
      |(1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r| := by
    exact congrArg abs hhalf
  have hcoef1 : 0 ≤ ((1 + r) ^ 2 / 4 : ℝ) := by positivity
  have hcoef2 : 0 ≤ (1 / 2 : ℝ) := by norm_num
  rw [abs_mul, abs_of_nonneg hcoef1, abs_mul, abs_of_nonneg hcoef2] at habs
  nlinarith [habs]

lemma hadamard_mobius_involutive
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    (1 - ((1 - r) / (1 + r))) / (1 + ((1 - r) / (1 + r))) = r := by
  field_simp [h1pr]
  ring

lemma hadamard_mobius_scale_product
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    ((1 + r) ^ 2 / 4) * ((1 + ((1 - r) / (1 + r))) ^ 2 / 4) = (1 / 4 : ℝ) := by
  have hnum : 1 + ((1 - r) / (1 + r)) = 2 / (1 + r) := by
    field_simp [h1pr]
    ring
  rw [hnum]
  field_simp [h1pr]
  ring

lemma one_add_inv_ne_zero_of_ne_zero_of_one_add_ne_zero
    {r : ℝ} (hr : r ≠ 0) (h1pr : 1 + r ≠ 0) :
    1 + (1 / r) ≠ 0 := by
  intro h
  have hmul : (1 + (1 / r)) * r = 0 := by rw [h, zero_mul]
  have hsum : (1 + (1 / r)) * r = 1 + r := by
    calc
      (1 + (1 / r)) * r = r + (1 / r) * r := by ring
      _ = r + 1 := by field_simp [hr]
      _ = 1 + r := by ring
  have : 1 + r = 0 := by linarith
  exact h1pr this

lemma hadamard_mobius_at_inv
    (r : ℝ) (hr : r ≠ 0) (h1pr : 1 + r ≠ 0) :
    (1 - (1 / r)) / (1 + (1 / r)) = -((1 - r) / (1 + r)) := by
  have h1p_inv : 1 + (1 / r) ≠ 0 :=
    one_add_inv_ne_zero_of_ne_zero_of_one_add_ne_zero hr h1pr
  have hleft : (1 - (1 / r)) / (1 + (1 / r)) = (r - 1) / (r + 1) := by
    have hnum : 1 - (1 / r) = (r - 1) / r := by
      field_simp [hr]
    have hden : 1 + (1 / r) = (r + 1) / r := by
      field_simp [hr]
    rw [hnum, hden]
    field_simp [hr, h1pr]
  have hright : -((1 - r) / (1 + r)) = (r - 1) / (r + 1) := by
    ring_nf
  exact hleft.trans hright.symm

lemma hadamard_recurrence_iff_half_local_defect
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    (hadamard_residual_one μ u v r =
      ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r)))
      ↔
    (hadamard_residual_one μ u v r =
      (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r) := by
  constructor <;> intro h
  · calc
      hadamard_residual_one μ u v r
          = ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r)) := h
      _ = (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by
            simpa using
              hadamard_residual_half_step_eq_half_local_defect
                hdim μ u v hu hv huv r h1pr
  · calc
      hadamard_residual_one μ u v r
          = (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := h
      _ = ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r)) := by
            simpa using
              (hadamard_residual_half_step_eq_half_local_defect
                hdim μ u v hu hv huv r h1pr).symm

lemma hadamard_residual_one_eq_mobius_scaled_local_defect
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    hadamard_residual_one μ u v r =
      ((1 + r) ^ 2 / 2) * GleasonBridge.local_defect_g μ u v ((1 - r) / (1 + r)) := by
  set φ : ℝ := (1 - r) / (1 + r)
  have h1pφ : 1 + φ ≠ 0 := by
    have hnum : 1 + φ = 2 / (1 + r) := by
      dsimp [φ]
      field_simp [h1pr]
      ring
    rw [hnum]
    exact div_ne_zero (by norm_num) h1pr
  have hhalf_φ :
      ((1 + φ) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - φ) / (1 + φ))
        =
      (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v φ := by
    simpa using
      hadamard_residual_half_step_eq_half_local_defect hdim μ u v hu hv huv φ h1pφ
  have hmob : (1 - φ) / (1 + φ) = r := by
    simpa [φ] using hadamard_mobius_involutive r h1pr
  have hcoef : ((1 + φ) ^ 2 / 4) = (1 / (1 + r) ^ 2) := by
    have hnum : 1 + φ = 2 / (1 + r) := by
      dsimp [φ]
      field_simp [h1pr]
      ring
    rw [hnum]
    field_simp [h1pr]
    ring
  have hmain :
      (1 / (1 + r) ^ 2) * hadamard_residual_one μ u v r =
        (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v φ := by
    simpa [hcoef, hmob] using hhalf_φ
  have h1pr_sq_ne : (1 + r) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 h1pr
  have hmul := congrArg (fun x : ℝ => (1 + r) ^ 2 * x) hmain
  have hleft :
      (1 + r) ^ 2 * ((1 / (1 + r) ^ 2) * hadamard_residual_one μ u v r) =
        hadamard_residual_one μ u v r := by
    field_simp [h1pr_sq_ne]
  have hright :
      (1 + r) ^ 2 * ((1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v φ) =
        ((1 + r) ^ 2 / 2) * GleasonBridge.local_defect_g μ u v φ := by
    ring
  have hmul' :
      (1 + r) ^ 2 * ((1 / (1 + r) ^ 2) * hadamard_residual_one μ u v r) =
        (1 + r) ^ 2 * ((1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v φ) := by
    simpa using hmul
  calc
    hadamard_residual_one μ u v r
        = (1 + r) ^ 2 * ((1 / (1 + r) ^ 2) * hadamard_residual_one μ u v r) := by
            exact hleft.symm
    _ = (1 + r) ^ 2 * ((1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v φ) := hmul'
    _ = ((1 + r) ^ 2 / 2) * GleasonBridge.local_defect_g μ u v φ := hright

lemma hadamard_mobius_swap_system
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    let φ : ℝ := (1 - r) / (1 + r)
    (1 + r) ^ 2 * hadamard_residual_one μ u v φ = 2 * GleasonBridge.local_defect_g μ u v r
      ∧
    (1 + r) ^ 2 * GleasonBridge.local_defect_g μ u v φ = 2 * hadamard_residual_one μ u v r := by
  intro φ
  constructor
  · have hhalf :=
      hadamard_residual_half_step_eq_half_local_defect hdim μ u v hu hv huv r h1pr
    linarith [hhalf]
  · have hmob :=
      hadamard_residual_one_eq_mobius_scaled_local_defect hdim μ u v hu hv huv r h1pr
    linarith [hmob]

lemma hadamard_recurrence_iff_local_defect_mobius
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    (hadamard_residual_one μ u v r =
      ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r)))
      ↔
    ((1 + r) ^ 2 * GleasonBridge.local_defect_g μ u v ((1 - r) / (1 + r)) =
      GleasonBridge.local_defect_g μ u v r) := by
  set φ : ℝ := (1 - r) / (1 + r)
  constructor <;> intro h
  · have hhalf :
        hadamard_residual_one μ u v r =
          (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by
      exact (hadamard_recurrence_iff_half_local_defect hdim μ u v hu hv huv r h1pr).1 h
    have hmob :
        hadamard_residual_one μ u v r =
          ((1 + r) ^ 2 / 2) * GleasonBridge.local_defect_g μ u v φ := by
      simpa [φ] using
        hadamard_residual_one_eq_mobius_scaled_local_defect hdim μ u v hu hv huv r h1pr
    linarith
  · have hhalf :
        hadamard_residual_one μ u v r =
          (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by
      have hmob :
          hadamard_residual_one μ u v r =
            ((1 + r) ^ 2 / 2) * GleasonBridge.local_defect_g μ u v φ := by
        simpa [φ] using
          hadamard_residual_one_eq_mobius_scaled_local_defect hdim μ u v hu hv huv r h1pr
      linarith [hmob, h]
    exact (hadamard_recurrence_iff_half_local_defect hdim μ u v hu hv huv r h1pr).2 hhalf

def hadamard_bridge_error
    (μ : FrameFunction H) (u v : H) (r : ℝ) : ℝ :=
  hadamard_residual_one μ u v r -
    (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r

lemma local_quad2DCross_neg_right
    (μ : FrameFunction H) (u v : H) (a b : ℝ) :
    local_quad2DCross μ u (-v) a b = -local_quad2DCross μ u v a b := by
  unfold local_quad2DCross
  have h1 : (a : ℂ) • u + (b : ℂ) • (-v) = (a : ℂ) • u - (b : ℂ) • v := by
    module
  have h2 : (a : ℂ) • u - (b : ℂ) • (-v) = (a : ℂ) • u + (b : ℂ) • v := by
    module
  rw [h1, h2]
  ring

lemma hadamard_bridge_error_zero
    (μ : FrameFunction H) (u v : H) :
    hadamard_bridge_error μ u v 0 = 0 := by
  unfold hadamard_bridge_error hadamard_residual_one
  simp [GleasonBridge.local_defect_g_zero_eq_zero, local_quad2DCross_residual_zero_right]

lemma hadamard_bridge_error_one
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    hadamard_bridge_error μ u v 1 = 0 := by
  have hres : hadamard_residual_one μ u v 1 = 0 := by
    unfold hadamard_residual_one
    simp [local_quad2DCross_residual_diag]
  have hg1 := GleasonBridge.local_defect_g_one_eq_zero hdim μ u v hu hv huv
  unfold hadamard_bridge_error
  linarith

lemma hadamard_bridge_error_growth_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      |hadamard_bridge_error μ u v r| ≤ C * (1 + r ^ 2) := by
  rcases GleasonBridge.local_defect_g_growth_bound μ u v hu hv huv with ⟨Cg, hCg⟩
  have hCg_nn : 0 ≤ Cg := by
    have h0 := hCg 0
    have hg0 : local_defect_g μ u v 0 = 0 := GleasonBridge.local_defect_g_zero_eq_zero μ u v
    have h0' : (0 : ℝ) ≤ Cg * (1 + (0 : ℝ) ^ 2) := by
      simpa [hg0] using h0
    simpa using h0'
  refine ⟨4 + Cg / 2, by nlinarith, ?_⟩
  intro r
  have hres := hadamard_residual_one_abs_bound hdim μ u v hu hv huv r
  have hg := hCg r
  unfold hadamard_bridge_error
  calc
    |hadamard_residual_one μ u v r - (1 / 2 : ℝ) * local_defect_g μ u v r|
        ≤ |hadamard_residual_one μ u v r| + |-(1 / 2 : ℝ) * local_defect_g μ u v r| := by
            simpa [sub_eq_add_neg] using
              (abs_add_le (hadamard_residual_one μ u v r)
                (-(1 / 2 : ℝ) * local_defect_g μ u v r))
    _ = |hadamard_residual_one μ u v r| + |(-(1 / 2 : ℝ))| * |local_defect_g μ u v r| := by
          rw [abs_mul]
    _ = |hadamard_residual_one μ u v r| + (1 / 2 : ℝ) * |local_defect_g μ u v r| := by
          norm_num
    _ ≤ 4 * (1 + r ^ 2) + (1 / 2 : ℝ) * (Cg * (1 + r ^ 2)) := by
          gcongr
    _ = (4 + Cg / 2) * (1 + r ^ 2) := by ring

lemma hadamard_bridge_error_eq_zero_iff_mobius
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    hadamard_bridge_error μ u v r = 0
      ↔
    ((1 + r) ^ 2 * GleasonBridge.local_defect_g μ u v ((1 - r) / (1 + r)) =
      GleasonBridge.local_defect_g μ u v r) := by
  constructor <;> intro h
  · have hhalf :
        hadamard_residual_one μ u v r =
          (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by
      unfold hadamard_bridge_error at h
      linarith
    have hrec :
        hadamard_residual_one μ u v r =
          ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r)) := by
      exact (hadamard_recurrence_iff_half_local_defect hdim μ u v hu hv huv r h1pr).2 hhalf
    exact (hadamard_recurrence_iff_local_defect_mobius hdim μ u v hu hv huv r h1pr).1 hrec
  · have hrec :
        hadamard_residual_one μ u v r =
          ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r)) := by
      exact (hadamard_recurrence_iff_local_defect_mobius hdim μ u v hu hv huv r h1pr).2 h
    have hhalf :
        hadamard_residual_one μ u v r =
          (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by
      exact (hadamard_recurrence_iff_half_local_defect hdim μ u v hu hv huv r h1pr).1 hrec
    unfold hadamard_bridge_error
    linarith

lemma hadamard_bridge_error_eq_recurrence_gap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    hadamard_bridge_error μ u v r =
      hadamard_residual_one μ u v r -
        ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r)) := by
  have hhalf :=
    hadamard_residual_half_step_eq_half_local_defect hdim μ u v hu hv huv r h1pr
  unfold hadamard_bridge_error
  linarith [hhalf]

lemma hadamard_recurrence_iff_bridge_error_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (r : ℝ) (h1pr : 1 + r ≠ 0) :
    (hadamard_residual_one μ u v r =
      ((1 + r) ^ 2 / 4) * hadamard_residual_one μ u v ((1 - r) / (1 + r)))
      ↔
    hadamard_bridge_error μ u v r = 0 := by
  constructor <;> intro h
  · have hhalf :
        hadamard_residual_one μ u v r =
          (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by
      exact (hadamard_recurrence_iff_half_local_defect hdim μ u v hu hv huv r h1pr).1 h
    unfold hadamard_bridge_error
    linarith
  · have hhalf :
        hadamard_residual_one μ u v r =
          (1 / 2 : ℝ) * GleasonBridge.local_defect_g μ u v r := by
      unfold hadamard_bridge_error at h
      linarith
    exact (hadamard_recurrence_iff_half_local_defect hdim μ u v hu hv huv r h1pr).2 hhalf

lemma hadamard_bridge_error_inversion
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    {r : ℝ} (hr : r ≠ 0) :
    hadamard_bridge_error μ u v r =
      -r ^ 2 * hadamard_bridge_error μ u v (-(1 / r)) := by
  have hF_inv := hadamard_residual_one_inversion hdim μ u v hu hv huv hr
  have hF_odd :
      hadamard_residual_one μ u v (-(1 / r)) =
        -hadamard_residual_one μ u v (1 / r) := by
    simpa using hadamard_residual_one_odd hdim μ u v hu hv huv (1 / r)
  have hF_odd' :
      hadamard_residual_one μ u v (1 / r) =
        -hadamard_residual_one μ u v (-(1 / r)) := by
    linarith [hF_odd]
  have hg_inv := GleasonBridge.local_defect_g_inversion hdim μ u v hu hv huv hr
  have hg_even :
      GleasonBridge.local_defect_g μ u v (-(1 / r)) =
        GleasonBridge.local_defect_g μ u v (1 / r) := by
    simpa using GleasonBridge.local_defect_g_even μ u v (1 / r)
  unfold hadamard_bridge_error
  calc
    hadamard_residual_one μ u v r - (1 / 2 : ℝ) * local_defect_g μ u v r
        = r ^ 2 * hadamard_residual_one μ u v (1 / r) +
            (r ^ 2 / 2) * local_defect_g μ u v (1 / r) := by
            rw [hF_inv, hg_inv]
            ring
    _ = r ^ 2 * (-hadamard_residual_one μ u v (-(1 / r))) +
          (r ^ 2 / 2) * local_defect_g μ u v (-(1 / r)) := by
            rw [hF_odd', ← hg_even]
    _ = -r ^ 2 *
          (hadamard_residual_one μ u v (-(1 / r)) -
            (1 / 2 : ℝ) * local_defect_g μ u v (-(1 / r))) := by
            ring


end
