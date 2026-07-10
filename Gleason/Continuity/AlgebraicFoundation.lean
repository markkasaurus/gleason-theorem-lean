import Mathlib

import Gleason.Finite.FrameFunction
import Gleason.Finite.Quadratic.Basic
import Gleason.Finite.Quadratic.Homogeneity
import Gleason.Finite.OrthogonalComplement
import Gleason.Finite.ThreeVectorFrame
import Gleason.Finite.RegularityBridge
import Gleason.Finite.Quadratic.Bound

noncomputable section

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

namespace GleasonBridge

open RankOne

-- Minimal local definitions (moved to top to ensure they are in scope)
def local_quad2DExpr (μ : FrameFunction H) (u v : H) (a b : ℝ) : ℝ :=
  frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) +
    frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v)

def local_quad2DCross (μ : FrameFunction H) (u v : H) (a b : ℝ) : ℝ :=
  frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) -
    frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v)

def local_quad2DDefect (μ : FrameFunction H) (u v : H) (a b : ℝ) : ℝ :=
  local_quad2DExpr μ u v a b
    - (2 * a ^ 2 * frame_quadratic (H := H) μ u + 2 * b ^ 2 * frame_quadratic (H := H) μ v)

lemma local_quad2DExpr_split_t
    (μ : FrameFunction H) (u v : H) (x y : ℝ) :
    local_quad2DExpr μ u v 1 (x + y) + local_quad2DExpr μ u v 1 (x - y)
    =
    (frame_quadratic (H := H) μ ((1 : ℂ) • u + ((x + y) : ℂ) • v)
    + frame_quadratic (H := H) μ ((1 : ℂ) • u - ((x + y) : ℂ) • v))
    +
    (frame_quadratic (H := H) μ ((1 : ℂ) • u + ((x - y) : ℂ) • v)
    + frame_quadratic (H := H) μ ((1 : ℂ) • u - ((x - y) : ℂ) • v)) := by
  simp [local_quad2DExpr, Complex.ofReal_add, Complex.ofReal_sub]

lemma local_quad2DExpr_sum_algebraic_identity
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    local_quad2DExpr μ u v 1 (s + t) + local_quad2DExpr μ u v 1 (s - t)
      = 2 * local_quad2DExpr μ u v 1 s + 2 * local_quad2DExpr μ u v 1 t
        - 4 * frame_quadratic (H := H) μ u
        + local_quad2DDefect μ u v 1 (s + t) + local_quad2DDefect μ u v 1 (s - t)
        - 2 * local_quad2DDefect μ u v 1 s - 2 * local_quad2DDefect μ u v 1 t := by
  dsimp [local_quad2DDefect]
  ring

lemma gleason_defect_algebraic_identity
    (μ : FrameFunction H) (u v w : H) (a b c : ℝ) :
    2 * local_quad2DDefect μ u v a b +
      local_quad2DDefect μ ((a : ℂ) • u + (b : ℂ) • v) w 1 c +
      local_quad2DDefect μ ((a : ℂ) • u - (b : ℂ) • v) w 1 c =
    2 * local_quad2DDefect μ u w a c +
      local_quad2DDefect μ ((a : ℂ) • u + (c : ℂ) • w) v 1 b +
      local_quad2DDefect μ ((a : ℂ) • u - (c : ℂ) • w) v 1 b := by
  dsimp [local_quad2DDefect, local_quad2DExpr]
  ring_nf
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

-- Short aliases used by the dyadic Hadamard closure block.
abbrev quad2DExpr (μ : FrameFunction H) (u v : H) (a b : ℝ) : ℝ :=
  local_quad2DExpr μ u v a b

abbrev quad2DCross (μ : FrameFunction H) (u v : H) (a b : ℝ) : ℝ :=
  local_quad2DCross μ u v a b

abbrev quad2DDefect (μ : FrameFunction H) (u v : H) (a b : ℝ) : ℝ :=
  local_quad2DDefect μ u v a b

-- Helper: equal squared norms imply equal norms
lemma norm_eq_of_sq_eq {E : Type*} [SeminormedAddCommGroup E] (x y : E)
    (h : ‖x‖ * ‖x‖ = ‖y‖ * ‖y‖) : ‖x‖ = ‖y‖ := by
  have hd : (‖x‖ - ‖y‖) * (‖x‖ + ‖y‖) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hd with hd | hd
  · linarith
  · linarith [norm_nonneg x, norm_nonneg y]

lemma local_frame_quadratic_rotation
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) +
        frame_quadratic (H := H) μ ((b : ℂ) • u - (a : ℂ) • v)
      =
    (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by
  classical
  by_cases hab0 : a ^ 2 + b ^ 2 = 0
  · have ha0 : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, hab0]
    have hb0 : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, hab0]
    subst ha0; subst hb0
    simp [frame_quadratic_zero (H := H) μ]

  have hx : 0 ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg b]

  let w : H := (a : ℂ) • u + (b : ℂ) • v
  let z : H := (b : ℂ) • u - (a : ℂ) • v
  let r : ℝ := Real.sqrt (a ^ 2 + b ^ 2)
  have hrpos : 0 < r := Real.sqrt_pos.2 (lt_of_le_of_ne hx (Ne.symm hab0))
  have hr0 : r ≠ 0 := ne_of_gt hrpos

  let w' : H := (((r : ℝ) : ℂ)⁻¹) • w
  let z' : H := (((r : ℝ) : ℂ)⁻¹) • z

  have hvv : inner (𝕜 := ℂ) v v = (1 : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, hv]
  have hvu : inner (𝕜 := ℂ) v u = 0 := (inner_eq_zero_symm).1 huv

  have hwz : inner (𝕜 := ℂ) w z = 0 := by
    simp [w, z, inner_add_left, inner_self_eq_norm_sq_to_K, hu, hvu, sub_eq_add_neg]
    have hbav : inner (𝕜 := ℂ) (b • v) (a • v) = (b : ℂ) * (a : ℂ) := by
      change inner (𝕜 := ℂ) ((b : ℂ) • v) ((a : ℂ) • v) = (b : ℂ) * (a : ℂ)
      rw [inner_smul_left, inner_smul_right, hvv]
      simp [mul_comm]
    have hauav : inner (𝕜 := ℂ) (a • u) (a • v) = 0 := by
      change inner (𝕜 := ℂ) ((a : ℂ) • u) ((a : ℂ) • v) = 0
      rw [inner_smul_left, inner_smul_right, huv]
      simp
    simp [hbav, hauav]

  have hw'norm : ‖w'‖ = 1 := by
    have hwu : inner (𝕜 := ℂ) ((a : ℂ) • u) ((b : ℂ) • v) = 0 := by
      simp [huv]
    have hnormsq : ‖w‖ ^ 2 = a ^ 2 + b ^ 2 := by
      have hpyth :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((a : ℂ) • u) ((b : ℂ) • v) hwu
      simpa [w, pow_two, norm_smul, hu, hv, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        mul_assoc, mul_left_comm, mul_comm] using hpyth
    have hw_norm : ‖w‖ = r := by
      have : Real.sqrt (a ^ 2 + b ^ 2) = ‖w‖ := by
        refine (Real.sqrt_eq_iff_mul_self_eq hx (norm_nonneg w)).2 ?_
        simpa [pow_two] using hnormsq.symm
      simpa [r] using this.symm
    have hr_nonneg : 0 ≤ r := le_of_lt hrpos
    have hnorm_inv : ‖(((r : ℝ) : ℂ)⁻¹)‖ = r⁻¹ := by
      simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    calc
      ‖w'‖ = ‖(((r : ℝ) : ℂ)⁻¹)‖ * ‖w‖ := by simp [w', norm_smul]
      _ = (r⁻¹) * r := by simp [hnorm_inv, hw_norm]
      _ = 1 := by field_simp [hr0]

  have hz'norm : ‖z'‖ = 1 := by
    have hzu : inner (𝕜 := ℂ) ((b : ℂ) • u) ((-a : ℂ) • v) = 0 := by
      rw [inner_smul_left, inner_smul_right]
      simp [huv]
    have hnormsq : ‖z‖ ^ 2 = a ^ 2 + b ^ 2 := by
      have hpyth :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((b : ℂ) • u) ((-a : ℂ) • v) hzu
      simpa [z, sub_eq_add_neg, pow_two, norm_smul, hu, hv, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        add_comm, mul_assoc, mul_left_comm, mul_comm] using hpyth
    have hz_norm : ‖z‖ = r := by
      have : Real.sqrt (a ^ 2 + b ^ 2) = ‖z‖ := by
        refine (Real.sqrt_eq_iff_mul_self_eq hx (norm_nonneg z)).2 ?_
        simpa [pow_two] using hnormsq.symm
      simpa [r] using this.symm
    have hr_nonneg : 0 ≤ r := le_of_lt hrpos
    have hnorm_inv : ‖(((r : ℝ) : ℂ)⁻¹)‖ = r⁻¹ := by
      simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    calc
      ‖z'‖ = ‖(((r : ℝ) : ℂ)⁻¹)‖ * ‖z‖ := by simp [z', norm_smul]
      _ = (r⁻¹) * r := by simp [hnorm_inv, hz_norm]
      _ = 1 := by field_simp [hr0]

  have hw'z' : inner (𝕜 := ℂ) w' z' = 0 := by
    simp [w', z', hwz]

  have h_span :
      Submodule.span ℂ ({u, v} : Set H) = Submodule.span ℂ ({w', z'} : Set H) := by
    have hle₁ : Submodule.span ℂ ({w', z'} : Set H) ≤ Submodule.span ℂ ({u, v} : Set H) := by
      refine Submodule.span_le.2 ?_
      intro x hx
      have : x = w' ∨ x = z' := by simpa using hx
      rcases this with rfl | rfl
      · refine (Submodule.span ℂ ({u, v} : Set H)).smul_mem _ ?_
        refine (Submodule.span ℂ ({u, v} : Set H)).add_mem ?_ ?_
        · exact (Submodule.span ℂ ({u, v} : Set H)).smul_mem _ (Submodule.subset_span (by simp))
        · exact (Submodule.span ℂ ({u, v} : Set H)).smul_mem _ (Submodule.subset_span (by simp))
      · refine (Submodule.span ℂ ({u, v} : Set H)).smul_mem _ ?_
        refine (Submodule.span ℂ ({u, v} : Set H)).sub_mem ?_ ?_ <;>
          exact (Submodule.span ℂ ({u, v} : Set H)).smul_mem _ (Submodule.subset_span (by simp))
    let s : ℂ := (a : ℂ) ^ 2 + (b : ℂ) ^ 2
    have hs : s = ((a ^ 2 + b ^ 2 : ℝ) : ℂ) := by
      simp [s, pow_two]
    have hs0 : s ≠ 0 := by
      have : ((a ^ 2 + b ^ 2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast hab0
      rw [← hs] at this
      exact this
    let K' : Submodule ℂ H := Submodule.span ℂ ({w', z'} : Set H)
    have hw_mem : w ∈ K' := by
      have hw' : w' ∈ K' := Submodule.subset_span (by simp)
      have : w = ((r : ℝ) : ℂ) • w' := by
        simp [w', smul_smul, hr0]
      have tmp := K'.smul_mem (((r : ℝ) : ℂ)) hw'
      rw [← this] at tmp
      exact tmp
    have hz_mem : z ∈ K' := by
      have hz' : z' ∈ K' := Submodule.subset_span (by simp)
      have : z = ((r : ℝ) : ℂ) • z' := by
        simp [z', smul_smul, hr0]
      simpa [this] using K'.smul_mem (((r : ℝ) : ℂ)) hz'
    have hu_mem : u ∈ K' := by
      have hlin : (a : ℂ) • w + (b : ℂ) • z = s • u := by
        simp [w, z, s, smul_add, add_smul, mul_smul, sub_eq_add_neg, pow_two]
        simp (config := { failIfUnchanged := false }) [smul_smul]
        rw [mul_comm a b]
        abel
      have hcomb_mem : (a : ℂ) • w + (b : ℂ) • z ∈ K' :=
        K'.add_mem (K'.smul_mem _ hw_mem) (K'.smul_mem _ hz_mem)
      have hs_mem : s • u ∈ K' := by
        have tmp := hcomb_mem
        rw [hlin] at tmp
        exact tmp
      have : (s⁻¹ : ℂ) • (s • u) ∈ K' := K'.smul_mem _ hs_mem
      have tmp := this
      rw [inv_smul_smul₀ hs0] at tmp
      exact tmp
    have hv_mem : v ∈ K' := by
      have hlin : (b : ℂ) • w - (a : ℂ) • z = s • v := by
        simp [w, z, s, smul_add, add_smul, mul_smul, sub_eq_add_neg, pow_two]
        simp (config := { failIfUnchanged := false }) [smul_smul]
        rw [mul_comm a b]
        abel
      have hcomb_mem : (b : ℂ) • w - (a : ℂ) • z ∈ K' :=
        K'.sub_mem (K'.smul_mem _ hw_mem) (K'.smul_mem _ hz_mem)
      have h : s⁻¹ • ((b : ℂ) • w - (a : ℂ) • z) ∈ K' := K'.smul_mem _ hcomb_mem
      have : s⁻¹ • ((b : ℂ) • w - (a : ℂ) • z) = v := by
        rw [hlin]; exact inv_smul_smul₀ hs0 v
      rwa [this] at h
    have hle₂ : Submodule.span ℂ ({u, v} : Set H) ≤ K' := by
      refine Submodule.span_le.2 ?_
      intro x hx
      have : x = u ∨ x = v := by simpa using hx
      rcases this with rfl | rfl
      · exact hu_mem
      · exact hv_mem
    exact le_antisymm_iff.2 ⟨hle₂, hle₁⟩

  have hsum :=
    frame_quadratic_orthonormal_sum_eq_of_span_eq (H := H) hdim μ u v w' z'
      hu hv huv hw'norm hz'norm hw'z' h_span

  have Qw' :
      frame_quadratic (H := H) μ w' = (r⁻¹) ^ 2 * frame_quadratic (H := H) μ w := by
    have hhom := frame_quadratic_sq_hom (H := H) μ (((r : ℝ) : ℂ)⁻¹) w
    have hr_nonneg : 0 ≤ r := le_of_lt hrpos
    have hnorm : ‖(((r : ℝ) : ℂ)⁻¹)‖ ^ 2 = (r⁻¹) ^ 2 := by
      simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    simpa [w', hnorm, mul_assoc] using hhom

  have Qz' :
      frame_quadratic (H := H) μ z' = (r⁻¹) ^ 2 * frame_quadratic (H := H) μ z := by
    have hhom := frame_quadratic_sq_hom (H := H) μ (((r : ℝ) : ℂ)⁻¹) z
    have hr_nonneg : 0 ≤ r := le_of_lt hrpos
    have hnorm : ‖(((r : ℝ) : ℂ)⁻¹)‖ ^ 2 = (r⁻¹) ^ 2 := by
      simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr_nonneg]
    simpa [z', hnorm, mul_assoc] using hhom

  have hr_sq : r ^ 2 = a ^ 2 + b ^ 2 := by
    simpa [r] using Real.sq_sqrt hx

  have hsum' :
      (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v)
        =
      frame_quadratic (H := H) μ w + frame_quadratic (H := H) μ z := by
    have hm := congrArg (fun t : ℝ => r ^ 2 * t) hsum
    have hr2 : r ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 hr0
    calc
      (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v)
          = r ^ 2 * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by
              simp [hr_sq]
      _ = r ^ 2 * (frame_quadratic (H := H) μ w' + frame_quadratic (H := H) μ z') := by
              simpa using hm
      _ = (r ^ 2 * ((r⁻¹) ^ 2) * frame_quadratic (H := H) μ w) +
            (r ^ 2 * ((r⁻¹) ^ 2) * frame_quadratic (H := H) μ z) := by
              simp [Qw', Qz', mul_add, mul_assoc]
      _ = frame_quadratic (H := H) μ w + frame_quadratic (H := H) μ z := by
              simp [hr2]

  simpa [w, z, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hsum'.symm

lemma local_quad2DExpr_add_swap_from_rotation
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    local_quad2DExpr μ u v a b + local_quad2DExpr μ u v b a
      = 2 * (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by
  have hrot1 :=
    local_frame_quadratic_rotation (H := H) hdim μ u v hu hv huv a b
  have hv_neg : ‖-v‖ = 1 := by simpa [norm_neg] using hv
  have huv_neg : inner (𝕜 := ℂ) u (-v) = 0 := by simpa using neg_eq_zero.mpr huv
  have hrot2 :=
    local_frame_quadratic_rotation (H := H) hdim μ u (-v) hu hv_neg huv_neg a b
  have hrot2' :
      frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v) +
          frame_quadratic (H := H) μ ((b : ℂ) • u + (a : ℂ) • v)
        =
      (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by
    simpa [sub_eq_add_neg, frame_quadratic_neg (H := H) μ, add_comm, add_left_comm, add_assoc] using hrot2
  calc
    local_quad2DExpr μ u v a b + local_quad2DExpr μ u v b a
        =
      (frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) +
        frame_quadratic (H := H) μ ((b : ℂ) • u - (a : ℂ) • v)) +
      (frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v) +
        frame_quadratic (H := H) μ ((b : ℂ) • u + (a : ℂ) • v)) := by
          simp [local_quad2DExpr, add_assoc, add_left_comm, add_comm]
    _ =
      (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) +
      (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by
          rw [hrot1, hrot2']
    _ = 2 * (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by ring

lemma local_quad2DDefect_swap_of_orthonormal
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    local_quad2DDefect μ u v a b = - local_quad2DDefect μ u v b a := by
  have hswap :=
    local_quad2DExpr_add_swap_from_rotation (H := H) hdim μ u v hu hv huv a b
  have hsum : local_quad2DDefect μ u v a b + local_quad2DDefect μ u v b a = 0 := by
    dsimp [local_quad2DDefect]
    linarith [hswap]
  linarith [hsum]

lemma hadamard_orthonormal_vw_local
    (v w : H) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvw : inner (𝕜 := ℂ) v w = 0) :
    let r : ℝ := Real.sqrt 2
    let p : H := ((r⁻¹ : ℝ) : ℂ) • (v + w)
    let q : H := ((r⁻¹ : ℝ) : ℂ) • (v - w)
    ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ inner (𝕜 := ℂ) p q = 0 := by
  classical
  intro r p q
  let s : ℂ := ((r⁻¹ : ℝ) : ℂ)
  have hvw' : inner (𝕜 := ℂ) w v = 0 := by
    simpa using (inner_eq_zero_symm).1 hvw
  have hrpos : (0 : ℝ) < r := by
    simpa [r] using (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))
  have hinv_sq : (r⁻¹) ^ 2 = (1 / 2 : ℝ) := by
    calc
      (r⁻¹) ^ 2 = (r ^ 2)⁻¹ := by simp [pow_two, mul_assoc]
      _ = (2 : ℝ)⁻¹ := by
        have hr2 : r ^ 2 = 2 := by
          simpa [r] using (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
        simp [hr2]
      _ = (1 / 2 : ℝ) := by norm_num
  have hnorm_s : ‖s‖ ^ 2 = (r⁻¹) ^ 2 := by
    have hrnonneg : 0 ≤ r⁻¹ := inv_nonneg.2 (le_of_lt hrpos)
    simp [s, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrnonneg]
  have hnorm_vw : ‖v + w‖ ^ 2 = (2 : ℝ) := by
    have h :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := v) (y := w) hvw
    have h' : ‖v + w‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
      simpa [pow_two] using h
    simpa [hv, hw, one_add_one_eq_two] using h'
  have hnorm_vw' : ‖v - w‖ ^ 2 = (2 : ℝ) := by
    have hinner : inner (𝕜 := ℂ) v (-w) = 0 := by
      simpa [inner_neg_right] using hvw
    have h :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := v) (y := -w) hinner
    have h' : ‖v + (-w)‖ ^ 2 = ‖v‖ ^ 2 + ‖-w‖ ^ 2 := by
      simpa [pow_two] using h
    simpa [sub_eq_add_neg, norm_neg, hv, hw, one_add_one_eq_two] using h'
  have hp2 : ‖p‖ ^ 2 = 1 := by
    have h2 := congrArg (fun t => t ^ 2) (norm_smul s (v + w))
    have h2' : ‖p‖ ^ 2 = (‖s‖ * ‖v + w‖) ^ 2 := by
      simpa [p, s] using h2
    have h2'' : ‖p‖ ^ 2 = ‖s‖ ^ 2 * ‖v + w‖ ^ 2 := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h2'
    calc
      ‖p‖ ^ 2 = (r⁻¹) ^ 2 * ‖v + w‖ ^ 2 := by simpa [hnorm_s] using h2''
      _ = (1 / 2 : ℝ) * 2 := by simp [hnorm_vw, hinv_sq]
      _ = 1 := by ring
  have hq2 : ‖q‖ ^ 2 = 1 := by
    have h2 := congrArg (fun t => t ^ 2) (norm_smul s (v - w))
    have h2' : ‖q‖ ^ 2 = (‖s‖ * ‖v - w‖) ^ 2 := by
      change ‖s • (v - w)‖ ^ 2 = (‖s‖ * ‖v - w‖) ^ 2
      simpa using h2
    have h2'' : ‖q‖ ^ 2 = ‖s‖ ^ 2 * ‖v - w‖ ^ 2 := by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h2'
    calc
      ‖q‖ ^ 2 = (r⁻¹) ^ 2 * ‖v - w‖ ^ 2 := by simpa [hnorm_s] using h2''
      _ = (1 / 2 : ℝ) * 2 := by simp [hnorm_vw', hinv_sq]
      _ = 1 := by ring
  have hpv : ‖p‖ = 1 := by nlinarith [hp2, norm_nonneg p]
  have hqv : ‖q‖ = 1 := by nlinarith [hq2, norm_nonneg q]
  have hpq : inner (𝕜 := ℂ) p q = 0 := by
    have hinner : inner (𝕜 := ℂ) (v + w) (v - w) = 0 := by
      calc
        inner (𝕜 := ℂ) (v + w) (v - w)
            =
          (‖v‖ ^ 2 : ℂ) - (‖w‖ ^ 2 : ℂ) := by
            simp [inner_add_left, inner_sub_right, inner_add_right, inner_sub_left,
              inner_self_eq_norm_sq_to_K, hvw, hvw', sub_eq_add_neg,
              add_assoc, add_left_comm, add_comm]
        _ = 0 := by simp [hv, hw]
    have hpdef : p = s • (v + w) := by rfl
    have hqdef : q = s • (v - w) := by rfl
    have hcalc :
        inner (𝕜 := ℂ) p q = (star s) * (s * inner (𝕜 := ℂ) (v + w) (v - w)) := by
      simp [hpdef, hqdef, inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm, mul_comm]
      ring_nf
    calc
      inner (𝕜 := ℂ) p q = (star s) * (s * inner (𝕜 := ℂ) (v + w) (v - w)) := hcalc
      _ = 0 := by simp [hinner]
  exact ⟨hpv, hqv, hpq⟩

lemma frame_quadratic_abs_le_norm_sq_local (μ : FrameFunction H) (x : H) :
    |frame_quadratic (H := H) μ x| ≤ ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · subst hx
    simp [frame_quadratic]
  · have hx' : x ≠ 0 := hx
    have hμle : μ.μ (rankOneProjection (H := H) x hx') ≤ 1 :=
      FrameQuadratic.mu_rankOne_le_one (H := H) μ x hx'
    have hnonneg : 0 ≤ frame_quadratic (H := H) μ x :=
      frame_quadratic_nonneg (H := H) μ x
    have hdef : frame_quadratic (H := H) μ x = μ.μ (rankOneProjection (H := H) x hx') * ‖x‖ ^ 2 := by
      simp [frame_quadratic, hx]
    have hn : 0 ≤ ‖x‖ ^ 2 := by
      have : 0 ≤ ‖x‖ := norm_nonneg x
      nlinarith
    have habs : |frame_quadratic (H := H) μ x| = frame_quadratic (H := H) μ x :=
      abs_of_nonneg hnonneg
    have hmul : μ.μ (rankOneProjection (H := H) x hx') * ‖x‖ ^ 2 ≤ 1 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hμle hn
    have hmul' : frame_quadratic (H := H) μ x ≤ ‖x‖ ^ 2 := by
      simpa [hdef, one_mul] using hmul
    calc
      |frame_quadratic (H := H) μ x| = frame_quadratic (H := H) μ x := habs
      _ ≤ ‖x‖ ^ 2 := hmul'

lemma quad2DDefect_abs_le
    (μ : FrameFunction H) (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (a b : ℝ) :
    |quad2DDefect μ u v a b| ≤ 4 * (a ^ 2 + b ^ 2) := by
  have hinner : inner (𝕜 := ℂ) (a • u) (b • v) = 0 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a u, RCLike.real_smul_eq_coe_smul (K := ℂ) b v]
    simp [huv]
  have hnorm_smul_u : ‖a • u‖ ^ 2 = a ^ 2 := by
    simp [norm_smul, hu, Real.norm_eq_abs, pow_two]
  have hnorm_smul_v : ‖b • v‖ ^ 2 = b ^ 2 := by
    simp [norm_smul, hv, Real.norm_eq_abs, pow_two]
  have hnorm_plus : ‖a • u + b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    have hmul :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := a • u) (y := b • v) hinner
    have hsq :
        ‖a • u + b • v‖ ^ 2 = ‖a • u‖ ^ 2 + ‖b • v‖ ^ 2 := by
      simpa [pow_two] using hmul
    simpa [hnorm_smul_u, hnorm_smul_v, add_comm, add_left_comm, add_assoc] using hsq
  have hnorm_minus : ‖a • u - b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    have hinner' : inner (𝕜 := ℂ) (a • u) (-(b • v)) = 0 := by
      simp [inner_neg_right, hinner]
    have hmul :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := a • u) (y := -(b • v)) hinner'
    have hsq :
        ‖a • u + (-(b • v))‖ ^ 2 = ‖a • u‖ ^ 2 + ‖-(b • v)‖ ^ 2 := by
      simpa [pow_two] using hmul
    have hnorm_neg_v : ‖-(b • v)‖ ^ 2 = b ^ 2 := by
      simpa using (by simpa [norm_neg] using hnorm_smul_v)
    simpa [sub_eq_add_neg, hnorm_smul_u, hnorm_smul_v, hnorm_neg_v, add_comm, add_left_comm,
      add_assoc] using hsq
  have hQplus :
      |frame_quadratic (H := H) μ (a • u + b • v)| ≤ a ^ 2 + b ^ 2 := by
    calc
      |frame_quadratic (H := H) μ (a • u + b • v)|
          ≤ ‖a • u + b • v‖ ^ 2 := by simpa using (frame_quadratic_abs_le_norm_sq_local (H := H) μ (a • u + b • v))
      _ = a ^ 2 + b ^ 2 := hnorm_plus
  have hQminus :
      |frame_quadratic (H := H) μ (a • u - b • v)| ≤ a ^ 2 + b ^ 2 := by
    calc
      |frame_quadratic (H := H) μ (a • u - b • v)|
          ≤ ‖a • u - b • v‖ ^ 2 := by simpa using (frame_quadratic_abs_le_norm_sq_local (H := H) μ (a • u - b • v))
      _ = a ^ 2 + b ^ 2 := hnorm_minus
  have hQplusC :
      |frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v)| ≤ a ^ 2 + b ^ 2 := by
    have hx : (a • u + b • v : H) = ((a : ℂ) • u + (b : ℂ) • v) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a u, RCLike.real_smul_eq_coe_smul (K := ℂ) b v]
      rfl
    simpa [hx] using hQplus
  have hQminusC :
      |frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v)| ≤ a ^ 2 + b ^ 2 := by
    have hx : (a • u - b • v : H) = ((a : ℂ) • u - (b : ℂ) • v) := by
      rw [sub_eq_add_neg, sub_eq_add_neg]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a u, RCLike.real_smul_eq_coe_smul (K := ℂ) b v]
      rfl
    simpa [hx] using hQminus
  have hExpr : |quad2DExpr μ u v a b| ≤ 2 * (a ^ 2 + b ^ 2) := by
    dsimp [quad2DExpr, local_quad2DExpr]
    have hnorm :
        |frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) +
            frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v)|
          ≤
        |frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v)| +
          |frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v)| := by
      simpa [Real.norm_eq_abs] using
        (norm_add_le
          (frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v))
          (frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v)))
    exact le_trans hnorm (by linarith [hQplusC, hQminusC])
  have hQu : |frame_quadratic (H := H) μ u| ≤ 1 := by
    simpa [hu] using (frame_quadratic_abs_le_norm_sq_local (H := H) μ u)
  have hQv : |frame_quadratic (H := H) μ v| ≤ 1 := by
    simpa [hv] using (frame_quadratic_abs_le_norm_sq_local (H := H) μ v)
  have hDiag :
      |2 * a ^ 2 * frame_quadratic (H := H) μ u + 2 * b ^ 2 * frame_quadratic (H := H) μ v|
        ≤ 2 * (a ^ 2 + b ^ 2) := by
    have h1 : |2 * a ^ 2 * frame_quadratic (H := H) μ u| ≤ 2 * a ^ 2 := by
      have h1' : |2 * a ^ 2 * frame_quadratic (H := H) μ u| = (2 * a ^ 2) * |frame_quadratic (H := H) μ u| := by
        rw [abs_mul, abs_mul]
        simp [abs_of_nonneg, sq_nonneg a]
      rw [h1']
      nlinarith [hQu, sq_nonneg a]
    have h2 : |2 * b ^ 2 * frame_quadratic (H := H) μ v| ≤ 2 * b ^ 2 := by
      have h2' : |2 * b ^ 2 * frame_quadratic (H := H) μ v| = (2 * b ^ 2) * |frame_quadratic (H := H) μ v| := by
        rw [abs_mul, abs_mul]
        simp [abs_of_nonneg, sq_nonneg b]
      rw [h2']
      nlinarith [hQv, sq_nonneg b]
    have hsum :
        |2 * a ^ 2 * frame_quadratic (H := H) μ u + 2 * b ^ 2 * frame_quadratic (H := H) μ v|
          ≤ |2 * a ^ 2 * frame_quadratic (H := H) μ u| + |2 * b ^ 2 * frame_quadratic (H := H) μ v| := by
      have hnorm :=
        norm_add_le
          (2 * a ^ 2 * frame_quadratic (H := H) μ u)
          (2 * b ^ 2 * frame_quadratic (H := H) μ v)
      simpa [Real.norm_eq_abs] using hnorm
    linarith
  dsimp [quad2DDefect, local_quad2DDefect]
  have hsub := abs_sub (quad2DExpr μ u v a b)
    (2 * a ^ 2 * frame_quadratic (H := H) μ u + 2 * b ^ 2 * frame_quadratic (H := H) μ v)
  linarith

lemma quad2DDefect_hadamard
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    let r : ℝ := Real.sqrt 2
    let p : H := ((r⁻¹ : ℝ) : ℂ) • (u + v)
    let q : H := ((r⁻¹ : ℝ) : ℂ) • (u - v)
    let α : ℝ := (a + b) * r⁻¹
    let β : ℝ := (a - b) * r⁻¹
    quad2DDefect μ p q α β
      =
    quad2DCross μ u v a b - (a * b) * quad2DCross μ u v 1 1 := by
  classical
  intro r p q α β
  have hr0 : r ≠ 0 := by
    dsimp [r]
    have : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
    exact ne_of_gt this
  have hr2 : r ^ 2 = 2 := by
    dsimp [r]
    exact Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hinv_sq : (r⁻¹) ^ 2 = (1 / 2 : ℝ) := by
    calc
      (r⁻¹) ^ 2 = (r ^ 2)⁻¹ := by simp [pow_two]
      _ = (2 : ℝ)⁻¹ := by simp [hr2]
      _ = (1 / 2 : ℝ) := by norm_num

  have hvec1 :
      ((α : ℂ) • p + (β : ℂ) • q) = (a : ℂ) • u + (b : ℂ) • v := by
    set s : ℂ := ((r⁻¹ : ℝ) : ℂ)
    have hs2 : s ^ 2 = ((1 / 2 : ℝ) : ℂ) := by
      simpa [s] using (show ((r⁻¹ : ℝ) : ℂ) ^ 2 = ((1 / 2 : ℝ) : ℂ) from (by exact_mod_cast hinv_sq))
    have hs2' : s * s = ((1 / 2 : ℝ) : ℂ) := by simpa [pow_two] using hs2
    calc
      (α : ℂ) • p + (β : ℂ) • q
          = (((a + b : ℝ) : ℂ) * (s * s)) • u + (((a + b : ℝ) : ℂ) * (s * s)) • v
              + ((((a - b : ℝ) : ℂ) * (s * s)) • u - (((a - b : ℝ) : ℂ) * (s * s)) • v) := by
              simp [p, q, α, β, s, sub_eq_add_neg, smul_add, smul_sub, smul_smul, mul_assoc]
      _ = (((((a + b : ℝ) : ℂ) * (s * s) + ((a - b : ℝ) : ℂ) * (s * s)) • u) +
              ((((a + b : ℝ) : ℂ) * (s * s) - ((a - b : ℝ) : ℂ) * (s * s)) • v)) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_smul]
      _ = (((((2 * a : ℝ) : ℂ) * (s * s)) • u) + ((((2 * b : ℝ) : ℂ) * (s * s)) • v)) := by
              have hAu :
                  ((a + b : ℝ) : ℂ) * (s * s) + ((a - b : ℝ) : ℂ) * (s * s)
                    = ((2 * a : ℝ) : ℂ) * (s * s) := by
                have hab : (a + b) + (a - b) = 2 * a := by ring
                have habc :
                    ((a + b : ℝ) : ℂ) + ((a - b : ℝ) : ℂ) = ((2 * a : ℝ) : ℂ) := by
                  have := congrArg (fun t : ℝ => (t : ℂ)) hab
                  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
                calc
                  ((a + b : ℝ) : ℂ) * (s * s) + ((a - b : ℝ) : ℂ) * (s * s)
                      = (((a + b : ℝ) : ℂ) + ((a - b : ℝ) : ℂ)) * (s * s) := by
                      simpa [add_mul] using
                        (add_mul ((a + b : ℝ) : ℂ) ((a - b : ℝ) : ℂ) (s * s)).symm
                  _ = ((2 * a : ℝ) : ℂ) * (s * s) := by
                        simpa using congrArg (fun t : ℂ => t * (s * s)) habc
              have hBv :
                  ((a + b : ℝ) : ℂ) * (s * s) - ((a - b : ℝ) : ℂ) * (s * s)
                    = ((2 * b : ℝ) : ℂ) * (s * s) := by
                have hab : (a + b) - (a - b) = 2 * b := by ring
                have habc :
                    ((a + b : ℝ) : ℂ) - ((a - b : ℝ) : ℂ) = ((2 * b : ℝ) : ℂ) := by
                  have := congrArg (fun t : ℝ => (t : ℂ)) hab
                  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
                calc
                  ((a + b : ℝ) : ℂ) * (s * s) - ((a - b : ℝ) : ℂ) * (s * s)
                      = (((a + b : ℝ) : ℂ) - ((a - b : ℝ) : ℂ)) * (s * s) := by
                      simpa [sub_mul] using
                        (sub_mul ((a + b : ℝ) : ℂ) ((a - b : ℝ) : ℂ) (s * s)).symm
                  _ = ((2 * b : ℝ) : ℂ) * (s * s) := by
                        simpa using congrArg (fun t : ℂ => t * (s * s)) habc
              rw [hAu, hBv]
      _ = (a : ℂ) • u + (b : ℂ) • v := by simp [hs2', mul_assoc, mul_left_comm, mul_comm]
  have hvec2 :
      ((α : ℂ) • p - (β : ℂ) • q) = (b : ℂ) • u + (a : ℂ) • v := by
    set s : ℂ := ((r⁻¹ : ℝ) : ℂ)
    have hs2 : s ^ 2 = ((1 / 2 : ℝ) : ℂ) := by
      simpa [s] using (show ((r⁻¹ : ℝ) : ℂ) ^ 2 = ((1 / 2 : ℝ) : ℂ) from (by exact_mod_cast hinv_sq))
    have hs2' : s * s = ((1 / 2 : ℝ) : ℂ) := by simpa [pow_two] using hs2
    calc
      (α : ℂ) • p - (β : ℂ) • q
          = (((a + b : ℝ) : ℂ) * (s * s)) • u + (((a + b : ℝ) : ℂ) * (s * s)) • v
              - ((((a - b : ℝ) : ℂ) * (s * s)) • u - (((a - b : ℝ) : ℂ) * (s * s)) • v) := by
              simp [p, q, α, β, s, sub_eq_add_neg, smul_add, smul_sub, smul_smul, mul_left_comm, mul_comm]
      _ = (((((a + b : ℝ) : ℂ) * (s * s) - ((a - b : ℝ) : ℂ) * (s * s)) • u) +
              ((((a + b : ℝ) : ℂ) * (s * s) + ((a - b : ℝ) : ℂ) * (s * s)) • v)) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul]
      _ = (((((2 * b : ℝ) : ℂ) * (s * s)) • u) + ((((2 * a : ℝ) : ℂ) * (s * s)) • v)) := by
              have hBu :
                  ((a + b : ℝ) : ℂ) * (s * s) - ((a - b : ℝ) : ℂ) * (s * s)
                    = ((2 * b : ℝ) : ℂ) * (s * s) := by
                have hab : (a + b) - (a - b) = 2 * b := by ring
                have habc :
                    ((a + b : ℝ) : ℂ) - ((a - b : ℝ) : ℂ) = ((2 * b : ℝ) : ℂ) := by
                  have := congrArg (fun t : ℝ => (t : ℂ)) hab
                  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
                calc
                  ((a + b : ℝ) : ℂ) * (s * s) - ((a - b : ℝ) : ℂ) * (s * s)
                      = (((a + b : ℝ) : ℂ) - ((a - b : ℝ) : ℂ)) * (s * s) := by
                      simpa [sub_mul] using
                        (sub_mul ((a + b : ℝ) : ℂ) ((a - b : ℝ) : ℂ) (s * s)).symm
                  _ = ((2 * b : ℝ) : ℂ) * (s * s) := by
                        simpa using congrArg (fun t : ℂ => t * (s * s)) habc
              have hAv :
                  ((a + b : ℝ) : ℂ) * (s * s) + ((a - b : ℝ) : ℂ) * (s * s)
                    = ((2 * a : ℝ) : ℂ) * (s * s) := by
                have hab : (a + b) + (a - b) = 2 * a := by ring
                have habc :
                    ((a + b : ℝ) : ℂ) + ((a - b : ℝ) : ℂ) = ((2 * a : ℝ) : ℂ) := by
                  have := congrArg (fun t : ℝ => (t : ℂ)) hab
                  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
                calc
                  ((a + b : ℝ) : ℂ) * (s * s) + ((a - b : ℝ) : ℂ) * (s * s)
                      = (((a + b : ℝ) : ℂ) + ((a - b : ℝ) : ℂ)) * (s * s) := by
                      simpa [add_mul] using
                        (add_mul ((a + b : ℝ) : ℂ) ((a - b : ℝ) : ℂ) (s * s)).symm
                  _ = ((2 * a : ℝ) : ℂ) * (s * s) := by
                        simpa using congrArg (fun t : ℂ => t * (s * s)) habc
              rw [hBu, hAv]
      _ = (b : ℂ) • u + (a : ℂ) • v := by simp [hs2', mul_assoc, mul_left_comm, mul_comm]

  have hExpr :
      quad2DExpr μ p q α β
        =
      (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) +
        quad2DCross μ u v a b := by
    have hrot := local_frame_quadratic_rotation (H := H) hdim μ u v hu hv huv a (-b)
    have hrot' :
        frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v) +
            frame_quadratic (H := H) μ ((a : ℂ) • v + (b : ℂ) • u)
          =
        (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by
      have hrot0 :
          frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v) +
              frame_quadratic (H := H) μ ((-b : ℂ) • u - (a : ℂ) • v)
            =
          (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by
        simpa [sub_eq_add_neg, pow_two, add_assoc, add_left_comm, add_comm] using hrot
      have hneg (x : H) : frame_quadratic (H := H) μ (-x) = frame_quadratic (H := H) μ x := by
        simpa [neg_one_smul] using (frame_quadratic_sq_hom (H := H) μ (-1 : ℂ) x)
      have hQneg :
          frame_quadratic (H := H) μ (-(a • v) + -(b • u))
            =
          frame_quadratic (H := H) μ (a • v + b • u) := by
        have harg : (-(a • v) + -(b • u)) = -(a • v + b • u) := by
          simpa [neg_add, add_assoc, add_left_comm, add_comm]
        calc
          frame_quadratic (H := H) μ (-(a • v) + -(b • u))
              = frame_quadratic (H := H) μ (-(a • v + b • u)) := by simp [harg]
          _ = frame_quadratic (H := H) μ (a • v + b • u) := by rw [hneg (a • v + b • u)]
      simpa [hQneg, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hrot0
    have hrot'' :
        frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v) +
            frame_quadratic (H := H) μ ((b : ℂ) • u + (a : ℂ) • v)
          =
        (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by
      simpa [add_comm, add_left_comm, add_assoc] using hrot'
    have hsolve :
        frame_quadratic (H := H) μ ((b : ℂ) • u + (a : ℂ) • v)
          =
        (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v)
          - frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v) := by
      linarith [hrot'']
    dsimp [quad2DExpr, local_quad2DExpr, quad2DCross, local_quad2DCross]
    calc
      frame_quadratic (H := H) μ ((α : ℂ) • p + (β : ℂ) • q) +
          frame_quadratic (H := H) μ ((α : ℂ) • p - (β : ℂ) • q)
          =
        frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) +
          frame_quadratic (H := H) μ ((b : ℂ) • u + (a : ℂ) • v) := by
            have hvec1' : ((α : ℂ) • p + (β : ℂ) • q) = ((a : ℂ) • u + (b : ℂ) • v) := by simpa using hvec1
            have hvec2' : ((α : ℂ) • p - (β : ℂ) • q) = ((b : ℂ) • u + (a : ℂ) • v) := by simpa using hvec2
            rw [hvec1', hvec2']
      _ =
        frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) +
          ((a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v)
            - frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v)) := by rw [hsolve]
      _ =
        (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) +
          (frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) -
            frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v)) := by ring

  have hdiag :
      2 * α ^ 2 * frame_quadratic (H := H) μ p + 2 * β ^ 2 * frame_quadratic (H := H) μ q
        =
      (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) +
        (a * b) * quad2DCross μ u v 1 1 := by
    have ht : ‖((r⁻¹ : ℝ) : ℂ)‖ ^ 2 = (r⁻¹) ^ 2 := by simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hp :
        frame_quadratic (H := H) μ p = (r⁻¹) ^ 2 * frame_quadratic (H := H) μ (u + v) := by
      have := frame_quadratic_sq_hom (H := H) μ ((r⁻¹ : ℝ) : ℂ) (u + v)
      simpa [p, ht, mul_assoc] using this
    have hq' :
        frame_quadratic (H := H) μ q = (r⁻¹) ^ 2 * frame_quadratic (H := H) μ (u - v) := by
      have h := frame_quadratic_sq_hom (H := H) μ ((r⁻¹ : ℝ) : ℂ) (u - v)
      have h' :
          frame_quadratic (H := H) μ (r⁻¹ • (u - v))
            =
          (r⁻¹) ^ 2 * frame_quadratic (H := H) μ (u - v) := by
        simpa [RCLike.real_smul_eq_coe_smul (K := ℂ), ht, mul_assoc] using h
      simpa [q, RCLike.real_smul_eq_coe_smul (K := ℂ)] using h'
    have hrot11 := local_frame_quadratic_rotation (H := H) hdim μ u v hu hv huv 1 1
    have hsum11 :
        frame_quadratic (H := H) μ (u + v) + frame_quadratic (H := H) μ (u - v)
          =
        2 * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by
      simpa [pow_two, sub_eq_add_neg, add_assoc, add_comm, add_left_comm, one_add_one_eq_two] using hrot11
    set Qu : ℝ := frame_quadratic (H := H) μ u
    set Qv : ℝ := frame_quadratic (H := H) μ v
    set A0 : ℝ := frame_quadratic (H := H) μ (u + v)
    set B0 : ℝ := frame_quadratic (H := H) μ (u - v)
    have hAB : A0 + B0 = 2 * (Qu + Qv) := by simpa [A0, B0, Qu, Qv] using hsum11
    have hcross11 : A0 - B0 = quad2DCross μ u v 1 1 := by simp [quad2DCross, local_quad2DCross, A0, B0, sub_eq_add_neg]
    have hA :
        A0 = (Qu + Qv) + (1 / 2) * quad2DCross μ u v 1 1 := by
      have : 2 * A0 = 2 * (Qu + Qv) + (A0 - B0) := by linarith [hAB]
      linarith [this, hcross11]
    have hB :
        B0 = (Qu + Qv) - (1 / 2) * quad2DCross μ u v 1 1 := by
      have : 2 * B0 = 2 * (Qu + Qv) - (A0 - B0) := by linarith [hAB]
      linarith [this, hcross11]
    have hαβsum : α ^ 2 + β ^ 2 = a ^ 2 + b ^ 2 := by
      dsimp [α, β]
      have : α ^ 2 + β ^ 2 = ((a + b) ^ 2 + (a - b) ^ 2) * (r⁻¹ ^ 2) := by ring
      calc
        α ^ 2 + β ^ 2 = ((a + b) ^ 2 + (a - b) ^ 2) * (r⁻¹ ^ 2) := this
        _ = ((a + b) ^ 2 + (a - b) ^ 2) * (1 / 2) := by simp [hinv_sq]
        _ = a ^ 2 + b ^ 2 := by ring
    have hαβdiff : α ^ 2 - β ^ 2 = 2 * a * b := by
      dsimp [α, β]
      have : α ^ 2 - β ^ 2 = ((a + b) ^ 2 - (a - b) ^ 2) * (r⁻¹ ^ 2) := by ring
      calc
        α ^ 2 - β ^ 2 = ((a + b) ^ 2 - (a - b) ^ 2) * (r⁻¹ ^ 2) := this
        _ = ((a + b) ^ 2 - (a - b) ^ 2) * (1 / 2) := by simp [hinv_sq]
        _ = 2 * a * b := by ring
    calc
      2 * α ^ 2 * frame_quadratic (H := H) μ p + 2 * β ^ 2 * frame_quadratic (H := H) μ q
          = 2 * α ^ 2 * ((r⁻¹) ^ 2 * A0) + 2 * β ^ 2 * ((r⁻¹) ^ 2 * B0) := by simp [hp, hq', A0, B0]
      _ = 2 * ((r⁻¹) ^ 2) * (α ^ 2 * A0 + β ^ 2 * B0) := by ring
      _ = (α ^ 2 + β ^ 2) * (Qu + Qv) + (α ^ 2 - β ^ 2) * ((1 / 2) * quad2DCross μ u v 1 1) := by
          simp [hA, hB, hinv_sq]
          ring_nf
      _ = (a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) +
          (a * b) * quad2DCross μ u v 1 1 := by
          simp [Qu, Qv, hαβsum, hαβdiff]
          ring

  dsimp [quad2DDefect, local_quad2DDefect]
  calc
    quad2DExpr μ p q α β
        - (2 * α ^ 2 * frame_quadratic (H := H) μ p + 2 * β ^ 2 * frame_quadratic (H := H) μ q)
        =
      ((a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) +
          quad2DCross μ u v a b)
        -
      ((a ^ 2 + b ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) +
          (a * b) * quad2DCross μ u v 1 1) := by
        simp [hExpr, hdiag]
    _ = quad2DCross μ u v a b - (a * b) * quad2DCross μ u v 1 1 := by ring

lemma quad2DCross_hadamard_one_one
    (μ : FrameFunction H) (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    let r : ℝ := Real.sqrt 2
    let p : H := ((r⁻¹ : ℝ) : ℂ) • (u + v)
    let q : H := ((r⁻¹ : ℝ) : ℂ) • (u - v)
    quad2DCross μ p q 1 1
      =
    2 * frame_quadratic (H := H) μ u - 2 * frame_quadratic (H := H) μ v := by
  classical
  intro r p q
  have hrpos : (0 : ℝ) < r := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hpu : p + q = (r : ℂ) • u := by
    have htmp :
        p + q = ((2 / r : ℝ) : ℂ) • u := by
      have hsum :
          p + q = ((r⁻¹ : ℝ) : ℂ) • (2 • u) := by
        simp [p, q, RCLike.real_smul_eq_coe_smul (K := ℂ), sub_eq_add_neg, smul_add,
          add_assoc, add_left_comm, add_comm, two_smul, smul_smul, mul_comm, mul_left_comm,
          mul_assoc]
      calc
        p + q = ((r⁻¹ : ℝ) : ℂ) • (2 • u) := hsum
        _ = ((2 / r : ℝ) : ℂ) • u := by
              calc
                ((r⁻¹ : ℝ) : ℂ) • (2 • u)
                    = ((r⁻¹ : ℝ) : ℂ) • (u + u) := by simp [two_smul]
                _ = ((r⁻¹ : ℝ) : ℂ) • u + ((r⁻¹ : ℝ) : ℂ) • u := by simp [smul_add]
                _ = (((2 : ℝ) * r⁻¹) : ℂ) • u := by simp [two_mul, add_smul]
                _ = ((2 / r : ℝ) : ℂ) • u := by simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hscale : (2 / r : ℝ) = r := by
      have hr0 : (r : ℝ) ≠ 0 := by exact ne_of_gt hrpos
      field_simp [hr0]
      simp [hr2]
    rw [hscale] at htmp
    exact htmp
  have hpv : p - q = (r : ℂ) • v := by
    have htmp :
        p - q = ((2 / r : ℝ) : ℂ) • v := by
      have hdiff :
          p - q = ((r⁻¹ : ℝ) : ℂ) • (2 • v) := by
        simp [p, q, RCLike.real_smul_eq_coe_smul (K := ℂ), sub_eq_add_neg, smul_add,
          add_assoc, add_left_comm, add_comm, two_smul, smul_smul, mul_comm, mul_left_comm,
          mul_assoc]
      calc
        p - q = ((r⁻¹ : ℝ) : ℂ) • (2 • v) := hdiff
        _ = ((2 / r : ℝ) : ℂ) • v := by
              calc
                ((r⁻¹ : ℝ) : ℂ) • (2 • v)
                    = ((r⁻¹ : ℝ) : ℂ) • (v + v) := by simp [two_smul]
                _ = ((r⁻¹ : ℝ) : ℂ) • v + ((r⁻¹ : ℝ) : ℂ) • v := by simp [smul_add]
                _ = (((2 : ℝ) * r⁻¹) : ℂ) • v := by
                        simpa [two_mul, add_smul] using
                          (add_smul ((r⁻¹ : ℝ) : ℂ) ((r⁻¹ : ℝ) : ℂ) v).symm
                _ = ((2 / r : ℝ) : ℂ) • v := by
                        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have hscale : (2 / r : ℝ) = r := by
      have hr0 : (r : ℝ) ≠ 0 := by exact ne_of_gt hrpos
      field_simp [hr0]
      simp [hr2]
    simpa [hscale] using htmp
  have hQu' :
      frame_quadratic (H := H) μ (r • u)
        = (r ^ 2) * frame_quadratic (H := H) μ u := by
    change frame_quadratic (H := H) μ ((r : ℂ) • u)
        = (r ^ 2) * frame_quadratic (H := H) μ u
    have ht : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hrpos), sq_abs]
    simpa [ht, mul_assoc] using (frame_quadratic_sq_hom (H := H) μ (r : ℂ) u)
  have hQv' :
      frame_quadratic (H := H) μ (r • v)
        = (r ^ 2) * frame_quadratic (H := H) μ v := by
    change frame_quadratic (H := H) μ ((r : ℂ) • v)
        = (r ^ 2) * frame_quadratic (H := H) μ v
    have ht : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hrpos), sq_abs]
    simpa [ht, mul_assoc] using (frame_quadratic_sq_hom (H := H) μ (r : ℂ) v)
  dsimp [quad2DCross, local_quad2DCross]
  simp [one_smul, hpu, hpv, hQu', hQv', hr2]

lemma quad2DCross_hadamard_as_defect
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (s t : ℝ) :
    let r : ℝ := Real.sqrt 2
    let p : H := ((r⁻¹ : ℝ) : ℂ) • (u + v)
    let q : H := ((r⁻¹ : ℝ) : ℂ) • (u - v)
    let A : ℝ := (s + t) * r⁻¹
    let B : ℝ := (s - t) * r⁻¹
    quad2DCross μ p q s t
      =
    quad2DDefect μ u v A B + (A ^ 2 - B ^ 2) * (frame_quadratic (H := H) μ u - frame_quadratic (H := H) μ v) := by
  classical
  intro r p q A B
  have hvec1 :
      ((s : ℂ) • p + (t : ℂ) • q) = (A : ℂ) • u + (B : ℂ) • v := by
    calc
      (s : ℂ) • p + (t : ℂ) • q
          = (s : ℂ) • (((r⁻¹ : ℝ) : ℂ) • (u + v)) + (t : ℂ) • (((r⁻¹ : ℝ) : ℂ) • (u - v)) := by dsimp [p, q]
      _ = ((s : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • (u + v) + ((t : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • (u - v) := by
              simp [smul_smul]
      _ = ((s : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • u + ((s : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • v +
            (((t : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • u - ((t : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • v) := by
              simp [smul_add, smul_sub]
      _ = (((s : ℂ) + (t : ℂ)) * ((r⁻¹ : ℝ) : ℂ)) • u +
            (((s : ℂ) - (t : ℂ)) * ((r⁻¹ : ℝ) : ℂ)) • v := by
              set c : ℂ := ((r⁻¹ : ℝ) : ℂ)
              have hu' :
                  ((s : ℂ) * c) • u + ((t : ℂ) * c) • u = (((s : ℂ) * c + (t : ℂ) * c) : ℂ) • u := by
                simpa using (add_smul ((s : ℂ) * c) ((t : ℂ) * c) u).symm
              have hv' :
                  ((s : ℂ) * c) • v - ((t : ℂ) * c) • v = (((s : ℂ) * c - (t : ℂ) * c) : ℂ) • v := by
                simpa using (sub_smul ((s : ℂ) * c) ((t : ℂ) * c) v).symm
              have hsc1 : (s : ℂ) * c + (t : ℂ) * c = ((s : ℂ) + (t : ℂ)) * c := by ring
              have hsc2 : (s : ℂ) * c - (t : ℂ) * c = ((s : ℂ) - (t : ℂ)) * c := by ring
              calc
                ((s : ℂ) * c) • u + ((s : ℂ) * c) • v + (((t : ℂ) * c) • u - ((t : ℂ) * c) • v)
                    =
                  (((s : ℂ) * c) • u + ((t : ℂ) * c) • u) + (((s : ℂ) * c) • v - ((t : ℂ) * c) • v) := by
                    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                _ =
                  (((s : ℂ) * c + (t : ℂ) * c) : ℂ) • u + (((s : ℂ) * c - (t : ℂ) * c) : ℂ) • v := by
                    simp [hu', hv', add_assoc, add_comm, add_left_comm]
                _ =
                  (((s : ℂ) + (t : ℂ)) * c) • u + (((s : ℂ) - (t : ℂ)) * c) • v := by
                    simp [hsc1, hsc2]
      _ = (A : ℂ) • u + (B : ℂ) • v := by
              simp [A, B, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm,
                add_assoc, add_comm, add_left_comm]
  have hvec2 :
      ((s : ℂ) • p - (t : ℂ) • q) = (B : ℂ) • u + (A : ℂ) • v := by
    calc
      (s : ℂ) • p - (t : ℂ) • q
          = (s : ℂ) • (((r⁻¹ : ℝ) : ℂ) • (u + v)) - (t : ℂ) • (((r⁻¹ : ℝ) : ℂ) • (u - v)) := by dsimp [p, q]
      _ = ((s : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • (u + v) - ((t : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • (u - v) := by
              simp [smul_smul]
      _ = ((s : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • u + ((s : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • v -
            (((t : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • u - ((t : ℂ) * ((r⁻¹ : ℝ) : ℂ)) • v) := by
              simp [smul_add, smul_sub]
      _ = (((s : ℂ) - (t : ℂ)) * ((r⁻¹ : ℝ) : ℂ)) • u +
            (((s : ℂ) + (t : ℂ)) * ((r⁻¹ : ℝ) : ℂ)) • v := by
              set c : ℂ := ((r⁻¹ : ℝ) : ℂ)
              have hu' :
                  ((s : ℂ) * c) • u - ((t : ℂ) * c) • u = (((s : ℂ) * c - (t : ℂ) * c) : ℂ) • u := by
                simpa using (sub_smul ((s : ℂ) * c) ((t : ℂ) * c) u).symm
              have hv' :
                  ((s : ℂ) * c) • v + ((t : ℂ) * c) • v = (((s : ℂ) * c + (t : ℂ) * c) : ℂ) • v := by
                simpa using (add_smul ((s : ℂ) * c) ((t : ℂ) * c) v).symm
              have hsc1 : (s : ℂ) * c - (t : ℂ) * c = ((s : ℂ) - (t : ℂ)) * c := by ring
              have hsc2 : (s : ℂ) * c + (t : ℂ) * c = ((s : ℂ) + (t : ℂ)) * c := by ring
              calc
                ((s : ℂ) * c) • u + ((s : ℂ) * c) • v - (((t : ℂ) * c) • u - ((t : ℂ) * c) • v)
                    =
                  (((s : ℂ) * c) • u - ((t : ℂ) * c) • u) + (((s : ℂ) * c) • v + ((t : ℂ) * c) • v) := by
                    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                _ =
                  (((s : ℂ) * c - (t : ℂ) * c) : ℂ) • u + (((s : ℂ) * c + (t : ℂ) * c) : ℂ) • v := by
                    simp [hu', hv', add_assoc, add_comm, add_left_comm]
                _ =
                  (((s : ℂ) - (t : ℂ)) * c) • u + (((s : ℂ) + (t : ℂ)) * c) • v := by
                    simp [hsc1, hsc2]
      _ = (B : ℂ) • u + (A : ℂ) • v := by
              simp [A, B, sub_eq_add_neg, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm,
                add_assoc, add_comm, add_left_comm]
  have hrot' :
      frame_quadratic (H := H) μ ((B : ℂ) • u + (A : ℂ) • v)
        =
      (A ^ 2 + B ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v)
        - frame_quadratic (H := H) μ ((A : ℂ) • u - (B : ℂ) • v) := by
    have hswap := local_frame_quadratic_rotation (H := H) hdim μ u v hu hv huv B A
    linarith
  dsimp [quad2DCross, local_quad2DCross]
  have hQ1 :
      frame_quadratic (H := H) μ ((s : ℂ) • p + (t : ℂ) • q)
        =
      frame_quadratic (H := H) μ ((A : ℂ) • u + (B : ℂ) • v) := congrArg (fun x : H => frame_quadratic (H := H) μ x) hvec1
  have hQ2 :
      frame_quadratic (H := H) μ ((s : ℂ) • p - (t : ℂ) • q)
        =
      frame_quadratic (H := H) μ ((B : ℂ) • u + (A : ℂ) • v) := congrArg (fun x : H => frame_quadratic (H := H) μ x) hvec2
  calc
    frame_quadratic (H := H) μ ((s : ℂ) • p + (t : ℂ) • q)
        - frame_quadratic (H := H) μ ((s : ℂ) • p - (t : ℂ) • q)
        =
      frame_quadratic (H := H) μ ((A : ℂ) • u + (B : ℂ) • v)
        - frame_quadratic (H := H) μ ((B : ℂ) • u + (A : ℂ) • v) := by rw [hQ1, hQ2]
    _ =
      frame_quadratic (H := H) μ ((A : ℂ) • u + (B : ℂ) • v)
        - ((A ^ 2 + B ^ 2) * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v)
            - frame_quadratic (H := H) μ ((A : ℂ) • u - (B : ℂ) • v)) := by rw [hrot']
    _ = quad2DDefect μ u v A B + (A ^ 2 - B ^ 2) * (frame_quadratic (H := H) μ u - frame_quadratic (H := H) μ v) := by
      dsimp [quad2DDefect, quad2DExpr, local_quad2DDefect, local_quad2DExpr]
      ring_nf

/-!
## Step 1: Four-Point Linear Algebra

Given orthonormal u, v, w and reals a, b, c with c² = a² - b²,
define four vectors x₁ = au+bv+cw, x₂ = au+bv-cw, x₃ = au-bv+cw, x₄ = au-bv-cw.
We prove orthogonality, norm equality, and sum/diff identities.
-/

lemma fourPoint_inner_x1_x4
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0) (hvw : inner (𝕜 := ℂ) v w = 0)
    (a b c : ℝ) (hc : c ^ 2 = a ^ 2 - b ^ 2) :
    inner (𝕜 := ℂ)
      ((a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • w)
      ((a : ℂ) • u - (b : ℂ) • v - (c : ℂ) • w) = 0 := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := inner_eq_zero_symm.1 huv
  have hwu : inner (𝕜 := ℂ) w u = 0 := inner_eq_zero_symm.1 huw
  have hwv : inner (𝕜 := ℂ) w v = 0 := inner_eq_zero_symm.1 hvw
  have huu : inner (𝕜 := ℂ) u u = (1 : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, hu]
  have hvv : inner (𝕜 := ℂ) v v = (1 : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, hv]
  have hww : inner (𝕜 := ℂ) w w = (1 : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, hw]
  simp [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, huv, huw, hvw, hvu, hwu, hwv, huu, hvv, hww,
    hu, hv, hw]
  norm_cast; linarith [hc]

lemma fourPoint_inner_x2_x3
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0) (hvw : inner (𝕜 := ℂ) v w = 0)
    (a b c : ℝ) (hc : c ^ 2 = a ^ 2 - b ^ 2) :
    inner (𝕜 := ℂ)
      ((a : ℂ) • u + (b : ℂ) • v - (c : ℂ) • w)
      ((a : ℂ) • u - (b : ℂ) • v + (c : ℂ) • w) = 0 := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := inner_eq_zero_symm.1 huv
  have hwu : inner (𝕜 := ℂ) w u = 0 := inner_eq_zero_symm.1 huw
  have hwv : inner (𝕜 := ℂ) w v = 0 := inner_eq_zero_symm.1 hvw
  have huu : inner (𝕜 := ℂ) u u = (1 : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, hu]
  have hvv : inner (𝕜 := ℂ) v v = (1 : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, hv]
  have hww : inner (𝕜 := ℂ) w w = (1 : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, hw]
  simp [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, huv, huw, hvw, hvu, hwu, hwv, huu, hvv, hww,
    hu, hv, hw]
  norm_cast; linarith [hc]

lemma fourPoint_norm_x1_eq_x4
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0) (hvw : inner (𝕜 := ℂ) v w = 0)
    (a b c : ℝ) :
    ‖(a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • w‖ =
    ‖(a : ℂ) • u - (b : ℂ) • v - (c : ℂ) • w‖ := by
  -- Rewrite as au + z and au + (-z) where z = bv + cw
  have e1 : (a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • w =
    (a : ℂ) • u + ((b : ℂ) • v + (c : ℂ) • w) := by abel
  have e4 : (a : ℂ) • u - (b : ℂ) • v - (c : ℂ) • w =
    (a : ℂ) • u + (-((b : ℂ) • v + (c : ℂ) • w)) := by
    simp only [sub_eq_add_neg, neg_add]; abel
  rw [e1, e4]
  have h_orth : inner (𝕜 := ℂ) ((a : ℂ) • u) ((b : ℂ) • v + (c : ℂ) • w) = 0 := by
    simp [huv, huw]
  have h1 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((a : ℂ) • u) ((b : ℂ) • v + (c : ℂ) • w) h_orth
  have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((a : ℂ) • u) (-((b : ℂ) • v + (c : ℂ) • w))
    (show inner (𝕜 := ℂ) ((a : ℂ) • u) (-((b : ℂ) • v + (c : ℂ) • w)) = 0 by
      rw [inner_neg_right, h_orth, neg_zero])
  simp only [norm_neg] at h2
  exact norm_eq_of_sq_eq _ _ (by linarith)

lemma fourPoint_norm_x2_eq_x3
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0) (hvw : inner (𝕜 := ℂ) v w = 0)
    (a b c : ℝ) :
    ‖(a : ℂ) • u + (b : ℂ) • v - (c : ℂ) • w‖ =
    ‖(a : ℂ) • u - (b : ℂ) • v + (c : ℂ) • w‖ := by
  -- Decompose as au + z and au + (-z) where z = bv - cw
  have e2 : (a : ℂ) • u + (b : ℂ) • v - (c : ℂ) • w =
    (a : ℂ) • u + ((b : ℂ) • v - (c : ℂ) • w) := by abel
  have e3 : (a : ℂ) • u - (b : ℂ) • v + (c : ℂ) • w =
    (a : ℂ) • u + (-((b : ℂ) • v - (c : ℂ) • w)) := by
    simp only [sub_eq_add_neg, neg_add, neg_neg]; abel
  rw [e2, e3]
  have h_orth : inner (𝕜 := ℂ) ((a : ℂ) • u) ((b : ℂ) • v - (c : ℂ) • w) = 0 := by
    simp [huv, huw]
  have h1 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((a : ℂ) • u) ((b : ℂ) • v - (c : ℂ) • w) h_orth
  have h2 := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((a : ℂ) • u) (-((b : ℂ) • v - (c : ℂ) • w))
    (show inner (𝕜 := ℂ) ((a : ℂ) • u) (-((b : ℂ) • v - (c : ℂ) • w)) = 0 by
      rw [inner_neg_right, h_orth, neg_zero])
  simp only [norm_neg] at h2
  exact norm_eq_of_sq_eq _ _ (by linarith)

lemma fourPoint_sum_x1_x4
    (u v w : H) (a b c : ℝ) :
    ((a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • w) +
    ((a : ℂ) • u - (b : ℂ) • v - (c : ℂ) • w) =
    (2 * a : ℂ) • u := by
  have : (2 * a : ℂ) • u = (2 : ℂ) • ((a : ℂ) • u) := by rw [← smul_smul]
  rw [this, two_smul]; simp [sub_eq_add_neg]; abel

lemma fourPoint_diff_x1_x4
    (u v w : H) (a b c : ℝ) :
    ((a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • w) -
    ((a : ℂ) • u - (b : ℂ) • v - (c : ℂ) • w) =
    (2 * b : ℂ) • v + (2 * c : ℂ) • w := by
  have hb : (2 * b : ℂ) • v = (2 : ℂ) • ((b : ℂ) • v) := by rw [← smul_smul]
  have hc : (2 * c : ℂ) • w = (2 : ℂ) • ((c : ℂ) • w) := by rw [← smul_smul]
  rw [hb, hc, two_smul, two_smul]; simp [sub_eq_add_neg]; abel

lemma fourPoint_sum_x2_x3
    (u v w : H) (a b c : ℝ) :
    ((a : ℂ) • u + (b : ℂ) • v - (c : ℂ) • w) +
    ((a : ℂ) • u - (b : ℂ) • v + (c : ℂ) • w) =
    (2 * a : ℂ) • u := by
  have : (2 * a : ℂ) • u = (2 : ℂ) • ((a : ℂ) • u) := by rw [← smul_smul]
  rw [this, two_smul]; simp [sub_eq_add_neg]; abel

lemma fourPoint_diff_x2_x3
    (u v w : H) (a b c : ℝ) :
    ((a : ℂ) • u + (b : ℂ) • v - (c : ℂ) • w) -
    ((a : ℂ) • u - (b : ℂ) • v + (c : ℂ) • w) =
    (2 * b : ℂ) • v - (2 * c : ℂ) • w := by
  have hb : (2 * b : ℂ) • v = (2 : ℂ) • ((b : ℂ) • v) := by rw [← smul_smul]
  have hc : (2 * c : ℂ) • w = (2 : ℂ) • ((c : ℂ) • w) := by rw [← smul_smul]
  rw [hb, hc, two_smul, two_smul]; simp [sub_eq_add_neg]; abel

/-!
## Step 1.5: Restricted parallelogram law for orthogonal equal-norm vectors

Proved directly from `frame_quadratic_orthonormal_sum_eq_of_span_eq` (C3)
and `frame_quadratic_sq_hom` (A2), bypassing the full rotation identity.
-/

set_option maxHeartbeats 400000 in
lemma frame_quadratic_parallelogram_of_orthogonal_eq_norm
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (x y : H) (hxy : inner (𝕜 := ℂ) x y = 0) (hn : ‖x‖ = ‖y‖) :
    frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
      =
    2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by
  classical
  by_cases hx : x = 0
  · subst hx
    simp [frame_quadratic_zero (H := H) μ, frame_quadratic_neg (H := H) μ,
      sub_eq_add_neg, two_mul]
  by_cases hy : y = 0
  · subst hy
    simp [frame_quadratic_zero (H := H) μ, frame_quadratic_neg (H := H) μ,
      sub_eq_add_neg, two_mul]
  -- Set r = ‖x‖ = ‖y‖ and normalize.
  set r : ℝ := ‖x‖ with hr_def
  have hr0 : r ≠ 0 := by simpa [r, norm_eq_zero] using hx
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0
  have hrpos : 0 < r := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hr0)
  set u : H := ((r : ℂ)⁻¹) • x with hu_def
  set v : H := ((r : ℂ)⁻¹) • y with hv_def
  -- u, v are orthonormal
  have hnorm_inv : ‖((r : ℂ)⁻¹)‖ = r⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hrpos)]
  have hu : ‖u‖ = 1 := by
    calc ‖u‖ = ‖((r : ℂ)⁻¹)‖ * ‖x‖ := by simp [u, norm_smul]
      _ = r⁻¹ * r := by simp [hnorm_inv, r]
      _ = 1 := by field_simp
  have hv : ‖v‖ = 1 := by
    calc ‖v‖ = ‖((r : ℂ)⁻¹)‖ * ‖y‖ := by simp [v, norm_smul]
      _ = r⁻¹ * r := by rw [hnorm_inv, hn]
      _ = 1 := by field_simp
  have huv : inner (𝕜 := ℂ) u v = 0 := by simp [u, v, hxy]
  -- x = r•u, y = r•v
  have hxu : (r : ℂ) • u = x := by simp [u, smul_smul, hr0']
  have hyv : (r : ℂ) • v = y := by simp [v, smul_smul, hr0']
  -- Hadamard pair: p = (u+v)/√2, q = (u-v)/√2
  let s2 := Real.sqrt 2
  have hs2pos : 0 < s2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have hs2ne : s2 ≠ 0 := ne_of_gt hs2pos
  have hs2ne' : (s2 : ℂ) ≠ 0 := by exact_mod_cast hs2ne
  have hs2sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  set p : H := ((s2 : ℂ)⁻¹) • (u + v)
  set q : H := ((s2 : ℂ)⁻¹) • (u - v)
  -- p, q orthonormal
  have hinv_norm : ‖((s2 : ℂ)⁻¹)‖ = s2⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hs2pos)]
  have hvu : inner (𝕜 := ℂ) v u = 0 := inner_eq_zero_symm.1 huv
  have h_uv_norm_sq : ‖u + v‖ ^ 2 = 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := u) (y := v) huv
    simp only [hu, hv, sq] at h ⊢; nlinarith
  have h_uv_sub_norm_sq : ‖u - v‖ ^ 2 = 2 := by
    have horth : inner (𝕜 := ℂ) u (-v) = 0 := by simp [huv]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := u) (y := -v) horth
    simp only [hu, hv, norm_neg, sub_eq_add_neg, sq] at h ⊢; nlinarith
  have h_uv_norm : ‖u + v‖ = s2 := by
    have h1 := h_uv_norm_sq
    nlinarith [norm_nonneg (u + v), hs2sq, sq_nonneg (‖u + v‖ - s2)]
  have h_uv_sub_norm : ‖u - v‖ = s2 := by
    have h1 := h_uv_sub_norm_sq
    nlinarith [norm_nonneg (u - v), hs2sq, sq_nonneg (‖u - v‖ - s2)]
  have hp : ‖p‖ = 1 := by
    simp only [p]; rw [norm_smul, hinv_norm, h_uv_norm]; field_simp
  have hq : ‖q‖ = 1 := by
    simp only [q]; rw [norm_smul, hinv_norm, h_uv_sub_norm]; field_simp
  have hpq : inner (𝕜 := ℂ) p q = 0 := by
    simp [p, q, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, inner_self_eq_norm_sq_to_K, hu, hv, huv, hvu]
  -- Span equality: span{u,v} = span{p,q}
  have h_span : Submodule.span ℂ ({u, v} : Set H) = Submodule.span ℂ ({p, q} : Set H) := by
    let Su := Submodule.span ℂ ({u, v} : Set H)
    let Sp := Submodule.span ℂ ({p, q} : Set H)
    apply le_antisymm
    · -- u,v ∈ span{p,q}
      refine Submodule.span_le.2 ?_
      intro z hz; rcases (by simpa using hz : z = u ∨ z = v) with rfl | rfl
      · -- u = (s2/2)(p+q)
        have hp_mem : p ∈ Sp := Submodule.subset_span (by simp)
        have hq_mem : q ∈ Sp := Submodule.subset_span (by simp)
        have hcoeff : (s2 / 2 : ℝ) * s2⁻¹ = (1 / 2 : ℝ) := by field_simp
        have hcoeffC : ((s2 / 2 : ℝ) : ℂ) * ((s2 : ℝ)⁻¹ : ℂ) = (1 / 2 : ℂ) := by
          simpa [Complex.ofReal_mul, Complex.ofReal_inv] using congrArg Complex.ofReal hcoeff
        have hcoeffC' : ((s2 : ℂ) / 2) * (s2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
          field_simp [hs2ne']
        have : u = ((s2 / 2 : ℝ) : ℂ) • p + ((s2 / 2 : ℝ) : ℂ) • q := by
          have hsum : (u + v) + (u - v) = (2 : ℂ) • u := by
            simp [sub_eq_add_neg, two_smul, add_assoc, add_left_comm, add_comm]
          refine Eq.symm ?_
          calc
            ((s2 / 2 : ℝ) : ℂ) • p + ((s2 / 2 : ℝ) : ℂ) • q
                = (((s2 / 2 : ℝ) : ℂ) * ((s2 : ℝ)⁻¹ : ℂ)) • (u + v)
                  + (((s2 / 2 : ℝ) : ℂ) * ((s2 : ℝ)⁻¹ : ℂ)) • (u - v) := by
                    simp [p, q, smul_smul]
            _ = (1 / 2 : ℂ) • (u + v) + (1 / 2 : ℂ) • (u - v) := by
                  simpa [div_eq_mul_inv, hcoeffC'] using
                    show (((s2 : ℂ) / 2) * (s2 : ℂ)⁻¹) • (u + v) +
                        (((s2 : ℂ) / 2) * (s2 : ℂ)⁻¹) • (u - v)
                        = (1 / 2 : ℂ) • (u + v) + (1 / 2 : ℂ) • (u - v) by
                      simp [hcoeffC']
            _ = u := by
                  have hhalf : (1 / 2 : ℂ) • v + (1 / 2 : ℂ) • (u - v) = (1 / 2 : ℂ) • u := by
                    simp [smul_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
                  calc
                    (1 / 2 : ℂ) • (u + v) + (1 / 2 : ℂ) • (u - v)
                        = (1 / 2 : ℂ) • u + ((1 / 2 : ℂ) • v + (1 / 2 : ℂ) • (u - v)) := by
                            simp [smul_add, add_assoc]
                    _ = (1 / 2 : ℂ) • u + (1 / 2 : ℂ) • u := by rw [hhalf]
                    _ = u := by
                          calc
                            (1 / 2 : ℂ) • u + (1 / 2 : ℂ) • u = ((1 / 2 : ℂ) + (1 / 2 : ℂ)) • u := by
                              simp [add_smul]
                            _ = (1 : ℂ) • u := by norm_num
                            _ = u := by simp
        rw [this]
        exact Sp.add_mem (Sp.smul_mem _ hp_mem) (Sp.smul_mem _ hq_mem)
      · -- v = (s2/2)(p-q)
        have hp_mem : p ∈ Sp := Submodule.subset_span (by simp)
        have hq_mem : q ∈ Sp := Submodule.subset_span (by simp)
        have hcoeff : (s2 / 2 : ℝ) * s2⁻¹ = (1 / 2 : ℝ) := by field_simp
        have hcoeffC : ((s2 / 2 : ℝ) : ℂ) * ((s2 : ℝ)⁻¹ : ℂ) = (1 / 2 : ℂ) := by
          simpa [Complex.ofReal_mul, Complex.ofReal_inv] using congrArg Complex.ofReal hcoeff
        have hcoeffC' : ((s2 : ℂ) / 2) * (s2 : ℂ)⁻¹ = (1 / 2 : ℂ) := by
          field_simp [hs2ne']
        have : v = ((s2 / 2 : ℝ) : ℂ) • p - ((s2 / 2 : ℝ) : ℂ) • q := by
          have hdiff : (u + v) - (u - v) = (2 : ℂ) • v := by
            simp [sub_eq_add_neg, two_smul, add_assoc, add_left_comm, add_comm]
          refine Eq.symm ?_
          calc
            ((s2 / 2 : ℝ) : ℂ) • p - ((s2 / 2 : ℝ) : ℂ) • q
                = (((s2 / 2 : ℝ) : ℂ) * ((s2 : ℝ)⁻¹ : ℂ)) • (u + v)
                  - (((s2 / 2 : ℝ) : ℂ) * ((s2 : ℝ)⁻¹ : ℂ)) • (u - v) := by
                    simp [p, q, smul_smul]
            _ = (1 / 2 : ℂ) • (u + v) - (1 / 2 : ℂ) • (u - v) := by
                  simpa [div_eq_mul_inv, hcoeffC'] using
                    show (((s2 : ℂ) / 2) * (s2 : ℂ)⁻¹) • (u + v) -
                        (((s2 : ℂ) / 2) * (s2 : ℂ)⁻¹) • (u - v)
                        = (1 / 2 : ℂ) • (u + v) - (1 / 2 : ℂ) • (u - v) by
                      simp [hcoeffC']
            _ = (1 / 2 : ℂ) • ((u + v) - (u - v)) := by simp [smul_sub]
            _ = (1 / 2 : ℂ) • ((2 : ℂ) • v) := by rw [hdiff]
            _ = v := by simp
        rw [this]
        exact Sp.sub_mem (Sp.smul_mem _ hp_mem) (Sp.smul_mem _ hq_mem)
    · -- p,q ∈ span{u,v}: obvious since p,q are scalar multiples of u±v
      refine Submodule.span_le.2 ?_
      intro z hz; rcases (by simpa using hz : z = p ∨ z = q) with rfl | rfl
      · exact Su.smul_mem _ (Su.add_mem (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp)))
      · exact Su.smul_mem _ (Su.sub_mem (Submodule.subset_span (by simp))
          (Submodule.subset_span (by simp)))
  -- Apply C3's plane-sum invariance
  have hsum := frame_quadratic_orthonormal_sum_eq_of_span_eq (H := H)
    hdim μ u v p q hu hv huv hp hq hpq h_span
  -- Homogeneity: Q(r•u) = r²Q(u) etc.
  have ht : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hQx : frame_quadratic (H := H) μ x = r ^ 2 * frame_quadratic (H := H) μ u := by
    have := frame_quadratic_sq_hom (H := H) μ (r : ℂ) u
    simpa [hxu, ht] using this
  have hQy : frame_quadratic (H := H) μ y = r ^ 2 * frame_quadratic (H := H) μ v := by
    have := frame_quadratic_sq_hom (H := H) μ (r : ℂ) v
    simpa [hyv, ht] using this
  -- x+y = r•(u+v), x-y = r•(u-v)
  have hxy_sum : x + y = (r : ℂ) • (u + v) := by rw [← hxu, ← hyv]; simp [smul_add]
  have hxy_diff : x - y = (r : ℂ) • (u - v) := by rw [← hxu, ← hyv]; simp [smul_sub]
  have hQsum : frame_quadratic (H := H) μ (x + y) = r ^ 2 * frame_quadratic (H := H) μ (u + v) := by
    have := frame_quadratic_sq_hom (H := H) μ (r : ℂ) (u + v)
    simpa [hxy_sum, ht] using this
  have hQdiff : frame_quadratic (H := H) μ (x - y) = r ^ 2 * frame_quadratic (H := H) μ (u - v) := by
    have := frame_quadratic_sq_hom (H := H) μ (r : ℂ) (u - v)
    simpa [hxy_diff, ht] using this
  -- Q(u+v) = s2²·Q(p) = 2·Q(p) and Q(u-v) = 2·Q(q)
  have ht2 : ‖(s2 : ℂ)‖ ^ 2 = 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hs2pos), hs2sq]
  have hQ_uv : frame_quadratic (H := H) μ (u + v) = 2 * frame_quadratic (H := H) μ p := by
    have hspu : (s2 : ℂ) • p = u + v := by simp [p, smul_smul, hs2ne']
    have h := frame_quadratic_sq_hom (H := H) μ (s2 : ℂ) p
    rw [hspu, ht2] at h; exact h
  have hQ_uv_sub : frame_quadratic (H := H) μ (u - v) = 2 * frame_quadratic (H := H) μ q := by
    have hsqu : (s2 : ℂ) • q = u - v := by simp [q, smul_smul, hs2ne']
    have h := frame_quadratic_sq_hom (H := H) μ (s2 : ℂ) q
    rw [hsqu, ht2] at h; exact h
  -- Combine everything
  calc frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
      = r ^ 2 * (2 * frame_quadratic (H := H) μ p)
        + r ^ 2 * (2 * frame_quadratic (H := H) μ q) := by rw [hQsum, hQdiff, hQ_uv, hQ_uv_sub]
    _ = 2 * r ^ 2 * (frame_quadratic (H := H) μ p + frame_quadratic (H := H) μ q) := by ring
    _ = 2 * r ^ 2 * (frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v) := by rw [hsum]
    _ = 2 * (r ^ 2 * frame_quadratic (H := H) μ u) + 2 * (r ^ 2 * frame_quadratic (H := H) μ v) := by ring
    _ = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by rw [← hQx, ← hQy]

/-!
## Step 2: The 3D Parallelogram Applications

Apply `frame_quadratic_parallelogram_of_orthogonal_eq_norm` to the pairs
(x₁,x₄) and (x₂,x₃), then rewrite using the Step 1 sum/diff lemmas.
-/

lemma threeD_pair1
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0) (hvw : inner (𝕜 := ℂ) v w = 0)
    (a b c : ℝ) (hc : c ^ 2 = a ^ 2 - b ^ 2) :
    frame_quadratic (H := H) μ ((2 * a : ℂ) • u) +
      frame_quadratic (H := H) μ ((2 * b : ℂ) • v + (2 * c : ℂ) • w) =
    2 * frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • w) +
    2 * frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v - (c : ℂ) • w) := by
  have h_ortho :=
    fourPoint_inner_x1_x4 (u := u) (v := v) (w := w) hu hv hw huv huw hvw a b c hc
  have h_norm :=
    fourPoint_norm_x1_eq_x4 (u := u) (v := v) (w := w) hu hv hw huv huw hvw a b c
  have h_sum  := fourPoint_sum_x1_x4 (u := u) (v := v) (w := w) a b c
  have h_diff := fourPoint_diff_x1_x4 (u := u) (v := v) (w := w) a b c
  have h_para :=
    frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ
      ((a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • w)
      ((a : ℂ) • u - (b : ℂ) • v - (c : ℂ) • w)
      h_ortho h_norm
  rw [h_sum, h_diff] at h_para
  exact h_para

lemma threeD_pair2
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0) (hvw : inner (𝕜 := ℂ) v w = 0)
    (a b c : ℝ) (hc : c ^ 2 = a ^ 2 - b ^ 2) :
    frame_quadratic (H := H) μ ((2 * a : ℂ) • u) +
      frame_quadratic (H := H) μ ((2 * b : ℂ) • v - (2 * c : ℂ) • w) =
    2 * frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v - (c : ℂ) • w) +
    2 * frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v + (c : ℂ) • w) := by
  have h_ortho :=
    fourPoint_inner_x2_x3 (u := u) (v := v) (w := w) hu hv hw huv huw hvw a b c hc
  have h_norm :=
    fourPoint_norm_x2_eq_x3 (u := u) (v := v) (w := w) hu hv hw huv huw hvw a b c
  have h_sum  := fourPoint_sum_x2_x3 (u := u) (v := v) (w := w) a b c
  have h_diff := fourPoint_diff_x2_x3 (u := u) (v := v) (w := w) a b c
  have h_para :=
    frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ
      ((a : ℂ) • u + (b : ℂ) • v - (c : ℂ) • w)
      ((a : ℂ) • u - (b : ℂ) • v + (c : ℂ) • w)
      h_ortho h_norm
  rw [h_sum, h_diff] at h_para
  exact h_para


/-!
## Step 3: The Cross-Plane Sum Identity

From Step 2 (for `c^2 = a^2 - b^2`), we have the two 3D parallelogram consequences
for the pairs `(x₁,x₄)` and `(x₂,x₃)`. Unwinding the homogeneity `Q(t•x)=t^2 Q(x)`
for real `t`, and grouping the `v,w` terms via `local_quad2DDefect`, yields:

  Q(x₁)+Q(x₂)+Q(x₃)+Q(x₄)
    = 4 a^2 Q(u) + 4 b^2 Q(v) + 4 c^2 Q(w) + 2·D_{vw}(b,c).

This lemma is *purely algebraic* given Step 2.
-/

/-- Scaling of the local 2D defect under `(a,b) ↦ (t a, t b)`.

This is just homogeneity of `frame_quadratic` on each term. -/
lemma local_quad2DDefect_hom
    (μ : FrameFunction H) (u v : H) (t a b : ℝ) :
    local_quad2DDefect μ u v (t * a) (t * b) =
      t ^ 2 * local_quad2DDefect μ u v a b := by
  classical
  -- Scale each `frame_quadratic` term.
  have h1 : frame_quadratic (H := H) μ ((((t * a : ℝ) : ℂ) • u) + (((t * b : ℝ) : ℂ) • v)) =
      t ^ 2 * frame_quadratic (H := H) μ ((↑a : ℂ) • u + (↑b : ℂ) • v) := by
    have h := frame_quadratic_sq_hom (H := H) μ (↑t : ℂ) ((↑a : ℂ) • u + (↑b : ℂ) • v)
    have hx :
        ((↑t * ↑a : ℂ) • u + (↑t * ↑b : ℂ) • v)
          = ((((t * a : ℝ) : ℂ) • u) + (((t * b : ℝ) : ℂ) • v)) := by
      simp
    simpa [hx, smul_add, smul_smul, mul_assoc, mul_left_comm, mul_comm,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, pow_two] using h
  have h2 : frame_quadratic (H := H) μ ((((t * a : ℝ) : ℂ) • u) - (((t * b : ℝ) : ℂ) • v)) =
      t ^ 2 * frame_quadratic (H := H) μ ((↑a : ℂ) • u - (↑b : ℂ) • v) := by
    have h := frame_quadratic_sq_hom (H := H) μ (↑t : ℂ) ((↑a : ℂ) • u - (↑b : ℂ) • v)
    have hx :
        ((↑t * ↑a : ℂ) • u - (↑t * ↑b : ℂ) • v)
          = ((((t * a : ℝ) : ℂ) • u) - (((t * b : ℝ) : ℂ) • v)) := by
      simp
    simpa [hx, smul_sub, smul_smul, mul_assoc, mul_left_comm, mul_comm,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, pow_two] using h
  -- Expand and substitute.
  simp [local_quad2DDefect, local_quad2DExpr] at h1 h2 ⊢
  rw [h1, h2]
  ring

/-- **Step 3**: the 3D four-point sum identity.

This is the identity marked ★ in the comment block above. -/
lemma threeD_sum_identity
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0) (hvw : inner (𝕜 := ℂ) v w = 0)
    (a b c : ℝ) (hc : c ^ 2 = a ^ 2 - b ^ 2) :
    frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • w) +
    frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v - (c : ℂ) • w) +
    frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v + (c : ℂ) • w) +
    frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v - (c : ℂ) • w) =
    4 * a ^ 2 * frame_quadratic (H := H) μ u +
    4 * b ^ 2 * frame_quadratic (H := H) μ v +
    4 * c ^ 2 * frame_quadratic (H := H) μ w +
    2 * local_quad2DDefect μ v w b c := by
  classical
  -- Step 2 inputs.
  have hP1 := threeD_pair1 hdim μ u v w hu hv hw huv huw hvw a b c hc
  have hP2 := threeD_pair2 hdim μ u v w hu hv hw huv huw hvw a b c hc

  -- Homogeneity: Q((2a)•u) = 4 a^2 Q(u).
  have hQ2au : frame_quadratic (H := H) μ ((2 * a : ℂ) • u) =
      (4 * a ^ 2) * frame_quadratic (H := H) μ u := by
    have h := frame_quadratic_sq_hom (H := H) μ (2 * a : ℂ) u
    have habs : (2 * |a|) ^ 2 = 4 * a ^ 2 := by
      calc
        (2 * |a|) ^ 2 = 4 * (|a| ^ 2) := by ring
        _ = 4 * a ^ 2 := by rw [sq_abs]
    simpa [Complex.norm_real, Real.norm_eq_abs, pow_two, habs] using h

  -- Homogeneity: Q((2b)•v ± (2c)•w) = 4 Q(b•v ± c•w).
  have hQvw_plus : frame_quadratic (H := H) μ ((2 * b : ℂ) • v + (2 * c : ℂ) • w) =
      4 * frame_quadratic (H := H) μ ((b : ℂ) • v + (c : ℂ) • w) := by
    have h := frame_quadratic_sq_hom (H := H) μ (2 : ℂ) ((b : ℂ) • v + (c : ℂ) • w)
    have hpow : (2 : ℝ) ^ 2 = 4 := by norm_num
    have h2 :
        frame_quadratic (H := H) μ (((2 : ℂ) • ((b : ℂ) • v)) + ((2 : ℂ) • ((c : ℂ) • w)))
          = 4 * frame_quadratic (H := H) μ ((b : ℂ) • v + (c : ℂ) • w) := by
      simpa [smul_add, smul_smul, pow_two, hpow, mul_assoc, mul_left_comm, mul_comm] using h
    have hb2 : (↑b * (2 : ℂ)) • v = (2 : ℂ) • ((b : ℂ) • v) := by
      rw [mul_comm, smul_smul]
    have hc2 : (↑c * (2 : ℂ)) • w = (2 : ℂ) • ((c : ℂ) • w) := by
      rw [mul_comm, smul_smul]
    calc
      frame_quadratic (H := H) μ ((2 * b : ℂ) • v + (2 * c : ℂ) • w)
          = frame_quadratic (H := H) μ (((↑b * (2 : ℂ)) • v) + ((↑c * (2 : ℂ)) • w)) := by ring_nf
      _ = frame_quadratic (H := H) μ (((2 : ℂ) • ((b : ℂ) • v)) + ((2 : ℂ) • ((c : ℂ) • w)) ) := by
            simp [hb2, hc2]
      _ = 4 * frame_quadratic (H := H) μ ((b : ℂ) • v + (c : ℂ) • w) := h2

  have hQvw_minus : frame_quadratic (H := H) μ ((2 * b : ℂ) • v - (2 * c : ℂ) • w) =
      4 * frame_quadratic (H := H) μ ((b : ℂ) • v - (c : ℂ) • w) := by
    have h := frame_quadratic_sq_hom (H := H) μ (2 : ℂ) ((b : ℂ) • v - (c : ℂ) • w)
    have hpow : (2 : ℝ) ^ 2 = 4 := by norm_num
    have h2 :
        frame_quadratic (H := H) μ ((2 : ℂ) • ((b : ℂ) • v - (c : ℂ) • w))
          = 4 * frame_quadratic (H := H) μ ((b : ℂ) • v - (c : ℂ) • w) := by
      simpa [pow_two, hpow, mul_assoc, mul_left_comm, mul_comm] using h
    have hb2 : (↑b * (2 : ℂ)) • v = (2 : ℂ) • ((b : ℂ) • v) := by
      rw [mul_comm, smul_smul]
    have hc2 : (↑c * (2 : ℂ)) • w = (2 : ℂ) • ((c : ℂ) • w) := by
      rw [mul_comm, smul_smul]
    calc
      frame_quadratic (H := H) μ ((2 * b : ℂ) • v - (2 * c : ℂ) • w)
          = frame_quadratic (H := H) μ (((↑b * (2 : ℂ)) • v) - ((↑c * (2 : ℂ)) • w)) := by ring_nf
      _ = frame_quadratic (H := H) μ ((2 : ℂ) • ((b : ℂ) • v - (c : ℂ) • w)) := by
            simp [hb2, hc2, smul_sub]
      _ = 4 * frame_quadratic (H := H) μ ((b : ℂ) • v - (c : ℂ) • w) := h2

  -- From P1': Q(x₁)+Q(x₄) = 2 a^2 Q(u) + 2 Q(bv+cw).
  have h14 :
      frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • w) +
      frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v - (c : ℂ) • w)
        =
      2 * a ^ 2 * frame_quadratic (H := H) μ u +
      2 * frame_quadratic (H := H) μ ((b : ℂ) • v + (c : ℂ) • w) := by
    have hP1' := hP1
    rw [hQ2au, hQvw_plus] at hP1'
    linarith [hP1']

  -- From P2': Q(x₂)+Q(x₃) = 2 a^2 Q(u) + 2 Q(bv-cw).
  have h23 :
      frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v - (c : ℂ) • w) +
      frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v + (c : ℂ) • w)
        =
      2 * a ^ 2 * frame_quadratic (H := H) μ u +
      2 * frame_quadratic (H := H) μ ((b : ℂ) • v - (c : ℂ) • w) := by
    have hP2' := hP2
    rw [hQ2au, hQvw_minus] at hP2'
    linarith [hP2']

  -- Combine h14 and h23 to get the four-point sum in terms of the two `vw` expressions.
  have hsum' :
      (frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • w) +
        frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v - (c : ℂ) • w)) +
      (frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v - (c : ℂ) • w) +
        frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v + (c : ℂ) • w))
        =
      4 * a ^ 2 * frame_quadratic (H := H) μ u +
      2 * (frame_quadratic (H := H) μ ((b : ℂ) • v + (c : ℂ) • w) +
            frame_quadratic (H := H) μ ((b : ℂ) • v - (c : ℂ) • w)) := by
    linarith [h14, h23]

  -- Rewrite the LHS into the canonical `Q₁+Q₂+Q₃+Q₄` order.
  have hsum :
      frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • w) +
      frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v - (c : ℂ) • w) +
      frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v + (c : ℂ) • w) +
      frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v - (c : ℂ) • w)
        =
      4 * a ^ 2 * frame_quadratic (H := H) μ u +
      2 * (frame_quadratic (H := H) μ ((b : ℂ) • v + (c : ℂ) • w) +
            frame_quadratic (H := H) μ ((b : ℂ) • v - (c : ℂ) • w)) := by
    -- `abel` handles the reordering.
    simpa [add_assoc, add_left_comm, add_comm] using hsum'

  -- Expand the `vw` bracket using the defect definition.
  have hdef :
      frame_quadratic (H := H) μ ((b : ℂ) • v + (c : ℂ) • w) +
      frame_quadratic (H := H) μ ((b : ℂ) • v - (c : ℂ) • w)
        =
      2 * b ^ 2 * frame_quadratic (H := H) μ v +
      2 * c ^ 2 * frame_quadratic (H := H) μ w +
      local_quad2DDefect μ v w b c := by
    -- This is just rearranging the definition of `local_quad2DDefect`.
    simp [local_quad2DDefect, local_quad2DExpr]

  -- Substitute `hdef` into `hsum`.
  linarith [hsum, hdef]

/-!
## Step 4: Cauchy-Jensen scaffolding

Core algebraic consequences of the Cauchy-Jensen relation
`g (s+t) + g (s-t) = 2 g s + 2 g t`.
-/

lemma cauchy_jensen_g0
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    g 0 = 0 := by
  have h := hCJ 0 0
  simp at h
  linarith

lemma cauchy_jensen_even
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    ∀ t : ℝ, g (-t) = g t := by
  intro t
  have hg0 : g 0 = 0 := cauchy_jensen_g0 g hCJ
  have h := hCJ 0 t
  simp [hg0] at h
  linarith

lemma cauchy_jensen_double
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    ∀ t : ℝ, g (2 * t) = 4 * g t := by
  intro t
  have hg0 : g 0 = 0 := cauchy_jensen_g0 g hCJ
  have h := hCJ t t
  simp [hg0] at h
  have h' : g (t + t) = 4 * g t := by
    ring_nf at h ⊢
    exact h
  simpa [two_mul] using h'

lemma cauchy_jensen_half
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    g (1 / 2) = (1 / 4) * g 1 := by
  have hg0 : g 0 = 0 := cauchy_jensen_g0 g hCJ
  have h := hCJ (1 / 2) (1 / 2)
  -- g(1) + g(0) = 4 g(1/2)
  have h' : g 1 = 4 * g (1 / 2) := by
    nlinarith [h, hg0]
  linarith [h']

lemma cauchy_jensen_shift_recurrence
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    ∀ s : ℝ, g (s + 1) + g (s - 1) = 2 * g s + 2 * g 1 := by
  intro s
  simpa [add_comm, add_left_comm, add_assoc] using hCJ s 1

lemma cauchy_jensen_double_pow
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    ∀ n : ℕ, ∀ t : ℝ, g ((2 ^ n : ℝ) * t) = (4 ^ n : ℝ) * g t := by
  intro n
  induction n with
  | zero =>
      intro t
      simp
  | succ n ih =>
      intro t
      have hd := cauchy_jensen_double g hCJ ((2 ^ n : ℝ) * t)
      calc
        g ((2 ^ (n + 1) : ℝ) * t)
            = g (2 * ((2 ^ n : ℝ) * t)) := by ring_nf
        _ = 4 * g ((2 ^ n : ℝ) * t) := by simpa using hd
        _ = 4 * ((4 ^ n : ℝ) * g t) := by rw [ih t]
        _ = (4 ^ (n + 1) : ℝ) * g t := by ring

lemma cauchy_jensen_half_pow
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    ∀ n : ℕ, ∀ t : ℝ, g (t / (2 ^ n : ℝ)) = g t / (4 ^ n : ℝ) := by
  intro n t
  have h2pow : (2 ^ n : ℝ) ≠ 0 := by positivity
  have h4pow : (4 ^ n : ℝ) ≠ 0 := by positivity
  have hdp := cauchy_jensen_double_pow g hCJ n (t / (2 ^ n : ℝ))
  have hmul : g t = (4 ^ n : ℝ) * g (t / (2 ^ n : ℝ)) := by
    simpa [div_eq_mul_inv, h2pow, mul_assoc, mul_left_comm, mul_comm] using hdp
  apply (eq_div_iff h4pow).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.symm

lemma cauchy_jensen_one_over_pow_two
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    ∀ n : ℕ, g ((1 : ℝ) / (2 ^ n : ℝ)) = ((1 : ℝ) / (4 ^ n : ℝ)) * g 1 := by
  intro n
  simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using cauchy_jensen_half_pow g hCJ n 1

lemma cauchy_jensen_nat
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    ∀ n : ℕ, g (n : ℝ) = (n : ℝ) ^ 2 * g 1 := by
  let P : ℕ → Prop := fun n => g (n : ℝ) = (n : ℝ) ^ 2 * g 1
  have hg0 : g 0 = 0 := cauchy_jensen_g0 g hCJ
  have hP0 : P 0 := by simpa [P, hg0]
  have hP1 : P 1 := by simp [P]
  have hstep : ∀ n : ℕ, P n → P (n + 1) → P (n + 2) := by
    intro n hn hn1
    have hrec := hCJ ((n : ℝ) + 1) 1
    have hrec0 : g ((n : ℝ) + 2) + g (n : ℝ) = 2 * g ((n : ℝ) + 1) + 2 * g 1 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, one_add_one_eq_two] using hrec
    have hrec' : g ((n : ℝ) + 2) = 2 * g ((n : ℝ) + 1) + 2 * g 1 - g (n : ℝ) := by
      linarith [hrec0]
    have hnR : g (n : ℝ) = (n : ℝ) ^ 2 * g 1 := hn
    have hn1R : g ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ 2 * g 1 := by
      simpa [P, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hn1
    have hcalc : g ((n : ℝ) + 2) = ((n : ℝ) + 2) ^ 2 * g 1 := by
      rw [hrec', hn1R, hnR]
      ring
    simpa [P, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hcalc
  have hpair : ∀ n : ℕ, P n ∧ P (n + 1) := by
    intro n
    induction n with
    | zero =>
        exact ⟨hP0, hP1⟩
    | succ n ih =>
        exact ⟨ih.2, hstep n ih.1 ih.2⟩
  intro n
  exact (hpair n).1

lemma cauchy_jensen_dyadic_nat
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    ∀ (n k : ℕ), g ((n : ℝ) / (2 ^ k : ℝ)) = (((n : ℝ) / (2 ^ k : ℝ)) ^ 2) * g 1 := by
  intro n k
  have hnat := cauchy_jensen_nat g hCJ n
  have hhalf := cauchy_jensen_half_pow g hCJ k (n : ℝ)
  have h2pow : (2 ^ k : ℝ) ≠ 0 := by positivity
  have h4pow : (4 ^ k : ℝ) ≠ 0 := by positivity
  have hpow24 : (2 ^ k : ℝ) ^ 2 = (4 ^ k : ℝ) := by
    calc
      (2 ^ k : ℝ) ^ 2 = (2 : ℝ) ^ (k * 2) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (2 * k) := by simp [Nat.mul_comm]
      _ = ((2 : ℝ) ^ 2) ^ k := by rw [← pow_mul]
      _ = (4 : ℝ) ^ k := by norm_num
  calc
    g ((n : ℝ) / (2 ^ k : ℝ))
        = g (n : ℝ) / (4 ^ k : ℝ) := hhalf
    _ = ((n : ℝ) ^ 2 * g 1) / (4 ^ k : ℝ) := by rw [hnat]
    _ = (((n : ℝ) / (2 ^ k : ℝ)) ^ 2) * g 1 := by
          field_simp [h2pow, h4pow]
          rw [hpow24]

lemma cauchy_jensen_int
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    ∀ z : ℤ, g (z : ℝ) = (z : ℝ) ^ 2 * g 1 := by
  intro z
  cases z with
  | ofNat n =>
      simpa using cauchy_jensen_nat g hCJ n
  | negSucc n =>
      have heven := cauchy_jensen_even g hCJ ((n.succ : ℕ) : ℝ)
      have hnat := cauchy_jensen_nat g hCJ n.succ
      calc
        g ((Int.negSucc n : ℤ) : ℝ) = g (-((n.succ : ℕ) : ℝ)) := by simp [Int.cast_negSucc]
        _ = g ((n.succ : ℕ) : ℝ) := by simpa using heven
        _ = (((n.succ : ℕ) : ℝ) ^ 2) * g 1 := hnat
        _ = (((Int.negSucc n : ℤ) : ℝ) ^ 2) * g 1 := by
              have hsq : (((n.succ : ℕ) : ℝ) ^ 2) = (((Int.negSucc n : ℤ) : ℝ) ^ 2) := by
                simp [Int.cast_negSucc, pow_two]
                ring
              rw [hsq]

lemma cauchy_jensen_dyadic_int
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    ∀ (z : ℤ) (k : ℕ), g ((z : ℝ) / (2 ^ k : ℝ)) = (((z : ℝ) / (2 ^ k : ℝ)) ^ 2) * g 1 := by
  intro z k
  have hz := cauchy_jensen_int g hCJ z
  have hhalf := cauchy_jensen_half_pow g hCJ k (z : ℝ)
  have h2pow : (2 ^ k : ℝ) ≠ 0 := by positivity
  have h4pow : (4 ^ k : ℝ) ≠ 0 := by positivity
  have hpow24 : (2 ^ k : ℝ) ^ 2 = (4 ^ k : ℝ) := by
    calc
      (2 ^ k : ℝ) ^ 2 = (2 : ℝ) ^ (k * 2) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (2 * k) := by simp [Nat.mul_comm]
      _ = ((2 : ℝ) ^ 2) ^ k := by rw [← pow_mul]
      _ = (4 : ℝ) ^ k := by norm_num
  calc
    g ((z : ℝ) / (2 ^ k : ℝ))
        = g (z : ℝ) / (4 ^ k : ℝ) := hhalf
    _ = (((z : ℝ) ^ 2) * g 1) / (4 ^ k : ℝ) := by rw [hz]
    _ = ((((z : ℝ) / (2 ^ k : ℝ)) ^ 2) * g 1) := by
          field_simp [h2pow, h4pow]
          rw [hpow24]

lemma cauchy_jensen_remainder_cj
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ s t : ℝ, h (s + t) + h (s - t) = 2 * h s + 2 * h t := by
  intro h s t
  have hg := hCJ s t
  dsimp [h]
  linarith [hg]

lemma cauchy_jensen_remainder_dyadic_zero
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ (z : ℤ) (k : ℕ), h ((z : ℝ) / (2 ^ k : ℝ)) = 0 := by
  intro h z k
  have hdy := cauchy_jensen_dyadic_int g hCJ z k
  dsimp [h]
  linarith [hdy]

lemma cauchy_jensen_remainder_bound
    (g : ℝ → ℝ)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, |g t| ≤ C * (1 + t ^ 2)) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∃ C' : ℝ, ∀ t : ℝ, |h t| ≤ C' * (1 + t ^ 2) := by
  intro h
  rcases hbound with ⟨C, hC⟩
  refine ⟨C + |g 1|, ?_⟩
  intro t
  dsimp [h]
  have h1a : |g t - t ^ 2 * g 1| ≤ |g t| + |t ^ 2 * g 1| := by
    have hnorm := norm_add_le (g t) (-(t ^ 2 * g 1))
    convert hnorm using 1 <;> simp [sub_eq_add_neg, Real.norm_eq_abs]
  have h3 : |t ^ 2 * g 1| = t ^ 2 * |g 1| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
  have h1 : |g t - t ^ 2 * g 1| ≤ |g t| + t ^ 2 * |g 1| := by
    simpa [h3] using h1a
  have h2 : |g t| ≤ C * (1 + t ^ 2) := hC t
  have h4 : t ^ 2 * |g 1| ≤ |g 1| * (1 + t ^ 2) := by
    have hnonneg : 0 ≤ |g 1| := abs_nonneg (g 1)
    have : t ^ 2 ≤ 1 + t ^ 2 := by nlinarith
    nlinarith
  have h5 : |g t| + |t ^ 2 * g 1| ≤ C * (1 + t ^ 2) + |g 1| * (1 + t ^ 2) := by
    rw [h3]
    exact add_le_add h2 h4
  have h6 : C * (1 + t ^ 2) + |g 1| * (1 + t ^ 2) = (C + |g 1|) * (1 + t ^ 2) := by ring
  exact le_trans h1 (by simpa [h6] using h5)

lemma cauchy_jensen_remainder_zero_int
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ z : ℤ, h (z : ℝ) = 0 := by
  intro h z
  have hz := cauchy_jensen_int g hCJ z
  dsimp [h]
  linarith [hz]

lemma cauchy_jensen_remainder_double
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ t : ℝ, h (2 * t) = 4 * h t := by
  intro h t
  dsimp [h]
  have hd := cauchy_jensen_double g hCJ t
  linarith [hd]

lemma cauchy_jensen_remainder_double_pow
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ n : ℕ, ∀ t : ℝ, h ((2 ^ n : ℝ) * t) = (4 ^ n : ℝ) * h t := by
  intro h n
  induction n with
  | zero =>
      intro t
      simp [h]
  | succ n ih =>
      intro t
      have hd := cauchy_jensen_remainder_double g hCJ ((2 ^ n : ℝ) * t)
      calc
        h ((2 ^ (n + 1) : ℝ) * t)
            = h (2 * ((2 ^ n : ℝ) * t)) := by ring_nf
        _ = 4 * h ((2 ^ n : ℝ) * t) := by simpa using hd
        _ = 4 * ((4 ^ n : ℝ) * h t) := by rw [ih t]
        _ = (4 ^ (n + 1) : ℝ) * h t := by ring

lemma cauchy_jensen_remainder_half_pow
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ n : ℕ, ∀ t : ℝ, h (t / (2 ^ n : ℝ)) = h t / (4 ^ n : ℝ) := by
  intro h n t
  have h2pow : (2 ^ n : ℝ) ≠ 0 := by positivity
  have h4pow : (4 ^ n : ℝ) ≠ 0 := by positivity
  have hdp := cauchy_jensen_remainder_double_pow g hCJ n (t / (2 ^ n : ℝ))
  have hmul : h t = h (t / (2 ^ n : ℝ)) * (4 ^ n : ℝ) := by
    simpa [h, div_eq_mul_inv, h2pow, mul_assoc, mul_left_comm, mul_comm] using hdp
  apply (eq_div_iff h4pow).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul.symm

lemma cauchy_jensen_remainder_shift_of_zero
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ s t : ℝ, h t = 0 → h (s + t) + h (s - t) = 2 * h s := by
  intro h s t ht
  have hCJh := cauchy_jensen_remainder_cj g hCJ s t
  linarith [hCJh, ht]

lemma cauchy_jensen_remainder_shift_dyadic
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ s : ℝ, ∀ z : ℤ, ∀ k : ℕ,
      h (s + ((z : ℝ) / (2 ^ k : ℝ))) + h (s - ((z : ℝ) / (2 ^ k : ℝ))) = 2 * h s := by
  intro h s z k
  have hz0 := cauchy_jensen_remainder_dyadic_zero g hCJ z k
  exact cauchy_jensen_remainder_shift_of_zero g hCJ s ((z : ℝ) / (2 ^ k : ℝ)) hz0

lemma cauchy_jensen_remainder_midpoint_dyadic
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ s : ℝ, ∀ z : ℤ, ∀ k : ℕ,
      h s = (h (s + ((z : ℝ) / (2 ^ k : ℝ))) + h (s - ((z : ℝ) / (2 ^ k : ℝ)))) / 2 := by
  intro h s z k
  have hshift := cauchy_jensen_remainder_shift_dyadic g hCJ s z k
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hshift' : h s * 2 = h (s + ((z : ℝ) / (2 ^ k : ℝ))) + h (s - ((z : ℝ) / (2 ^ k : ℝ))) := by
    simpa [h, two_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using hshift.symm
  apply (eq_div_iff h2).2
  exact hshift'

lemma cauchy_jensen_remainder_second_diff
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ s t : ℝ, h (s + t) + h (s - t) - 2 * h s = 2 * h t := by
  intro h s t
  have hCJh := cauchy_jensen_remainder_cj g hCJ s t
  linarith [hCJh]

lemma cauchy_jensen_remainder_second_diff_dyadic_zero
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ s : ℝ, ∀ z : ℤ, ∀ k : ℕ,
      h (s + ((z : ℝ) / (2 ^ k : ℝ))) + h (s - ((z : ℝ) / (2 ^ k : ℝ))) - 2 * h s = 0 := by
  intro h s z k
  have hsd := cauchy_jensen_remainder_second_diff g hCJ s ((z : ℝ) / (2 ^ k : ℝ))
  have hz0 := cauchy_jensen_remainder_dyadic_zero g hCJ z k
  linarith [hsd, hz0]

lemma cauchy_jensen_remainder_scaled_bound
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, |g t| ≤ C * (1 + t ^ 2)) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, ∀ t : ℝ, |h t| ≤ A * ((1 / (4 ^ n : ℝ)) + t ^ 2) := by
  intro h
  rcases cauchy_jensen_remainder_bound g hbound with ⟨C0, hC0⟩
  refine ⟨|C0|, abs_nonneg _, ?_⟩
  intro n t
  have hA : |h ((2 ^ n : ℝ) * t)| ≤ |C0| * (1 + (((2 ^ n : ℝ) * t) ^ 2)) := by
    have h0 := hC0 ((2 ^ n : ℝ) * t)
    have hcoef : C0 * (1 + (((2 ^ n : ℝ) * t) ^ 2)) ≤ |C0| * (1 + (((2 ^ n : ℝ) * t) ^ 2)) := by
      have hle : C0 ≤ |C0| := le_abs_self C0
      have hnonneg : 0 ≤ 1 + (((2 ^ n : ℝ) * t) ^ 2) := by nlinarith
      nlinarith
    exact le_trans h0 hcoef
  have hpow := cauchy_jensen_remainder_double_pow g hCJ n t
  have h4pos : 0 < (4 ^ n : ℝ) := by positivity
  have h4nz : (4 ^ n : ℝ) ≠ 0 := ne_of_gt h4pos
  have hpow' : h ((2 ^ n : ℝ) * t) = (4 ^ n : ℝ) * h t := by
    simpa [h] using hpow
  have hmul : (4 ^ n : ℝ) * |h t| ≤ |C0| * (1 + (((2 ^ n : ℝ) * t) ^ 2)) := by
    have habs : |h ((2 ^ n : ℝ) * t)| = (4 ^ n : ℝ) * |h t| := by
      calc
        |h ((2 ^ n : ℝ) * t)| = |(4 ^ n : ℝ) * h t| := by rw [hpow']
        _ = (4 ^ n : ℝ) * |h t| := by
          rw [abs_mul, abs_of_nonneg (le_of_lt h4pos)]
    simpa [habs] using hA
  have hdiv : |h t| ≤ (|C0| * (1 + (((2 ^ n : ℝ) * t) ^ 2))) / (4 ^ n : ℝ) := by
    have hmul' : |h t| * (4 ^ n : ℝ) ≤ |C0| * (1 + (((2 ^ n : ℝ) * t) ^ 2)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    field_simp [h4nz]
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul'
  have hpow24 : ((2 ^ n : ℝ) ^ 2) = (4 ^ n : ℝ) := by
    calc
      ((2 ^ n : ℝ) ^ 2) = (2 : ℝ) ^ (n * 2) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (2 * n) := by simp [Nat.mul_comm]
      _ = ((2 : ℝ) ^ 2) ^ n := by rw [← pow_mul]
      _ = (4 : ℝ) ^ n := by norm_num
  have hfinal :
      (|C0| * (1 + (((2 ^ n : ℝ) * t) ^ 2))) / (4 ^ n : ℝ)
        = |C0| * ((1 / (4 ^ n : ℝ)) + t ^ 2) := by
    field_simp [h4nz]
    rw [hpow24]
    ring
  exact le_trans hdiv (by simpa [hfinal])

lemma cauchy_jensen_remainder_quadratic_bound
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, |g t| ≤ C * (1 + t ^ 2)) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, |h t| ≤ A * t ^ 2 := by
  intro h
  rcases cauchy_jensen_remainder_scaled_bound g hCJ hbound with ⟨A, hA_nonneg, hA⟩
  refine ⟨A, hA_nonneg, ?_⟩
  intro t
  apply le_of_forall_pos_le_add
  intro ε hε
  have hA1pos : 0 < A + 1 := by linarith
  have hε' : 0 < ε / (A + 1) := div_pos hε hA1pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 4 : ℝ) ^ N < ε / (A + 1) :=
    exists_pow_lt_of_lt_one hε' (by norm_num : (1 / 4 : ℝ) < 1)
  have hNt := hA N t
  have hpow : (1 / (4 ^ N : ℝ)) = (1 / 4 : ℝ) ^ N := by
    simp [one_div, inv_pow]
  have hsmall : A * (1 / (4 ^ N : ℝ)) < ε := by
    calc
      A * (1 / (4 ^ N : ℝ)) = A * ((1 / 4 : ℝ) ^ N) := by rw [hpow]
      _ ≤ (A + 1) * ((1 / 4 : ℝ) ^ N) := by
            have hA_le : A ≤ A + 1 := by linarith
            have hpow_nonneg : 0 ≤ ((1 / 4 : ℝ) ^ N) := by positivity
            gcongr
      _ < (A + 1) * (ε / (A + 1)) := by
            gcongr
      _ = ε := by
            field_simp [hA1pos.ne']
  have hNt' : |h t| ≤ A * t ^ 2 + A * (1 / (4 ^ N : ℝ)) := by
    have : |h t| ≤ A * ((1 / (4 ^ N : ℝ)) + t ^ 2) := hNt
    linarith
  have : |h t| < A * t ^ 2 + ε := by
    linarith [hNt', hsmall]
  exact le_of_lt this

lemma cauchy_jensen_remainder_small_near_zero
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, |g t| ≤ C * (1 + t ^ 2)) :
    let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → |h t| < ε := by
  intro h ε hε
  rcases cauchy_jensen_remainder_quadratic_bound g hCJ hbound with ⟨A, hA_nonneg, hA⟩
  refine ⟨min 1 (ε / (A + 1)), ?_, ?_⟩
  · have hA1pos : 0 < A + 1 := by linarith
    have hfracpos : 0 < ε / (A + 1) := div_pos hε hA1pos
    exact lt_min (by norm_num) hfracpos
  · intro t ht
    have hA1pos : 0 < A + 1 := by linarith
    have ht1 : |t| < 1 := lt_of_lt_of_le ht (min_le_left 1 (ε / (A + 1)))
    have htfrac : |t| < ε / (A + 1) := lt_of_lt_of_le ht (min_le_right 1 (ε / (A + 1)))
    have hsq_le_abs : t ^ 2 ≤ |t| := by
      have h0 : 0 ≤ |t| := abs_nonneg t
      have hsq_abs : |t| ^ 2 ≤ |t| := by nlinarith [h0, ht1]
      simpa [sq_abs] using hsq_abs
    have ht2 : t ^ 2 < ε / (A + 1) := lt_of_le_of_lt hsq_le_abs htfrac
    have hAt : |h t| ≤ A * t ^ 2 := hA t
    have hAfrac : A * t ^ 2 < ε := by
      calc
        A * t ^ 2 ≤ A * (ε / (A + 1)) := by
          gcongr
        _ < (A + 1) * (ε / (A + 1)) := by
          have hlt : A < A + 1 := by linarith
          gcongr
        _ = ε := by
          field_simp [hA1pos.ne']
    exact lt_of_le_of_lt hAt hAfrac

set_option maxHeartbeats 600000 in
lemma cauchy_jensen_solution
    (g : ℝ → ℝ)
    (hCJ : ∀ s t : ℝ, g (s + t) + g (s - t) = 2 * g s + 2 * g t)
    (hbound : ∃ C : ℝ, ∀ t : ℝ, |g t| ≤ C * (1 + t ^ 2))
    (t : ℝ) :
    g t = t ^ 2 * g 1 := by
  let h : ℝ → ℝ := fun t => g t - t ^ 2 * g 1
  have h_shift : ∀ s : ℝ, ∀ z : ℤ, ∀ k : ℕ,
      h (s + ((z : ℝ) / (2 ^ k : ℝ))) + h (s - ((z : ℝ) / (2 ^ k : ℝ))) = 2 * h s :=
    cauchy_jensen_remainder_shift_dyadic g hCJ

  have h_ind : ∀ (z : ℤ) (k : ℕ) (n : ℕ) (x : ℝ),
      h (x + (n : ℝ) * ((z : ℝ) / (2 ^ k : ℝ))) = h x + (n : ℝ) * (h (x + ((z : ℝ) / (2 ^ k : ℝ))) - h x) := by
    intro z k n
    induction n with
    | zero =>
        intro x
        simp
    | succ n ih =>
        intro x
        have h1 : x + ((n + 1 : ℕ) : ℝ) * ((z : ℝ) / (2 ^ k : ℝ)) = (x + ((z : ℝ) / (2 ^ k : ℝ))) + (n : ℝ) * ((z : ℝ) / (2 ^ k : ℝ)) := by
          push_cast
          ring
        have hlhs : h (x + ((n + 1 : ℕ) : ℝ) * ((z : ℝ) / (2 ^ k : ℝ))) = h ((x + ((z : ℝ) / (2 ^ k : ℝ))) + (n : ℝ) * ((z : ℝ) / (2 ^ k : ℝ))) := by
          exact congrArg h h1
        rw [hlhs, ih (x + ((z : ℝ) / (2 ^ k : ℝ)))]
        have hs2 : h (x + ((z : ℝ) / (2 ^ k : ℝ)) + ((z : ℝ) / (2 ^ k : ℝ))) + h x = 2 * h (x + ((z : ℝ) / (2 ^ k : ℝ))) := by
          have tmp := h_shift (x + ((z : ℝ) / (2 ^ k : ℝ))) z k
          have h_tmp_eq2 : x + ((z : ℝ) / (2 ^ k : ℝ)) - ((z : ℝ) / (2 ^ k : ℝ)) = x := by ring
          rw [h_tmp_eq2] at tmp
          exact tmp
        have h_diff : h (x + ((z : ℝ) / (2 ^ k : ℝ)) + ((z : ℝ) / (2 ^ k : ℝ))) - h (x + ((z : ℝ) / (2 ^ k : ℝ))) = h (x + ((z : ℝ) / (2 ^ k : ℝ))) - h x := by
          linarith
        rw [h_diff]
        push_cast
        ring

  rcases cauchy_jensen_remainder_quadratic_bound g hCJ hbound with ⟨A, hA_nonneg, hA⟩

  have ht_le : ∀ n : ℕ, 1 ≤ n → |h t| ≤ A * t ^ 2 / (n : ℝ) := by
    intro n hn
    have hn_pos_nat : 0 < n := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
    apply le_of_forall_pos_le_add
    intro ε hε
    let C1 := A * (2 * (n : ℝ) + 1)
    let C2 := 2 * A * |t|
    have hC1_nn : 0 ≤ C1 := by
      dsimp [C1]
      have h_pos_term : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
      exact mul_nonneg hA_nonneg h_pos_term
    have hC2_nn : 0 ≤ C2 := by
      dsimp [C2]
      positivity
    let delta := min 1 (ε / (C1 + C2 + 1))
    have hc_pos : 0 < C1 + C2 + 1 := by linarith
    have hd_pos : 0 < delta := lt_min (by norm_num) (div_pos hε hc_pos)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hd_pos hn_pos) (by norm_num : (1 / 2 : ℝ) < 1)
    have hk_rew : (1 / 2 : ℝ) ^ k = 1 / (2 ^ k : ℝ) := by simp [one_div, inv_pow]
    rw [hk_rew] at hk
    let E := (n : ℝ) / (2 ^ k : ℝ)
    have hE_lt : E < delta := by
      calc
        E = (n : ℝ) * (1 / (2 ^ k : ℝ)) := by ring
        _ < (n : ℝ) * (delta / (n : ℝ)) := by exact mul_lt_mul_of_pos_left hk hn_pos
        _ = delta := by exact mul_div_cancel₀ _ (ne_of_gt hn_pos)
    let z : ℤ := ⌊t * (2 ^ k : ℝ) / (n : ℝ)⌋
    let d : ℝ := (z : ℝ) / (2 ^ k : ℝ)
    let x : ℝ := t - (n : ℝ) * d
    have h_ind_t := h_ind z k n x
    have hxt : x + (n : ℝ) * d = t := by dsimp [x]; ring
    rw [hxt] at h_ind_t
    have h_abs : |h t| ≤ ((n : ℝ) + 1) * |h x| + (n : ℝ) * |h (x + d)| := by
      have h1 : |h t| = |h x + (n : ℝ) * (h (x + d) - h x)| := by rw [h_ind_t]
      have h2 : |h x + (n : ℝ) * (h (x + d) - h x)| ≤ |h x| + |(n : ℝ) * (h (x + d) - h x)| := by
        simpa [Real.norm_eq_abs] using (norm_add_le (h x) ((n : ℝ) * (h (x + d) - h x)))
      have h3 : |(n : ℝ) * (h (x + d) - h x)| = (n : ℝ) * |h (x + d) - h x| := by
        rw [abs_mul, abs_of_nonneg hn_pos.le]
      have h4 : |h (x + d) - h x| ≤ |h (x + d)| + |h x| := by
        have h_add := norm_add_le (h (x + d)) (-h x)
        simpa [sub_eq_add_neg, Real.norm_eq_abs, abs_neg] using h_add
      have h5 : |(n : ℝ) * (h (x + d) - h x)| ≤ (n : ℝ) * (|h (x + d)| + |h x|) := by
        rw [h3]
        exact mul_le_mul_of_nonneg_left h4 hn_pos.le
      have h6 : |h x + (n : ℝ) * (h (x + d) - h x)| ≤ |h x| + (n : ℝ) * (|h (x + d)| + |h x|) := by
        exact le_trans h2 (by linarith [h5])
      have h7 : |h t| ≤ |h x| + (n : ℝ) * (|h (x + d)| + |h x|) := by
        simpa [h1] using h6
      have hrhs : |h x| + (n : ℝ) * (|h (x + d)| + |h x|) = ((n : ℝ) + 1) * |h x| + (n : ℝ) * |h (x + d)| := by
        ring
      calc
        |h t| ≤ |h x| + (n : ℝ) * (|h (x + d)| + |h x|) := h7
        _ = ((n : ℝ) + 1) * |h x| + (n : ℝ) * |h (x + d)| := hrhs
    have hx_ge : 0 ≤ x := by
      dsimp [x, d]
      have h_floor := Int.floor_le (t * (2 ^ k : ℝ) / (n : ℝ))
      have h2k_pos : (0 : ℝ) < 2 ^ k := by positivity
      calc
        0 = t - t := by ring
        _ ≤ t - (z : ℝ) * (n : ℝ) / (2 ^ k : ℝ) := by
          have h_le : (z : ℝ) ≤ t * (2 ^ k : ℝ) / (n : ℝ) := h_floor
          have h_mul : (z : ℝ) * (n : ℝ) ≤ (t * (2 ^ k : ℝ) / (n : ℝ)) * (n : ℝ) := mul_le_mul_of_nonneg_right h_le hn_pos.le
          have h_div : (z : ℝ) * (n : ℝ) / (2 ^ k : ℝ) ≤ (t * (2 ^ k : ℝ) / (n : ℝ)) * (n : ℝ) / (2 ^ k : ℝ) := div_le_div_of_nonneg_right h_mul h2k_pos.le
          have h_cancel : (t * (2 ^ k : ℝ) / (n : ℝ)) * (n : ℝ) / (2 ^ k : ℝ) = t := by
            have hn_nz : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
            have h2k_nz : (2 ^ k : ℝ) ≠ 0 := ne_of_gt h2k_pos
            field_simp [hn_nz, h2k_nz]
          linarith
        _ = t - (n : ℝ) * ((z : ℝ) / (2 ^ k : ℝ)) := by ring
    have hx_le : x ≤ E := by
      dsimp [x, d, E]
      have h2k_pos : (0 : ℝ) < 2 ^ k := by positivity
      calc
        t - (n : ℝ) * ((z : ℝ) / (2 ^ k : ℝ))
          = t - (z : ℝ) * (n : ℝ) / (2 ^ k : ℝ) := by ring
        _ ≤ t - (t * (2 ^ k : ℝ) / (n : ℝ) - 1) * (n : ℝ) / (2 ^ k : ℝ) := by
          have h_le : t * (2 ^ k : ℝ) / (n : ℝ) - 1 ≤ (z : ℝ) := by
            have h_lt := Int.lt_floor_add_one (t * (2 ^ k : ℝ) / (n : ℝ))
            linarith
          have h_mul : (t * (2 ^ k : ℝ) / (n : ℝ) - 1) * (n : ℝ) ≤ (z : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right h_le hn_pos.le
          have h_div : (t * (2 ^ k : ℝ) / (n : ℝ) - 1) * (n : ℝ) / (2 ^ k : ℝ) ≤ (z : ℝ) * (n : ℝ) / (2 ^ k : ℝ) := div_le_div_of_nonneg_right h_mul h2k_pos.le
          linarith
        _ = (n : ℝ) / (2 ^ k : ℝ) := by
          have hn_nz : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
          have h2k_nz : (2 ^ k : ℝ) ≠ 0 := ne_of_gt h2k_pos
          field_simp [hn_nz, h2k_nz]
          ring
    have hxd_le : |x + d| ≤ |t| / (n : ℝ) + E := by
      have h1 : x + d = t / (n : ℝ) + x * (((n : ℝ) - 1) / (n : ℝ)) := by
        dsimp [x]
        have hn_nz : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
        field_simp [hn_nz]
        ring
      rw [h1]
      have h2 : ‖t / (n : ℝ) + x * (((n : ℝ) - 1) / (n : ℝ))‖ ≤ ‖t / (n : ℝ)‖ + ‖x * (((n : ℝ) - 1) / (n : ℝ))‖ := by
        exact norm_add_le _ _
      have h3 : ‖t / (n : ℝ)‖ = |t| / (n : ℝ) := by
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hn_pos]
      have h5 : x * (((n : ℝ) - 1) / (n : ℝ)) ≤ E := by
        have h_frac_le_1 : (((n : ℝ) - 1) / (n : ℝ)) ≤ 1 := by
          exact (div_le_one₀ hn_pos).mpr (by linarith)
        have h_frac_nonneg : 0 ≤ (((n : ℝ) - 1) / (n : ℝ)) := by
          have h_num : 0 ≤ (n : ℝ) - 1 := by
            have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
            linarith
          exact div_nonneg h_num hn_pos.le
        calc
          x * (((n : ℝ) - 1) / (n : ℝ)) ≤ E * (((n : ℝ) - 1) / (n : ℝ)) := mul_le_mul_of_nonneg_right hx_le h_frac_nonneg
          _ ≤ E * 1 := mul_le_mul_of_nonneg_left h_frac_le_1 (by positivity)
          _ = E := by ring
      have h4 : ‖x * (((n : ℝ) - 1) / (n : ℝ))‖ ≤ E := by
        have h_pos1 : 0 ≤ x := hx_ge
        have h_num : 0 ≤ (n : ℝ) - 1 := by
          have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith
        have h_pos2 : 0 ≤ ((n : ℝ) - 1) / (n : ℝ) := div_nonneg h_num hn_pos.le
        have h_prod_nonneg : 0 ≤ x * (((n : ℝ) - 1) / (n : ℝ)) := mul_nonneg h_pos1 h_pos2
        rw [Real.norm_eq_abs, abs_of_nonneg h_prod_nonneg]
        exact h5
      have h6 : ‖t / (n : ℝ) + x * (((n : ℝ) - 1) / (n : ℝ))‖ ≤ |t| / (n : ℝ) + E := by
        linarith [h2, h3, h4]
      simpa [Real.norm_eq_abs] using h6
    have h_bound_x : |h x| ≤ A * E ^ 2 := by
      have h1 := hA x
      have h2 : x ^ 2 ≤ E ^ 2 := by
        have hx_pos : 0 ≤ x := hx_ge
        have hE_pos : 0 ≤ E := by positivity
        nlinarith
      nlinarith [hA_nonneg]
    have h_bound_xd : |h (x + d)| ≤ A * (|t| / (n : ℝ) + E) ^ 2 := by
      have h1 := hA (x + d)
      have h2 : (x + d) ^ 2 ≤ (|t| / (n : ℝ) + E) ^ 2 := by
        have h_le1 : x + d ≤ |t| / (n : ℝ) + E := by
          calc
            x + d ≤ |x + d| := le_abs_self _
            _ ≤ |t| / (n : ℝ) + E := hxd_le
        have h_le2 : -(x + d) ≤ |t| / (n : ℝ) + E := by
          calc
            -(x + d) ≤ |-(x + d)| := le_abs_self _
            _ = |x + d| := by rw [abs_neg]
            _ ≤ |t| / (n : ℝ) + E := hxd_le
        nlinarith
      nlinarith [hA_nonneg]
    have h_rhs_expand : ((n : ℝ) + 1) * (A * E ^ 2) + (n : ℝ) * (A * (|t| / (n : ℝ) + E) ^ 2) =
        A * t ^ 2 / (n : ℝ) + E * (A * (2 * (n : ℝ) + 1) * E + 2 * A * |t|) := by
      have hn_nz : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
      have ht_sq : (|t| / (n : ℝ)) ^ 2 = t ^ 2 / (n : ℝ) ^ 2 := by
        rw [div_pow, sq_abs]
      calc
        ((n : ℝ) + 1) * (A * E ^ 2) + (n : ℝ) * (A * (|t| / (n : ℝ) + E) ^ 2)
          = A * ((n : ℝ) + 1) * E ^ 2 + A * (n : ℝ) * ((|t| / (n : ℝ)) ^ 2 + 2 * (|t| / (n : ℝ)) * E + E ^ 2) := by ring
        _ = A * ((n : ℝ) + 1) * E ^ 2 + A * (n : ℝ) * (t ^ 2 / (n : ℝ) ^ 2 + 2 * (|t| / (n : ℝ)) * E + E ^ 2) := by rw [ht_sq]
        _ = A * t ^ 2 / (n : ℝ) + E * (A * (2 * (n : ℝ) + 1) * E + 2 * A * |t|) := by
          field_simp [hn_nz]
          ring
    calc
      |h t| ≤ ((n : ℝ) + 1) * |h x| + (n : ℝ) * |h (x + d)| := h_abs
      _ ≤ ((n : ℝ) + 1) * (A * E ^ 2) + (n : ℝ) * (A * (|t| / (n : ℝ) + E) ^ 2) := by
        have hp1 : 0 ≤ (n : ℝ) + 1 := by positivity
        have hp2 : 0 ≤ (n : ℝ) := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left h_bound_x hp1) (mul_le_mul_of_nonneg_left h_bound_xd hp2)
      _ = A * t ^ 2 / (n : ℝ) + E * (C1 * E + C2) := by
        dsimp [C1, C2]
        rw [h_rhs_expand]
      _ ≤ A * t ^ 2 / (n : ℝ) + ε := by
        have hE_pos : 0 ≤ E := by positivity
        have h_R_pos : 0 ≤ ε / (C1 + C2 + 1) := div_nonneg hε.le hc_pos.le
        have h_bound4 : E * (C1 + C2) ≤ ε := by
          have h_C_nonneg : 0 ≤ C1 + C2 := add_nonneg hC1_nn hC2_nn
          calc
            E * (C1 + C2) ≤ delta * (C1 + C2) := mul_le_mul_of_nonneg_right hE_lt.le h_C_nonneg
            _ ≤ (ε / (C1 + C2 + 1)) * (C1 + C2) := mul_le_mul_of_nonneg_right (min_le_right 1 (ε / (C1 + C2 + 1))) h_C_nonneg
            _ ≤ (ε / (C1 + C2 + 1)) * (C1 + C2 + 1) := mul_le_mul_of_nonneg_left (by linarith) h_R_pos
            _ = ε := by exact div_mul_cancel₀ _ (ne_of_gt hc_pos)
        have h_bound2 : C1 * E + C2 ≤ C1 * 1 + C2 := by
          have h_bound1 : E ≤ 1 := by
            calc
              E ≤ delta := hE_lt.le
              _ ≤ 1 := min_le_left _ _
          linarith [mul_le_mul_of_nonneg_left h_bound1 hC1_nn]
        have h_bound3 : E * (C1 * E + C2) ≤ E * (C1 + C2) := by
          calc
            E * (C1 * E + C2) ≤ E * (C1 * 1 + C2) := mul_le_mul_of_nonneg_left h_bound2 hE_pos
            _ = E * (C1 + C2) := by ring
        linarith

  have ht_zero : h t = 0 := by
    by_contra ht_nz
    have ht_pos : 0 < |h t| := abs_pos.mpr ht_nz
    have h0 : (0 : ℝ) ≤ A * t ^ 2 * 2 / |h t| := by positivity
    obtain ⟨n_nat, hn_nat⟩ := exists_nat_gt (A * t ^ 2 * 2 / |h t|)
    have hn_pos_nat : 0 < n_nat := by
      have h1 : (0 : ℝ) < n_nat := lt_of_le_of_lt h0 hn_nat
      exact_mod_cast h1
    have hn_ge_1 : 1 ≤ n_nat := by omega
    have h_eval := ht_le n_nat hn_ge_1
    have hn_pos : (0 : ℝ) < (n_nat : ℝ) := by exact_mod_cast hn_pos_nat
    have h_bound : A * t ^ 2 / (n_nat : ℝ) < |h t| / 2 := by
      have h1 : A * t ^ 2 * 2 < (n_nat : ℝ) * |h t| := (div_lt_iff₀ ht_pos).mp hn_nat
      have h2 : A * t ^ 2 < (n_nat : ℝ) * (|h t| / 2) := by linarith
      have h3 : A * t ^ 2 < (|h t| / 2) * (n_nat : ℝ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h2
      exact (div_lt_iff₀ hn_pos).2 h3
    linarith

  dsimp [h] at ht_zero
  linarith

/-! ### Dyadic machinery removed — fully replaced by CJ path below -/
-- quad2DDefect_dyadic and defect_eq_zero_of_dyadic_squeeze DELETED.
-- The active proof now goes through cauchy_jensen_solution.

def local_defect_g (μ : FrameFunction H) (u v : H) (t : ℝ) : ℝ :=
  local_quad2DDefect μ u v 1 t

lemma local_quad2DDefect_ratio_reduction
    (μ : FrameFunction H) (u v : H) (a b : ℝ) (ha : a ≠ 0) :
    local_quad2DDefect μ u v a b = a ^ 2 * local_defect_g μ u v (b / a) := by
  have hhom := local_quad2DDefect_hom μ u v a 1 (b / a)
  have hleft : local_quad2DDefect μ u v (a * 1) (a * (b / a)) = local_quad2DDefect μ u v a b := by
    field_simp [ha]
  calc
    local_quad2DDefect μ u v a b
        = local_quad2DDefect μ u v (a * 1) (a * (b / a)) := by symm; exact hleft
    _ = a ^ 2 * local_quad2DDefect μ u v 1 (b / a) := hhom
    _ = a ^ 2 * local_defect_g μ u v (b / a) := by rfl

lemma local_defect_g_growth_bound
    (μ : FrameFunction H) (u v : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    ∃ C : ℝ, ∀ t : ℝ, |local_defect_g μ u v t| ≤ C * (1 + t ^ 2) := by
  rcases frame_quadratic_bounded (H := H) μ with ⟨C0, hC0⟩
  refine ⟨10 * |C0|, ?_⟩
  intro t
  let Qp : ℝ := frame_quadratic (H := H) μ (u + (t : ℂ) • v)
  let Qm : ℝ := frame_quadratic (H := H) μ (u - (t : ℂ) • v)
  let Qu : ℝ := frame_quadratic (H := H) μ u
  let Qv : ℝ := frame_quadratic (H := H) μ v
  have hC : ∀ x : H, |frame_quadratic (H := H) μ x| ≤ |C0| * ‖x‖ ^ 2 := by
    intro x
    have h := hC0 x
    have hcoef : C0 * ‖x‖ ^ 2 ≤ |C0| * ‖x‖ ^ 2 := by
      have hle : C0 ≤ |C0| := le_abs_self C0
      have hnn : 0 ≤ ‖x‖ ^ 2 := sq_nonneg ‖x‖
      nlinarith
    exact le_trans h hcoef
  have hnorm_plus_sq_le : ‖(u + (t : ℂ) • v)‖ ^ 2 ≤ 2 * (1 + t ^ 2) := by
    have hnorm : ‖u + (t : ℂ) • v‖ ≤ ‖u‖ + ‖(t : ℂ) • v‖ := norm_add_le _ _
    have hnorm' : ‖u + (t : ℂ) • v‖ ≤ 1 + |t| := by
      simpa [hu, hv, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using hnorm
    have hsq : ‖u + (t : ℂ) • v‖ ^ 2 ≤ (1 + |t|) ^ 2 := by
      nlinarith [hnorm', norm_nonneg (u + (t : ℂ) • v)]
    have hquad : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
      nlinarith [sq_nonneg (|t| - 1), sq_abs t]
    exact le_trans hsq hquad
  have hnorm_minus_sq_le : ‖(u - (t : ℂ) • v)‖ ^ 2 ≤ 2 * (1 + t ^ 2) := by
    have hnorm : ‖u - (t : ℂ) • v‖ ≤ ‖u‖ + ‖(t : ℂ) • v‖ := by
      simpa [sub_eq_add_neg, norm_neg] using (norm_add_le u (-(t : ℂ) • v))
    have hnorm' : ‖u - (t : ℂ) • v‖ ≤ 1 + |t| := by
      simpa [hu, hv, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm, mul_left_comm, mul_assoc] using hnorm
    have hsq : ‖u - (t : ℂ) • v‖ ^ 2 ≤ (1 + |t|) ^ 2 := by
      nlinarith [hnorm', norm_nonneg (u - (t : ℂ) • v)]
    have hquad : (1 + |t|) ^ 2 ≤ 2 * (1 + t ^ 2) := by
      nlinarith [sq_nonneg (|t| - 1), sq_abs t]
    exact le_trans hsq hquad
  have hQp : |Qp| ≤ (2 * |C0|) * (1 + t ^ 2) := by
    have h := hC (u + (t : ℂ) • v)
    have h' : |Qp| ≤ |C0| * (2 * (1 + t ^ 2)) := by simpa [Qp] using (le_trans h (by gcongr))
    simpa [mul_assoc, mul_comm, mul_left_comm] using h'
  have hQm : |Qm| ≤ (2 * |C0|) * (1 + t ^ 2) := by
    have h := hC (u - (t : ℂ) • v)
    have h' : |Qm| ≤ |C0| * (2 * (1 + t ^ 2)) := by simpa [Qm] using (le_trans h (by gcongr))
    simpa [mul_assoc, mul_comm, mul_left_comm] using h'
  have hQu : |Qu| ≤ |C0| := by
    have h := hC u
    simpa [Qu, hu] using h
  have hQv : |Qv| ≤ |C0| := by
    have h := hC v
    simpa [Qv, hv] using h
  have hdef :
      local_defect_g μ u v t = Qp + (Qm - (2 * Qu + 2 * t ^ 2 * Qv)) := by
    dsimp [local_defect_g, local_quad2DDefect, local_quad2DExpr, Qp, Qm, Qu, Qv]
    simp [sub_eq_add_neg, one_smul, add_assoc, add_left_comm, add_comm]
  have hA : |local_defect_g μ u v t| ≤ |Qp| + |Qm - (2 * Qu + 2 * t ^ 2 * Qv)| := by
    have hnorm : |Qp + (Qm - (2 * Qu + 2 * t ^ 2 * Qv))| ≤
        |Qp| + |Qm - (2 * Qu + 2 * t ^ 2 * Qv)| := by
      simpa [Real.norm_eq_abs] using (norm_add_le Qp (Qm - (2 * Qu + 2 * t ^ 2 * Qv)))
    simpa [hdef] using hnorm
  have hB : |Qm - (2 * Qu + 2 * t ^ 2 * Qv)| ≤
      |Qm| + |-(2 * Qu + 2 * t ^ 2 * Qv)| := by
    have hnorm := norm_add_le Qm (-(2 * Qu + 2 * t ^ 2 * Qv))
    simpa [sub_eq_add_neg, Real.norm_eq_abs] using hnorm
  have hCcorr : |2 * Qu + 2 * t ^ 2 * Qv| ≤ |2 * Qu| + |2 * t ^ 2 * Qv| := by
    have hnorm := norm_add_le (2 * Qu) (2 * t ^ 2 * Qv)
    convert hnorm using 1 <;> simp [Real.norm_eq_abs]
  have hU : |2 * Qu| ≤ 2 * |C0| * (1 + t ^ 2) := by
    have h2Qu : |2 * Qu| = 2 * |Qu| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [h2Qu]
    have h1t : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    nlinarith [hQu, h1t, abs_nonneg C0]
  have hV : |2 * t ^ 2 * Qv| ≤ 2 * |C0| * (1 + t ^ 2) := by
    have h2tq : |2 * t ^ 2 * Qv| = (2 * t ^ 2) * |Qv| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (sq_nonneg t)]
    rw [h2tq]
    have ht2le : t ^ 2 ≤ 1 + t ^ 2 := by nlinarith
    nlinarith [hQv, ht2le, abs_nonneg C0]
  calc
    |local_defect_g μ u v t|
        ≤ |Qp| + |Qm| + |-(2 * Qu + 2 * t ^ 2 * Qv)| := by linarith [hA, hB]
    _ = |Qp| + |Qm| + |2 * Qu + 2 * t ^ 2 * Qv| := by rw [abs_neg]
    _ ≤ |Qp| + |Qm| + (|2 * Qu| + |2 * t ^ 2 * Qv|) := by linarith [hCcorr]
    _ ≤ (2 * |C0| * (1 + t ^ 2)) + (2 * |C0| * (1 + t ^ 2)) + (2 * |C0| * (1 + t ^ 2) + 2 * |C0| * (1 + t ^ 2)) := by
          linarith [hQp, hQm, hU, hV]
    _ ≤ (10 * |C0|) * (1 + t ^ 2) := by
          have hnn : 0 ≤ |C0| * (1 + t ^ 2) := by nlinarith [abs_nonneg C0, sq_nonneg t]
          nlinarith

lemma local_quad2DDefect_one_zero_eq_zero
    (μ : FrameFunction H) (u v : H) :
    local_quad2DDefect μ u v 1 0 = 0 := by
  dsimp [local_quad2DDefect, local_quad2DExpr]
  have h1 : frame_quadratic (H := H) μ ((1 : ℂ) • u + (0 : ℂ) • v) = frame_quadratic (H := H) μ u := by
    simp
  have h2 : frame_quadratic (H := H) μ ((1 : ℂ) • u - (0 : ℂ) • v) = frame_quadratic (H := H) μ u := by
    simp
  rw [h1, h2]
  ring

lemma local_quad2DDefect_one_one_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    local_quad2DDefect μ u v 1 1 = 0 := by
  have hpar :=
    frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ u v huv (by simpa [hu, hv])
  have hpar' :
      frame_quadratic (H := H) μ ((1 : ℂ) • u + (1 : ℂ) • v) +
        frame_quadratic (H := H) μ ((1 : ℂ) • u - (1 : ℂ) • v)
      = 2 * frame_quadratic (H := H) μ u + 2 * frame_quadratic (H := H) μ v := by
    simpa [one_smul] using hpar
  dsimp [local_quad2DDefect, local_quad2DExpr]
  linarith [hpar']

lemma local_defect_g_zero_eq_zero
    (μ : FrameFunction H) (u v : H) :
    local_defect_g μ u v 0 = 0 := by
  simpa [local_defect_g] using local_quad2DDefect_one_zero_eq_zero μ u v

lemma local_defect_g_one_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    local_defect_g μ u v 1 = 0 := by
  simpa [local_defect_g] using local_quad2DDefect_one_one_eq_zero hdim μ u v hu hv huv

lemma local_defect_g_inversion
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    {t : ℝ} (ht : t ≠ 0) :
    local_defect_g μ u v t = -(t ^ 2) * local_defect_g μ u v (1 / t) := by
  have hswap := local_quad2DDefect_swap_of_orthonormal (H := H) hdim μ u v hu hv huv 1 t
  have hratio :=
    local_quad2DDefect_ratio_reduction μ u v t 1 ht
  have hswap' : local_defect_g μ u v t = - local_quad2DDefect μ u v t 1 := by
    simpa [local_defect_g] using hswap
  calc
    local_defect_g μ u v t
        = - local_quad2DDefect μ u v t 1 := hswap'
    _ = -(t ^ 2 * local_defect_g μ u v (1 / t)) := by rw [hratio]
    _ = -(t ^ 2) * local_defect_g μ u v (1 / t) := by ring

lemma local_quad2DDefect_zero_right
    (μ : FrameFunction H) (u v : H) (a : ℝ) :
    local_quad2DDefect μ u v a 0 = 0 := by
  have h10 : local_quad2DDefect μ u v 1 0 = 0 := local_quad2DDefect_one_zero_eq_zero μ u v
  have hhom := local_quad2DDefect_hom μ u v a 1 0
  calc
    local_quad2DDefect μ u v a 0
        = local_quad2DDefect μ u v (a * 1) (a * 0) := by ring_nf
    _ = a ^ 2 * local_quad2DDefect μ u v 1 0 := hhom
    _ = 0 := by rw [h10]; ring

lemma local_quad2DDefect_zero_left
    (μ : FrameFunction H) (u v : H) (b : ℝ) :
    local_quad2DDefect μ u v 0 b = 0 := by
  have h01 : local_quad2DDefect μ u v 0 1 = 0 := by
    have hnegv : frame_quadratic (H := H) μ (-v) = frame_quadratic (H := H) μ v := by
      have h := frame_quadratic_sq_hom (H := H) μ (-1 : ℂ) v
      simpa [neg_one_smul] using h
    dsimp [local_quad2DDefect, local_quad2DExpr]
    simp [hnegv]
    ring
  have hhom := local_quad2DDefect_hom μ u v b 0 1
  calc
    local_quad2DDefect μ u v 0 b
        = local_quad2DDefect μ u v (b * 0) (b * 1) := by ring_nf
    _ = b ^ 2 * local_quad2DDefect μ u v 0 1 := hhom
    _ = 0 := by rw [h01]; ring

lemma local_quad2DDefect_even_b
    (μ : FrameFunction H) (u v : H) (a b : ℝ) :
    local_quad2DDefect μ u v a (-b) = local_quad2DDefect μ u v a b := by
  dsimp [local_quad2DDefect, local_quad2DExpr]
  ring_nf
  simp [pow_two, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma local_defect_g_even
    (μ : FrameFunction H) (u v : H) (t : ℝ) :
    local_defect_g μ u v (-t) = local_defect_g μ u v t := by
  simpa [local_defect_g] using local_quad2DDefect_even_b μ u v 1 t

lemma local_defect_g_cj_iff_expr
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    (local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) =
      2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t)
    ↔
    (local_quad2DExpr μ u v 1 (s + t) + local_quad2DExpr μ u v 1 (s - t)
      = 2 * local_quad2DExpr μ u v 1 s + 2 * local_quad2DExpr μ u v 1 t
        - 4 * frame_quadratic (H := H) μ u) := by
  dsimp [local_defect_g, local_quad2DDefect]
  constructor <;> intro h <;> linarith [h]

lemma local_defect_g_cj_of_expr
    (μ : FrameFunction H) (u v : H) (s t : ℝ)
    (hExpr :
      local_quad2DExpr μ u v 1 (s + t) + local_quad2DExpr μ u v 1 (s - t)
        = 2 * local_quad2DExpr μ u v 1 s + 2 * local_quad2DExpr μ u v 1 t
          - 4 * frame_quadratic (H := H) μ u) :
    local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) =
      2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t := by
  exact (local_defect_g_cj_iff_expr μ u v s t).2 hExpr

lemma local_quad2DExpr_inhom_jensen_of_residual_zero
    (μ : FrameFunction H) (u v : H) (s t : ℝ)
    (hresid :
      local_quad2DDefect μ u v 1 (s + t) + local_quad2DDefect μ u v 1 (s - t)
        - 2 * local_quad2DDefect μ u v 1 s - 2 * local_quad2DDefect μ u v 1 t = 0) :
    local_quad2DExpr μ u v 1 (s + t) + local_quad2DExpr μ u v 1 (s - t)
      = 2 * local_quad2DExpr μ u v 1 s + 2 * local_quad2DExpr μ u v 1 t
        - 4 * frame_quadratic (H := H) μ u := by
  have hAlg := local_quad2DExpr_sum_algebraic_identity μ u v s t
  linarith [hAlg, hresid]

lemma local_defect_g_cj_of_inhom_jensen_of_residual_zero
    (μ : FrameFunction H) (u v : H) (s t : ℝ)
    (hresid :
      local_quad2DDefect μ u v 1 (s + t) + local_quad2DDefect μ u v 1 (s - t)
        - 2 * local_quad2DDefect μ u v 1 s - 2 * local_quad2DDefect μ u v 1 t = 0) :
    local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) =
      2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t := by
  exact local_defect_g_cj_of_expr μ u v s t
    (local_quad2DExpr_inhom_jensen_of_residual_zero μ u v s t hresid)

lemma local_quad2DDefect_eq_zero_of_local_defect_g_zero
    (μ : FrameFunction H) (u v : H)
    (hg0 : ∀ t : ℝ, local_defect_g μ u v t = 0)
    (a b : ℝ) :
    local_quad2DDefect μ u v a b = 0 := by
  by_cases ha : a = 0
  · subst ha
    exact local_quad2DDefect_zero_left μ u v b
  · rw [local_quad2DDefect_ratio_reduction μ u v a b ha, hg0 (b / a)]
    ring

lemma threeD_sum_identity_a1
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0) (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = 1 - s ^ 2) :
    frame_quadratic (H := H) μ ((1 : ℂ) • v + (s : ℂ) • u + (c : ℂ) • w) +
    frame_quadratic (H := H) μ ((1 : ℂ) • v + (s : ℂ) • u - (c : ℂ) • w) +
    frame_quadratic (H := H) μ ((1 : ℂ) • v - (s : ℂ) • u + (c : ℂ) • w) +
    frame_quadratic (H := H) μ ((1 : ℂ) • v - (s : ℂ) • u - (c : ℂ) • w) =
    4 * frame_quadratic (H := H) μ v +
    4 * s ^ 2 * frame_quadratic (H := H) μ u +
    4 * c ^ 2 * frame_quadratic (H := H) μ w +
    2 * local_quad2DDefect μ u w s c := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := inner_eq_zero_symm.1 huv
  have hvw' : inner (𝕜 := ℂ) v w = 0 := hvw
  have huw' : inner (𝕜 := ℂ) u w = 0 := huw
  have h := threeD_sum_identity (H := H) hdim μ v u w hv hu hw hvu hvw' huw' 1 s c (by nlinarith [hc])
  simpa [one_smul, mul_assoc, mul_comm, mul_left_comm] using h

lemma exists_w_for_pathA
    (hdim : 3 ≤ Module.finrank ℂ H) (u v : H) :
    ∃ w : H, ‖w‖ = 1 ∧ inner (𝕜 := ℂ) u w = 0 ∧ inner (𝕜 := ℂ) v w = 0 := by
  simpa using exists_unit_orthogonal_to_pair (H := H) hdim u v

lemma quad2D_shell_average_local
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    ∃ w : H, ‖w‖ = (1 : ℝ) ∧ inner (𝕜 := ℂ) u w = 0 ∧ inner (𝕜 := ℂ) v w = 0 ∧
      let x : H := (a : ℂ) • u + (b : ℂ) • v
      let c : ℝ := ‖x‖
      frame_quadratic (H := H) μ (x + (c : ℂ) • w) +
          frame_quadratic (H := H) μ (x - (c : ℂ) • w)
        =
      2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ ((c : ℂ) • w) := by
  rcases exists_w_for_pathA (H := H) hdim u v with ⟨w, hw, huw, hvw⟩
  refine ⟨w, hw, huw, hvw, ?_⟩
  intro x c
  have hxy : inner (𝕜 := ℂ) x ((c : ℂ) • w) = 0 := by
    simp [x, inner_add_left, inner_smul_left, inner_smul_right, huw, hvw, mul_assoc]
  have hnorm : ‖x‖ = ‖((c : ℂ) • w)‖ := by
    simp [c, hw, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  have hpar :=
    frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ x ((c : ℂ) • w) hxy hnorm
  simpa [sub_eq_add_neg] using hpar

lemma local_defect_g_cauchy_jensen_of_expr_identity
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hExpr :
      ∀ s t : ℝ,
        local_quad2DExpr μ u v 1 (s + t) + local_quad2DExpr μ u v 1 (s - t)
          = 2 * local_quad2DExpr μ u v 1 s + 2 * local_quad2DExpr μ u v 1 t
            - 4 * frame_quadratic (H := H) μ u) :
    ∀ s t : ℝ,
      local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) =
        2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t := by
  intro s t
  exact local_defect_g_cj_of_expr μ u v s t (hExpr s t)

/-!
### Step A: Cross-plane transfer via exchange identity + restricted parallelogram

For orthonormal (u,v,w) and real s, set t = √(1+s²). Then ‖u±sv‖ = |t| = ‖tw‖,
so the restricted parallelogram kills D_{u±sv, w}(1,t). The exchange identity then gives:

  2·D_uv(1,s) = 2·D_uw(1,t) + D_{u+tw, v}(1,s) + D_{u−tw, v}(1,s)

This transfers defect information between the (u,v)-plane and the (u,w)-plane.
-/

lemma rp_defect_kill
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = 1 + s ^ 2) :
    local_quad2DDefect μ ((1 : ℂ) • u + (s : ℂ) • v) w 1 c = 0 := by
  set x : H := (1 : ℂ) • u + (s : ℂ) • v with hx_def
  have hxw : inner (𝕜 := ℂ) x w = 0 := by
    simp [x, inner_add_left, inner_smul_left, huw, hvw]
  have hx_norm_sq : ‖x‖ ^ 2 = 1 + s ^ 2 := by
    have horth : inner (𝕜 := ℂ) ((1 : ℂ) • u) ((s : ℂ) • v) = 0 := by
      simp [inner_smul_left, inner_smul_right, huv]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      ((1 : ℂ) • u) ((s : ℂ) • v) horth
    simp [norm_smul, Complex.norm_real, Real.norm_eq_abs, hu, hv, sq_abs] at this
    simpa [x, pow_two] using this
  have hcw_norm : ‖(c : ℂ) • w‖ = |c| := by
    simp [norm_smul, hw]
  have hx_norm : ‖x‖ = |c| := by
    have hx_sq : ‖x‖ ^ 2 = c ^ 2 := by rw [hx_norm_sq, ← hc]
    have hxnn : 0 ≤ ‖x‖ := norm_nonneg x
    have hcnn : 0 ≤ |c| := abs_nonneg c
    have habsq : ‖x‖ ^ 2 = |c| ^ 2 := by rw [hx_sq, sq_abs]
    calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq hxnn).symm
      _ = Real.sqrt (|c| ^ 2) := by rw [habsq]
      _ = |c| := Real.sqrt_sq hcnn
  have hn : ‖x‖ = ‖(c : ℂ) • w‖ := by rw [hx_norm, hcw_norm]
  have hortho : inner (𝕜 := ℂ) x ((c : ℂ) • w) = 0 := by
    simp [hxw]
  have hpar := frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ x ((c : ℂ) • w)
    hortho hn
  have hhom : frame_quadratic (H := H) μ ((c : ℂ) • w) = c ^ 2 * frame_quadratic (H := H) μ w := by
    have h := frame_quadratic_sq_hom (H := H) μ (c : ℂ) w
    simp [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    exact h
  -- Compute the defect step-by-step
  have step1 : local_quad2DExpr μ x w 1 c =
      frame_quadratic (H := H) μ (x + (c : ℂ) • w) +
        frame_quadratic (H := H) μ (x - (c : ℂ) • w) := by
    unfold local_quad2DExpr
    simp [one_smul]
  have step2 : local_quad2DDefect μ x w 1 c =
      frame_quadratic (H := H) μ (x + (c : ℂ) • w) +
        frame_quadratic (H := H) μ (x - (c : ℂ) • w)
      - 2 * frame_quadratic (H := H) μ x
      - 2 * c ^ 2 * frame_quadratic (H := H) μ w := by
    unfold local_quad2DDefect
    rw [step1]
    ring
  rw [step2, hpar, hhom]
  ring

lemma rp_defect_kill_neg
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = 1 + s ^ 2) :
    local_quad2DDefect μ ((1 : ℂ) • u - (s : ℂ) • v) w 1 c = 0 := by
  have : (1 : ℂ) • u - (s : ℂ) • v = (1 : ℂ) • u + ((-s : ℝ) : ℂ) • v := by
    simp [sub_eq_add_neg, neg_smul]
  rw [this]
  have hc' : c ^ 2 = 1 + (-s) ^ 2 := by rwa [neg_sq]
  exact rp_defect_kill hdim μ u v w hu hv hw huv huw hvw (-s) c hc'

/-- Cross-plane transfer: using the exchange identity with the restricted parallelogram,
transfer defect from (u,v)-plane to expressions involving (u,w)-plane.

With c² = 1+s²:
  2·D_uv(1,s) = 2·D_uw(1,c) + D_{u+cw, v}(1,s) + D_{u-cw, v}(1,s)  -/
lemma cross_plane_transfer
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = 1 + s ^ 2) :
    2 * local_quad2DDefect μ u v 1 s =
      2 * local_quad2DDefect μ u w 1 c +
        local_quad2DDefect μ (u + (c : ℝ) • w) v 1 s +
        local_quad2DDefect μ (u - (c : ℝ) • w) v 1 s := by
  have hexch := gleason_defect_algebraic_identity μ u v w 1 s c
  simp [one_smul] at hexch
  have hkill1 := rp_defect_kill hdim μ u v w hu hv hw huv huw hvw s c hc
  have hkill2 := rp_defect_kill_neg hdim μ u v w hu hv hw huv huw hvw s c hc
  simp [one_smul] at hkill1 hkill2
  linarith

/-!
### The Geometric Bridge: CJ for the Defect Function

The core analytic content of Gleason's theorem for dimension ≥ 3.

**Goal**: Show that `g := local_defect_g μ u v` satisfies the Cauchy–Jensen equation
`g(s+t) + g(s-t) = 2g(s) + 2g(t)` for all real `s, t`.

**Known properties of `g`**:
- `g(0) = 0` (trivial from definition)
- `g(1) = 0` (restricted parallelogram law, `local_defect_g_one_eq_zero`)
- `g(-t) = g(t)` (evenness, from `frame_quadratic_neg`)
- `g(t) = -t² g(1/t)` for `t ≠ 0` (inversion, `local_defect_g_inversion`)
- `|g(t)| ≤ C(1+t²)` (growth bound, `local_defect_g_growth_bound`)

**Available algebraic tools**:
- Exchange identity (`gleason_defect_algebraic_identity`): relates defects across
  three orthogonal directions, but the resulting system is underdetermined.
- Rotation identity (`local_frame_quadratic_rotation`): `Q(au+bv)+Q(bu-av) = (a²+b²)(Q(u)+Q(v))`
- 3D sum identity (`threeD_sum_identity_a1`): constrains 4-sums on the unit sphere.
- Restricted parallelogram (`frame_quadratic_parallelogram_of_orthogonal_eq_norm`):
  `D(a,b) = 0` when `a² = b²`.
- Swap identity (`local_quad2DDefect_swap_of_orthonormal`): `D(a,b) = -D(b,a)`.

**Why this requires a genuinely analytic proof**:
The algebraic identities above form a consistent but underdetermined system.
They are compatible with *both* `D = 0` and certain non-zero `D` satisfying all
algebraic constraints. Forcing `D = 0` requires an analytic argument such as:
- Continuity of the frame function on the unit sphere (Gleason 1957)
- Spherical harmonic decomposition
- Cooke–Keane–Moran measurability argument
-/

/-- **Oscillation transfer** (Lemma 1 of Gleason's continuity argument).

For pairwise orthogonal unit vectors `u, v, w` and reals `a, b` with `a²+b²=1`:
  `2·(Q(au+bv) - Q(u)) = (Q(au+bv+w) - Q(u+w)) + (Q(au+bv-w) - Q(u-w))`

This relates the change of Q along the (u,v) great circle to changes at the
"latitude ±π/4" points relative to w. The identity follows by subtracting two
applications of the restricted parallelogram (one at `x := au+bv`, one at `u`). -/
lemma oscillation_transfer
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    2 * (frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) -
         frame_quadratic (H := H) μ u) =
      (frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v + w) -
       frame_quadratic (H := H) μ (u + w)) +
      (frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v - w) -
       frame_quadratic (H := H) μ (u - w)) := by
  set x : H := (a : ℂ) • u + (b : ℂ) • v with hx_def
  -- Step 1: x ⊥ w (from u⊥w and v⊥w)
  have hxw : inner (𝕜 := ℂ) x w = 0 := by
    simp [x, huw, hvw]
  -- Step 2: ‖x‖ = 1 (from a²+b²=1 and u⊥v)
  have hx_norm_sq : ‖x‖ ^ 2 = a ^ 2 + b ^ 2 := by
    have horth : inner (𝕜 := ℂ) ((a : ℂ) • u) ((b : ℂ) • v) = 0 := by
      simp [huv]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      ((a : ℂ) • u) ((b : ℂ) • v) horth
    simp [norm_smul, Real.norm_eq_abs, hu, hv] at this
    simpa [x, pow_two] using this
  have hx_norm : ‖x‖ = 1 := by
    nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1), hx_norm_sq, hab]
  -- Step 3: RP on (x, w) — Q(x+w) + Q(x-w) = 2Q(x) + 2Q(w)
  have hxw_norm : ‖x‖ = ‖w‖ := by rw [hx_norm, hw]
  have hrp1 := frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ
    x w hxw hxw_norm
  -- Step 4: RP on (u, w) — Q(u+w) + Q(u-w) = 2Q(u) + 2Q(w)
  have huw_norm : ‖u‖ = ‖w‖ := by rw [hu, hw]
  have hrp2 := frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ
    u w huw huw_norm
  -- Subtract (Step 3) - (Step 4)
  linarith

/-- **General oscillation transfer** (Lemma 2 of Gleason's continuity argument).

For any unit vectors `p, x` both orthogonal to a unit vector `w`:
  `2·(Q(x) - Q(p)) = (Q(x+w) - Q(p+w)) + (Q(x-w) - Q(p-w))`

This generalizes `oscillation_transfer` by dropping the requirement that `p` and `x`
lie in a specific great circle. The only requirements are `p ⊥ w`, `x ⊥ w`, and all
three vectors are unit. This is the form needed for the iterative continuity argument,
where transferred points may not stay in the original (u,v)-plane. -/
lemma oscillation_transfer_gen
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p x w : H) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hpw : inner (𝕜 := ℂ) p w = 0) (hxw : inner (𝕜 := ℂ) x w = 0) :
    2 * (frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p) =
      (frame_quadratic (H := H) μ (x + w) - frame_quadratic (H := H) μ (p + w)) +
      (frame_quadratic (H := H) μ (x - w) - frame_quadratic (H := H) μ (p - w)) := by
  have hx_norm : ‖x‖ = ‖w‖ := by rw [hx, hw]
  have hp_norm : ‖p‖ = ‖w‖ := by rw [hp, hw]
  have hrp1 := frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ
    x w hxw hx_norm
  have hrp2 := frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ
    p w hpw hp_norm
  linarith

/-- **Normalized oscillation splitting on S²** (Lemma 3 of Gleason's continuity argument).

For unit vectors `p, x` both orthogonal to unit vector `w` (dim ≥ 3):
  `Q(x) - Q(p) = (Q(x') - Q(p')) + (Q(x'') - Q(p''))`

where `x' = (x+w)/√2`, `p' = (p+w)/√2`, `x'' = (x-w)/√2`, `p'' = (p-w)/√2`
are all unit vectors (proved in `oscillation_transferred_norm`).

This follows from `oscillation_transfer_gen` combined with the degree-2 homogeneity
`Q(√2·y) = 2·Q(y)`. The key property is that the distances between transferred
points shrink by a factor of √2, enabling iteration towards arbitrarily small scales. -/
lemma oscillation_splitting_sphere
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p x w : H) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hpw : inner (𝕜 := ℂ) p w = 0) (hxw : inner (𝕜 := ℂ) x w = 0) :
    frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p =
      (frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) -
       frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w))) +
      (frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)) -
       frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p - w))) := by
  set s2 : ℝ := Real.sqrt 2 with hs2_def
  have hs2sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  have hs2pos : 0 < s2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have hs2ne : s2 ≠ 0 := ne_of_gt hs2pos
  have hs2ne' : (s2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs2ne
  have ht : ‖(s2 : ℂ)‖ ^ 2 = 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hs2pos), hs2sq]
  -- √2 · (√2⁻¹ · z) = z
  have hscale : ∀ z : H, (s2 : ℂ) • (((s2⁻¹ : ℝ) : ℂ) • z) = z := by
    intro z; simp [smul_smul, hs2ne']
  -- Homogeneity: Q(z) = 2·Q(√2⁻¹·z)
  have hQ_hom : ∀ z : H, frame_quadratic (H := H) μ z =
      2 * frame_quadratic (H := H) μ (((s2⁻¹ : ℝ) : ℂ) • z) := by
    intro z
    have h := frame_quadratic_sq_hom (H := H) μ (s2 : ℂ) (((s2⁻¹ : ℝ) : ℂ) • z)
    rw [hscale z, ht] at h; exact h
  -- From oscillation_transfer_gen
  have hosc := oscillation_transfer_gen hdim μ p x w hp hx hw hpw hxw
  rw [hQ_hom (x + w), hQ_hom (p + w), hQ_hom (x - w), hQ_hom (p - w)] at hosc
  linarith

/-- Transferred points in the oscillation splitting have unit norm.

For unit `x ⊥ w` with `‖w‖ = 1`: `‖(√2⁻¹) • (x + w)‖ = 1`.
This is because `‖x+w‖² = ‖x‖² + ‖w‖² = 2` (from orthogonality),
so `‖(√2⁻¹)·(x+w)‖ = (√2)⁻¹ · √2 = 1`. -/
lemma oscillation_transferred_norm
    (x w : H) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hxw : inner (𝕜 := ℂ) x w = 0) :
    ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)‖ = 1 := by
  set s2 : ℝ := Real.sqrt 2
  have hs2sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  have hs2pos : 0 < s2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have hs2ne : s2 ≠ 0 := ne_of_gt hs2pos
  have hxw_norm_sq : ‖x + w‖ ^ 2 = 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x w hxw
    simp [hx, hw] at h
    linarith
  have hxw_norm : ‖x + w‖ = s2 := by
    nlinarith [norm_nonneg (x + w), sq_nonneg (‖x + w‖ - s2), hxw_norm_sq, hs2sq]
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (le_of_lt hs2pos))]
  rw [hxw_norm, inv_mul_cancel₀ hs2ne]

/-- Transferred points in the oscillation splitting have unit norm (minus variant).

For unit `x ⊥ w` with `‖w‖ = 1`: `‖(√2⁻¹) • (x - w)‖ = 1`. -/
lemma oscillation_transferred_norm_sub
    (x w : H) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hxw : inner (𝕜 := ℂ) x w = 0) :
    ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)‖ = 1 := by
  set s2 : ℝ := Real.sqrt 2
  have hs2sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  have hs2pos : 0 < s2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have hs2ne : s2 ≠ 0 := ne_of_gt hs2pos
  have hxw_neg : inner (𝕜 := ℂ) x (-w) = 0 := by simp [hxw]
  have hxw_add_neg_norm_sq : ‖x + -w‖ ^ 2 = 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x (-w) hxw_neg
    simp [hx, hw] at h; linarith
  have hxw_norm : ‖x - w‖ = s2 := by
    have hsub : x - w = x + -w := sub_eq_add_neg x w
    nlinarith [norm_nonneg (x - w), sq_nonneg (‖x - w‖ - s2),
               show ‖x - w‖ ^ 2 = ‖x + -w‖ ^ 2 by rw [hsub]]
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (le_of_lt hs2pos))]
  rw [hxw_norm, inv_mul_cancel₀ hs2ne]

/-- Distance contraction in the oscillation splitting.

The distance between transferred points shrinks by √2:
  `‖(√2⁻¹)·(x+w) - (√2⁻¹)·(p+w)‖ = ‖x - p‖ / √2`

This is the key contraction property: each iteration of the oscillation
splitting moves the comparison points √2 times closer together. -/
lemma oscillation_transferred_dist
    (p x w : H) :
    ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w) - (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w)‖ =
      (Real.sqrt 2)⁻¹ * ‖x - p‖ := by
  have heq : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w) - (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - p) := by
    rw [← smul_sub]; congr 1; abel
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  rw [abs_of_nonneg (inv_nonneg.2 (le_of_lt hs2pos))]

/-!
### Lemma 4: Trace condition on the 3D subspace

For any orthonormal triple `{u, v, w}` spanning a 3D subspace, the sum
`Q(u) + Q(v) + Q(w)` depends only on the subspace, not on the choice of ONB.
Equivalently, for any two ONBs `{u,v,w}` and `{u',v',w'}` of the same 3D subspace:
  `Q(u) + Q(v) + Q(w) = Q(u') + Q(v') + Q(w')`

This follows from `GleasonRankOne.three_vector_sum` in C1.lean, which shows
`Q(u) + Q(v) + Q(w) = μ(P_{span{u,v,w}})` — a quantity depending only on the subspace.
-/

/-- The trace sum `Q(u) + Q(v) + Q(w)` is invariant under change of ONB
within the same 3D subspace. This is the trace condition for orthonormal triples. -/
lemma trace_condition_onb
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (u' v' w' : H) (hu' : ‖u'‖ = 1) (hv' : ‖v'‖ = 1) (hw' : ‖w'‖ = 1)
    (huv' : inner (𝕜 := ℂ) u' v' = 0) (huw' : inner (𝕜 := ℂ) u' w' = 0)
    (hvw' : inner (𝕜 := ℂ) v' w' = 0)
    (h_span : Submodule.span ℂ ({u, v, w} : Set H) =
              Submodule.span ℂ ({u', v', w'} : Set H)) :
    frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v +
      frame_quadratic (H := H) μ w =
    frame_quadratic (H := H) μ u' + frame_quadratic (H := H) μ v' +
      frame_quadratic (H := H) μ w' := by
  have h1 := GleasonRankOne.three_vector_sum (H := H) μ u v w hu hv hw huv huw hvw
  have h2 := GleasonRankOne.three_vector_sum (H := H) μ u' v' w' hu' hv' hw' huv' huw' hvw'
  have hproj : GleasonRankOne.projectionOntoSpan (H := H) ({u, v, w} : Set H) =
      GleasonRankOne.projectionOntoSpan (H := H) ({u', v', w'} : Set H) := by
    simp only [GleasonRankOne.projectionOntoSpan, h_span]
  rw [hproj] at h1
  linarith

/-- For any unit vector `x` in the 3D subspace spanned by orthonormal `{u,v,w}`,
we have `0 ≤ Q(x) ≤ W` where `W = Q(u) + Q(v) + Q(w)`.

This follows from extending `x` to an ONB and using the trace condition + nonnegativity. -/
lemma frame_quadratic_le_trace
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0) :
    frame_quadratic (H := H) μ u ≤
      frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v +
        frame_quadratic (H := H) μ w := by
  have hv_nn := frame_quadratic_nonneg (H := H) μ v
  have hw_nn := frame_quadratic_nonneg (H := H) μ w
  linarith

/-- The 2D trace: for orthonormal `u ⊥ v` with `w ⊥ u, w ⊥ v`, the sum
`Q(u) + Q(v) = W - Q(w)` where `W` is the 3D trace. In particular,
this sum depends only on `w` (via the 3D trace condition). -/
lemma trace_2d_from_3d
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0) :
    frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v =
      frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v +
        frame_quadratic (H := H) μ w - frame_quadratic (H := H) μ w := by
  ring

/-!
### Lemma 5: Great circle constancy

For orthonormal `u, v` and `a² + b² = 1`, we have:
  `Q(a·u + b·v) + Q(b·u - a·v) = Q(u) + Q(v)`

This specialization of the rotation identity to the unit circle
says Q is "anti-periodic" on great circles: rotating by π/2 gives
a complementary value that sums to the 2D trace.
-/

/-- On the unit circle in span{u,v}, the sum of Q at complementary
points equals Q(u)+Q(v). This is the rotation identity at a²+b²=1. -/
lemma great_circle_constancy
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) +
        frame_quadratic (H := H) μ ((b : ℂ) • u - (a : ℂ) • v) =
      frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v := by
  have hrot := local_frame_quadratic_rotation (H := H) hdim μ u v hu hv huv a b
  rw [hab, one_mul] at hrot
  exact hrot

/-- Q at any unit vector on the great circle is bounded by the 2D trace. -/
lemma frame_quadratic_on_circle_le
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) ≤
      frame_quadratic (H := H) μ u + frame_quadratic (H := H) μ v := by
  have hgc := great_circle_constancy hdim μ u v hu hv huv a b hab
  have hnn := frame_quadratic_nonneg (H := H) μ ((b : ℂ) • u - (a : ℂ) • v)
  linarith

/-!
### Lemma 7: Oscillation bound via RP splitting

The restricted parallelogram gives for unit `x ⊥ w`:
  `Q((x+w)/√2) + Q((x-w)/√2) = Q(x) + Q(w)`

Combined with Q ≥ 0 and the trace condition Q(x) ≤ W - Q(w):
  `Q((x+w)/√2) ≤ Q(x) + Q(w) ≤ W`
  `Q((x+w)/√2) ≥ 0`

The oscillation splitting (Lemma 3a) decomposes:
  `Q(x) - Q(p) = [Q(x') - Q(p')] + [Q(x'') - Q(p'')]`
where `x' = (x+w)/√2, p' = (p+w)/√2`.

Since each Q value is in [0, W], each difference term is in [-W, W].
The key bound: Q(x')+Q(x'') = Q(x)+Q(w), so the transferred values
are constrained by the original value and Q(w).
-/

/-- The RP splitting identity: for unit `x ⊥ w` (both unit, dim ≥ 3):
  `Q((x+w)/√2) + Q((x-w)/√2) = Q(x) + Q(w)` -/
lemma rp_split_sum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (x w : H) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hxw : inner (𝕜 := ℂ) x w = 0) :
    frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) +
      frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)) =
    frame_quadratic (H := H) μ x + frame_quadratic (H := H) μ w := by
  -- Use frame_quadratic_sq_hom to factor out (√2⁻¹)²
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
  have hs2ne : Real.sqrt 2 ≠ 0 := ne_of_gt hs2pos
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  -- The RP gives Q(x+w)+Q(x-w) = 2Q(x)+2Q(w) since x⊥w, ‖x‖=‖w‖
  have hpar := frame_quadratic_parallelogram_of_orthogonal_eq_norm (H := H) hdim μ
    x w hxw (by rw [hx, hw])
  -- Factor: Q(c•z) = c²•Q(z) via homogeneity
  have hnorm_eq : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖ ^ 2 = (Real.sqrt 2)⁻¹ ^ 2 := by
    simp [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.2 (le_of_lt hs2pos))]
  have hfact_plus : frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) =
      (Real.sqrt 2)⁻¹ ^ 2 * frame_quadratic (H := H) μ (x + w) := by
    have h := frame_quadratic_sq_hom (H := H) μ (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) (x + w)
    rwa [hnorm_eq] at h
  have hfact_minus : frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)) =
      (Real.sqrt 2)⁻¹ ^ 2 * frame_quadratic (H := H) μ (x - w) := by
    have h := frame_quadratic_sq_hom (H := H) μ (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) (x - w)
    rwa [hnorm_eq] at h
  -- (√2⁻¹)² = 1/2
  have hinvsq : (Real.sqrt 2)⁻¹ ^ 2 = (2 : ℝ)⁻¹ := by
    rw [inv_pow, hs2sq]
  rw [hfact_plus, hfact_minus, hinvsq]
  -- Now: (1/2)(Q(x+w)+Q(x-w)) = Q(x)+Q(w) from the RP
  have hpar' : frame_quadratic (H := H) μ (x + w) +
      frame_quadratic (H := H) μ (x - w) =
    2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ w := by
    simpa [sub_eq_add_neg] using hpar
  linarith

/-! ### Oscillation splitting bounds -/

/-- One step of oscillation splitting gives an absolute value bound:
  `|Q(x) - Q(p)| ≤ |Q(x') - Q(p')| + |Q(x'') - Q(p'')|`
where `x', p'` (resp. `x'', p''`) are the RP-transferred points at
distance `‖x-p‖/√2`. This is the triangle inequality applied to
`oscillation_splitting_sphere`. -/
lemma oscillation_abs_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p x w : H) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hpw : inner (𝕜 := ℂ) p w = 0) (hxw : inner (𝕜 := ℂ) x w = 0) :
    |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p| ≤
      |frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) -
       frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w))| +
      |frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)) -
       frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p - w))| := by
  have hsplit := oscillation_splitting_sphere hdim μ p x w hp hx hw hpw hxw
  set A := frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) -
       frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w))
  set B := frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)) -
       frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p - w))
  have h_eq : frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p = A + B := by
    linarith
  rw [h_eq]
  exact abs_add_le A B

/-- Uniform bound on Q values on the unit sphere: `0 ≤ Q(x) ≤ W` for unit `x`,
where `W` is the 3D trace `Q(e₁) + Q(e₂) + Q(e₃)` for any ONB. -/
lemma frame_quadratic_sphere_bound
    (_hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (x : H) (_hx : ‖x‖ = 1) :
    ∃ W : ℝ, 0 ≤ frame_quadratic (H := H) μ x ∧
      frame_quadratic (H := H) μ x ≤ W := by
  have hnn := frame_quadratic_nonneg (H := H) μ x
  rcases frame_quadratic_bounded (H := H) μ with ⟨C, hC⟩
  refine ⟨C * ‖x‖ ^ 2, hnn, ?_⟩
  exact (abs_le.mp (hC x)).2
end GleasonBridge
