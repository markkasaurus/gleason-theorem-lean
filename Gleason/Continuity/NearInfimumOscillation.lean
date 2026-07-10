import Gleason.Continuity.Defect.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section

open GleasonBridge RankOne Set

section Thm26

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

def realFramePoint (u v w : H) (ξ η r : ℝ) : H :=
  (ξ : ℂ) • u + (η : ℂ) • v + (r : ℂ) • w

lemma realFramePoint_add (u v w : H) (ξ₁ η₁ r₁ ξ₂ η₂ r₂ : ℝ) :
    realFramePoint u v w ξ₁ η₁ r₁ + realFramePoint u v w ξ₂ η₂ r₂ =
      realFramePoint u v w (ξ₁ + ξ₂) (η₁ + η₂) (r₁ + r₂) := by
  unfold realFramePoint
  simp [add_smul, add_assoc, add_left_comm, add_comm]

lemma realFramePoint_real_smul (u v w : H) (c ξ η r : ℝ) :
    (((c : ℝ) : ℂ) • realFramePoint u v w ξ η r) =
      realFramePoint u v w (c * ξ) (c * η) (c * r) := by
  unfold realFramePoint
  simp only [smul_add, smul_smul]
  congr 1 <;> simp [Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]

lemma inner_realFramePoint_realFramePoint
    {u v w : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (ξ₁ η₁ r₁ ξ₂ η₂ r₂ : ℝ) :
    inner (𝕜 := ℂ)
      (realFramePoint u v w ξ₁ η₁ r₁)
      (realFramePoint u v w ξ₂ η₂ r₂)
      =
    ((ξ₁ * ξ₂ + η₁ * η₂ + r₁ * r₂ : ℝ) : ℂ) := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by simpa [inner_eq_zero_symm] using huv
  have hwu : inner (𝕜 := ℂ) w u = 0 := by simpa [inner_eq_zero_symm] using huw
  have hwv : inner (𝕜 := ℂ) w v = 0 := by simpa [inner_eq_zero_symm] using hvw
  unfold realFramePoint
  simp [huv, huw, hvw, hvu, hwu, hwv, hu, hv, hw, inner_self_eq_norm_sq_to_K]
  ring

lemma norm_sq_realFramePoint
    {u v w : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (ξ η r : ℝ) :
    ‖realFramePoint u v w ξ η r‖ ^ 2 = ξ ^ 2 + η ^ 2 + r ^ 2 := by
  unfold realFramePoint
  have huv' : inner (𝕜 := ℂ) ((ξ : ℂ) • u) ((η : ℂ) • v) = 0 := by
    simp [huv]
  have huw' : inner (𝕜 := ℂ) (((ξ : ℂ) • u + (η : ℂ) • v)) ((r : ℂ) • w) = 0 := by
    simp [huw, hvw]
  have hxy :
      ‖(ξ : ℂ) • u + (η : ℂ) • v‖ ^ 2 = ξ ^ 2 + η ^ 2 := by
    have h :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        ((ξ : ℂ) • u) ((η : ℂ) • v) huv'
    simpa [pow_two, norm_smul, hu, hv, Real.norm_eq_abs, sq_abs] using h
  have h :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (((ξ : ℂ) • u + (η : ℂ) • v)) ((r : ℂ) • w) huw'
  calc
    ‖(ξ : ℂ) • u + (η : ℂ) • v + (r : ℂ) • w‖ ^ 2
        = ‖(ξ : ℂ) • u + (η : ℂ) • v‖ ^ 2 + ‖(r : ℂ) • w‖ ^ 2 := by
            simpa [pow_two, add_assoc] using h
    _ = ξ ^ 2 + η ^ 2 + r ^ 2 := by
          rw [hxy]
          simp [norm_smul, hw, Real.norm_eq_abs, sq_abs]

def equatorPoint (u v p : H) (φ : ℝ) : H :=
  realFramePoint u v p (Real.cos φ) (Real.sin φ) 0

def southPoint (u v p : H) (α : ℝ) : H :=
  realFramePoint u v p (Real.cos α) 0 (-Real.sin α)

def circleDen (α φ : ℝ) : ℝ :=
  Real.sqrt (1 - Real.cos α ^ 2 * Real.cos φ ^ 2)

def qPerpPoint (u v p : H) (α φ : ℝ) : H :=
  realFramePoint u v p
    (-(Real.cos α * Real.sin φ ^ 2) / circleDen α φ)
    ((Real.cos α) * Real.cos φ * Real.sin φ / circleDen α φ)
    (Real.sin α / circleDen α φ)

def rPerpPoint (u v p : H) (α φ : ℝ) : H :=
  realFramePoint u v p
    (Real.sin α ^ 2 * Real.cos φ / circleDen α φ)
    (Real.sin φ / circleDen α φ)
    (Real.sin α * Real.cos α * Real.cos φ / circleDen α φ)

lemma circleDen_sq (α φ : ℝ) :
    circleDen α φ ^ 2 = 1 - Real.cos α ^ 2 * Real.cos φ ^ 2 := by
  unfold circleDen
  rw [Real.sq_sqrt]
  nlinarith [sq_nonneg (Real.sin α), sq_nonneg (Real.sin φ), Real.sin_sq_add_cos_sq α,
    Real.sin_sq_add_cos_sq φ]

lemma circleDen_pos
    {α φ : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    0 < circleDen α φ := by
  unfold circleDen
  apply Real.sqrt_pos.2
  have hsina : 0 < Real.sin α := by
    have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
  have hsina_sq : 0 < Real.sin α ^ 2 := by positivity
  have hbound : Real.cos α ^ 2 * Real.cos φ ^ 2 ≤ Real.cos α ^ 2 := by
    have hcosφ : 0 ≤ Real.cos φ ^ 2 := sq_nonneg _
    have hcosφ_le : Real.cos φ ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (Real.sin φ), Real.sin_sq_add_cos_sq φ]
    simpa [mul_one] using
      (mul_le_mul_of_nonneg_left hcosφ_le (sq_nonneg (Real.cos α)))
  have hcos : 1 - Real.cos α ^ 2 = Real.sin α ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have hgt : 0 < 1 - Real.cos α ^ 2 * Real.cos φ ^ 2 := by
    have : 1 - Real.cos α ^ 2 ≤ 1 - Real.cos α ^ 2 * Real.cos φ ^ 2 := by linarith
    rw [hcos] at this
    linarith
  exact hgt

lemma circleDen_ne_zero
    {α φ : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    circleDen α φ ≠ 0 := ne_of_gt (circleDen_pos hα0 hαpi)

lemma equatorPoint_norm
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (φ : ℝ) :
    ‖equatorPoint u v p φ‖ = 1 := by
  have hnorm_sq :=
    norm_sq_realFramePoint hu hv hp huv hup hvp (Real.cos φ) (Real.sin φ) 0
  have hsq : ‖equatorPoint u v p φ‖ ^ 2 = 1 := by
    simpa [equatorPoint, Real.sin_sq_add_cos_sq φ] using hnorm_sq
  nlinarith [hsq, norm_nonneg (equatorPoint u v p φ)]

lemma southPoint_norm
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (α : ℝ) :
    ‖southPoint u v p α‖ = 1 := by
  have hnorm_sq :=
    norm_sq_realFramePoint hu hv hp huv hup hvp (Real.cos α) 0 (-Real.sin α)
  have hsq : ‖southPoint u v p α‖ ^ 2 = 1 := by
    simpa [southPoint, Real.sin_sq_add_cos_sq α] using hnorm_sq
  nlinarith [hsq, norm_nonneg (southPoint u v p α)]

lemma equatorPoint_qPerp_orth
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {α φ : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    inner (𝕜 := ℂ) (equatorPoint u v p φ) (qPerpPoint u v p α φ) = 0 := by
  have hden : circleDen α φ ≠ 0 := circleDen_ne_zero hα0 hαpi
  have hinner :=
    inner_realFramePoint_realFramePoint hu hv hp huv hup hvp
      (Real.cos φ) (Real.sin φ) 0
      (-(Real.cos α * Real.sin φ ^ 2) / circleDen α φ)
      ((Real.cos α) * Real.cos φ * Real.sin φ / circleDen α φ)
      (Real.sin α / circleDen α φ)
  have hscalar :
      Real.cos φ * (-(Real.cos α * Real.sin φ ^ 2) / circleDen α φ) +
        Real.sin φ * ((Real.cos α) * Real.cos φ * Real.sin φ / circleDen α φ) +
        0 * (Real.sin α / circleDen α φ) = 0 := by
    field_simp [hden]
    ring
  calc
    inner (𝕜 := ℂ) (equatorPoint u v p φ) (qPerpPoint u v p α φ)
        =
      ((Real.cos φ * (-(Real.cos α * Real.sin φ ^ 2) / circleDen α φ) +
          Real.sin φ * ((Real.cos α) * Real.cos φ * Real.sin φ / circleDen α φ) +
          0 * (Real.sin α / circleDen α φ) : ℝ) : ℂ) := by
            unfold equatorPoint qPerpPoint
            simpa using hinner
    _ = 0 := by exact_mod_cast hscalar

lemma qPerpPoint_norm
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {α φ : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    ‖qPerpPoint u v p α φ‖ = 1 := by
  have hden : circleDen α φ ≠ 0 := circleDen_ne_zero hα0 hαpi
  have hnorm_sq :=
    norm_sq_realFramePoint hu hv hp huv hup hvp
      (-(Real.cos α * Real.sin φ ^ 2) / circleDen α φ)
      ((Real.cos α) * Real.cos φ * Real.sin φ / circleDen α φ)
      (Real.sin α / circleDen α φ)
  have hden_sq : circleDen α φ ^ 2 = 1 - Real.cos α ^ 2 * Real.cos φ ^ 2 :=
    circleDen_sq α φ
  have hcoeff :
      (-(Real.cos α * Real.sin φ ^ 2) / circleDen α φ) ^ 2 +
        ((Real.cos α) * Real.cos φ * Real.sin φ / circleDen α φ) ^ 2 +
        (Real.sin α / circleDen α φ) ^ 2 = 1 := by
    have hden_sq' : circleDen α φ ^ 2 = Real.sin α ^ 2 + Real.cos α ^ 2 * Real.sin φ ^ 2 := by
      rw [hden_sq]
      nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq φ]
    field_simp [hden]
    ring_nf
    nlinarith [hden_sq', Real.sin_sq_add_cos_sq φ]
  have hsq : ‖qPerpPoint u v p α φ‖ ^ 2 = 1 := by
    calc
      ‖qPerpPoint u v p α φ‖ ^ 2
          =
        (-(Real.cos α * Real.sin φ ^ 2) / circleDen α φ) ^ 2 +
          ((Real.cos α) * Real.cos φ * Real.sin φ / circleDen α φ) ^ 2 +
          (Real.sin α / circleDen α φ) ^ 2 := by
            simpa [qPerpPoint] using hnorm_sq
      _ = 1 := hcoeff
  nlinarith [hsq, norm_nonneg (qPerpPoint u v p α φ)]

lemma southPoint_rPerp_orth
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {α φ : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    inner (𝕜 := ℂ) (southPoint u v p α) (rPerpPoint u v p α φ) = 0 := by
  have hden : circleDen α φ ≠ 0 := circleDen_ne_zero hα0 hαpi
  have hinner :=
    inner_realFramePoint_realFramePoint hu hv hp huv hup hvp
      (Real.cos α) 0 (-Real.sin α)
      (Real.sin α ^ 2 * Real.cos φ / circleDen α φ)
      (Real.sin φ / circleDen α φ)
      (Real.sin α * Real.cos α * Real.cos φ / circleDen α φ)
  have hscalar :
      Real.cos α * (Real.sin α ^ 2 * Real.cos φ / circleDen α φ) +
        0 * (Real.sin φ / circleDen α φ) +
        (-Real.sin α) * (Real.sin α * Real.cos α * Real.cos φ / circleDen α φ) = 0 := by
    field_simp [hden]
    ring
  calc
    inner (𝕜 := ℂ) (southPoint u v p α) (rPerpPoint u v p α φ)
        =
      ((Real.cos α * (Real.sin α ^ 2 * Real.cos φ / circleDen α φ) +
          0 * (Real.sin φ / circleDen α φ) +
          (-Real.sin α) * (Real.sin α * Real.cos α * Real.cos φ / circleDen α φ) : ℝ) : ℂ) := by
            unfold southPoint rPerpPoint
            simpa using hinner
    _ = 0 := by exact_mod_cast hscalar

lemma rPerpPoint_norm
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {α φ : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    ‖rPerpPoint u v p α φ‖ = 1 := by
  have hnorm_sq :=
    norm_sq_realFramePoint hu hv hp huv hup hvp
      (Real.sin α ^ 2 * Real.cos φ / circleDen α φ)
      (Real.sin φ / circleDen α φ)
      (Real.sin α * Real.cos α * Real.cos φ / circleDen α φ)
  have hden_sq : circleDen α φ ^ 2 = 1 - Real.cos α ^ 2 * Real.cos φ ^ 2 :=
    circleDen_sq α φ
  have hden : circleDen α φ ≠ 0 := circleDen_ne_zero hα0 hαpi
  have hcoeff :
      (Real.sin α ^ 2 * Real.cos φ / circleDen α φ) ^ 2 +
        (Real.sin φ / circleDen α φ) ^ 2 +
        (Real.sin α * Real.cos α * Real.cos φ / circleDen α φ) ^ 2 = 1 := by
    have hden_sq' : circleDen α φ ^ 2 = Real.sin φ ^ 2 + Real.sin α ^ 2 * Real.cos φ ^ 2 := by
      rw [hden_sq]
      nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq φ]
    field_simp [hden]
    ring_nf
    nlinarith [hden_sq', Real.sin_sq_add_cos_sq α]
  have hsq : ‖rPerpPoint u v p α φ‖ ^ 2 = 1 := by
    calc
      ‖rPerpPoint u v p α φ‖ ^ 2
          =
        (Real.sin α ^ 2 * Real.cos φ / circleDen α φ) ^ 2 +
          (Real.sin φ / circleDen α φ) ^ 2 +
          (Real.sin α * Real.cos α * Real.cos φ / circleDen α φ) ^ 2 := by
            simpa [rPerpPoint] using hnorm_sq
      _ = 1 := hcoeff
  nlinarith [hsq, norm_nonneg (rPerpPoint u v p α φ)]

lemma southPoint_eq_combo_equator_qPerp
    {u v p : H} {α φ : ℝ}
    (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    southPoint u v p α =
      (((Real.cos α * Real.cos φ : ℝ) : ℂ) • equatorPoint u v p φ) +
        (((-circleDen α φ : ℝ) : ℂ) • qPerpPoint u v p α φ) := by
  have hden : circleDen α φ ≠ 0 := circleDen_ne_zero hα0 hαpi
  unfold southPoint equatorPoint qPerpPoint
  rw [realFramePoint_real_smul, realFramePoint_real_smul, realFramePoint_add]
  congr 1
  · field_simp [hden]
    have hs : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    rw [hs]
    ring
  · field_simp [hden]
    ring
  · field_simp [hden]
    ring

lemma rPerpPoint_eq_combo_equator_qPerp
    {u v p : H} {α φ : ℝ}
    (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    rPerpPoint u v p α φ =
      (((circleDen α φ : ℝ) : ℂ) • equatorPoint u v p φ) +
        ((((Real.cos α * Real.cos φ) : ℝ) : ℂ) • qPerpPoint u v p α φ) := by
  have hden : circleDen α φ ≠ 0 := circleDen_ne_zero hα0 hαpi
  unfold rPerpPoint equatorPoint qPerpPoint
  rw [realFramePoint_real_smul, realFramePoint_real_smul, realFramePoint_add]
  congr 1
  · field_simp [hden]
    have hden_sq := circleDen_sq α φ
    have haux : Real.sin α ^ 2 = circleDen α φ ^ 2 - Real.cos α ^ 2 * Real.sin φ ^ 2 := by
      nlinarith [hden_sq, Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq φ]
    rw [haux]
    ring
  · field_simp [hden]
    have hden_sq := circleDen_sq α φ
    have haux : 1 = circleDen α φ ^ 2 + Real.cos α ^ 2 * Real.cos φ ^ 2 := by
      nlinarith [hden_sq]
    calc
      Real.sin φ = Real.sin φ * 1 := by ring
      _ = Real.sin φ * (circleDen α φ ^ 2 + Real.cos α ^ 2 * Real.cos φ ^ 2) := by
            rw [haux]
  · field_simp [hden]
    have hden_sq := circleDen_sq α φ
    nlinarith [hden_sq, Real.sin_sq_add_cos_sq α]

lemma south_combo_coeff_sq
    (α φ : ℝ) :
    (Real.cos α * Real.cos φ) ^ 2 + (-circleDen α φ) ^ 2 = 1 := by
  have hsq : (-circleDen α φ) ^ 2 = circleDen α φ ^ 2 := by ring
  rw [hsq, circleDen_sq α φ]
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq φ]

lemma south_rPerp_frame_sum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {α φ : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    frame_quadratic μ (southPoint u v p α) + frame_quadratic μ (rPerpPoint u v p α φ) =
      frame_quadratic μ (equatorPoint u v p φ) + frame_quadratic μ (qPerpPoint u v p α φ) := by
  let a : ℝ := Real.cos α * Real.cos φ
  let b : ℝ := -circleDen α φ
  have hab : a ^ 2 + b ^ 2 = 1 := by
    simpa [a, b] using south_combo_coeff_sq α φ
  have hgc :=
    GleasonBridge.great_circle_constancy hdim μ
      (equatorPoint u v p φ) (qPerpPoint u v p α φ)
      (equatorPoint_norm hu hv hp huv hup hvp φ)
      (qPerpPoint_norm hu hv hp huv hup hvp hα0 hαpi)
      (equatorPoint_qPerp_orth hu hv hp huv hup hvp hα0 hαpi)
      a b hab
  have hsouth :
      southPoint u v p α =
        ((a : ℂ) • equatorPoint u v p φ) + ((b : ℂ) • qPerpPoint u v p α φ) := by
    simpa [a, b] using southPoint_eq_combo_equator_qPerp (u := u) (v := v) (p := p) hα0 hαpi
  have hrperp :
      frame_quadratic μ (rPerpPoint u v p α φ) =
        frame_quadratic μ (((b : ℂ) • equatorPoint u v p φ) - ((a : ℂ) • qPerpPoint u v p α φ)) := by
    have hvec :
        rPerpPoint u v p α φ =
          -((((b : ℂ) • equatorPoint u v p φ) - ((a : ℂ) • qPerpPoint u v p α φ))) := by
      calc
        rPerpPoint u v p α φ
            = (((-b) : ℂ) • equatorPoint u v p φ) + ((a : ℂ) • qPerpPoint u v p α φ) := by
                simpa [a, b] using
                  rPerpPoint_eq_combo_equator_qPerp (u := u) (v := v) (p := p)
                    (α := α) (φ := φ) hα0 hαpi
        _ = -((((b : ℂ) • equatorPoint u v p φ) - ((a : ℂ) • qPerpPoint u v p α φ))) := by
              simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [hvec, frame_quadratic_neg]
  calc
    frame_quadratic μ (southPoint u v p α) + frame_quadratic μ (rPerpPoint u v p α φ)
        =
      frame_quadratic μ (((a : ℂ) • equatorPoint u v p φ) + ((b : ℂ) • qPerpPoint u v p α φ)) +
        frame_quadratic μ (((b : ℂ) • equatorPoint u v p φ) - ((a : ℂ) • qPerpPoint u v p α φ)) := by
          rw [hsouth, hrperp]
    _ =
      frame_quadratic μ (equatorPoint u v p φ) + frame_quadratic μ (qPerpPoint u v p α φ) := hgc

lemma qPerpPoint_zero
    {u v p : H} {α : ℝ}
    (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    qPerpPoint u v p α 0 = p := by
  have hsina_pos : 0 < Real.sin α := by
    have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
  have hsina_ne : Real.sin α ≠ 0 := ne_of_gt hsina_pos
  have hcircle : circleDen α 0 = Real.sin α := by
    have hsq : 1 - Real.cos α ^ 2 * Real.cos 0 ^ 2 = Real.sin α ^ 2 := by
      rw [Real.cos_zero]
      nlinarith [Real.sin_sq_add_cos_sq α]
    unfold circleDen
    rw [hsq, Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg hsina_pos.le
  have hcoeff : Real.sin α ^ 2 / Real.sin α = Real.sin α := by
    field_simp [hsina_ne]
  unfold qPerpPoint realFramePoint
  simp [Real.sin_zero, Real.cos_zero, hcircle, hsina_ne, hcoeff]

lemma rPerpPoint_zero
    {u v p : H} {α : ℝ}
    (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    rPerpPoint u v p α 0 = realFramePoint u v p (Real.sin α) 0 (Real.cos α) := by
  have hsina_pos : 0 < Real.sin α := by
    have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
  have hsina_ne : Real.sin α ≠ 0 := ne_of_gt hsina_pos
  have hcircle : circleDen α 0 = Real.sin α := by
    have hsq : 1 - Real.cos α ^ 2 * Real.cos 0 ^ 2 = Real.sin α ^ 2 := by
      rw [Real.cos_zero]
      nlinarith [Real.sin_sq_add_cos_sq α]
    unfold circleDen
    rw [hsq, Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg hsina_pos.le
  have hcoeff : Real.sin α ^ 2 / Real.sin α = Real.sin α := by
    field_simp [hsina_ne]
  unfold rPerpPoint
  simp [Real.sin_zero, Real.cos_zero, hcircle, hsina_ne, hcoeff, realFramePoint]

lemma continuous_qPerpPoint
    {u v p : H} {α : ℝ}
    (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    Continuous fun φ => qPerpPoint u v p α φ := by
  have hden : ∀ φ : ℝ, circleDen α φ ≠ 0 := fun φ => circleDen_ne_zero hα0 hαpi
  have hcircle : Continuous fun φ : ℝ => circleDen α φ := by
    unfold circleDen
    continuity
  have hA : Continuous fun φ : ℝ => -(Real.cos α * Real.sin φ ^ 2) / circleDen α φ := by
    exact (by continuity : Continuous fun φ : ℝ => -(Real.cos α * Real.sin φ ^ 2)).div hcircle hden
  have hB : Continuous fun φ : ℝ => Real.cos α * Real.cos φ * Real.sin φ / circleDen α φ := by
    exact (by continuity : Continuous fun φ : ℝ => Real.cos α * Real.cos φ * Real.sin φ).div hcircle hden
  have hC : Continuous fun φ : ℝ => Real.sin α / circleDen α φ := by
    exact (by continuity : Continuous fun φ : ℝ => Real.sin α).div hcircle hden
  have hAc : Continuous fun φ : ℝ => (((-(Real.cos α * Real.sin φ ^ 2) / circleDen α φ) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hA
  have hBc : Continuous fun φ : ℝ => (((Real.cos α * Real.cos φ * Real.sin φ / circleDen α φ : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp hB
  have hCc : Continuous fun φ : ℝ => (((Real.sin α / circleDen α φ : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp hC
  have hu : Continuous fun _ : ℝ => u := continuous_const
  have hv : Continuous fun _ : ℝ => v := continuous_const
  have hp : Continuous fun _ : ℝ => p := continuous_const
  simpa [qPerpPoint, realFramePoint, add_assoc] using
    (hAc.smul hu).add ((hBc.smul hv).add (hCc.smul hp))

lemma continuous_rPerpPoint
    {u v p : H} {α : ℝ}
    (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    Continuous fun φ => rPerpPoint u v p α φ := by
  have hden : ∀ φ : ℝ, circleDen α φ ≠ 0 := fun φ => circleDen_ne_zero hα0 hαpi
  have hcircle : Continuous fun φ : ℝ => circleDen α φ := by
    unfold circleDen
    continuity
  have hA : Continuous fun φ : ℝ => Real.sin α ^ 2 * Real.cos φ / circleDen α φ := by
    exact (by continuity : Continuous fun φ : ℝ => Real.sin α ^ 2 * Real.cos φ).div hcircle hden
  have hB : Continuous fun φ : ℝ => Real.sin φ / circleDen α φ := by
    exact (by continuity : Continuous fun φ : ℝ => Real.sin φ).div hcircle hden
  have hC : Continuous fun φ : ℝ => Real.sin α * Real.cos α * Real.cos φ / circleDen α φ := by
    exact (by continuity : Continuous fun φ : ℝ => Real.sin α * Real.cos α * Real.cos φ).div hcircle hden
  have hAc : Continuous fun φ : ℝ => (((Real.sin α ^ 2 * Real.cos φ / circleDen α φ : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp hA
  have hBc : Continuous fun φ : ℝ => (((Real.sin φ / circleDen α φ : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp hB
  have hCc : Continuous fun φ : ℝ => (((Real.sin α * Real.cos α * Real.cos φ / circleDen α φ : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp hC
  have hu : Continuous fun _ : ℝ => u := continuous_const
  have hv : Continuous fun _ : ℝ => v := continuous_const
  have hp : Continuous fun _ : ℝ => p := continuous_const
  simpa [rPerpPoint, realFramePoint, add_assoc] using
    (hAc.smul hu).add ((hBc.smul hv).add (hCc.smul hp))

lemma exists_small_companion_cap
    {u v p : H} {ε : ℝ} (hε : 0 < ε) :
    ∃ α δ : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < δ ∧
      ∀ {φ : ℝ}, |φ| < δ →
        dist (qPerpPoint u v p α φ) p < ε ∧
        dist (rPerpPoint u v p α φ) p < ε := by
  let northFun : ℝ → H := fun a => realFramePoint u v p (Real.sin a) 0 (Real.cos a)
  have hnorth_zero : northFun 0 = p := by
    simp [northFun, realFramePoint]
  have hnorth_cont : ContinuousAt northFun 0 := by
    have hsinC : Continuous fun a : ℝ => ((Real.sin a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp Real.continuous_sin
    have hzeroC : Continuous fun _ : ℝ => (0 : ℂ) := continuous_const
    have hcosC : Continuous fun a : ℝ => ((Real.cos a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp Real.continuous_cos
    have hu : Continuous fun _ : ℝ => u := continuous_const
    have hv : Continuous fun _ : ℝ => v := continuous_const
    have hp : Continuous fun _ : ℝ => p := continuous_const
    have hcont : Continuous northFun := by
      simpa [northFun, realFramePoint, add_assoc] using
        (hsinC.smul hu).add ((hzeroC.smul hv).add (hcosC.smul hp))
    exact hcont.continuousAt
  have hε2 : 0 < ε / 2 := by positivity
  rcases (Metric.continuousAt_iff.mp hnorth_cont) (ε / 2) hε2 with ⟨δα, hδα, hδαprop⟩
  let α : ℝ := min (δα / 2) (Real.pi / 4)
  have hα0 : 0 < α := by
    have hhalf_pos : 0 < δα / 2 := by positivity
    have hquarter_pos : 0 < Real.pi / 4 := by positivity
    exact lt_min hhalf_pos hquarter_pos
  have hαsmall : α < δα := by
    have hhalf_lt : δα / 2 < δα := by nlinarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf_lt
  have hαpi : α < Real.pi / 2 := by
    have hquarter_lt : Real.pi / 4 < Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    exact lt_of_le_of_lt (min_le_right _ _) hquarter_lt
  have hαdist : dist α 0 < δα := by
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos hα0] using hαsmall
  have hr0 : dist (rPerpPoint u v p α 0) p < ε / 2 := by
    have hraw := hδαprop hαdist
    simpa [hnorth_zero, rPerpPoint_zero (u := u) (v := v) (p := p) hα0 hαpi] using hraw
  have hqcont : ContinuousAt (fun φ : ℝ => qPerpPoint u v p α φ) 0 :=
    (continuous_qPerpPoint (u := u) (v := v) (p := p) hα0 hαpi).continuousAt
  have hrcont : ContinuousAt (fun φ : ℝ => rPerpPoint u v p α φ) 0 :=
    (continuous_rPerpPoint (u := u) (v := v) (p := p) hα0 hαpi).continuousAt
  rcases (Metric.continuousAt_iff.mp hqcont) ε hε with ⟨δq, hδq, hδqprop⟩
  rcases (Metric.continuousAt_iff.mp hrcont) (ε / 2) hε2 with ⟨δr, hδr, hδrprop⟩
  refine ⟨α, min δq δr, hα0, hαpi, lt_min hδq hδr, ?_⟩
  intro φ hφ
  have hφq : dist φ 0 < δq := by
    have : |φ| < δq := lt_of_lt_of_le hφ (min_le_left _ _)
    simpa [dist_eq_norm, Real.norm_eq_abs] using this
  have hφr : dist φ 0 < δr := by
    have : |φ| < δr := lt_of_lt_of_le hφ (min_le_right _ _)
    simpa [dist_eq_norm, Real.norm_eq_abs] using this
  have hq : dist (qPerpPoint u v p α φ) p < ε := by
    have hraw := hδqprop hφq
    simpa [qPerpPoint_zero (u := u) (v := v) (p := p) hα0 hαpi] using hraw
  have hrmid : dist (rPerpPoint u v p α φ) (rPerpPoint u v p α 0) < ε / 2 := hδrprop hφr
  have hr : dist (rPerpPoint u v p α φ) p < ε := by
    have htri :
        dist (rPerpPoint u v p α φ) p ≤
          dist (rPerpPoint u v p α φ) (rPerpPoint u v p α 0) +
            dist (rPerpPoint u v p α 0) p := by
      simpa using dist_triangle (rPerpPoint u v p α φ) (rPerpPoint u v p α 0) p
    have hlt :
        dist (rPerpPoint u v p α φ) p < ε / 2 + ε / 2 := by
      exact lt_of_le_of_lt htri (add_lt_add hrmid hr0)
    nlinarith
  exact ⟨hq, hr⟩

lemma equator_oscillation_bound_of_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hosc :
      ∀ x y : H, ‖x‖ = 1 → ‖y‖ = 1 →
        dist x p < ε → dist y p < ε →
        |frame_quadratic μ x - frame_quadratic μ y| ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {φ₁ φ₂ : ℝ}, |φ₁| < δ → |φ₂| < δ →
        |frame_quadratic μ (equatorPoint u v p φ₁) -
            frame_quadratic μ (equatorPoint u v p φ₂)| ≤ 2 * a := by
  rcases exists_small_companion_cap (u := u) (v := v) (p := p) hε with
    ⟨α, δ, hα0, hαpi, hδ, hcap⟩
  refine ⟨δ, hδ, ?_⟩
  intro φ₁ φ₂ hφ₁ hφ₂
  have hcap₁ := hcap hφ₁
  have hcap₂ := hcap hφ₂
  rcases hcap₁ with ⟨hq₁p, hr₁p⟩
  rcases hcap₂ with ⟨hq₂p, hr₂p⟩
  have hqbound :
      |frame_quadratic μ (qPerpPoint u v p α φ₂) -
          frame_quadratic μ (qPerpPoint u v p α φ₁)| ≤ a := by
    simpa [abs_sub_comm] using
      hosc (qPerpPoint u v p α φ₁) (qPerpPoint u v p α φ₂)
        (qPerpPoint_norm hu hv hp huv hup hvp hα0 hαpi)
        (qPerpPoint_norm hu hv hp huv hup hvp hα0 hαpi)
        hq₁p hq₂p
  have hrbound :
      |frame_quadratic μ (rPerpPoint u v p α φ₁) -
          frame_quadratic μ (rPerpPoint u v p α φ₂)| ≤ a := by
    exact hosc (rPerpPoint u v p α φ₁) (rPerpPoint u v p α φ₂)
      (rPerpPoint_norm hu hv hp huv hup hvp hα0 hαpi)
      (rPerpPoint_norm hu hv hp huv hup hvp hα0 hαpi)
      hr₁p hr₂p
  have hsum₁ :=
    south_rPerp_frame_sum hdim μ hu hv hp huv hup hvp (α := α) (φ := φ₁) hα0 hαpi
  have hsum₂ :=
    south_rPerp_frame_sum hdim μ hu hv hp huv hup hvp (α := α) (φ := φ₂) hα0 hαpi
  have hEq :
      frame_quadratic μ (equatorPoint u v p φ₁) -
          frame_quadratic μ (equatorPoint u v p φ₂) =
        (frame_quadratic μ (rPerpPoint u v p α φ₁) -
            frame_quadratic μ (rPerpPoint u v p α φ₂)) +
          (frame_quadratic μ (qPerpPoint u v p α φ₂) -
            frame_quadratic μ (qPerpPoint u v p α φ₁)) := by
    linarith
  calc
    |frame_quadratic μ (equatorPoint u v p φ₁) -
        frame_quadratic μ (equatorPoint u v p φ₂)|
        =
      |(frame_quadratic μ (rPerpPoint u v p α φ₁) -
          frame_quadratic μ (rPerpPoint u v p α φ₂)) +
        (frame_quadratic μ (qPerpPoint u v p α φ₂) -
          frame_quadratic μ (qPerpPoint u v p α φ₁))| := by
            rw [hEq]
    _ ≤
      |frame_quadratic μ (rPerpPoint u v p α φ₁) -
          frame_quadratic μ (rPerpPoint u v p α φ₂)| +
        |frame_quadratic μ (qPerpPoint u v p α φ₂) -
          frame_quadratic μ (qPerpPoint u v p α φ₁)| := by
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (abs_sub_le
                (frame_quadratic μ (rPerpPoint u v p α φ₁) -
                  frame_quadratic μ (rPerpPoint u v p α φ₂))
                0
                (-(frame_quadratic μ (qPerpPoint u v p α φ₂) -
                    frame_quadratic μ (qPerpPoint u v p α φ₁))))
    _ ≤ a + a := add_le_add hrbound hqbound
    _ = 2 * a := by ring

def coordBase : ℝ × ℝ × ℝ := (1, (0, 0))

def coordPoint (u v p : H) (x : ℝ × ℝ × ℝ) : H :=
  ((x.1 : ℝ) : ℂ) • u + ((((x.2.1 : ℝ) : ℂ) • v) + (((x.2.2 : ℝ) : ℂ) • p))

def southInnerCoord (α : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  x.1 * Real.cos α - x.2.2 * Real.sin α

def southDenCoord (α : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  Real.sqrt (1 - southInnerCoord α x ^ 2)

def ambientQPerpCoord (u v p : H) (α : ℝ) (x : ℝ × ℝ × ℝ) : H :=
  ((↑(southDenCoord α x) : ℂ)⁻¹) •
    ((((southInnerCoord α x : ℝ) : ℂ) • coordPoint u v p x) - southPoint u v p α)

def ambientRPerpCoord (u v p : H) (α : ℝ) (x : ℝ × ℝ × ℝ) : H :=
  ((↑(southDenCoord α x) : ℂ)⁻¹) •
    (coordPoint u v p x - (((southInnerCoord α x : ℝ) : ℂ) • southPoint u v p α))

lemma coordPoint_base (u v p : H) :
    coordPoint u v p coordBase = u := by
  simp [coordBase, coordPoint, realFramePoint]

lemma southInnerCoord_base (α : ℝ) :
    southInnerCoord α coordBase = Real.cos α := by
  simp [coordBase, southInnerCoord]

lemma southDenCoord_base
    {α : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    southDenCoord α coordBase = Real.sin α := by
  have hsina_pos : 0 < Real.sin α := by
    have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
  have hsq : 1 - Real.cos α ^ 2 = Real.sin α ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  unfold southDenCoord
  rw [southInnerCoord_base, hsq, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg hsina_pos.le

lemma ambientQPerpCoord_base
    {u v p : H} {α : ℝ}
    (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    ambientQPerpCoord u v p α coordBase = p := by
  have hsina_pos : 0 < Real.sin α := by
    have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
  have hsina_ne : Real.sin α ≠ 0 := ne_of_gt hsina_pos
  have hsina_neC : ((Real.sin α : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsina_ne
  rw [ambientQPerpCoord, coordPoint_base, southInnerCoord_base, southDenCoord_base hα0 hαpi]
  unfold southPoint realFramePoint
  have hscalar : ((↑(Real.sin α) : ℂ)⁻¹) * (Real.sin α : ℂ) = 1 := by
    simpa using (inv_mul_cancel₀ hsina_neC :
      ((↑(Real.sin α) : ℂ)⁻¹) * (Real.sin α : ℂ) = 1)
  calc
    ((↑(Real.sin α) : ℂ)⁻¹) •
        ((Real.cos α : ℂ) • u - ((Real.cos α : ℂ) • u + (0 : ℂ) • v + ((-Real.sin α : ℝ) : ℂ) • p))
        = ((↑(Real.sin α) : ℂ)⁻¹) • ((Real.sin α : ℂ) • p) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = p := by
          rw [smul_smul, hscalar, one_smul]

lemma ambientRPerpCoord_base
    {u v p : H} {α : ℝ}
    (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    ambientRPerpCoord u v p α coordBase =
      realFramePoint u v p (Real.sin α) 0 (Real.cos α) := by
  have hsina_pos : 0 < Real.sin α := by
    have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
  have hsina_ne : Real.sin α ≠ 0 := ne_of_gt hsina_pos
  have hsq : 1 - Real.cos α ^ 2 = Real.sin α ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  rw [ambientRPerpCoord, coordPoint_base, southInnerCoord_base, southDenCoord_base hα0 hαpi]
  nth_rewrite 1 [show u = realFramePoint u v p 1 0 0 by
    simp [realFramePoint]]
  have hscaledSouth :
      (Real.cos α : ℂ) • southPoint u v p α =
        realFramePoint u v p (Real.cos α ^ 2) 0 (-(Real.sin α * Real.cos α)) := by
    simpa [southPoint, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (realFramePoint_real_smul u v p (Real.cos α) (Real.cos α) 0 (-Real.sin α))
  rw [hscaledSouth, sub_eq_add_neg]
  have hnegScaledSouth :
      -realFramePoint u v p (Real.cos α ^ 2) 0 (-(Real.sin α * Real.cos α)) =
        realFramePoint u v p (-Real.cos α ^ 2) 0 (Real.sin α * Real.cos α) := by
    unfold realFramePoint
    simp [smul_add, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm, mul_assoc]
  rw [hnegScaledSouth, realFramePoint_add]
  have hinv : ((↑(Real.sin α) : ℂ)⁻¹) = (((Real.sin α)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hinv, realFramePoint_real_smul]
  congr 3
  · calc
      (Real.sin α)⁻¹ * (1 + -Real.cos α ^ 2)
          = (Real.sin α)⁻¹ * (1 - Real.cos α ^ 2) := by ring
      _ = (Real.sin α)⁻¹ * (Real.sin α ^ 2) := by rw [hsq]
      _ = ((Real.sin α)⁻¹ * Real.sin α) * Real.sin α := by ring
      _ = Real.sin α := by
            rw [inv_mul_cancel₀ hsina_ne, one_mul]
  · simp
  · calc
      (Real.sin α)⁻¹ * (0 + Real.sin α * Real.cos α)
          = (Real.sin α)⁻¹ * (Real.sin α * Real.cos α) := by ring
      _ 
          = ((Real.sin α)⁻¹ * Real.sin α) * Real.cos α := by ring
      _ = Real.cos α := by
            rw [inv_mul_cancel₀ hsina_ne, one_mul]

lemma coordPoint_norm
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    ‖coordPoint u v p x‖ = 1 := by
  have hnorm_sq :=
    norm_sq_realFramePoint hu hv hp huv hup hvp x.1 x.2.1 x.2.2
  have hsq : ‖coordPoint u v p x‖ ^ 2 = 1 := by
    simpa [coordPoint, realFramePoint, add_assoc, hx] using hnorm_sq
  nlinarith [hsq, norm_nonneg (coordPoint u v p x)]

lemma inner_coordPoint_southPoint
    {u v p : H} {α : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (x : ℝ × ℝ × ℝ) :
    inner (𝕜 := ℂ) (coordPoint u v p x) (southPoint u v p α) =
      ((southInnerCoord α x : ℝ) : ℂ) := by
  have hinner :=
    inner_realFramePoint_realFramePoint hu hv hp huv hup hvp
      x.1 x.2.1 x.2.2 (Real.cos α) 0 (-Real.sin α)
  simpa [coordPoint, southPoint, realFramePoint, southInnerCoord, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm] using hinner

lemma southInnerCoord_sq_le_one
    {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    southInnerCoord α x ^ 2 ≤ 1 := by
  unfold southInnerCoord
  have hrot :
      (x.1 * Real.cos α - x.2.2 * Real.sin α) ^ 2 +
        (x.1 * Real.sin α + x.2.2 * Real.cos α) ^ 2
        = x.1 ^ 2 + x.2.2 ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have hxr : x.1 ^ 2 + x.2.2 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (x.2.1), hx]
  nlinarith [hrot]

lemma southDenCoord_sq
    {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    southDenCoord α x ^ 2 = 1 - southInnerCoord α x ^ 2 := by
  unfold southDenCoord
  rw [Real.sq_sqrt]
  exact sub_nonneg.mpr (southInnerCoord_sq_le_one hx)

lemma coordPoint_ambientQPerp_orth
    {u v p : H} {α : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    inner (𝕜 := ℂ) (coordPoint u v p x) (ambientQPerpCoord u v p α x) = 0 := by
  let q := coordPoint u v p x
  let s : ℝ := southInnerCoord α x
  have hqnorm : ‖q‖ = 1 := coordPoint_norm hu hv hp huv hup hvp hx
  have hqq : inner (𝕜 := ℂ) q q = 1 := by
    simpa [q, inner_self_eq_norm_sq_to_K, hqnorm]
  have hqs :
      inner (𝕜 := ℂ) q (southPoint u v p α) = ((s : ℝ) : ℂ) := by
    simpa [q, s] using inner_coordPoint_southPoint hu hv hp huv hup hvp (α := α) x
  unfold ambientQPerpCoord
  calc
    inner (𝕜 := ℂ) q (((↑(southDenCoord α x) : ℂ)⁻¹) •
        ((((s : ℝ) : ℂ) • q) - southPoint u v p α))
        = ((↑(southDenCoord α x) : ℂ)⁻¹) *
            ((((s : ℝ) : ℂ) * inner (𝕜 := ℂ) q q) -
              inner (𝕜 := ℂ) q (southPoint u v p α)) := by
              rw [inner_smul_right, inner_sub_right, inner_smul_right]
    _ = 0 := by
          rw [hqq, hqs]
          ring

lemma southPoint_ambientRPerp_orth
    {u v p : H} {α : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    inner (𝕜 := ℂ) (southPoint u v p α) (ambientRPerpCoord u v p α x) = 0 := by
  let s : ℝ := southInnerCoord α x
  have hsouth :
      inner (𝕜 := ℂ) (southPoint u v p α) (southPoint u v p α) = 1 := by
    have hnorm := southPoint_norm hu hv hp huv hup hvp α
    simpa [inner_self_eq_norm_sq_to_K, hnorm]
  have hsq :
      inner (𝕜 := ℂ) (southPoint u v p α) (coordPoint u v p x) = ((s : ℝ) : ℂ) := by
    have hinner :=
      inner_realFramePoint_realFramePoint hu hv hp huv hup hvp
        (Real.cos α) 0 (-Real.sin α) x.1 x.2.1 x.2.2
    simpa [coordPoint, southPoint, realFramePoint, s, southInnerCoord, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hinner
  unfold ambientRPerpCoord
  calc
    inner (𝕜 := ℂ) (southPoint u v p α)
        (((↑(southDenCoord α x) : ℂ)⁻¹) •
          (coordPoint u v p x - (((s : ℝ) : ℂ) • southPoint u v p α)))
        = ((↑(southDenCoord α x) : ℂ)⁻¹) *
            (inner (𝕜 := ℂ) (southPoint u v p α) (coordPoint u v p x) -
              (((s : ℝ) : ℂ) * inner (𝕜 := ℂ) (southPoint u v p α) (southPoint u v p α))) := by
                rw [inner_smul_right, inner_sub_right, inner_smul_right]
    _ = 0 := by
          rw [hsq, hsouth]
          ring

lemma southPoint_eq_combo_coord_ambientQPerp
    {u v p : H} {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hden : southDenCoord α x ≠ 0) :
    southPoint u v p α =
      (((southInnerCoord α x : ℝ) : ℂ) • coordPoint u v p x) -
        (((southDenCoord α x : ℝ) : ℂ) • ambientQPerpCoord u v p α x) := by
  have hdenC : ((southDenCoord α x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hden
  symm
  unfold ambientQPerpCoord
  calc
    (((southInnerCoord α x : ℝ) : ℂ) • coordPoint u v p x) -
        (((southDenCoord α x : ℝ) : ℂ) •
          (((↑(southDenCoord α x) : ℂ)⁻¹) •
            ((((southInnerCoord α x : ℝ) : ℂ) • coordPoint u v p x) - southPoint u v p α)))
        =
      (((southInnerCoord α x : ℝ) : ℂ) • coordPoint u v p x) -
        ((((↑(southDenCoord α x) : ℂ) * (↑(southDenCoord α x) : ℂ)⁻¹) : ℂ) •
          ((((southInnerCoord α x : ℝ) : ℂ) • coordPoint u v p x) - southPoint u v p α)) := by
            rw [smul_smul]
    _ =
      (((southInnerCoord α x : ℝ) : ℂ) • coordPoint u v p x) -
        ((((southInnerCoord α x : ℝ) : ℂ) • coordPoint u v p x) - southPoint u v p α) := by
          rw [mul_inv_cancel₀ hdenC, one_smul]
    _ = southPoint u v p α := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma coordPoint_eq_combo_south_ambientRPerp
    {u v p : H} {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hden : southDenCoord α x ≠ 0) :
    coordPoint u v p x =
      (((southInnerCoord α x : ℝ) : ℂ) • southPoint u v p α) +
        (((southDenCoord α x : ℝ) : ℂ) • ambientRPerpCoord u v p α x) := by
  have hdenC : ((southDenCoord α x : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hden
  symm
  unfold ambientRPerpCoord
  calc
    (((southInnerCoord α x : ℝ) : ℂ) • southPoint u v p α) +
        (((southDenCoord α x : ℝ) : ℂ) •
          (((↑(southDenCoord α x) : ℂ)⁻¹) •
            (coordPoint u v p x -
              (((southInnerCoord α x : ℝ) : ℂ) • southPoint u v p α))))
        =
      (((southInnerCoord α x : ℝ) : ℂ) • southPoint u v p α) +
        ((((↑(southDenCoord α x) : ℂ) * (↑(southDenCoord α x) : ℂ)⁻¹) : ℂ) •
          (coordPoint u v p x -
            (((southInnerCoord α x : ℝ) : ℂ) • southPoint u v p α))) := by
              rw [smul_smul]
    _ =
      (((southInnerCoord α x : ℝ) : ℂ) • southPoint u v p α) +
        (coordPoint u v p x -
          (((southInnerCoord α x : ℝ) : ℂ) • southPoint u v p α)) := by
            rw [mul_inv_cancel₀ hdenC, one_smul]
    _ = coordPoint u v p x := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma coordPoint_sub_base
    (u v p : H) (x : ℝ × ℝ × ℝ) :
    coordPoint u v p x - u =
      realFramePoint u v p (x.1 - 1) x.2.1 x.2.2 := by
  calc
    coordPoint u v p x - u
        = ((((x.1 : ℝ) : ℂ) - 1) • u) +
            ((((x.2.1 : ℝ) : ℂ) • v) + (((x.2.2 : ℝ) : ℂ) • p)) := by
              simp [coordPoint, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_smul]
    _ = realFramePoint u v p (x.1 - 1) x.2.1 x.2.2 := by
          simp [realFramePoint, add_assoc, sub_eq_add_neg]

lemma coordPoint_sub
    (u v p : H) (x y : ℝ × ℝ × ℝ) :
    coordPoint u v p x - coordPoint u v p y =
      realFramePoint u v p (x.1 - y.1) (x.2.1 - y.2.1) (x.2.2 - y.2.2) := by
  simp [coordPoint, realFramePoint, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    add_smul]

lemma realFramePoint_abs_fst_le
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (ξ η r : ℝ) :
    |ξ| ≤ ‖realFramePoint u v p ξ η r‖ := by
  have hsq := norm_sq_realFramePoint hu hv hp huv hup hvp ξ η r
  have hsquare : |ξ| ^ 2 ≤ ‖realFramePoint u v p ξ η r‖ ^ 2 := by
    rw [hsq, sq_abs]
    nlinarith [sq_nonneg η, sq_nonneg r]
  exact (sq_le_sq₀ (abs_nonneg ξ) (norm_nonneg _)).1 hsquare

lemma realFramePoint_abs_snd_fst_le
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (ξ η r : ℝ) :
    |η| ≤ ‖realFramePoint u v p ξ η r‖ := by
  have hsq := norm_sq_realFramePoint hu hv hp huv hup hvp ξ η r
  have hsquare : |η| ^ 2 ≤ ‖realFramePoint u v p ξ η r‖ ^ 2 := by
    rw [hsq, sq_abs]
    nlinarith [sq_nonneg ξ, sq_nonneg r]
  exact (sq_le_sq₀ (abs_nonneg η) (norm_nonneg _)).1 hsquare

lemma realFramePoint_abs_snd_snd_le
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (ξ η r : ℝ) :
    |r| ≤ ‖realFramePoint u v p ξ η r‖ := by
  have hsq := norm_sq_realFramePoint hu hv hp huv hup hvp ξ η r
  have hsquare : |r| ^ 2 ≤ ‖realFramePoint u v p ξ η r‖ ^ 2 := by
    rw [hsq, sq_abs]
    nlinarith [sq_nonneg ξ, sq_nonneg η]
  exact (sq_le_sq₀ (abs_nonneg r) (norm_nonneg _)).1 hsquare

lemma dist_coordBase_le_dist_coordPoint
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (x : ℝ × ℝ × ℝ) :
    dist x coordBase ≤ dist (coordPoint u v p x) u := by
  let a : ℝ := x.1 - 1
  let b : ℝ := x.2.1
  let c : ℝ := x.2.2
  have ha : |a| ≤ ‖realFramePoint u v p a b c‖ := by
    exact realFramePoint_abs_fst_le hu hv hp huv hup hvp a b c
  have hb : |b| ≤ ‖realFramePoint u v p a b c‖ := by
    exact realFramePoint_abs_snd_fst_le hu hv hp huv hup hvp a b c
  have hc : |c| ≤ ‖realFramePoint u v p a b c‖ := by
    exact realFramePoint_abs_snd_snd_le hu hv hp huv hup hvp a b c
  have hmax :
      max |a| (max |b| |c|) ≤ ‖realFramePoint u v p a b c‖ := by
    exact max_le ha (max_le hb hc)
  have hdist_coords :
      dist x coordBase = max |a| (max |b| |c|) := by
    rcases x with ⟨x1, x23⟩
    rcases x23 with ⟨x2, x3⟩
    simp [coordBase, a, b, c, Prod.dist_eq, Prod.norm_def, Real.dist_eq, Real.norm_eq_abs]
  have hdist_vec :
      dist (coordPoint u v p x) u = ‖realFramePoint u v p a b c‖ := by
    simp [dist_eq_norm, coordPoint_sub_base, a, b, c]
  rw [hdist_coords, hdist_vec]
  exact hmax

lemma dist_coords_le_dist_coordPoint
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (x y : ℝ × ℝ × ℝ) :
    dist x y ≤ dist (coordPoint u v p x) (coordPoint u v p y) := by
  let a : ℝ := x.1 - y.1
  let b : ℝ := x.2.1 - y.2.1
  let c : ℝ := x.2.2 - y.2.2
  have ha : |a| ≤ ‖realFramePoint u v p a b c‖ := by
    exact realFramePoint_abs_fst_le hu hv hp huv hup hvp a b c
  have hb : |b| ≤ ‖realFramePoint u v p a b c‖ := by
    exact realFramePoint_abs_snd_fst_le hu hv hp huv hup hvp a b c
  have hc : |c| ≤ ‖realFramePoint u v p a b c‖ := by
    exact realFramePoint_abs_snd_snd_le hu hv hp huv hup hvp a b c
  have hmax :
      max |a| (max |b| |c|) ≤ ‖realFramePoint u v p a b c‖ := by
    exact max_le ha (max_le hb hc)
  have hdist_coords :
      dist x y = max |a| (max |b| |c|) := by
    rcases x with ⟨x1, x23⟩
    rcases x23 with ⟨x2, x3⟩
    rcases y with ⟨y1, y23⟩
    rcases y23 with ⟨y2, y3⟩
    simp [a, b, c, Prod.dist_eq, Prod.norm_def, Real.dist_eq, Real.norm_eq_abs]
  have hdist_vec :
      dist (coordPoint u v p x) (coordPoint u v p y) = ‖realFramePoint u v p a b c‖ := by
    simp [dist_eq_norm, coordPoint_sub, a, b, c]
  rw [hdist_coords, hdist_vec]
  exact hmax

lemma dist_coordPoint_le_three_mul_dist_coords
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (x y : ℝ × ℝ × ℝ) :
    dist (coordPoint u v p x) (coordPoint u v p y) ≤ 3 * dist x y := by
  let a : ℝ := x.1 - y.1
  let b : ℝ := x.2.1 - y.2.1
  let c : ℝ := x.2.2 - y.2.2
  have hdist_coords :
      dist x y = max |a| (max |b| |c|) := by
    rcases x with ⟨x1, x23⟩
    rcases x23 with ⟨x2, x3⟩
    rcases y with ⟨y1, y23⟩
    rcases y23 with ⟨y2, y3⟩
    simp [a, b, c, Prod.dist_eq, Prod.norm_def, Real.dist_eq, Real.norm_eq_abs]
  have ha : |a| ≤ dist x y := by
    rw [hdist_coords]
    exact le_max_left _ _
  have hb : |b| ≤ dist x y := by
    rw [hdist_coords]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hc : |c| ≤ dist x y := by
    rw [hdist_coords]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have habc : |a| + |b| + |c| ≤ 3 * dist x y := by
    nlinarith
  have hnorm :
      ‖realFramePoint u v p a b c‖ ≤ |a| + |b| + |c| := by
    unfold realFramePoint
    calc
      ‖(a : ℂ) • u + (b : ℂ) • v + (c : ℂ) • p‖
          ≤ ‖(a : ℂ) • u + (b : ℂ) • v‖ + ‖(c : ℂ) • p‖ := by
            exact norm_add_le _ _
      _ ≤ ‖(a : ℂ) • u‖ + ‖(b : ℂ) • v‖ + ‖(c : ℂ) • p‖ := by
            linarith [norm_add_le ((a : ℂ) • u) ((b : ℂ) • v)]
      _ = |a| + |b| + |c| := by
            simp [norm_smul, hu, hv, hp, Real.norm_eq_abs, add_assoc]
  have hdist_vec :
      dist (coordPoint u v p x) (coordPoint u v p y) = ‖realFramePoint u v p a b c‖ := by
    simp [dist_eq_norm, coordPoint_sub, a, b, c]
  rw [hdist_vec]
  exact le_trans hnorm habc

lemma ambientQPerpCoord_norm
    {u v p : H} {α : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    ‖ambientQPerpCoord u v p α x‖ = 1 := by
  let q := coordPoint u v p x
  let w := ambientQPerpCoord u v p α x
  let s : ℝ := southInnerCoord α x
  let d : ℝ := southDenCoord α x
  have hq : ‖q‖ = 1 := by
    simpa [q] using coordPoint_norm hu hv hp huv hup hvp hx
  have hsouth : ‖southPoint u v p α‖ = 1 := southPoint_norm hu hv hp huv hup hvp α
  have horth : inner (𝕜 := ℂ) q w = 0 := by
    simpa [q, w] using coordPoint_ambientQPerp_orth hu hv hp huv hup hvp (α := α) hx
  have hdecomp :
      southPoint u v p α = ((s : ℂ) • q) + (((-d : ℝ) : ℂ) • w) := by
    simpa [q, w, s, d, sub_eq_add_neg, neg_smul] using
      southPoint_eq_combo_coord_ambientQPerp (u := u) (v := v) (p := p) (α := α) (x := x) hden
  have hsouth_sq : ‖southPoint u v p α‖ ^ 2 = 1 := by
    nlinarith [hsouth, norm_nonneg (southPoint u v p α)]
  have hpyth :
      ‖southPoint u v p α‖ ^ 2 = s ^ 2 + d ^ 2 * ‖w‖ ^ 2 := by
    have horth' : inner (𝕜 := ℂ) ((s : ℂ) • q) (((-d : ℝ) : ℂ) • w) = 0 := by
      rw [inner_smul_left, inner_smul_right, horth]
      simp
    have hsq :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        ((s : ℂ) • q) ((((-d : ℝ) : ℂ) • w)) horth'
    have hs_term : ‖((s : ℂ) • q)‖ ^ 2 = s ^ 2 := by
      calc
        ‖((s : ℂ) • q)‖ ^ 2 = (|s| * ‖q‖) ^ 2 := by
          simp [norm_smul, Real.norm_eq_abs]
        _ = (|s| * 1) ^ 2 := by rw [hq]
        _ = s ^ 2 := by
          nlinarith [sq_abs s]
    have hd_term : ‖(((-d : ℝ) : ℂ) • w)‖ ^ 2 = d ^ 2 * ‖w‖ ^ 2 := by
      calc
        ‖(((-d : ℝ) : ℂ) • w)‖ ^ 2 = (|d| * ‖w‖) ^ 2 := by
          simp [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
        _ = d ^ 2 * ‖w‖ ^ 2 := by
          nlinarith [sq_abs d]
    calc
      ‖southPoint u v p α‖ ^ 2
          = ‖((s : ℂ) • q) + (((-d : ℝ) : ℂ) • w)‖ ^ 2 := by rw [hdecomp]
      _ = ‖((s : ℂ) • q)‖ ^ 2 + ‖(((-d : ℝ) : ℂ) • w)‖ ^ 2 := by
            simpa [pow_two] using hsq
      _ = s ^ 2 + d ^ 2 * ‖w‖ ^ 2 := by rw [hs_term, hd_term]
  have hd_sq : d ^ 2 = 1 - s ^ 2 := by
    simpa [d, s] using southDenCoord_sq (α := α) (x := x) hx
  have hd_sq_pos : 0 < d ^ 2 := sq_pos_iff.mpr hden
  have hw_sq : ‖w‖ ^ 2 = 1 := by
    nlinarith [hsouth_sq, hpyth, hd_sq, hd_sq_pos]
  nlinarith [hw_sq, norm_nonneg w]

lemma ambientRPerpCoord_norm
    {u v p : H} {α : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    ‖ambientRPerpCoord u v p α x‖ = 1 := by
  let w := ambientRPerpCoord u v p α x
  let s : ℝ := southInnerCoord α x
  let d : ℝ := southDenCoord α x
  have hsouth : ‖southPoint u v p α‖ = 1 := southPoint_norm hu hv hp huv hup hvp α
  have hq : ‖coordPoint u v p x‖ = 1 := coordPoint_norm hu hv hp huv hup hvp hx
  have horth :
      inner (𝕜 := ℂ) (southPoint u v p α) w = 0 := by
    simpa [w] using southPoint_ambientRPerp_orth hu hv hp huv hup hvp (α := α) hx
  have hdecomp :
      coordPoint u v p x =
        ((s : ℂ) • southPoint u v p α) + ((d : ℂ) • w) := by
    simpa [w, s, d] using
      coordPoint_eq_combo_south_ambientRPerp (u := u) (v := v) (p := p) (α := α) (x := x) hden
  have hq_sq : ‖coordPoint u v p x‖ ^ 2 = 1 := by
    nlinarith [hq, norm_nonneg (coordPoint u v p x)]
  have hpyth :
      ‖coordPoint u v p x‖ ^ 2 = s ^ 2 + d ^ 2 * ‖w‖ ^ 2 := by
    have horth' :
        inner (𝕜 := ℂ) ((s : ℂ) • southPoint u v p α) ((d : ℂ) • w) = 0 := by
      rw [inner_smul_left, inner_smul_right, horth]
      simp
    have hsq :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        ((s : ℂ) • southPoint u v p α) (((d : ℝ) : ℂ) • w) horth'
    have hs_term : ‖((s : ℂ) • southPoint u v p α)‖ ^ 2 = s ^ 2 := by
      calc
        ‖((s : ℂ) • southPoint u v p α)‖ ^ 2 = (|s| * ‖southPoint u v p α‖) ^ 2 := by
          simp [norm_smul, Real.norm_eq_abs]
        _ = (|s| * 1) ^ 2 := by rw [hsouth]
        _ = s ^ 2 := by
          nlinarith [sq_abs s]
    have hd_term : ‖((d : ℂ) • w)‖ ^ 2 = d ^ 2 * ‖w‖ ^ 2 := by
      calc
        ‖((d : ℂ) • w)‖ ^ 2 = (|d| * ‖w‖) ^ 2 := by
          simp [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        _ = d ^ 2 * ‖w‖ ^ 2 := by
          nlinarith [sq_abs d]
    calc
      ‖coordPoint u v p x‖ ^ 2
          = ‖((s : ℂ) • southPoint u v p α) + ((d : ℂ) • w)‖ ^ 2 := by rw [hdecomp]
      _ = ‖((s : ℂ) • southPoint u v p α)‖ ^ 2 + ‖((d : ℂ) • w)‖ ^ 2 := by
            simpa [pow_two] using hsq
      _ = s ^ 2 + d ^ 2 * ‖w‖ ^ 2 := by rw [hs_term, hd_term]
  have hd_sq : d ^ 2 = 1 - s ^ 2 := by
    simpa [d, s] using southDenCoord_sq (α := α) (x := x) hx
  have hd_sq_pos : 0 < d ^ 2 := sq_pos_iff.mpr hden
  have hw_sq : ‖w‖ ^ 2 = 1 := by
    nlinarith [hq_sq, hpyth, hd_sq, hd_sq_pos]
  nlinarith [hw_sq, norm_nonneg w]

lemma southInnerCoord_sq_add_southDenCoord_sq
    {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    southInnerCoord α x ^ 2 + southDenCoord α x ^ 2 = 1 := by
  have hsq := southDenCoord_sq (α := α) (x := x) hx
  nlinarith

lemma ambientQPerpCoord_eq_combo_south_ambientRPerp
    {u v p : H} {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    ambientQPerpCoord u v p α x =
      (((-southDenCoord α x : ℝ) : ℂ) • southPoint u v p α) +
        (((southInnerCoord α x : ℝ) : ℂ) • ambientRPerpCoord u v p α x) := by
  let s : ℝ := southInnerCoord α x
  let d : ℝ := southDenCoord α x
  have hdecomp :=
    coordPoint_eq_combo_south_ambientRPerp (u := u) (v := v) (p := p) (α := α) (x := x) hden
  have hd_sq : d ^ 2 = 1 - s ^ 2 := by
    simpa [d, s] using southDenCoord_sq (α := α) (x := x) hx
  have hdenC : ((d : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hden
  let dc : ℂ := (d : ℂ)
  have hdc_ne : dc ≠ 0 := by
    simpa [dc] using hdenC
  have hscaled :
      dc • ambientQPerpCoord u v p α x =
        dc •
          ((((-d : ℝ) : ℂ) • southPoint u v p α) +
            (((s : ℝ) : ℂ) • ambientRPerpCoord u v p α x)) := by
    unfold ambientQPerpCoord
    change dc • (((d : ℂ)⁻¹) •
        ((((s : ℂ) • coordPoint u v p x) - southPoint u v p α))) =
      dc •
        ((((-d : ℝ) : ℂ) • southPoint u v p α) +
          (((s : ℝ) : ℂ) • ambientRPerpCoord u v p α x))
    rw [smul_smul, mul_inv_cancel₀ hdenC, one_smul, hdecomp]
    have hs_coeffC :
        ((s : ℂ) * ((southInnerCoord α x : ℝ) : ℂ)) = (((s ^ 2 : ℝ) : ℂ)) := by
      simp [s, pow_two]
    have hr_coeffC :
        ((s : ℂ) * ((southDenCoord α x : ℝ) : ℂ)) = (((d * s : ℝ) : ℂ)) := by
      simp [d, mul_comm]
    rw [smul_add, smul_smul, smul_smul, hs_coeffC, hr_coeffC]
    have hcoeff : (s ^ 2 - 1 : ℝ) = -(d * d) := by
      nlinarith [hd_sq]
    calc
      (((s ^ 2 : ℝ) : ℂ) • southPoint u v p α) +
          (((d * s : ℝ) : ℂ) • ambientRPerpCoord u v p α x) -
          southPoint u v p α
          =
        ((((s ^ 2 - 1 : ℝ)) : ℂ) • southPoint u v p α) +
          (((d * s : ℝ) : ℂ) • ambientRPerpCoord u v p α x) := by
            simp [sub_eq_add_neg, add_smul, add_assoc, add_left_comm, add_comm]
      _ =
        (((-(d * d) : ℝ) : ℂ) • southPoint u v p α) +
          (((d * s : ℝ) : ℂ) • ambientRPerpCoord u v p α x) := by
            rw [hcoeff]
      _ =
        -(((↑d * ↑d : ℂ)) • southPoint u v p α) +
          (((↑d * ↑s : ℂ)) • ambientRPerpCoord u v p α x) := by
            have hddneg : (((-(d * d) : ℝ) : ℂ)) = -((↑d * ↑d : ℂ)) := by
              simp [Complex.ofReal_mul]
            have hds : (((d * s : ℝ) : ℂ)) = ((↑d * ↑s : ℂ)) := by
              simp [Complex.ofReal_mul]
            rw [hddneg, hds]
            simp [neg_smul]
      _ =
        dc •
          ((((-d : ℝ) : ℂ) • southPoint u v p α) +
            (((s : ℝ) : ℂ) • ambientRPerpCoord u v p α x)) := by
              have hdd : ((↑d * ↑d : ℂ)) = (((d * d : ℝ) : ℂ)) := by
                simp [Complex.ofReal_mul]
              have hds' : ((↑d * ↑s : ℂ)) = (((d * s : ℝ) : ℂ)) := by
                simp [Complex.ofReal_mul]
              rw [hdd, hds']
              dsimp [dc]
              rw [smul_add, smul_smul, smul_smul]
              have hmR : d * -d = -(d * d) := by ring
              rw [hmR]
              simp [neg_smul]
  have hzero :
      (dc •
        (ambientQPerpCoord u v p α x -
          ((((-d : ℝ) : ℂ) • southPoint u v p α) +
            (((s : ℝ) : ℂ) • ambientRPerpCoord u v p α x)))) = 0 := by
    rw [smul_sub, hscaled, sub_self]
  rcases smul_eq_zero.mp hzero with hd0 | hsub
  · exact (hdc_ne hd0).elim
  · exact sub_eq_zero.mp hsub

lemma south_ambientRPerp_frame_sum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H} {α : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    frame_quadratic μ (southPoint u v p α) + frame_quadratic μ (ambientRPerpCoord u v p α x) =
      frame_quadratic μ (coordPoint u v p x) + frame_quadratic μ (ambientQPerpCoord u v p α x) := by
  let a : ℝ := southInnerCoord α x
  let b : ℝ := southDenCoord α x
  have hab : a ^ 2 + b ^ 2 = 1 := by
    simpa [a, b, add_comm] using southInnerCoord_sq_add_southDenCoord_sq (α := α) (x := x) hx
  have hgc :=
    GleasonBridge.great_circle_constancy hdim μ
      (southPoint u v p α) (ambientRPerpCoord u v p α x)
      (southPoint_norm hu hv hp huv hup hvp α)
      (ambientRPerpCoord_norm hu hv hp huv hup hvp hx hden)
      (southPoint_ambientRPerp_orth hu hv hp huv hup hvp (α := α) hx)
      a b hab
  have hcoord :
      coordPoint u v p x =
        ((a : ℂ) • southPoint u v p α) + ((b : ℂ) • ambientRPerpCoord u v p α x) := by
    simpa [a, b] using
      coordPoint_eq_combo_south_ambientRPerp (u := u) (v := v) (p := p) (α := α) (x := x) hden
  have hqperp :
      frame_quadratic μ (ambientQPerpCoord u v p α x) =
        frame_quadratic μ (((b : ℂ) • southPoint u v p α) -
          ((a : ℂ) • ambientRPerpCoord u v p α x)) := by
    have hvec :
        ambientQPerpCoord u v p α x =
          -((((b : ℂ) • southPoint u v p α) -
            ((a : ℂ) • ambientRPerpCoord u v p α x))) := by
      calc
        ambientQPerpCoord u v p α x
            = (((-b) : ℂ) • southPoint u v p α) +
                ((a : ℂ) • ambientRPerpCoord u v p α x) := by
                  simpa [a, b] using
                    ambientQPerpCoord_eq_combo_south_ambientRPerp
                      (u := u) (v := v) (p := p) (α := α) (x := x) hx hden
        _ = -((((b : ℂ) • southPoint u v p α) -
              ((a : ℂ) • ambientRPerpCoord u v p α x))) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hvec, frame_quadratic_neg]
  calc
    frame_quadratic μ (southPoint u v p α) + frame_quadratic μ (ambientRPerpCoord u v p α x)
        =
      frame_quadratic μ (((a : ℂ) • southPoint u v p α) +
          ((b : ℂ) • ambientRPerpCoord u v p α x)) +
        frame_quadratic μ (((b : ℂ) • southPoint u v p α) -
          ((a : ℂ) • ambientRPerpCoord u v p α x)) := by
            simpa [hcoord, hqperp] using hgc.symm
    _ =
      frame_quadratic μ (coordPoint u v p x) + frame_quadratic μ (ambientQPerpCoord u v p α x) := by
        rw [hcoord, hqperp]

lemma continuous_coordPoint (u v p : H) :
    Continuous (coordPoint u v p) := by
  have hxc : Continuous fun x : ℝ × ℝ × ℝ => (((x.1 : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_fst
  have hy : Continuous fun x : ℝ × ℝ × ℝ => x.2.1 :=
    continuous_fst.comp continuous_snd
  have hyc : Continuous fun x : ℝ × ℝ × ℝ => (((x.2.1 : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp hy
  have hz : Continuous fun x : ℝ × ℝ × ℝ => x.2.2 :=
    continuous_snd.comp continuous_snd
  have hzc : Continuous fun x : ℝ × ℝ × ℝ => (((x.2.2 : ℝ)) : ℂ) :=
    Complex.continuous_ofReal.comp hz
  have hu : Continuous fun _ : ℝ × ℝ × ℝ => u := continuous_const
  have hv : Continuous fun _ : ℝ × ℝ × ℝ => v := continuous_const
  have hp : Continuous fun _ : ℝ × ℝ × ℝ => p := continuous_const
  simpa [coordPoint] using
    (hxc.smul hu).add ((hyc.smul hv).add (hzc.smul hp))

lemma continuous_southInnerCoord (α : ℝ) :
    Continuous (southInnerCoord α) := by
  unfold southInnerCoord
  have hz : Continuous fun x : ℝ × ℝ × ℝ => x.2.2 :=
    continuous_snd.comp continuous_snd
  exact (continuous_fst.mul continuous_const).sub (hz.mul continuous_const)

lemma continuous_southDenCoord (α : ℝ) :
    Continuous (southDenCoord α) := by
  exact Real.continuous_sqrt.comp
    ((continuous_const : Continuous fun _ : ℝ × ℝ × ℝ => (1 : ℝ)).sub
      ((continuous_southInnerCoord α).pow 2))

lemma continuousAt_ambientQPerpCoord
    {u v p : H} {α : ℝ}
    (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    ContinuousAt (ambientQPerpCoord u v p α) coordBase := by
  have hcoord : ContinuousAt (coordPoint u v p) coordBase := (continuous_coordPoint u v p).continuousAt
  have hinner : ContinuousAt (southInnerCoord α) coordBase := (continuous_southInnerCoord α).continuousAt
  have hden : ContinuousAt (southDenCoord α) coordBase := (continuous_southDenCoord α).continuousAt
  have hden_ne : southDenCoord α coordBase ≠ 0 := by
    rw [southDenCoord_base hα0 hαpi]
    have hsina_pos : 0 < Real.sin α := by
      have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
      exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
    exact ne_of_gt hsina_pos
  have hcoef :
      ContinuousAt (fun x : ℝ × ℝ × ℝ =>
        ((↑(southDenCoord α x) : ℂ)⁻¹)) coordBase := by
    exact ContinuousAt.inv₀ (Complex.continuous_ofReal.continuousAt.comp hden) (by simpa using hden_ne)
  have hvec :
      ContinuousAt (fun x : ℝ × ℝ × ℝ =>
        (((southInnerCoord α x : ℝ) : ℂ) • coordPoint u v p x) - southPoint u v p α) coordBase := by
    have hinnerc :
        ContinuousAt (fun x : ℝ × ℝ × ℝ => (((southInnerCoord α x : ℝ) : ℂ))) coordBase :=
      Complex.continuous_ofReal.continuousAt.comp hinner
    exact (hinnerc.smul hcoord).sub continuousAt_const
  simpa [ambientQPerpCoord] using hcoef.smul hvec

lemma continuousAt_ambientRPerpCoord
    {u v p : H} {α : ℝ}
    (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    ContinuousAt (ambientRPerpCoord u v p α) coordBase := by
  have hcoord : ContinuousAt (coordPoint u v p) coordBase := (continuous_coordPoint u v p).continuousAt
  have hinner : ContinuousAt (southInnerCoord α) coordBase := (continuous_southInnerCoord α).continuousAt
  have hden : ContinuousAt (southDenCoord α) coordBase := (continuous_southDenCoord α).continuousAt
  have hden_ne : southDenCoord α coordBase ≠ 0 := by
    rw [southDenCoord_base hα0 hαpi]
    have hsina_pos : 0 < Real.sin α := by
      have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
      exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
    exact ne_of_gt hsina_pos
  have hcoef :
      ContinuousAt (fun x : ℝ × ℝ × ℝ =>
        ((↑(southDenCoord α x) : ℂ)⁻¹)) coordBase := by
    exact ContinuousAt.inv₀ (Complex.continuous_ofReal.continuousAt.comp hden) (by simpa using hden_ne)
  have hvec :
      ContinuousAt (fun x : ℝ × ℝ × ℝ =>
        coordPoint u v p x - (((southInnerCoord α x : ℝ) : ℂ) • southPoint u v p α)) coordBase := by
    have hinnerc :
        ContinuousAt (fun x : ℝ × ℝ × ℝ => (((southInnerCoord α x : ℝ) : ℂ))) coordBase :=
      Complex.continuous_ofReal.continuousAt.comp hinner
    exact hcoord.sub (hinnerc.smul continuousAt_const)
  simpa [ambientRPerpCoord] using hcoef.smul hvec

lemma exists_small_ambient_companion_cap
    {u v p : H} {ε : ℝ} (hε : 0 < ε) :
    ∃ α δ : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < δ ∧
      ∀ {x : ℝ × ℝ × ℝ}, dist x coordBase < δ →
        0 < southDenCoord α x ∧
        dist (ambientQPerpCoord u v p α x) p < ε ∧
        dist (ambientRPerpCoord u v p α x) p < ε := by
  let northFun : ℝ → H := fun a => realFramePoint u v p (Real.sin a) 0 (Real.cos a)
  have hnorth_zero : northFun 0 = p := by
    simp [northFun, realFramePoint]
  have hnorth_cont : ContinuousAt northFun 0 := by
    have hsinC : Continuous fun a : ℝ => ((Real.sin a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp Real.continuous_sin
    have hzeroC : Continuous fun _ : ℝ => (0 : ℂ) := continuous_const
    have hcosC : Continuous fun a : ℝ => ((Real.cos a : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp Real.continuous_cos
    have hu : Continuous fun _ : ℝ => u := continuous_const
    have hv : Continuous fun _ : ℝ => v := continuous_const
    have hp : Continuous fun _ : ℝ => p := continuous_const
    have hcont : Continuous northFun := by
      simpa [northFun, realFramePoint, add_assoc] using
        (hsinC.smul hu).add ((hzeroC.smul hv).add (hcosC.smul hp))
    exact hcont.continuousAt
  have hε2 : 0 < ε / 2 := by positivity
  rcases (Metric.continuousAt_iff.mp hnorth_cont) (ε / 2) hε2 with ⟨δα, hδα, hδαprop⟩
  let α : ℝ := min (δα / 2) (Real.pi / 4)
  have hα0 : 0 < α := by
    have hhalf_pos : 0 < δα / 2 := by positivity
    have hquarter_pos : 0 < Real.pi / 4 := by positivity
    exact lt_min hhalf_pos hquarter_pos
  have hαsmall : α < δα := by
    have hhalf_lt : δα / 2 < δα := by nlinarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf_lt
  have hαpi : α < Real.pi / 2 := by
    have hquarter_lt : Real.pi / 4 < Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    exact lt_of_le_of_lt (min_le_right _ _) hquarter_lt
  have hαdist : dist α 0 < δα := by
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos hα0] using hαsmall
  have hr0 : dist (northFun α) p < ε / 2 := by
    simpa [hnorth_zero] using hδαprop hαdist
  have hqcont : ContinuousAt (ambientQPerpCoord u v p α) coordBase :=
    continuousAt_ambientQPerpCoord (u := u) (v := v) (p := p) hα0 hαpi
  have hrcont : ContinuousAt (ambientRPerpCoord u v p α) coordBase :=
    continuousAt_ambientRPerpCoord (u := u) (v := v) (p := p) hα0 hαpi
  have hden_cont : ContinuousAt (southDenCoord α) coordBase :=
    (continuous_southDenCoord α).continuousAt
  have hsina_pos : 0 < Real.sin α := by
    have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
  rcases (Metric.continuousAt_iff.mp hqcont) ε hε with ⟨δq, hδq, hδqprop⟩
  rcases (Metric.continuousAt_iff.mp hrcont) (ε / 2) hε2 with ⟨δr, hδr, hδrprop⟩
  rcases (Metric.continuousAt_iff.mp hden_cont) (Real.sin α / 2) (by positivity) with
    ⟨δden, hδden, hδdenprop⟩
  refine ⟨α, min δq (min δr δden), hα0, hαpi, lt_min hδq (lt_min hδr hδden), ?_⟩
  intro x hx
  have hxq : dist x coordBase < δq := by
    exact lt_of_lt_of_le hx (min_le_left _ _)
  have hxr : dist x coordBase < δr := by
    exact lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
  have hxden : dist x coordBase < δden := by
    exact lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_right _ _))
  have hq : dist (ambientQPerpCoord u v p α x) (ambientQPerpCoord u v p α coordBase) < ε := by
    exact hδqprop hxq
  have hrmid : dist (ambientRPerpCoord u v p α x) (ambientRPerpCoord u v p α coordBase) < ε / 2 := by
    exact hδrprop hxr
  have hden_close : dist (southDenCoord α x) (southDenCoord α coordBase) < Real.sin α / 2 := by
    exact hδdenprop hxden
  have hden_pos : 0 < southDenCoord α x := by
    have hbase : southDenCoord α coordBase = Real.sin α := southDenCoord_base hα0 hαpi
    have habs : |southDenCoord α x - Real.sin α| < Real.sin α / 2 := by
      simpa [Real.dist_eq, hbase, abs_sub_comm] using hden_close
    have hlower : Real.sin α - Real.sin α / 2 < southDenCoord α x := by
      nlinarith [abs_lt.mp habs |>.1]
    nlinarith
  have hq' : dist (ambientQPerpCoord u v p α x) p < ε := by
    simpa [ambientQPerpCoord_base (u := u) (v := v) (p := p) hα0 hαpi] using hq
  have hr' : dist (ambientRPerpCoord u v p α x) p < ε := by
    have htri :
        dist (ambientRPerpCoord u v p α x) p ≤
          dist (ambientRPerpCoord u v p α x) (ambientRPerpCoord u v p α coordBase) +
            dist (ambientRPerpCoord u v p α coordBase) p := by
      simpa using
        dist_triangle (ambientRPerpCoord u v p α x) (ambientRPerpCoord u v p α coordBase) p
    have hbase :
        dist (ambientRPerpCoord u v p α coordBase) p < ε / 2 := by
      simpa [ambientRPerpCoord_base (u := u) (v := v) (p := p) hα0 hαpi, northFun] using hr0
    have hlt : dist (ambientRPerpCoord u v p α x) p < ε / 2 + ε / 2 := by
      exact lt_of_le_of_lt htri (add_lt_add hrmid hbase)
    nlinarith
  exact ⟨hden_pos, hq', hr'⟩

lemma ambient_oscillation_bound_of_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hosc :
      ∀ x y : H, ‖x‖ = 1 → ‖y‖ = 1 →
        dist x p < ε → dist y p < ε →
        |frame_quadratic μ x - frame_quadratic μ y| ≤ a) :
    ∃ α δ : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
        x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
        dist x₁ coordBase < δ → dist x₂ coordBase < δ →
        |frame_quadratic μ (coordPoint u v p x₁) -
            frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * a := by
  rcases exists_small_ambient_companion_cap (u := u) (v := v) (p := p) hε with
    ⟨α, δ, hα0, hαpi, hδ, hcap⟩
  refine ⟨α, δ, hα0, hαpi, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdist₁ hdist₂
  rcases hcap hdist₁ with ⟨hden₁, hq₁p, hr₁p⟩
  rcases hcap hdist₂ with ⟨hden₂, hq₂p, hr₂p⟩
  have hqbound :
      |frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
          frame_quadratic μ (ambientQPerpCoord u v p α x₁)| ≤ a := by
    simpa [abs_sub_comm] using
      hosc (ambientQPerpCoord u v p α x₁) (ambientQPerpCoord u v p α x₂)
        (ambientQPerpCoord_norm hu hv hp huv hup hvp hx₁ (ne_of_gt hden₁))
        (ambientQPerpCoord_norm hu hv hp huv hup hvp hx₂ (ne_of_gt hden₂))
        hq₁p hq₂p
  have hrbound :
      |frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
          frame_quadratic μ (ambientRPerpCoord u v p α x₂)| ≤ a := by
    exact hosc (ambientRPerpCoord u v p α x₁) (ambientRPerpCoord u v p α x₂)
      (ambientRPerpCoord_norm hu hv hp huv hup hvp hx₁ (ne_of_gt hden₁))
      (ambientRPerpCoord_norm hu hv hp huv hup hvp hx₂ (ne_of_gt hden₂))
      hr₁p hr₂p
  have hsum₁ :=
    south_ambientRPerp_frame_sum hdim μ hu hv hp huv hup hvp
      (α := α) (x := x₁) hx₁ (ne_of_gt hden₁)
  have hsum₂ :=
    south_ambientRPerp_frame_sum hdim μ hu hv hp huv hup hvp
      (α := α) (x := x₂) hx₂ (ne_of_gt hden₂)
  have hEq :
      frame_quadratic μ (coordPoint u v p x₁) -
          frame_quadratic μ (coordPoint u v p x₂) =
        (frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
            frame_quadratic μ (ambientRPerpCoord u v p α x₂)) +
          (frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
            frame_quadratic μ (ambientQPerpCoord u v p α x₁)) := by
    linarith
  calc
    |frame_quadratic μ (coordPoint u v p x₁) -
        frame_quadratic μ (coordPoint u v p x₂)|
        =
      |(frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
          frame_quadratic μ (ambientRPerpCoord u v p α x₂)) +
        (frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
          frame_quadratic μ (ambientQPerpCoord u v p α x₁))| := by
            rw [hEq]
    _ ≤
      |frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
          frame_quadratic μ (ambientRPerpCoord u v p α x₂)| +
        |frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
          frame_quadratic μ (ambientQPerpCoord u v p α x₁)| := by
            exact abs_add_le _ _
    _ ≤ a + a := add_le_add hrbound hqbound
    _ = 2 * a := by ring

lemma ambient_oscillation_bound_of_cap_realframe
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hosc :
      ∀ x y : H, ‖x‖ = 1 → ‖y‖ = 1 →
        dist x p < ε → dist y p < ε →
        |frame_quadratic μ x - frame_quadratic μ y| ≤ a) :
    ∃ α δ : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
        x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x₁) u < δ →
        dist (coordPoint u v p x₂) u < δ →
        |frame_quadratic μ (coordPoint u v p x₁) -
            frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * a := by
  rcases ambient_oscillation_bound_of_cap hdim μ hu hv hp huv hup hvp ha hε hosc with
    ⟨α, δ, hα0, hαpi, hδ, hlocal⟩
  refine ⟨α, δ, hα0, hαpi, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdist₁ hdist₂
  apply hlocal hx₁ hx₂
  · exact lt_of_le_of_lt (dist_coordBase_le_dist_coordPoint hu hv hp huv hup hvp x₁) hdist₁
  · exact lt_of_le_of_lt (dist_coordBase_le_dist_coordPoint hu hv hp huv hup hvp x₂) hdist₂

end Thm26

section Thm27

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

def coordDot (x y : ℝ × ℝ × ℝ) : ℝ :=
  x.1 * y.1 + x.2.1 * y.2.1 + x.2.2 * y.2.2

def coordLinearCombo
    (a b c : ℝ) (x y z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (a * x.1 + b * y.1 + c * z.1,
    (a * x.2.1 + b * y.2.1 + c * z.2.1,
      a * x.2.2 + b * y.2.2 + c * z.2.2))

def cycleCoord (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.2.2, (x.1, x.2.1))

def cycleCoordInv (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (x.2.1, (x.2.2, x.1))

lemma cycleCoord_sq_sum
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    (cycleCoord x).1 ^ 2 + (cycleCoord x).2.1 ^ 2 + (cycleCoord x).2.2 ^ 2 = 1 := by
  simpa [cycleCoord, add_assoc, add_left_comm, add_comm] using hx

lemma cycleCoordInv_sq_sum
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    (cycleCoordInv x).1 ^ 2 + (cycleCoordInv x).2.1 ^ 2 + (cycleCoordInv x).2.2 ^ 2 = 1 := by
  simpa [cycleCoordInv, add_assoc, add_left_comm, add_comm] using hx

lemma coordPoint_cycle
    (a b c : H) (x : ℝ × ℝ × ℝ) :
    coordPoint b c a x = coordPoint a b c (cycleCoord x) := by
  simp [coordPoint, cycleCoord, add_assoc, add_left_comm, add_comm]

lemma coordPoint_cycleInv
    (a b c : H) (x : ℝ × ℝ × ℝ) :
    coordPoint b c a (cycleCoordInv x) = coordPoint a b c x := by
  simp [coordPoint, cycleCoordInv, add_assoc, add_left_comm, add_comm]

lemma coordPoint_eq_realFramePoint
    (u v p : H) (x : ℝ × ℝ × ℝ) :
    coordPoint u v p x = realFramePoint u v p x.1 x.2.1 x.2.2 := by
  unfold coordPoint realFramePoint
  simp [add_assoc]

lemma inner_coordPoint_coordPoint
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (x y : ℝ × ℝ × ℝ) :
    inner (𝕜 := ℂ) (coordPoint u v p x) (coordPoint u v p y) =
      ((coordDot x y : ℝ) : ℂ) := by
  simpa [coordPoint_eq_realFramePoint, coordDot] using
    inner_realFramePoint_realFramePoint hu hv hp huv hup hvp
      x.1 x.2.1 x.2.2 y.1 y.2.1 y.2.2

lemma coordPoint_coordLinearCombo
    (u v p : H)
    (x y z t : ℝ × ℝ × ℝ) :
    coordPoint (coordPoint u v p x) (coordPoint u v p y) (coordPoint u v p z) t =
      coordPoint u v p (coordLinearCombo t.1 t.2.1 t.2.2 x y z) := by
  have hx :
      (((t.1 : ℝ) : ℂ) • coordPoint u v p x) =
        realFramePoint u v p (t.1 * x.1) (t.1 * x.2.1) (t.1 * x.2.2) := by
    rw [coordPoint_eq_realFramePoint]
    simpa using realFramePoint_real_smul u v p t.1 x.1 x.2.1 x.2.2
  have hy :
      (((t.2.1 : ℝ) : ℂ) • coordPoint u v p y) =
        realFramePoint u v p (t.2.1 * y.1) (t.2.1 * y.2.1) (t.2.1 * y.2.2) := by
    rw [coordPoint_eq_realFramePoint]
    simpa using realFramePoint_real_smul u v p t.2.1 y.1 y.2.1 y.2.2
  have hz :
      (((t.2.2 : ℝ) : ℂ) • coordPoint u v p z) =
        realFramePoint u v p (t.2.2 * z.1) (t.2.2 * z.2.1) (t.2.2 * z.2.2) := by
    rw [coordPoint_eq_realFramePoint]
    simpa using realFramePoint_real_smul u v p t.2.2 z.1 z.2.1 z.2.2
  rw [coordPoint_eq_realFramePoint (coordPoint u v p x) (coordPoint u v p y)
      (coordPoint u v p z) t]
  rw [coordPoint_eq_realFramePoint u v p (coordLinearCombo t.1 t.2.1 t.2.2 x y z)]
  unfold realFramePoint
  rw [hx, hy, hz, realFramePoint_add, realFramePoint_add]
  simp [coordLinearCombo, realFramePoint, add_assoc, add_left_comm, add_comm,
    mul_comm, mul_left_comm, mul_assoc]

def quarterTurnCLM (u v : H) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H
    - (ContinuousLinearMap.smulRight (innerSL ℂ u) u)
    - (ContinuousLinearMap.smulRight (innerSL ℂ v) v)
    + (ContinuousLinearMap.smulRight (innerSL ℂ u) v)
    - (ContinuousLinearMap.smulRight (innerSL ℂ v) u)

lemma quarterTurnCLM_apply
    (u v : H) (x : H) :
    quarterTurnCLM u v x =
      x - (inner (𝕜 := ℂ) u x : ℂ) • u - (inner (𝕜 := ℂ) v x : ℂ) • v +
        (inner (𝕜 := ℂ) u x : ℂ) • v - (inner (𝕜 := ℂ) v x : ℂ) • u := by
  simp [quarterTurnCLM, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

lemma quarterTurnCLM_eq_self_of_orthogonal
    {u v x : H}
    (hux : inner (𝕜 := ℂ) u x = 0)
    (hvx : inner (𝕜 := ℂ) v x = 0) :
    quarterTurnCLM u v x = x := by
  rw [quarterTurnCLM_apply, hux, hvx]
  simp

def horizontalRadius (z : ℝ × ℝ × ℝ) : ℝ :=
  Real.sqrt (z.1 ^ 2 + z.2.1 ^ 2)

def targetPoleCoord (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (-z.2.1 / horizontalRadius z, (z.1 / horizontalRadius z, 0))

def targetBridgeCoord (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (z.2.2 * z.1 / horizontalRadius z,
    (z.2.2 * z.2.1 / horizontalRadius z, -horizontalRadius z))

def targetFrameReparam
    (z y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  coordLinearCombo y.1 y.2.1 y.2.2 z (targetBridgeCoord z) (targetPoleCoord z)

def targetFrameReparamSwap
    (z y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  coordLinearCombo y.1 y.2.1 y.2.2 z (targetPoleCoord z) (targetBridgeCoord z)

def bridgePoleSwapCoord (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (y.1, (y.2.2, y.2.1))

lemma bridgePoleSwapCoord_sq_sum
    {y : ℝ × ℝ × ℝ}
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1) :
    (bridgePoleSwapCoord y).1 ^ 2 +
      (bridgePoleSwapCoord y).2.1 ^ 2 +
        (bridgePoleSwapCoord y).2.2 ^ 2 = 1 := by
  dsimp [bridgePoleSwapCoord]
  linarith

lemma targetFrameReparam_eq_targetFrameReparamSwap_bridgePoleSwap
    (z y : ℝ × ℝ × ℝ) :
    targetFrameReparam z y =
      targetFrameReparamSwap z (bridgePoleSwapCoord y) := by
  ext <;> simp [targetFrameReparam, targetFrameReparamSwap,
    bridgePoleSwapCoord, coordLinearCombo] <;> ring

def targetFrameCoords
    (z x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (coordDot x z, (coordDot x (targetBridgeCoord z), coordDot x (targetPoleCoord z)))

def targetFrameCoordsSwap
    (z x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (coordDot x z, (coordDot x (targetPoleCoord z), coordDot x (targetBridgeCoord z)))

def poleCoord : ℝ × ℝ × ℝ :=
  (0, (0, 1))

def horizontalUnitCoord
    (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (z.1 / horizontalRadius z, (z.2.1 / horizontalRadius z, 0))

def equatorFrameReparam
    (z y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  coordLinearCombo y.1 y.2.1 y.2.2
    (targetPoleCoord z) (horizontalUnitCoord z) poleCoord

def equatorFrameCoords
    (z x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (coordDot x (targetPoleCoord z),
    (coordDot x (horizontalUnitCoord z), x.2.2))

def southCoord (α : ℝ) : ℝ × ℝ × ℝ :=
  (Real.cos α, (0, -Real.sin α))

def ambientQCoord (α : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ((southInnerCoord α x * x.1 - Real.cos α) / southDenCoord α x,
    ((southInnerCoord α x * x.2.1) / southDenCoord α x,
      (southInnerCoord α x * x.2.2 + Real.sin α) / southDenCoord α x))

def ambientRCoord (α : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  ((x.1 - southInnerCoord α x * Real.cos α) / southDenCoord α x,
    (x.2.1 / southDenCoord α x,
      (x.2.2 + southInnerCoord α x * Real.sin α) / southDenCoord α x))

lemma horizontalRadius_sq (z : ℝ × ℝ × ℝ) :
    horizontalRadius z ^ 2 = z.1 ^ 2 + z.2.1 ^ 2 := by
  unfold horizontalRadius
  rw [Real.sq_sqrt]
  positivity

lemma coordPoint_poleCoord
    (u v p : H) :
    coordPoint u v p poleCoord = p := by
  simp [coordPoint, poleCoord]

lemma horizontalUnitCoord_sq_sum
    {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    (horizontalUnitCoord z).1 ^ 2 +
        (horizontalUnitCoord z).2.1 ^ 2 +
        (horizontalUnitCoord z).2.2 ^ 2 = 1 := by
  have hρsq := horizontalRadius_sq z
  unfold horizontalUnitCoord
  field_simp [hρ]
  nlinarith [hρsq]

lemma coordDot_targetPole_horizontalUnitCoord
    {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
  unfold coordDot targetPoleCoord horizontalUnitCoord
  field_simp [hρ]
  ring

lemma coordDot_pole_targetPoleCoord
    (z : ℝ × ℝ × ℝ) :
    coordDot poleCoord (targetPoleCoord z) = 0 := by
  unfold coordDot poleCoord targetPoleCoord
  simp

lemma coordDot_pole_horizontalUnitCoord
    (z : ℝ × ℝ × ℝ) :
    coordDot poleCoord (horizontalUnitCoord z) = 0 := by
  unfold coordDot poleCoord horizontalUnitCoord
  simp

lemma targetFrameCoords_poleCoord
    (z : ℝ × ℝ × ℝ) :
    targetFrameCoords z poleCoord =
      (z.2.2, (-horizontalRadius z, 0)) := by
  ext <;> simp [targetFrameCoords, coordDot, poleCoord, targetBridgeCoord, targetPoleCoord]

lemma horizontalRadius_cycleCoordInv_targetFrameCoords_poleCoord_ne_zero
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    horizontalRadius (cycleCoordInv (targetFrameCoords z poleCoord)) ≠ 0 := by
  have hsq :
      horizontalRadius (cycleCoordInv (targetFrameCoords z poleCoord)) ^ 2 =
        horizontalRadius z ^ 2 := by
    rw [horizontalRadius_sq, targetFrameCoords_poleCoord]
    simp [cycleCoordInv]
  by_contra h0
  have hsq0 : horizontalRadius z ^ 2 = 0 := by
    rw [← hsq, h0]
    ring
  have hz0 : horizontalRadius z = 0 := by
    nlinarith [sq_nonneg (horizontalRadius z)]
  exact hρ hz0

lemma equatorFrameReparam_base
    {z : ℝ × ℝ × ℝ} :
    equatorFrameReparam z coordBase = targetPoleCoord z := by
  ext <;> simp [equatorFrameReparam, coordLinearCombo, coordBase, targetPoleCoord]

lemma equatorFrameReparam_sq_sum
    {z y : ℝ × ℝ × ℝ}
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    (equatorFrameReparam z y).1 ^ 2 +
        (equatorFrameReparam z y).2.1 ^ 2 +
        (equatorFrameReparam z y).2.2 ^ 2 = 1 := by
  have hρsq := horizontalRadius_sq z
  unfold equatorFrameReparam coordLinearCombo targetPoleCoord horizontalUnitCoord poleCoord
  field_simp [hρ]
  nlinarith [hy, hρsq]

lemma equatorFrameCoords_equatorFrameReparam
    {z y : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    equatorFrameCoords z (equatorFrameReparam z y) = y := by
  have hρsq := horizontalRadius_sq z
  ext <;> unfold equatorFrameCoords equatorFrameReparam coordDot coordLinearCombo
    targetPoleCoord horizontalUnitCoord poleCoord
  · field_simp [hρ]
    ring_nf
    have h :
        z.2.1 ^ 2 * y.1 + y.1 * z.1 ^ 2 = y.1 * horizontalRadius z ^ 2 := by
      rw [hρsq]
      ring
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h
  · field_simp [hρ]
    ring_nf
    have h :
        z.1 ^ 2 * y.2.1 + z.2.1 ^ 2 * y.2.1 = y.2.1 * horizontalRadius z ^ 2 := by
      rw [hρsq]
      ring
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h
  · simp [equatorFrameCoords, equatorFrameReparam, coordLinearCombo, poleCoord]

lemma equatorFrameReparam_equatorFrameCoords
    {z x : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    equatorFrameReparam z (equatorFrameCoords z x) = x := by
  have hρsq := horizontalRadius_sq z
  ext <;> unfold equatorFrameReparam equatorFrameCoords coordLinearCombo coordDot
    targetPoleCoord horizontalUnitCoord poleCoord
  · field_simp [hρ]
    ring_nf
    have h :
        z.2.1 ^ 2 * x.1 + x.1 * z.1 ^ 2 = x.1 * horizontalRadius z ^ 2 := by
      rw [hρsq]
      ring
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h
  · field_simp [hρ]
    ring_nf
    have h :
        z.1 ^ 2 * x.2.1 + z.2.1 ^ 2 * x.2.1 = x.2.1 * horizontalRadius z ^ 2 := by
      rw [hρsq]
      ring
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h
  · simp [equatorFrameReparam, equatorFrameCoords, coordLinearCombo, poleCoord]

lemma equatorFrameCoords_sq_sum
    {z x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    (equatorFrameCoords z x).1 ^ 2 +
        (equatorFrameCoords z x).2.1 ^ 2 +
        (equatorFrameCoords z x).2.2 ^ 2 = 1 := by
  have hρsq := horizontalRadius_sq z
  unfold equatorFrameCoords coordDot targetPoleCoord horizontalUnitCoord
  field_simp [hρ]
  nlinarith [hx, hρsq]

lemma coordPoint_equatorFrameReparam
    (u v p : H)
    (z y : ℝ × ℝ × ℝ) :
    coordPoint (coordPoint u v p (targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z)) p y =
      coordPoint u v p (equatorFrameReparam z y) := by
  have hcombo :
      coordPoint (coordPoint u v p (targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) y =
        coordPoint u v p (equatorFrameReparam z y) := by
    simpa [equatorFrameReparam] using
      coordPoint_coordLinearCombo u v p
        (targetPoleCoord z) (horizontalUnitCoord z) poleCoord y
  simpa [coordPoint_poleCoord u v p] using hcombo

lemma coordPoint_southCoord
    (u v p : H) (α : ℝ) :
    coordPoint u v p (southCoord α) = southPoint u v p α := by
  unfold coordPoint southCoord southPoint realFramePoint
  simp [add_assoc]

lemma coordPoint_ambientQCoord
    (u v p : H) {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hden : southDenCoord α x ≠ 0) :
    coordPoint u v p (ambientQCoord α x) = ambientQPerpCoord u v p α x := by
  let s : ℝ := southInnerCoord α x
  let d : ℝ := southDenCoord α x
  let t : ℝ × ℝ × ℝ := (s / d, (-1 / d, 0))
  have hd : d ≠ 0 := by simpa [d] using hden
  have ht :
      coordLinearCombo t.1 t.2.1 t.2.2 x (southCoord α) coordBase = ambientQCoord α x := by
    ext <;> simp [coordLinearCombo, ambientQCoord, southCoord, coordBase, t, s, d] <;>
      field_simp [hd] <;> ring
  calc
    coordPoint u v p (ambientQCoord α x)
        = coordPoint u v p (coordLinearCombo t.1 t.2.1 t.2.2 x (southCoord α) coordBase) := by
            rw [ht]
    _ =
      coordPoint (coordPoint u v p x) (coordPoint u v p (southCoord α))
        (coordPoint u v p coordBase) t := by
          symm
          simpa [t] using
            coordPoint_coordLinearCombo u v p x (southCoord α) coordBase t
    _ = ambientQPerpCoord u v p α x := by
          rw [coordPoint_southCoord, coordPoint_base]
          unfold coordPoint
          change
            ((((s / d : ℝ) : ℂ) • coordPoint u v p x) +
                ((((-1 / d : ℝ) : ℂ) • southPoint u v p α) + ((0 : ℂ) • u))) =
              ambientQPerpCoord u v p α x
          have hsdiv :
              (((s / d : ℝ) : ℂ) • coordPoint u v p x) =
                ((((d : ℝ) : ℂ)⁻¹ * (((s : ℝ) : ℂ))) • coordPoint u v p x) := by
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
          have hnegdiv :
              ((((-1 / d : ℝ) : ℂ) • southPoint u v p α)) =
                -((((d : ℝ) : ℂ)⁻¹) • southPoint u v p α) := by
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
          calc
            ((((s / d : ℝ) : ℂ) • coordPoint u v p x) +
                ((((-1 / d : ℝ) : ℂ) • southPoint u v p α) + ((0 : ℂ) • u)))
                =
                  ((((d : ℝ) : ℂ)⁻¹ * (((s : ℝ) : ℂ))) • coordPoint u v p x) -
                    ((((d : ℝ) : ℂ)⁻¹) • southPoint u v p α) := by
                      rw [hsdiv, hnegdiv]
                      simp [sub_eq_add_neg]
            _ = (((d : ℝ) : ℂ)⁻¹) •
                  ((((s : ℝ) : ℂ) • coordPoint u v p x) - southPoint u v p α) := by
                    rw [smul_sub, smul_smul]
            _ = ambientQPerpCoord u v p α x := by
                  simp [ambientQPerpCoord, s, d]

lemma coordPoint_ambientRCoord
    (u v p : H) {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hden : southDenCoord α x ≠ 0) :
    coordPoint u v p (ambientRCoord α x) = ambientRPerpCoord u v p α x := by
  let s : ℝ := southInnerCoord α x
  let d : ℝ := southDenCoord α x
  let t : ℝ × ℝ × ℝ := (1 / d, (-s / d, 0))
  have hd : d ≠ 0 := by simpa [d] using hden
  have ht :
      coordLinearCombo t.1 t.2.1 t.2.2 x (southCoord α) coordBase = ambientRCoord α x := by
    ext <;> simp [coordLinearCombo, ambientRCoord, southCoord, coordBase, t, s, d] <;>
      field_simp [hd] <;> ring
  calc
    coordPoint u v p (ambientRCoord α x)
        = coordPoint u v p (coordLinearCombo t.1 t.2.1 t.2.2 x (southCoord α) coordBase) := by
            rw [ht]
    _ =
      coordPoint (coordPoint u v p x) (coordPoint u v p (southCoord α))
        (coordPoint u v p coordBase) t := by
          symm
          simpa [t] using
            coordPoint_coordLinearCombo u v p x (southCoord α) coordBase t
    _ = ambientRPerpCoord u v p α x := by
          rw [coordPoint_southCoord, coordPoint_base]
          unfold coordPoint
          change
            ((((1 / d : ℝ) : ℂ) • coordPoint u v p x) +
                ((((-s / d : ℝ) : ℂ) • southPoint u v p α) + ((0 : ℂ) • u))) =
              ambientRPerpCoord u v p α x
          have hqdiv :
              (((1 / d : ℝ) : ℂ) • coordPoint u v p x) =
                ((((d : ℝ) : ℂ)⁻¹) • coordPoint u v p x) := by
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
          have hmain :
              ((((-s / d : ℝ) : ℂ) • southPoint u v p α)) =
                -(((((d : ℝ) : ℂ)⁻¹ * (((s : ℝ) : ℂ))) • southPoint u v p α)) := by
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
          calc
            ((((1 / d : ℝ) : ℂ) • coordPoint u v p x) +
                ((((-s / d : ℝ) : ℂ) • southPoint u v p α) + ((0 : ℂ) • u)))
                =
                  ((((d : ℝ) : ℂ)⁻¹) • coordPoint u v p x) -
                    ((((d : ℝ) : ℂ)⁻¹ * (((s : ℝ) : ℂ))) • southPoint u v p α) := by
                      rw [hqdiv, hmain]
                      simp [sub_eq_add_neg]
            _ = (((d : ℝ) : ℂ)⁻¹) •
                  (coordPoint u v p x - (((s : ℝ) : ℂ) • southPoint u v p α)) := by
                    rw [smul_sub, smul_smul]
            _ = ambientRPerpCoord u v p α x := by
                  simp [ambientRPerpCoord, s, d]

lemma ambientQCoord_base
    {α : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    ambientQCoord α coordBase = poleCoord := by
  have hsina_pos : 0 < Real.sin α := by
    have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
  have hsina_ne : Real.sin α ≠ 0 := ne_of_gt hsina_pos
  have hden : southDenCoord α (1, (0, 0)) = Real.sin α := by
    simpa [coordBase] using southDenCoord_base (α := α) hα0 hαpi
  ext
  · simp [ambientQCoord, coordBase, poleCoord, southInnerCoord]
  · simp [ambientQCoord, coordBase, poleCoord, southInnerCoord]
  · dsimp [ambientQCoord, coordBase, poleCoord, southInnerCoord]
    rw [hden]
    simp [div_self hsina_ne]

lemma ambientRCoord_base
    {α : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    ambientRCoord α coordBase = (Real.sin α, (0, Real.cos α)) := by
  have hsina_pos : 0 < Real.sin α := by
    have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
  have hsina_ne : Real.sin α ≠ 0 := ne_of_gt hsina_pos
  have hden : southDenCoord α (1, (0, 0)) = Real.sin α := by
    simpa [coordBase] using southDenCoord_base (α := α) hα0 hαpi
  ext
  · dsimp [ambientRCoord, coordBase, southInnerCoord]
    rw [hden]
    have hsq : 1 - Real.cos α ^ 2 = Real.sin α ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq α]
    rw [show 1 - (1 * Real.cos α - 0 * Real.sin α) * Real.cos α =
        1 - Real.cos α ^ 2 by ring, hsq]
    field_simp [hsina_ne]
  · simp [ambientRCoord, coordBase, southInnerCoord]
  · dsimp [ambientRCoord, coordBase, southInnerCoord]
    rw [hden]
    ring_nf
    field_simp [hsina_ne]

lemma continuousAt_ambientQCoord
    {α : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    ContinuousAt (ambientQCoord α) coordBase := by
  have hx : ContinuousAt (fun x : ℝ × ℝ × ℝ => x.1) coordBase :=
    continuous_fst.continuousAt
  have hy : ContinuousAt (fun x : ℝ × ℝ × ℝ => x.2.1) coordBase :=
    continuous_snd.fst.continuousAt
  have hz : ContinuousAt (fun x : ℝ × ℝ × ℝ => x.2.2) coordBase :=
    continuous_snd.snd.continuousAt
  have hs : ContinuousAt (southInnerCoord α) coordBase :=
    (continuous_southInnerCoord α).continuousAt
  have hd : ContinuousAt (southDenCoord α) coordBase :=
    (continuous_southDenCoord α).continuousAt
  have hden_ne : southDenCoord α coordBase ≠ 0 := by
    rw [southDenCoord_base hα0 hαpi]
    have hsina_pos : 0 < Real.sin α := by
      have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
      exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
    exact ne_of_gt hsina_pos
  have h1 :
      ContinuousAt
        (fun x : ℝ × ℝ × ℝ =>
          (southInnerCoord α x * x.1 - Real.cos α) / southDenCoord α x)
        coordBase := by
    exact ((hs.mul hx).sub continuousAt_const).div hd hden_ne
  have h2 :
      ContinuousAt
        (fun x : ℝ × ℝ × ℝ =>
          (southInnerCoord α x * x.2.1) / southDenCoord α x)
        coordBase := by
    exact (hs.mul hy).div hd hden_ne
  have h3 :
      ContinuousAt
        (fun x : ℝ × ℝ × ℝ =>
          (southInnerCoord α x * x.2.2 + Real.sin α) / southDenCoord α x)
        coordBase := by
    exact ((hs.mul hz).add continuousAt_const).div hd hden_ne
  simpa [ambientQCoord] using h1.prodMk (h2.prodMk h3)

lemma continuousAt_ambientRCoord
    {α : ℝ} (hα0 : 0 < α) (hαpi : α < Real.pi / 2) :
    ContinuousAt (ambientRCoord α) coordBase := by
  have hx : ContinuousAt (fun x : ℝ × ℝ × ℝ => x.1) coordBase :=
    continuous_fst.continuousAt
  have hy : ContinuousAt (fun x : ℝ × ℝ × ℝ => x.2.1) coordBase :=
    continuous_snd.fst.continuousAt
  have hz : ContinuousAt (fun x : ℝ × ℝ × ℝ => x.2.2) coordBase :=
    continuous_snd.snd.continuousAt
  have hs : ContinuousAt (southInnerCoord α) coordBase :=
    (continuous_southInnerCoord α).continuousAt
  have hd : ContinuousAt (southDenCoord α) coordBase :=
    (continuous_southDenCoord α).continuousAt
  have hden_ne : southDenCoord α coordBase ≠ 0 := by
    rw [southDenCoord_base hα0 hαpi]
    have hsina_pos : 0 < Real.sin α := by
      have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
      exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
    exact ne_of_gt hsina_pos
  have h1 :
      ContinuousAt
        (fun x : ℝ × ℝ × ℝ =>
          (x.1 - southInnerCoord α x * Real.cos α) / southDenCoord α x)
        coordBase := by
    exact (hx.sub (hs.mul continuousAt_const)).div hd hden_ne
  have h2 :
      ContinuousAt
        (fun x : ℝ × ℝ × ℝ => x.2.1 / southDenCoord α x)
        coordBase := by
    exact hy.div hd hden_ne
  have h3 :
      ContinuousAt
        (fun x : ℝ × ℝ × ℝ =>
          (x.2.2 + southInnerCoord α x * Real.sin α) / southDenCoord α x)
        coordBase := by
    exact (hz.add (hs.mul continuousAt_const)).div hd hden_ne
  simpa [ambientRCoord] using h1.prodMk (h2.prodMk h3)

lemma exists_small_ambient_companion_cap_uniform
    {ε : ℝ} (hε : 0 < ε) :
    ∃ α δ : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < δ ∧
      ∀ {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        ∀ {x : ℝ × ℝ × ℝ}, dist x coordBase < δ →
          0 < southDenCoord α x ∧
          dist (ambientQPerpCoord u v p α x) p < ε ∧
          dist (ambientRPerpCoord u v p α x) p < ε := by
  let northCoord : ℝ → ℝ × ℝ × ℝ := fun a => (Real.sin a, (0, Real.cos a))
  have hnorth_zero : northCoord 0 = poleCoord := by
    simp [northCoord, poleCoord]
  have hnorth_cont : ContinuousAt northCoord 0 := by
    have hsin : Continuous fun a : ℝ => Real.sin a := Real.continuous_sin
    have hzero : Continuous fun _ : ℝ => (0 : ℝ) := continuous_const
    have hcos : Continuous fun a : ℝ => Real.cos a := Real.continuous_cos
    exact (hsin.prodMk (hzero.prodMk hcos)).continuousAt
  have hε6 : 0 < ε / 6 := by positivity
  rcases (Metric.continuousAt_iff.mp hnorth_cont) (ε / 6) hε6 with
    ⟨δα, hδα, hδαprop⟩
  let α : ℝ := min (δα / 2) (Real.pi / 4)
  have hα0 : 0 < α := by
    have hhalf_pos : 0 < δα / 2 := by positivity
    have hquarter_pos : 0 < Real.pi / 4 := by positivity
    exact lt_min hhalf_pos hquarter_pos
  have hαsmall : α < δα := by
    have hhalf_lt : δα / 2 < δα := by nlinarith
    exact lt_of_le_of_lt (min_le_left _ _) hhalf_lt
  have hαpi : α < Real.pi / 2 := by
    have hquarter_lt : Real.pi / 4 < Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    exact lt_of_le_of_lt (min_le_right _ _) hquarter_lt
  have hαdist : dist α 0 < δα := by
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos hα0] using hαsmall
  have hrbase_close : dist (northCoord α) poleCoord < ε / 6 := by
    simpa [hnorth_zero] using hδαprop hαdist
  have hqcont : ContinuousAt (ambientQCoord α) coordBase :=
    continuousAt_ambientQCoord hα0 hαpi
  have hrcont : ContinuousAt (ambientRCoord α) coordBase :=
    continuousAt_ambientRCoord hα0 hαpi
  have hden_cont : ContinuousAt (southDenCoord α) coordBase :=
    (continuous_southDenCoord α).continuousAt
  have hsina_pos : 0 < Real.sin α := by
    have hltπ : α < Real.pi := by nlinarith [hαpi, Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hα0 hltπ
  have hε3 : 0 < ε / 3 := by positivity
  rcases (Metric.continuousAt_iff.mp hqcont) (ε / 3) hε3 with
    ⟨δq, hδq, hδqprop⟩
  rcases (Metric.continuousAt_iff.mp hrcont) (ε / 6) hε6 with
    ⟨δr, hδr, hδrprop⟩
  rcases (Metric.continuousAt_iff.mp hden_cont) (Real.sin α / 2) (by positivity) with
    ⟨δden, hδden, hδdenprop⟩
  refine ⟨α, min δq (min δr δden), hα0, hαpi,
    lt_min hδq (lt_min hδr hδden), ?_⟩
  intro u v p hu hv hp x hx
  have hxq : dist x coordBase < δq := lt_of_lt_of_le hx (min_le_left _ _)
  have hxr : dist x coordBase < δr :=
    lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_left _ _))
  have hxden : dist x coordBase < δden :=
    lt_of_lt_of_le hx ((min_le_right _ _).trans (min_le_right _ _))
  have hqcoord : dist (ambientQCoord α x) (ambientQCoord α coordBase) < ε / 3 :=
    hδqprop hxq
  have hrcoord : dist (ambientRCoord α x) (ambientRCoord α coordBase) < ε / 6 :=
    hδrprop hxr
  have hden_close : dist (southDenCoord α x) (southDenCoord α coordBase) < Real.sin α / 2 :=
    hδdenprop hxden
  have hden_pos : 0 < southDenCoord α x := by
    have hbase : southDenCoord α coordBase = Real.sin α := southDenCoord_base hα0 hαpi
    have habs : |southDenCoord α x - Real.sin α| < Real.sin α / 2 := by
      simpa [Real.dist_eq, hbase, abs_sub_comm] using hden_close
    have hlower : Real.sin α - Real.sin α / 2 < southDenCoord α x := by
      nlinarith [(abs_lt.mp habs).1]
    nlinarith
  have hqcoord_pole : dist (ambientQCoord α x) poleCoord < ε / 3 := by
    simpa [ambientQCoord_base hα0 hαpi] using hqcoord
  have hqH : dist (ambientQPerpCoord u v p α x) p < ε := by
    have hden_ne : southDenCoord α x ≠ 0 := ne_of_gt hden_pos
    rw [← coordPoint_ambientQCoord (u := u) (v := v) (p := p) hden_ne]
    have hle := dist_coordPoint_le_three_mul_dist_coords hu hv hp
      (ambientQCoord α x) poleCoord
    simpa [coordPoint_poleCoord] using lt_of_le_of_lt hle (by nlinarith)
  have hrcoord_base :
      dist (ambientRCoord α x) (northCoord α) < ε / 6 := by
    simpa [northCoord, ambientRCoord_base hα0 hαpi] using hrcoord
  have hrcoord_pole : dist (ambientRCoord α x) poleCoord < ε / 3 := by
    have htri := dist_triangle (ambientRCoord α x) (northCoord α) poleCoord
    exact lt_of_le_of_lt htri (by nlinarith)
  have hrH : dist (ambientRPerpCoord u v p α x) p < ε := by
    have hden_ne : southDenCoord α x ≠ 0 := ne_of_gt hden_pos
    rw [← coordPoint_ambientRCoord (u := u) (v := v) (p := p) hden_ne]
    have hle := dist_coordPoint_le_three_mul_dist_coords hu hv hp
      (ambientRCoord α x) poleCoord
    simpa [coordPoint_poleCoord] using lt_of_le_of_lt hle (by nlinarith)
  exact ⟨hden_pos, hqH, hrH⟩

lemma ambientQCoord_sq_sum
    {u v p : H} {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    (ambientQCoord α x).1 ^ 2 + (ambientQCoord α x).2.1 ^ 2 + (ambientQCoord α x).2.2 ^ 2 = 1 := by
  have hnorm : ‖coordPoint u v p (ambientQCoord α x)‖ = 1 := by
    rw [coordPoint_ambientQCoord (u := u) (v := v) (p := p) hden]
    exact ambientQPerpCoord_norm hu hv hp huv hup hvp hx hden
  have hsq :=
    norm_sq_realFramePoint hu hv hp huv hup hvp
      (ambientQCoord α x).1 (ambientQCoord α x).2.1 (ambientQCoord α x).2.2
  have hnorm' :
      ‖realFramePoint u v p
          (ambientQCoord α x).1 (ambientQCoord α x).2.1 (ambientQCoord α x).2.2‖ = 1 := by
    simpa [coordPoint_eq_realFramePoint] using hnorm
  rw [hnorm'] at hsq
  nlinarith

lemma ambientRCoord_sq_sum
    {u v p : H} {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    (ambientRCoord α x).1 ^ 2 + (ambientRCoord α x).2.1 ^ 2 + (ambientRCoord α x).2.2 ^ 2 = 1 := by
  have hnorm : ‖coordPoint u v p (ambientRCoord α x)‖ = 1 := by
    rw [coordPoint_ambientRCoord (u := u) (v := v) (p := p) hden]
    exact ambientRPerpCoord_norm hu hv hp huv hup hvp hx hden
  have hsq :=
    norm_sq_realFramePoint hu hv hp huv hup hvp
      (ambientRCoord α x).1 (ambientRCoord α x).2.1 (ambientRCoord α x).2.2
  have hnorm' :
      ‖realFramePoint u v p
          (ambientRCoord α x).1 (ambientRCoord α x).2.1 (ambientRCoord α x).2.2‖ = 1 := by
    simpa [coordPoint_eq_realFramePoint] using hnorm
  rw [hnorm'] at hsq
  nlinarith

lemma ambient_oscillation_bound_of_cap_coords
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hosc :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < ε →
        dist (coordPoint u v p y) p < ε →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤ a) :
    ∃ α δ : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
        x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
        dist x₁ coordBase < δ →
        dist x₂ coordBase < δ →
        |frame_quadratic μ (coordPoint u v p x₁) -
            frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * a := by
  rcases exists_small_ambient_companion_cap (u := u) (v := v) (p := p) hε with
    ⟨α, δ, hα0, hαpi, hδ, hcap⟩
  refine ⟨α, δ, hα0, hαpi, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdist₁ hdist₂
  rcases hcap hdist₁ with ⟨hden₁, hq₁p, hr₁p⟩
  rcases hcap hdist₂ with ⟨hden₂, hq₂p, hr₂p⟩
  have hqbound :
      |frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
          frame_quadratic μ (ambientQPerpCoord u v p α x₁)| ≤ a := by
    rw [← coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₂) (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
    rw [← coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₁) (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
    apply hosc
    · exact ambientQCoord_sq_sum hu hv hp huv hup hvp hx₂ (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)
    · exact ambientQCoord_sq_sum hu hv hp huv hup hvp hx₁ (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)
    · simpa [coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₂)
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
        using hq₂p
    · simpa [coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₁)
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
        using hq₁p
  have hrbound :
      |frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
          frame_quadratic μ (ambientRPerpCoord u v p α x₂)| ≤ a := by
    rw [← coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₁) (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
    rw [← coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₂) (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
    apply hosc
    · exact ambientRCoord_sq_sum hu hv hp huv hup hvp hx₁ (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)
    · exact ambientRCoord_sq_sum hu hv hp huv hup hvp hx₂ (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)
    · simpa [coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₁)
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
        using hr₁p
    · simpa [coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₂)
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
        using hr₂p
  have hsum₁ :=
    south_ambientRPerp_frame_sum hdim μ hu hv hp huv hup hvp
      (α := α) (x := x₁) hx₁ (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)
  have hsum₂ :=
    south_ambientRPerp_frame_sum hdim μ hu hv hp huv hup hvp
      (α := α) (x := x₂) hx₂ (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)
  have hEq :
      frame_quadratic μ (coordPoint u v p x₁) -
          frame_quadratic μ (coordPoint u v p x₂) =
        (frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
            frame_quadratic μ (ambientRPerpCoord u v p α x₂)) +
          (frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
            frame_quadratic μ (ambientQPerpCoord u v p α x₁)) := by
    linarith
  calc
    |frame_quadratic μ (coordPoint u v p x₁) -
        frame_quadratic μ (coordPoint u v p x₂)|
        =
      |(frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
          frame_quadratic μ (ambientRPerpCoord u v p α x₂)) +
        (frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
          frame_quadratic μ (ambientQPerpCoord u v p α x₁))| := by
            rw [hEq]
    _ ≤
      |frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
          frame_quadratic μ (ambientRPerpCoord u v p α x₂)| +
        |frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
          frame_quadratic μ (ambientQPerpCoord u v p α x₁)| := by
            exact abs_add_le _ _
    _ ≤ a + a := add_le_add hrbound hqbound
    _ = 2 * a := by ring

lemma ambient_oscillation_bound_of_cap_coords_uniform
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ α δ : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < δ ∧
      ∀ {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) p < ε →
          dist (coordPoint u v p y) p < ε →
          |frame_quadratic μ (coordPoint u v p x) -
              frame_quadratic μ (coordPoint u v p y)| ≤ a) →
        ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
          x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
          x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
          dist x₁ coordBase < δ →
          dist x₂ coordBase < δ →
          |frame_quadratic μ (coordPoint u v p x₁) -
              frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * a := by
  rcases exists_small_ambient_companion_cap_uniform (H := H) hε with
    ⟨α, δ, hα0, hαpi, hδ, hcap⟩
  refine ⟨α, δ, hα0, hαpi, hδ, ?_⟩
  intro u v p hu hv hp huv hup hvp hosc x₁ x₂ hx₁ hx₂ hdist₁ hdist₂
  rcases hcap hu hv hp hdist₁ with ⟨hden₁, hq₁p, hr₁p⟩
  rcases hcap hu hv hp hdist₂ with ⟨hden₂, hq₂p, hr₂p⟩
  have hqbound :
      |frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
          frame_quadratic μ (ambientQPerpCoord u v p α x₁)| ≤ a := by
    rw [← coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₂)
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
    rw [← coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₁)
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
    apply hosc
    · exact ambientQCoord_sq_sum hu hv hp huv hup hvp hx₂
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)
    · exact ambientQCoord_sq_sum hu hv hp huv hup hvp hx₁
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)
    · simpa [coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₂)
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
        using hq₂p
    · simpa [coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₁)
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
        using hq₁p
  have hrbound :
      |frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
          frame_quadratic μ (ambientRPerpCoord u v p α x₂)| ≤ a := by
    rw [← coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₁)
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
    rw [← coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₂)
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
    apply hosc
    · exact ambientRCoord_sq_sum hu hv hp huv hup hvp hx₁
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)
    · exact ambientRCoord_sq_sum hu hv hp huv hup hvp hx₂
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)
    · simpa [coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₁)
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
        using hr₁p
    · simpa [coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₂)
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
        using hr₂p
  have hsum₁ :=
    south_ambientRPerp_frame_sum hdim μ hu hv hp huv hup hvp
      (α := α) (x := x₁) hx₁ (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)
  have hsum₂ :=
    south_ambientRPerp_frame_sum hdim μ hu hv hp huv hup hvp
      (α := α) (x := x₂) hx₂ (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)
  have hEq :
      frame_quadratic μ (coordPoint u v p x₁) -
          frame_quadratic μ (coordPoint u v p x₂) =
        (frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
            frame_quadratic μ (ambientRPerpCoord u v p α x₂)) +
          (frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
            frame_quadratic μ (ambientQPerpCoord u v p α x₁)) := by
    linarith
  calc
    |frame_quadratic μ (coordPoint u v p x₁) -
        frame_quadratic μ (coordPoint u v p x₂)|
        =
      |(frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
          frame_quadratic μ (ambientRPerpCoord u v p α x₂)) +
        (frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
          frame_quadratic μ (ambientQPerpCoord u v p α x₁))| := by
            rw [hEq]
    _ ≤
      |frame_quadratic μ (ambientRPerpCoord u v p α x₁) -
          frame_quadratic μ (ambientRPerpCoord u v p α x₂)| +
        |frame_quadratic μ (ambientQPerpCoord u v p α x₂) -
          frame_quadratic μ (ambientQPerpCoord u v p α x₁)| := by
            exact abs_add_le _ _
    _ ≤ a + a := add_le_add hrbound hqbound
    _ = 2 * a := by ring

lemma ambient_oscillation_bound_of_cap_coords_uniform_any
    (hdim : 3 ≤ Module.finrank ℂ H)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ α δ : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < δ ∧
      ∀ (ν : FrameFunction H) {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) p < ε →
          dist (coordPoint u v p y) p < ε →
          |frame_quadratic ν (coordPoint u v p x) -
              frame_quadratic ν (coordPoint u v p y)| ≤ a) →
        ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
          x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
          x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
          dist x₁ coordBase < δ →
          dist x₂ coordBase < δ →
          |frame_quadratic ν (coordPoint u v p x₁) -
              frame_quadratic ν (coordPoint u v p x₂)| ≤ 2 * a := by
  rcases exists_small_ambient_companion_cap_uniform (H := H) hε with
    ⟨α, δ, hα0, hαpi, hδ, hcap⟩
  refine ⟨α, δ, hα0, hαpi, hδ, ?_⟩
  intro ν u v p hu hv hp huv hup hvp hosc x₁ x₂ hx₁ hx₂ hdist₁ hdist₂
  rcases hcap hu hv hp hdist₁ with ⟨hden₁, hq₁p, hr₁p⟩
  rcases hcap hu hv hp hdist₂ with ⟨hden₂, hq₂p, hr₂p⟩
  have hqbound :
      |frame_quadratic ν (ambientQPerpCoord u v p α x₂) -
          frame_quadratic ν (ambientQPerpCoord u v p α x₁)| ≤ a := by
    rw [← coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₂)
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
    rw [← coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₁)
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
    apply hosc
    · exact ambientQCoord_sq_sum hu hv hp huv hup hvp hx₂
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)
    · exact ambientQCoord_sq_sum hu hv hp huv hup hvp hx₁
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)
    · simpa [coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₂)
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
        using hq₂p
    · simpa [coordPoint_ambientQCoord (u := u) (v := v) (p := p) (x := x₁)
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
        using hq₁p
  have hrbound :
      |frame_quadratic ν (ambientRPerpCoord u v p α x₁) -
          frame_quadratic ν (ambientRPerpCoord u v p α x₂)| ≤ a := by
    rw [← coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₁)
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
    rw [← coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₂)
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
    apply hosc
    · exact ambientRCoord_sq_sum hu hv hp huv hup hvp hx₁
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)
    · exact ambientRCoord_sq_sum hu hv hp huv hup hvp hx₂
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)
    · simpa [coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₁)
        (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)]
        using hr₁p
    · simpa [coordPoint_ambientRCoord (u := u) (v := v) (p := p) (x := x₂)
        (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)]
        using hr₂p
  have hsum₁ :=
    south_ambientRPerp_frame_sum hdim ν hu hv hp huv hup hvp
      (α := α) (x := x₁) hx₁ (show southDenCoord α x₁ ≠ 0 from ne_of_gt hden₁)
  have hsum₂ :=
    south_ambientRPerp_frame_sum hdim ν hu hv hp huv hup hvp
      (α := α) (x := x₂) hx₂ (show southDenCoord α x₂ ≠ 0 from ne_of_gt hden₂)
  have hEq :
      frame_quadratic ν (coordPoint u v p x₁) -
          frame_quadratic ν (coordPoint u v p x₂) =
        (frame_quadratic ν (ambientRPerpCoord u v p α x₁) -
            frame_quadratic ν (ambientRPerpCoord u v p α x₂)) +
          (frame_quadratic ν (ambientQPerpCoord u v p α x₂) -
            frame_quadratic ν (ambientQPerpCoord u v p α x₁)) := by
    linarith
  calc
    |frame_quadratic ν (coordPoint u v p x₁) -
        frame_quadratic ν (coordPoint u v p x₂)|
        =
      |(frame_quadratic ν (ambientRPerpCoord u v p α x₁) -
          frame_quadratic ν (ambientRPerpCoord u v p α x₂)) +
        (frame_quadratic ν (ambientQPerpCoord u v p α x₂) -
          frame_quadratic ν (ambientQPerpCoord u v p α x₁))| := by
            rw [hEq]
    _ ≤
      |frame_quadratic ν (ambientRPerpCoord u v p α x₁) -
          frame_quadratic ν (ambientRPerpCoord u v p α x₂)| +
        |frame_quadratic ν (ambientQPerpCoord u v p α x₂) -
          frame_quadratic ν (ambientQPerpCoord u v p α x₁)| := by
            exact abs_add_le _ _
    _ ≤ a + a := add_le_add hrbound hqbound
    _ = 2 * a := by ring

lemma targetPoleCoord_sq_sum
    {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    (targetPoleCoord z).1 ^ 2 + (targetPoleCoord z).2.1 ^ 2 + (targetPoleCoord z).2.2 ^ 2 = 1 := by
  have hρsq := horizontalRadius_sq z
  unfold targetPoleCoord
  field_simp [hρ]
  nlinarith [hρsq]

lemma targetBridgeCoord_sq_sum
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    (targetBridgeCoord z).1 ^ 2 + (targetBridgeCoord z).2.1 ^ 2 + (targetBridgeCoord z).2.2 ^ 2 = 1 := by
  have hρsq := horizontalRadius_sq z
  unfold targetBridgeCoord
  field_simp [hρ]
  nlinarith [hρsq, hz]

lemma coordPoint_eq_horizontalUnit_add_pole
    (u v p : H) {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    coordPoint u v p z =
      ((horizontalRadius z : ℝ) : ℂ) • coordPoint u v p (horizontalUnitCoord z) +
        ((z.2.2 : ℝ) : ℂ) • p := by
  rw [coordPoint_eq_realFramePoint,
    coordPoint_eq_realFramePoint u v p (horizontalUnitCoord z)]
  have hpTerm :
      (((z.2.2 : ℝ) : ℂ) • p) =
        realFramePoint u v p 0 0 z.2.2 := by
    simp [realFramePoint]
  rw [hpTerm, realFramePoint_real_smul, realFramePoint_add]
  congr 1 <;> simp [horizontalUnitCoord] <;> field_simp [hρ]

lemma coordPoint_targetBridgeCoord_eq_horizontalUnit_sub_pole
    (u v p : H) {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    coordPoint u v p (targetBridgeCoord z) =
      ((z.2.2 : ℝ) : ℂ) • coordPoint u v p (horizontalUnitCoord z) -
        ((horizontalRadius z : ℝ) : ℂ) • p := by
  rw [coordPoint_eq_realFramePoint,
    coordPoint_eq_realFramePoint u v p (horizontalUnitCoord z)]
  simp only [targetBridgeCoord, Prod.fst]
  have hpTerm :
      (((horizontalRadius z : ℝ) : ℂ) • p) =
        realFramePoint u v p 0 0 (horizontalRadius z) := by
    simp [realFramePoint]
  rw [hpTerm, realFramePoint_real_smul, sub_eq_add_neg]
  have hneg :
      -realFramePoint u v p 0 0 (horizontalRadius z) =
        realFramePoint u v p 0 0 (-horizontalRadius z) := by
    simp [realFramePoint]
  rw [hneg, realFramePoint_add]
  congr 1 <;> simp [horizontalUnitCoord] <;> field_simp [hρ]

lemma frame_quadratic_targetBridge_identity
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    frame_quadratic μ (coordPoint u v p z) +
        frame_quadratic μ (coordPoint u v p (targetBridgeCoord z)) =
      frame_quadratic μ (coordPoint u v p (horizontalUnitCoord z)) +
        frame_quadratic μ p := by
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    dsimp [w]
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, horizontalUnitCoord]
    simpa [coordPoint_poleCoord u v p] using hwp'
  have hunit : horizontalRadius z ^ 2 + z.2.2 ^ 2 = 1 := by
    have hρsq := horizontalRadius_sq z
    nlinarith
  have hgc :=
    GleasonBridge.great_circle_constancy hdim μ w p hw hp hwp
      (horizontalRadius z) z.2.2 hunit
  have hzrepr :
      ((horizontalRadius z : ℝ) : ℂ) • w + ((z.2.2 : ℝ) : ℂ) • p =
        coordPoint u v p z := by
    dsimp [w]
    exact (coordPoint_eq_horizontalUnit_add_pole (u := u) (v := v) (p := p) hρ).symm
  have hbrepr :
      ((z.2.2 : ℝ) : ℂ) • w - ((horizontalRadius z : ℝ) : ℂ) • p =
        coordPoint u v p (targetBridgeCoord z) := by
    dsimp [w]
    exact (coordPoint_targetBridgeCoord_eq_horizontalUnit_sub_pole
      (u := u) (v := v) (p := p) hρ).symm
  rw [hzrepr, hbrepr] at hgc
  exact hgc

lemma frame_quadratic_horizontalUnit_sub_targetBridge
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    frame_quadratic μ (coordPoint u v p (horizontalUnitCoord z)) -
        frame_quadratic μ (coordPoint u v p (targetBridgeCoord z)) =
      frame_quadratic μ (coordPoint u v p z) - frame_quadratic μ p := by
  have h :=
    frame_quadratic_targetBridge_identity
      (H := H) hdim μ hu hv hp huv hup hvp hz hρ
  linarith

lemma norm_sq_coordPoint_horizontalUnit_sub_targetBridgeCoord
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    ‖coordPoint u v p (horizontalUnitCoord z) -
        coordPoint u v p (targetBridgeCoord z)‖ ^ 2 =
      horizontalRadius z ^ 2 + (1 - z.2.2) ^ 2 := by
  rw [coordPoint_sub]
  have hsq := norm_sq_realFramePoint hu hv hp huv hup hvp
    ((horizontalUnitCoord z).1 - (targetBridgeCoord z).1)
    ((horizontalUnitCoord z).2.1 - (targetBridgeCoord z).2.1)
    ((horizontalUnitCoord z).2.2 - (targetBridgeCoord z).2.2)
  rw [hsq]
  simp [horizontalUnitCoord, targetBridgeCoord]
  field_simp [hρ]
  have hρsq := horizontalRadius_sq z
  nlinarith [hρsq]

lemma norm_sq_coordPoint_sub_poleCoord
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (z : ℝ × ℝ × ℝ) :
    ‖coordPoint u v p z - p‖ ^ 2 =
      horizontalRadius z ^ 2 + (1 - z.2.2) ^ 2 := by
  calc
    ‖coordPoint u v p z - p‖ ^ 2
        = ‖coordPoint u v p z - coordPoint u v p poleCoord‖ ^ 2 := by
            rw [coordPoint_poleCoord]
    _ = horizontalRadius z ^ 2 + (1 - z.2.2) ^ 2 := by
      rw [coordPoint_sub]
      have hsq := norm_sq_realFramePoint hu hv hp huv hup hvp
        (z.1 - poleCoord.1) (z.2.1 - poleCoord.2.1) (z.2.2 - poleCoord.2.2)
      rw [hsq]
      simp [poleCoord]
      have hρsq := horizontalRadius_sq z
      nlinarith [hρsq]

lemma norm_sq_coordPoint_sub_poleCoord_eq_two_mul_one_sub_third
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1) :
    ‖coordPoint u v p z - p‖ ^ 2 = 2 * (1 - z.2.2) := by
  rw [norm_sq_coordPoint_sub_poleCoord hu hv hp huv hup hvp z]
  have hρsq := horizontalRadius_sq z
  nlinarith [hρsq, hz]

lemma dist_coordPoint_pole_sq_eq_two_mul_one_sub_third
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1) :
    dist (coordPoint u v p z) p ^ 2 = 2 * (1 - z.2.2) := by
  rw [dist_eq_norm]
  exact norm_sq_coordPoint_sub_poleCoord_eq_two_mul_one_sub_third
    hu hv hp huv hup hvp hz

lemma horizontalRadius_sq_le_dist_coordPoint_pole_sq
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1) :
    horizontalRadius z ^ 2 ≤ dist (coordPoint u v p z) p ^ 2 := by
  rw [dist_coordPoint_pole_sq_eq_two_mul_one_sub_third hu hv hp huv hup hvp hz]
  have hρsq := horizontalRadius_sq z
  nlinarith [hρsq, hz]

lemma dist_coordPoint_pole_sq_le_two_mul_horizontalRadius_sq_of_third_nonneg
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hz_nonneg : 0 ≤ z.2.2) :
    dist (coordPoint u v p z) p ^ 2 ≤ 2 * horizontalRadius z ^ 2 := by
  rw [dist_coordPoint_pole_sq_eq_two_mul_one_sub_third hu hv hp huv hup hvp hz]
  have hρsq := horizontalRadius_sq z
  have hz_le_one : z.2.2 ≤ 1 := by
    nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, sq_nonneg (z.2.2 - 1), hz]
  nlinarith [hρsq, hz, hz_nonneg, hz_le_one]

lemma dist_coordPoint_horizontalUnit_targetBridgeCoord_eq_dist_coordPoint_pole
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    dist (coordPoint u v p (horizontalUnitCoord z))
        (coordPoint u v p (targetBridgeCoord z)) =
      dist (coordPoint u v p z) p := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [norm_sq_coordPoint_horizontalUnit_sub_targetBridgeCoord
      hu hv hp huv hup hvp hρ,
    norm_sq_coordPoint_sub_poleCoord hu hv hp huv hup hvp z]

lemma exists_subseq_pair_tendsto_same_of_dist_tendsto_zero
    {w b : ℕ → H}
    (hw : ∀ n, ‖w n‖ = 1)
    (hdist : Filter.Tendsto (fun n : ℕ => dist (w n) (b n)) Filter.atTop (nhds 0)) :
    ∃ w₀ : H, ‖w₀‖ = 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (w ∘ φ) Filter.atTop (nhds w₀) ∧
        Filter.Tendsto (b ∘ φ) Filter.atTop (nhds w₀) := by
  haveI : ProperSpace H := FiniteDimensional.proper_rclike ℂ H
  have hcpt : IsCompact (Metric.sphere (0 : H) 1) := isCompact_sphere 0 1
  have hw_mem : ∀ n, w n ∈ Metric.sphere (0 : H) 1 := by
    intro n
    simp [Metric.mem_sphere, hw n]
  rcases hcpt.tendsto_subseq hw_mem with ⟨w₀, hw₀_mem, φ, hφ, hwφ⟩
  have hw₀ : ‖w₀‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hw₀_mem
  have hdistφ :
      Filter.Tendsto (fun n : ℕ => dist (w (φ n)) (b (φ n))) Filter.atTop
        (nhds 0) := by
    simpa [Function.comp_def] using hdist.comp hφ.tendsto_atTop
  have hbφ : Filter.Tendsto (b ∘ φ) Filter.atTop (nhds w₀) := by
    rw [Metric.tendsto_atTop] at hwφ hdistφ ⊢
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    rcases hwφ (ε / 2) hε2 with ⟨Nw, hNw⟩
    rcases hdistφ (ε / 2) hε2 with ⟨Nd, hNd⟩
    refine ⟨max Nw Nd, ?_⟩
    intro n hn
    have hwclose : dist (w (φ n)) w₀ < ε / 2 :=
      hNw n (le_trans (le_max_left _ _) hn)
    have hdclose_raw :
        dist (dist (w (φ n)) (b (φ n))) 0 < ε / 2 :=
      hNd n (le_trans (le_max_right _ _) hn)
    have hdclose : dist (w (φ n)) (b (φ n)) < ε / 2 := by
      simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hdclose_raw
    have htri :
        dist (b (φ n)) w₀ ≤
          dist (b (φ n)) (w (φ n)) + dist (w (φ n)) w₀ :=
      dist_triangle _ _ _
    have hdclose' : dist (b (φ n)) (w (φ n)) < ε / 2 := by
      simpa [dist_comm] using hdclose
    dsimp [Function.comp]
    linarith
  exact ⟨w₀, hw₀, φ, hφ, hwφ, hbφ⟩

lemma dist_phase_aligned_coordPoint_pole_le
    {c : ℂ} {u v p q : H} {z : ℝ × ℝ × ℝ}
    (hc : ‖c‖ = 1)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hz_nonneg : 0 ≤ z.2.2)
    (hcoord : c • q = coordPoint u v p z) :
    dist (coordPoint u v p z) (coordPoint u v p poleCoord) ≤ dist q p := by
  rw [← hcoord, coordPoint_poleCoord]
  rw [dist_eq_norm, dist_eq_norm]
  have hinner_cq_eq : inner (𝕜 := ℂ) (c • q) p = (z.2.2 : ℂ) := by
    rw [hcoord, coordPoint]
    simp only [inner_add_left, inner_smul_left, hup, hvp, mul_zero, zero_add]
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hp]
    simp [starRingEnd_self_apply, Complex.conj_ofReal]
  have hre_q_le : RCLike.re (inner (𝕜 := ℂ) q p) ≤ z.2.2 := by
    have hval : starRingEnd ℂ c * inner (𝕜 := ℂ) q p = (z.2.2 : ℂ) := by
      have hsml : inner (𝕜 := ℂ) (c • q) p =
          starRingEnd ℂ c * inner (𝕜 := ℂ) q p := by
        rw [inner_smul_left]
      rw [← hsml]
      exact hinner_cq_eq
    have hnorm_prod : ‖inner (𝕜 := ℂ) q p‖ = z.2.2 := by
      have h1 : ‖starRingEnd ℂ c * inner (𝕜 := ℂ) q p‖ = z.2.2 := by
        rw [hval]
        simp [Complex.norm_real, abs_of_nonneg hz_nonneg]
      rwa [norm_mul, RCLike.norm_conj, hc, one_mul] at h1
    calc
      RCLike.re (inner (𝕜 := ℂ) q p)
          = (inner (𝕜 := ℂ) q p : ℂ).re := rfl
      _ ≤ ‖(inner (𝕜 := ℂ) q p : ℂ)‖ := Complex.re_le_norm _
      _ = z.2.2 := hnorm_prod
  have hre_cq_eq : RCLike.re (inner (𝕜 := ℂ) (c • q) p) = z.2.2 := by
    rw [hinner_cq_eq]
    simp
  have hns1 := @norm_sub_sq ℂ H _ _ _ (c • q) p
  have hns2 := @norm_sub_sq ℂ H _ _ _ q p
  have hcq_norm : ‖c • q‖ = 1 := by
    rw [norm_smul, hc, one_mul, hq]
  nlinarith [norm_nonneg (c • q - p), norm_nonneg (q - p),
    sq_nonneg (‖q - p‖ - ‖c • q - p‖),
    hns1, hns2, hcq_norm, hp, hq, hre_cq_eq, hre_q_le]

lemma exists_subseq_pair_tendsto_same_of_dist_le_tendsto
    {w b p : ℕ → H} {p₀ : H}
    (hw : ∀ n, ‖w n‖ = 1)
    (hp : Filter.Tendsto p Filter.atTop (nhds p₀))
    (hle : ∀ n, dist (w n) (b n) ≤ dist p₀ (p n)) :
    ∃ w₀ : H, ‖w₀‖ = 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto (w ∘ φ) Filter.atTop (nhds w₀) ∧
        Filter.Tendsto (b ∘ φ) Filter.atTop (nhds w₀) := by
  have hpdist :
      Filter.Tendsto (fun n : ℕ => dist p₀ (p n)) Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases Metric.tendsto_atTop.mp hp ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have h := hN n hn
    simpa [Real.dist_eq, abs_of_nonneg dist_nonneg, dist_comm] using h
  have hdist :
      Filter.Tendsto (fun n : ℕ => dist (w n) (b n)) Filter.atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hpdist
      (fun n => dist_nonneg) hle
  exact exists_subseq_pair_tendsto_same_of_dist_tendsto_zero hw hdist

lemma exists_subseq_targetBridge_pair_tendsto_same
    {pseq u v : ℕ → H} {z : ℕ → ℝ × ℝ × ℝ} {p₀ : H}
    (hpseq_norm : ∀ n, ‖pseq n‖ = 1)
    (hpseq_tendsto : Filter.Tendsto pseq Filter.atTop (nhds p₀))
    (hu : ∀ n, ‖u n‖ = 1)
    (hv : ∀ n, ‖v n‖ = 1)
    (huv : ∀ n, inner (𝕜 := ℂ) (u n) (v n) = 0)
    (hup : ∀ n, inner (𝕜 := ℂ) (u n) (pseq n) = 0)
    (hvp : ∀ n, inner (𝕜 := ℂ) (v n) (pseq n) = 0)
    (hz : ∀ n, (z n).1 ^ 2 + (z n).2.1 ^ 2 + (z n).2.2 ^ 2 = 1)
    (hρ : ∀ n, horizontalRadius (z n) ≠ 0)
    (hdist_phase :
      ∀ n, dist (coordPoint (u n) (v n) (pseq n) (z n)) (pseq n) ≤
        dist p₀ (pseq n)) :
    ∃ w₀ : H, ‖w₀‖ = 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto
          ((fun n => coordPoint (u n) (v n) (pseq n) (horizontalUnitCoord (z n))) ∘ φ)
          Filter.atTop (nhds w₀) ∧
        Filter.Tendsto
          ((fun n => coordPoint (u n) (v n) (pseq n) (targetBridgeCoord (z n))) ∘ φ)
          Filter.atTop (nhds w₀) := by
  let w : ℕ → H :=
    fun n => coordPoint (u n) (v n) (pseq n) (horizontalUnitCoord (z n))
  let b : ℕ → H :=
    fun n => coordPoint (u n) (v n) (pseq n) (targetBridgeCoord (z n))
  have hw : ∀ n, ‖w n‖ = 1 := by
    intro n
    dsimp [w]
    exact coordPoint_norm (hu n) (hv n) (hpseq_norm n) (huv n) (hup n) (hvp n)
      (horizontalUnitCoord_sq_sum (hρ n))
  have hle : ∀ n, dist (w n) (b n) ≤ dist p₀ (pseq n) := by
    intro n
    dsimp [w, b]
    calc
      dist (coordPoint (u n) (v n) (pseq n) (horizontalUnitCoord (z n)))
          (coordPoint (u n) (v n) (pseq n) (targetBridgeCoord (z n)))
          =
        dist (coordPoint (u n) (v n) (pseq n) (z n)) (pseq n) := by
          exact
            dist_coordPoint_horizontalUnit_targetBridgeCoord_eq_dist_coordPoint_pole
              (hu n) (hv n) (hpseq_norm n) (huv n) (hup n) (hvp n) (hρ n)
      _ ≤ dist p₀ (pseq n) := hdist_phase n
  simpa [w, b] using
    exists_subseq_pair_tendsto_same_of_dist_le_tendsto
      (w := w) (b := b) (p := pseq) (p₀ := p₀) hw hpseq_tendsto hle

lemma exists_subseq_targetBridge_pair_tendsto_same_of_phase_aligned
    {pseq u v : ℕ → H} {c : ℕ → ℂ} {z : ℕ → ℝ × ℝ × ℝ} {p₀ : H}
    (hpseq_norm : ∀ n, ‖pseq n‖ = 1)
    (hp₀_norm : ‖p₀‖ = 1)
    (hpseq_tendsto : Filter.Tendsto pseq Filter.atTop (nhds p₀))
    (hc : ∀ n, ‖c n‖ = 1)
    (hu : ∀ n, ‖u n‖ = 1)
    (hv : ∀ n, ‖v n‖ = 1)
    (huv : ∀ n, inner (𝕜 := ℂ) (u n) (v n) = 0)
    (hup : ∀ n, inner (𝕜 := ℂ) (u n) (pseq n) = 0)
    (hvp : ∀ n, inner (𝕜 := ℂ) (v n) (pseq n) = 0)
    (hz : ∀ n, (z n).1 ^ 2 + (z n).2.1 ^ 2 + (z n).2.2 ^ 2 = 1)
    (hρ : ∀ n, horizontalRadius (z n) ≠ 0)
    (hz_nonneg : ∀ n, 0 ≤ (z n).2.2)
    (hcoord : ∀ n, c n • p₀ = coordPoint (u n) (v n) (pseq n) (z n)) :
    ∃ w₀ : H, ‖w₀‖ = 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Filter.Tendsto
          ((fun n => coordPoint (u n) (v n) (pseq n) (horizontalUnitCoord (z n))) ∘ φ)
          Filter.atTop (nhds w₀) ∧
        Filter.Tendsto
          ((fun n => coordPoint (u n) (v n) (pseq n) (targetBridgeCoord (z n))) ∘ φ)
          Filter.atTop (nhds w₀) := by
  exact exists_subseq_targetBridge_pair_tendsto_same
    (pseq := pseq) (u := u) (v := v) (z := z) (p₀ := p₀)
    hpseq_norm hpseq_tendsto hu hv huv hup hvp hz hρ
    (fun n => by
      simpa [coordPoint_poleCoord] using
        dist_phase_aligned_coordPoint_pole_le
          (c := c n) (u := u n) (v := v n) (p := pseq n) (q := p₀)
          (z := z n) (hc n) (hpseq_norm n) hp₀_norm (hup n) (hvp n)
          (hz_nonneg n) (hcoord n))

lemma coordDot_target_targetPoleCoord
    {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    coordDot z (targetPoleCoord z) = 0 := by
  unfold coordDot targetPoleCoord
  field_simp [hρ]
  ring

lemma coordDot_target_targetBridgeCoord
    {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    coordDot z (targetBridgeCoord z) = 0 := by
  have hρsq := horizontalRadius_sq z
  have hρsq' : z.1 ^ 2 + z.2.1 ^ 2 = horizontalRadius z ^ 2 := by
    simpa [eq_comm] using hρsq
  unfold coordDot targetBridgeCoord
  field_simp [hρ]
  rw [hρsq']
  ring

lemma coordDot_targetPole_targetBridgeCoord
    {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    coordDot (targetPoleCoord z) (targetBridgeCoord z) = 0 := by
  unfold coordDot targetPoleCoord targetBridgeCoord
  field_simp [hρ]
  ring

lemma coordPoint_targetPoleCoord_norm
    {u v p : H} {z : ℝ × ℝ × ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hρ : horizontalRadius z ≠ 0) :
    ‖coordPoint u v p (targetPoleCoord z)‖ = 1 := by
  apply coordPoint_norm hu hv hp huv hup hvp
  exact targetPoleCoord_sq_sum hρ

lemma coordPoint_targetBridgeCoord_norm
    {u v p : H} {z : ℝ × ℝ × ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    ‖coordPoint u v p (targetBridgeCoord z)‖ = 1 := by
  apply coordPoint_norm hu hv hp huv hup hvp
  exact targetBridgeCoord_sq_sum hz hρ

lemma inner_coordPoint_targetPoleCoord_zero
    {u v p : H} {z : ℝ × ℝ × ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hρ : horizontalRadius z ≠ 0) :
    inner (𝕜 := ℂ) (coordPoint u v p z) (coordPoint u v p (targetPoleCoord z)) = 0 := by
  rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
  simp [coordDot_target_targetPoleCoord hρ]

lemma inner_coordPoint_targetBridgeCoord_zero
    {u v p : H} {z : ℝ × ℝ × ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hρ : horizontalRadius z ≠ 0) :
    inner (𝕜 := ℂ) (coordPoint u v p z) (coordPoint u v p (targetBridgeCoord z)) = 0 := by
  rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
  simp [coordDot_target_targetBridgeCoord hρ]

lemma inner_targetPoleCoord_targetBridgeCoord_zero
    {u v p : H} {z : ℝ × ℝ × ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hρ : horizontalRadius z ≠ 0) :
    inner (𝕜 := ℂ)
      (coordPoint u v p (targetPoleCoord z))
      (coordPoint u v p (targetBridgeCoord z)) = 0 := by
  rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
  simp [coordDot_targetPole_targetBridgeCoord hρ]

lemma targetFrameReparam_base
    (z : ℝ × ℝ × ℝ) :
    targetFrameReparam z coordBase = z := by
  ext <;> simp [targetFrameReparam, coordLinearCombo, coordBase]

lemma targetFrameReparam_sq_sum
    {u v p : H} {z y : ℝ × ℝ × ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    (targetFrameReparam z y).1 ^ 2 +
        (targetFrameReparam z y).2.1 ^ 2 +
        (targetFrameReparam z y).2.2 ^ 2 = 1 := by
  have hzNorm : ‖coordPoint u v p z‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hz
  have hbNorm : ‖coordPoint u v p (targetBridgeCoord z)‖ = 1 := by
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hz hρ
  have hqNorm : ‖coordPoint u v p (targetPoleCoord z)‖ = 1 := by
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hzb : inner (𝕜 := ℂ)
      (coordPoint u v p z) (coordPoint u v p (targetBridgeCoord z)) = 0 := by
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have hzq : inner (𝕜 := ℂ)
      (coordPoint u v p z) (coordPoint u v p (targetPoleCoord z)) = 0 := by
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρ
  have hbq : inner (𝕜 := ℂ)
      (coordPoint u v p (targetBridgeCoord z))
      (coordPoint u v p (targetPoleCoord z)) = 0 := by
    have htmp := inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
    simpa [inner_eq_zero_symm] using htmp
  have hnormY :
      ‖coordPoint (coordPoint u v p z)
          (coordPoint u v p (targetBridgeCoord z))
          (coordPoint u v p (targetPoleCoord z)) y‖ = 1 := by
    exact coordPoint_norm hzNorm hbNorm hqNorm hzb hzq hbq hy
  have hreprEq :
      coordPoint (coordPoint u v p z)
          (coordPoint u v p (targetBridgeCoord z))
          (coordPoint u v p (targetPoleCoord z)) y =
        coordPoint u v p (targetFrameReparam z y) := by
    simpa [targetFrameReparam] using
      coordPoint_coordLinearCombo u v p z (targetBridgeCoord z) (targetPoleCoord z) y
  have hrepr :
      ‖coordPoint u v p (targetFrameReparam z y)‖ = 1 := by
    rw [← hreprEq]
    exact hnormY
  have hrepr' :
      ‖realFramePoint u v p
          (targetFrameReparam z y).1
          (targetFrameReparam z y).2.1
          (targetFrameReparam z y).2.2‖ = 1 := by
    simpa [coordPoint_eq_realFramePoint] using hrepr
  have hsq :=
    norm_sq_realFramePoint hu hv hp huv hup hvp
      (targetFrameReparam z y).1 (targetFrameReparam z y).2.1 (targetFrameReparam z y).2.2
  rw [hrepr'] at hsq
  nlinarith

lemma coordPoint_targetFrameReparam
    (u v p : H)
    (z y : ℝ × ℝ × ℝ) :
    coordPoint (coordPoint u v p z) (coordPoint u v p (targetBridgeCoord z))
        (coordPoint u v p (targetPoleCoord z)) y =
      coordPoint u v p (targetFrameReparam z y) := by
  simpa [targetFrameReparam] using
    coordPoint_coordLinearCombo u v p z (targetBridgeCoord z) (targetPoleCoord z) y

lemma targetFrameReparamSwap_base
    (z : ℝ × ℝ × ℝ) :
    targetFrameReparamSwap z coordBase = z := by
  ext <;> simp [targetFrameReparamSwap, coordLinearCombo, coordBase]

lemma targetFrameReparamSwap_sq_sum
    {u v p : H} {z y : ℝ × ℝ × ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    (targetFrameReparamSwap z y).1 ^ 2 +
        (targetFrameReparamSwap z y).2.1 ^ 2 +
        (targetFrameReparamSwap z y).2.2 ^ 2 = 1 := by
  have hzNorm : ‖coordPoint u v p z‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hz
  have hbNorm : ‖coordPoint u v p (targetPoleCoord z)‖ = 1 := by
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hqNorm : ‖coordPoint u v p (targetBridgeCoord z)‖ = 1 := by
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hz hρ
  have hzb : inner (𝕜 := ℂ)
      (coordPoint u v p z) (coordPoint u v p (targetPoleCoord z)) = 0 := by
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρ
  have hzq : inner (𝕜 := ℂ)
      (coordPoint u v p z) (coordPoint u v p (targetBridgeCoord z)) = 0 := by
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have hbq : inner (𝕜 := ℂ)
      (coordPoint u v p (targetPoleCoord z))
      (coordPoint u v p (targetBridgeCoord z)) = 0 := by
    exact inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have hnormY :
      ‖coordPoint (coordPoint u v p z)
          (coordPoint u v p (targetPoleCoord z))
          (coordPoint u v p (targetBridgeCoord z)) y‖ = 1 := by
    exact coordPoint_norm hzNorm hbNorm hqNorm hzb hzq hbq hy
  have hreprEq :
      coordPoint (coordPoint u v p z)
          (coordPoint u v p (targetPoleCoord z))
          (coordPoint u v p (targetBridgeCoord z)) y =
        coordPoint u v p (targetFrameReparamSwap z y) := by
    simpa [targetFrameReparamSwap] using
      coordPoint_coordLinearCombo u v p z (targetPoleCoord z) (targetBridgeCoord z) y
  have hrepr :
      ‖coordPoint u v p (targetFrameReparamSwap z y)‖ = 1 := by
    rw [← hreprEq]
    exact hnormY
  have hrepr' :
      ‖realFramePoint u v p
          (targetFrameReparamSwap z y).1
          (targetFrameReparamSwap z y).2.1
          (targetFrameReparamSwap z y).2.2‖ = 1 := by
    simpa [coordPoint_eq_realFramePoint] using hrepr
  have hsq :=
    norm_sq_realFramePoint hu hv hp huv hup hvp
      (targetFrameReparamSwap z y).1
      (targetFrameReparamSwap z y).2.1
      (targetFrameReparamSwap z y).2.2
  rw [hrepr'] at hsq
  nlinarith

lemma coordPoint_targetFrameReparamSwap
    (u v p : H)
    (z y : ℝ × ℝ × ℝ) :
    coordPoint (coordPoint u v p z) (coordPoint u v p (targetPoleCoord z))
        (coordPoint u v p (targetBridgeCoord z)) y =
      coordPoint u v p (targetFrameReparamSwap z y) := by
  simpa [targetFrameReparamSwap] using
    coordPoint_coordLinearCombo u v p z (targetPoleCoord z) (targetBridgeCoord z) y

lemma coordDot_coordLinearCombo_right
    (a b c : ℝ) (x y z w : ℝ × ℝ × ℝ) :
    coordDot (coordLinearCombo a b c x y z) w =
      a * coordDot x w + b * coordDot y w + c * coordDot z w := by
  unfold coordDot coordLinearCombo
  ring

lemma coordDot_comm
    (x y : ℝ × ℝ × ℝ) :
    coordDot x y = coordDot y x := by
  unfold coordDot
  ring

lemma targetFrameCoords_targetFrameReparam
    {z y : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    targetFrameCoords z (targetFrameReparam z y) = y := by
  have hzz : coordDot z z = 1 := by
    simpa [coordDot, pow_two] using hz
  have hbb : coordDot (targetBridgeCoord z) (targetBridgeCoord z) = 1 := by
    simpa [coordDot, pow_two] using targetBridgeCoord_sq_sum hz hρ
  have hpp : coordDot (targetPoleCoord z) (targetPoleCoord z) = 1 := by
    simpa [coordDot, pow_two] using targetPoleCoord_sq_sum hρ
  have hbz : coordDot (targetBridgeCoord z) z = 0 := by
    rw [coordDot_comm]
    exact coordDot_target_targetBridgeCoord hρ
  have hpz : coordDot (targetPoleCoord z) z = 0 := by
    rw [coordDot_comm]
    exact coordDot_target_targetPoleCoord hρ
  have hbp : coordDot (targetBridgeCoord z) (targetPoleCoord z) = 0 := by
    rw [coordDot_comm]
    exact coordDot_targetPole_targetBridgeCoord hρ
  ext <;> simp [targetFrameCoords, targetFrameReparam, coordDot_coordLinearCombo_right,
    hzz, hbb, hpp, hbz, hpz, hbp,
    coordDot_target_targetBridgeCoord hρ, coordDot_target_targetPoleCoord hρ,
    coordDot_targetPole_targetBridgeCoord hρ]

lemma targetFrameCoordsSwap_targetFrameReparamSwap
    {z y : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    targetFrameCoordsSwap z (targetFrameReparamSwap z y) = y := by
  have hzz : coordDot z z = 1 := by
    simpa [coordDot, pow_two] using hz
  have hbb : coordDot (targetBridgeCoord z) (targetBridgeCoord z) = 1 := by
    simpa [coordDot, pow_two] using targetBridgeCoord_sq_sum hz hρ
  have hpp : coordDot (targetPoleCoord z) (targetPoleCoord z) = 1 := by
    simpa [coordDot, pow_two] using targetPoleCoord_sq_sum hρ
  have hbz : coordDot (targetBridgeCoord z) z = 0 := by
    rw [coordDot_comm]
    exact coordDot_target_targetBridgeCoord hρ
  have hpz : coordDot (targetPoleCoord z) z = 0 := by
    rw [coordDot_comm]
    exact coordDot_target_targetPoleCoord hρ
  have hbp : coordDot (targetBridgeCoord z) (targetPoleCoord z) = 0 := by
    rw [coordDot_comm]
    exact coordDot_targetPole_targetBridgeCoord hρ
  ext <;> simp [targetFrameCoordsSwap, targetFrameReparamSwap, coordDot_coordLinearCombo_right,
    hzz, hbb, hpp, hbz, hpz, hbp,
    coordDot_target_targetBridgeCoord hρ, coordDot_target_targetPoleCoord hρ,
    coordDot_targetPole_targetBridgeCoord hρ]

lemma targetFrameReparam_targetFrameCoords
    {z x : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    targetFrameReparam z (targetFrameCoords z x) = x := by
  have hρsq := horizontalRadius_sq z
  have hunit : z.2.2 ^ 2 + horizontalRadius z ^ 2 = 1 := by
    nlinarith [hz, hρsq]
  ext <;> unfold targetFrameReparam targetFrameCoords coordLinearCombo coordDot
    targetBridgeCoord targetPoleCoord
  · field_simp [hρ]
    ring_nf
    calc
      -(z.1 * x.2.1 * z.2.1) + z.1 * x.2.1 * z.2.1 * z.2.2 ^ 2 +
            z.1 * x.2.1 * z.2.1 * horizontalRadius z ^ 2 +
            z.1 ^ 2 * x.1 * z.2.2 ^ 2 +
            z.1 ^ 2 * x.1 * horizontalRadius z ^ 2 +
            x.1 * z.2.1 ^ 2
          =
            z.1 * x.2.1 * z.2.1 * (z.2.2 ^ 2 + horizontalRadius z ^ 2 - 1) +
              x.1 * (z.1 ^ 2 * (z.2.2 ^ 2 + horizontalRadius z ^ 2) + z.2.1 ^ 2) := by
                ring
      _ = x.1 * (z.1 ^ 2 + z.2.1 ^ 2) := by
            rw [hunit]
            ring
      _ = x.1 * horizontalRadius z ^ 2 := by
            rw [← hρsq]
  · field_simp [hρ]
    ring_nf
    have hρsq' : z.2.1 ^ 2 + z.1 ^ 2 = horizontalRadius z ^ 2 := by
      simpa [add_comm] using hρsq.symm
    calc
      -(z.2.1 * x.1 * z.1) + z.2.1 * x.1 * z.1 * z.2.2 ^ 2 +
            z.2.1 * x.1 * z.1 * horizontalRadius z ^ 2 +
            z.2.1 ^ 2 * x.2.1 * z.2.2 ^ 2 +
            z.2.1 ^ 2 * x.2.1 * horizontalRadius z ^ 2 +
            z.1 ^ 2 * x.2.1
          =
            z.2.1 * x.1 * z.1 * (z.2.2 ^ 2 + horizontalRadius z ^ 2 - 1) +
              x.2.1 * (z.2.1 ^ 2 * (z.2.2 ^ 2 + horizontalRadius z ^ 2) + z.1 ^ 2) := by
                ring
      _ = x.2.1 * (z.2.1 ^ 2 + z.1 ^ 2) := by
            rw [hunit]
            ring
      _ = x.2.1 * horizontalRadius z ^ 2 := by
            rw [hρsq']
  · field_simp [hρ]
    ring_nf
    calc
      horizontalRadius z * z.2.2 ^ 2 * x.2.2 + horizontalRadius z ^ 3 * x.2.2
          = horizontalRadius z * x.2.2 * (z.2.2 ^ 2 + horizontalRadius z ^ 2) := by
              ring
      _ = x.2.2 * horizontalRadius z := by
            rw [hunit]
            ring
      _ = horizontalRadius z * x.2.2 := by
            ring

lemma targetFrameReparamSwap_targetFrameCoordsSwap
    {z x : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    targetFrameReparamSwap z (targetFrameCoordsSwap z x) = x := by
  have hρsq := horizontalRadius_sq z
  have hunit : z.2.2 ^ 2 + horizontalRadius z ^ 2 = 1 := by
    nlinarith [hz, hρsq]
  ext <;> unfold targetFrameReparamSwap targetFrameCoordsSwap coordLinearCombo coordDot
    targetBridgeCoord targetPoleCoord
  · field_simp [hρ]
    ring_nf
    calc
      -(z.1 * x.2.1 * z.2.1) + z.1 * x.2.1 * z.2.1 * z.2.2 ^ 2 +
            z.1 * x.2.1 * z.2.1 * horizontalRadius z ^ 2 +
            z.1 ^ 2 * x.1 * z.2.2 ^ 2 +
            z.1 ^ 2 * x.1 * horizontalRadius z ^ 2 +
            x.1 * z.2.1 ^ 2
          =
            z.1 * x.2.1 * z.2.1 * (z.2.2 ^ 2 + horizontalRadius z ^ 2 - 1) +
              x.1 * (z.1 ^ 2 * (z.2.2 ^ 2 + horizontalRadius z ^ 2) + z.2.1 ^ 2) := by
                ring
      _ = x.1 * (z.1 ^ 2 + z.2.1 ^ 2) := by
            rw [hunit]
            ring
      _ = x.1 * horizontalRadius z ^ 2 := by
            rw [← hρsq]
  · field_simp [hρ]
    ring_nf
    have hρsq' : z.2.1 ^ 2 + z.1 ^ 2 = horizontalRadius z ^ 2 := by
      simpa [add_comm] using hρsq.symm
    calc
      -(z.2.1 * x.1 * z.1) + z.2.1 * x.1 * z.1 * z.2.2 ^ 2 +
            z.2.1 * x.1 * z.1 * horizontalRadius z ^ 2 +
            z.2.1 ^ 2 * x.2.1 * z.2.2 ^ 2 +
            z.2.1 ^ 2 * x.2.1 * horizontalRadius z ^ 2 +
            z.1 ^ 2 * x.2.1
          =
            z.2.1 * x.1 * z.1 * (z.2.2 ^ 2 + horizontalRadius z ^ 2 - 1) +
              x.2.1 * (z.2.1 ^ 2 * (z.2.2 ^ 2 + horizontalRadius z ^ 2) + z.1 ^ 2) := by
                ring
      _ = x.2.1 * (z.2.1 ^ 2 + z.1 ^ 2) := by
            rw [hunit]
            ring
      _ = x.2.1 * horizontalRadius z ^ 2 := by
            rw [hρsq']
  · field_simp [hρ]
    ring_nf
    calc
      z.2.2 ^ 2 * x.2.2 * horizontalRadius z + x.2.2 * horizontalRadius z ^ 3
          = x.2.2 * horizontalRadius z * (z.2.2 ^ 2 + horizontalRadius z ^ 2) := by
              ring
      _ = x.2.2 * horizontalRadius z := by
            rw [hunit]
            ring

lemma targetPole_oscillation_bound_of_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hosc :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < ε →
        dist (coordPoint u v p y) p < ε →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤ a)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
        x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x₁) (coordPoint u v p (targetPoleCoord z)) < δ →
        dist (coordPoint u v p x₂) (coordPoint u v p (targetPoleCoord z)) < δ →
        |frame_quadratic μ (coordPoint u v p x₁) -
            frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * a := by
  let q := coordPoint u v p (targetPoleCoord z)
  let w := coordPoint u v p (horizontalUnitCoord z)
  have hqNorm : ‖q‖ = 1 := by
    dsimp [q]
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hqw : inner (𝕜 := ℂ) q w = 0 := by
    dsimp [q, w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    simp [coordDot_targetPole_horizontalUnitCoord hρ]
  have hqp : inner (𝕜 := ℂ) q p = 0 := by
    have hqp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_targetPoleCoord, coordDot_comm]
    simpa [q, coordPoint_poleCoord u v p] using hqp'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  have hoscEquator :
      ∀ {y₁ y₂ : ℝ × ℝ × ℝ},
        y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 →
        y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 →
        dist (coordPoint q w p y₁) p < ε →
        dist (coordPoint q w p y₂) p < ε →
        |frame_quadratic μ (coordPoint q w p y₁) -
            frame_quadratic μ (coordPoint q w p y₂)| ≤ a := by
    intro y₁ y₂ hy₁ hy₂ hdist₁ hdist₂
    have hrepr₁ :
        coordPoint q w p y₁ = coordPoint u v p (equatorFrameReparam z y₁) := by
      simpa [q, w] using
        coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₁)
    have hrepr₂ :
        coordPoint q w p y₂ = coordPoint u v p (equatorFrameReparam z y₂) := by
      simpa [q, w] using
        coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₂)
    calc
      |frame_quadratic μ (coordPoint q w p y₁) -
          frame_quadratic μ (coordPoint q w p y₂)|
          =
        |frame_quadratic μ (coordPoint u v p (equatorFrameReparam z y₁)) -
            frame_quadratic μ (coordPoint u v p (equatorFrameReparam z y₂))| := by
              rw [hrepr₁, hrepr₂]
      _ ≤ a := by
            apply hosc
            · exact equatorFrameReparam_sq_sum hy₁ hρ
            · exact equatorFrameReparam_sq_sum hy₂ hρ
            · simpa [hrepr₁] using hdist₁
            · simpa [hrepr₂] using hdist₂
  rcases ambient_oscillation_bound_of_cap_coords
      (hdim := hdim) (μ := μ) (u := q) (v := w) (p := p)
      hqNorm hwNorm hp hqw hqp hwp ha hε hoscEquator with
    ⟨α, δ, hα0, hαpi, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdist₁ hdist₂
  let y₁ := equatorFrameCoords z x₁
  let y₂ := equatorFrameCoords z x₂
  have hy₁ :
      y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 := by
    exact equatorFrameCoords_sq_sum (z := z) (x := x₁) hx₁ hρ
  have hy₂ :
      y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 := by
    exact equatorFrameCoords_sq_sum (z := z) (x := x₂) hx₂ hρ
  have hrepr₁ : coordPoint q w p y₁ = coordPoint u v p x₁ := by
    dsimp [y₁]
    rw [coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := equatorFrameCoords z x₁)]
    rw [equatorFrameReparam_equatorFrameCoords (z := z) (x := x₁) hρ]
  have hrepr₂ : coordPoint q w p y₂ = coordPoint u v p x₂ := by
    dsimp [y₂]
    rw [coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := equatorFrameCoords z x₂)]
    rw [equatorFrameReparam_equatorFrameCoords (z := z) (x := x₂) hρ]
  have hyDist₁H : dist (coordPoint q w p y₁) q < δ := by
    simpa [q, hrepr₁] using hdist₁
  have hyDist₂H : dist (coordPoint q w p y₂) q < δ := by
    simpa [q, hrepr₂] using hdist₂
  have hyDist₁ : dist y₁ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hwNorm hp hqw hqp hwp y₁) hyDist₁H
  have hyDist₂ : dist y₂ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hwNorm hp hqw hqp hwp y₂) hyDist₂H
  calc
    |frame_quadratic μ (coordPoint u v p x₁) -
        frame_quadratic μ (coordPoint u v p x₂)|
        =
      |frame_quadratic μ (coordPoint q w p y₁) -
          frame_quadratic μ (coordPoint q w p y₂)| := by
            rw [hrepr₁, hrepr₂]
    _ ≤ 2 * a := hlocal hy₁ hy₂ hyDist₁ hyDist₂

lemma targetPole_oscillation_bound_of_cap_uniform
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) p < ε →
          dist (coordPoint u v p y) p < ε →
          |frame_quadratic μ (coordPoint u v p x) -
              frame_quadratic μ (coordPoint u v p y)| ≤ a) →
        ∀ {z x₁ x₂ : ℝ × ℝ × ℝ},
          z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
          horizontalRadius z ≠ 0 →
          x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
          x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x₁) (coordPoint u v p (targetPoleCoord z)) < δ →
          dist (coordPoint u v p x₂) (coordPoint u v p (targetPoleCoord z)) < δ →
          |frame_quadratic μ (coordPoint u v p x₁) -
              frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * a := by
  rcases ambient_oscillation_bound_of_cap_coords_uniform
      (hdim := hdim) (μ := μ) ha hε with
    ⟨α, δ, hα0, hαpi, hδ, hambient⟩
  refine ⟨δ, hδ, ?_⟩
  intro u v p hu hv hp huv hup hvp hosc z x₁ x₂ hz hρ hx₁ hx₂ hdist₁ hdist₂
  let q := coordPoint u v p (targetPoleCoord z)
  let w := coordPoint u v p (horizontalUnitCoord z)
  have hqNorm : ‖q‖ = 1 := by
    dsimp [q]
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hqw : inner (𝕜 := ℂ) q w = 0 := by
    dsimp [q, w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    simp [coordDot_targetPole_horizontalUnitCoord hρ]
  have hqp : inner (𝕜 := ℂ) q p = 0 := by
    have hqp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_targetPoleCoord, coordDot_comm]
    simpa [q, coordPoint_poleCoord u v p] using hqp'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  have hoscEquator :
      ∀ {y₁ y₂ : ℝ × ℝ × ℝ},
        y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 →
        y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 →
        dist (coordPoint q w p y₁) p < ε →
        dist (coordPoint q w p y₂) p < ε →
        |frame_quadratic μ (coordPoint q w p y₁) -
            frame_quadratic μ (coordPoint q w p y₂)| ≤ a := by
    intro y₁ y₂ hy₁ hy₂ hdisty₁ hdisty₂
    have hrepr₁ :
        coordPoint q w p y₁ = coordPoint u v p (equatorFrameReparam z y₁) := by
      simpa [q, w] using
        coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₁)
    have hrepr₂ :
        coordPoint q w p y₂ = coordPoint u v p (equatorFrameReparam z y₂) := by
      simpa [q, w] using
        coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₂)
    calc
      |frame_quadratic μ (coordPoint q w p y₁) -
          frame_quadratic μ (coordPoint q w p y₂)|
          =
        |frame_quadratic μ (coordPoint u v p (equatorFrameReparam z y₁)) -
            frame_quadratic μ (coordPoint u v p (equatorFrameReparam z y₂))| := by
              rw [hrepr₁, hrepr₂]
      _ ≤ a := by
            apply hosc
            · exact equatorFrameReparam_sq_sum hy₁ hρ
            · exact equatorFrameReparam_sq_sum hy₂ hρ
            · simpa [hrepr₁] using hdisty₁
            · simpa [hrepr₂] using hdisty₂
  let y₁ := equatorFrameCoords z x₁
  let y₂ := equatorFrameCoords z x₂
  have hy₁ :
      y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 := by
    exact equatorFrameCoords_sq_sum (z := z) (x := x₁) hx₁ hρ
  have hy₂ :
      y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 := by
    exact equatorFrameCoords_sq_sum (z := z) (x := x₂) hx₂ hρ
  have hrepr₁ : coordPoint q w p y₁ = coordPoint u v p x₁ := by
    dsimp [y₁]
    rw [coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := equatorFrameCoords z x₁)]
    rw [equatorFrameReparam_equatorFrameCoords (z := z) (x := x₁) hρ]
  have hrepr₂ : coordPoint q w p y₂ = coordPoint u v p x₂ := by
    dsimp [y₂]
    rw [coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := equatorFrameCoords z x₂)]
    rw [equatorFrameReparam_equatorFrameCoords (z := z) (x := x₂) hρ]
  have hyDist₁H : dist (coordPoint q w p y₁) q < δ := by
    simpa [q, hrepr₁] using hdist₁
  have hyDist₂H : dist (coordPoint q w p y₂) q < δ := by
    simpa [q, hrepr₂] using hdist₂
  have hyDist₁ : dist y₁ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hwNorm hp hqw hqp hwp y₁) hyDist₁H
  have hyDist₂ : dist y₂ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hwNorm hp hqw hqp hwp y₂) hyDist₂H
  calc
    |frame_quadratic μ (coordPoint u v p x₁) -
        frame_quadratic μ (coordPoint u v p x₂)|
        =
      |frame_quadratic μ (coordPoint q w p y₁) -
          frame_quadratic μ (coordPoint q w p y₂)| := by
            rw [hrepr₁, hrepr₂]
    _ ≤ 2 * a := hambient hqNorm hwNorm hp hqw hqp hwp hoscEquator
      hy₁ hy₂ hyDist₁ hyDist₂

lemma targetPole_oscillation_bound_of_cap_uniform_any
    (hdim : 3 ≤ Module.finrank ℂ H)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (ν : FrameFunction H) {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) p < ε →
          dist (coordPoint u v p y) p < ε →
          |frame_quadratic ν (coordPoint u v p x) -
              frame_quadratic ν (coordPoint u v p y)| ≤ a) →
        ∀ {z x₁ x₂ : ℝ × ℝ × ℝ},
          z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
          horizontalRadius z ≠ 0 →
          x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
          x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x₁) (coordPoint u v p (targetPoleCoord z)) < δ →
          dist (coordPoint u v p x₂) (coordPoint u v p (targetPoleCoord z)) < δ →
          |frame_quadratic ν (coordPoint u v p x₁) -
              frame_quadratic ν (coordPoint u v p x₂)| ≤ 2 * a := by
  rcases ambient_oscillation_bound_of_cap_coords_uniform_any
      (H := H) hdim ha hε with
    ⟨α, δ, hα0, hαpi, hδ, hambient⟩
  refine ⟨δ, hδ, ?_⟩
  intro ν u v p hu hv hp huv hup hvp hosc z x₁ x₂ hz hρ hx₁ hx₂ hdist₁ hdist₂
  let q := coordPoint u v p (targetPoleCoord z)
  let w := coordPoint u v p (horizontalUnitCoord z)
  have hqNorm : ‖q‖ = 1 := by
    dsimp [q]
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hqw : inner (𝕜 := ℂ) q w = 0 := by
    dsimp [q, w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    simp [coordDot_targetPole_horizontalUnitCoord hρ]
  have hqp : inner (𝕜 := ℂ) q p = 0 := by
    have hqp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_targetPoleCoord, coordDot_comm]
    simpa [q, coordPoint_poleCoord u v p] using hqp'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  have hoscEquator :
      ∀ {y₁ y₂ : ℝ × ℝ × ℝ},
        y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 →
        y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 →
        dist (coordPoint q w p y₁) p < ε →
        dist (coordPoint q w p y₂) p < ε →
        |frame_quadratic ν (coordPoint q w p y₁) -
            frame_quadratic ν (coordPoint q w p y₂)| ≤ a := by
    intro y₁ y₂ hy₁ hy₂ hdisty₁ hdisty₂
    have hrepr₁ :
        coordPoint q w p y₁ = coordPoint u v p (equatorFrameReparam z y₁) := by
      simpa [q, w] using
        coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₁)
    have hrepr₂ :
        coordPoint q w p y₂ = coordPoint u v p (equatorFrameReparam z y₂) := by
      simpa [q, w] using
        coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₂)
    calc
      |frame_quadratic ν (coordPoint q w p y₁) -
          frame_quadratic ν (coordPoint q w p y₂)|
          =
        |frame_quadratic ν (coordPoint u v p (equatorFrameReparam z y₁)) -
            frame_quadratic ν (coordPoint u v p (equatorFrameReparam z y₂))| := by
              rw [hrepr₁, hrepr₂]
      _ ≤ a := by
            apply hosc
            · exact equatorFrameReparam_sq_sum hy₁ hρ
            · exact equatorFrameReparam_sq_sum hy₂ hρ
            · simpa [hrepr₁] using hdisty₁
            · simpa [hrepr₂] using hdisty₂
  let y₁ := equatorFrameCoords z x₁
  let y₂ := equatorFrameCoords z x₂
  have hy₁ :
      y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 := by
    exact equatorFrameCoords_sq_sum (z := z) (x := x₁) hx₁ hρ
  have hy₂ :
      y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 := by
    exact equatorFrameCoords_sq_sum (z := z) (x := x₂) hx₂ hρ
  have hrepr₁ : coordPoint q w p y₁ = coordPoint u v p x₁ := by
    dsimp [y₁]
    rw [coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := equatorFrameCoords z x₁)]
    rw [equatorFrameReparam_equatorFrameCoords (z := z) (x := x₁) hρ]
  have hrepr₂ : coordPoint q w p y₂ = coordPoint u v p x₂ := by
    dsimp [y₂]
    rw [coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := equatorFrameCoords z x₂)]
    rw [equatorFrameReparam_equatorFrameCoords (z := z) (x := x₂) hρ]
  have hyDist₁H : dist (coordPoint q w p y₁) q < δ := by
    simpa [q, hrepr₁] using hdist₁
  have hyDist₂H : dist (coordPoint q w p y₂) q < δ := by
    simpa [q, hrepr₂] using hdist₂
  have hyDist₁ : dist y₁ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hwNorm hp hqw hqp hwp y₁) hyDist₁H
  have hyDist₂ : dist y₂ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hwNorm hp hqw hqp hwp y₂) hyDist₂H
  calc
    |frame_quadratic ν (coordPoint u v p x₁) -
        frame_quadratic ν (coordPoint u v p x₂)|
        =
      |frame_quadratic ν (coordPoint q w p y₁) -
          frame_quadratic ν (coordPoint q w p y₂)| := by
            rw [hrepr₁, hrepr₂]
    _ ≤ 2 * a := hambient ν hqNorm hwNorm hp hqw hqp hwp hoscEquator
      hy₁ hy₂ hyDist₁ hyDist₂

lemma targetFrameCoords_sq_sum
    {u v p : H} {z x : ℝ × ℝ × ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    (targetFrameCoords z x).1 ^ 2 +
        (targetFrameCoords z x).2.1 ^ 2 +
        (targetFrameCoords z x).2.2 ^ 2 = 1 := by
  have hzNorm : ‖coordPoint u v p z‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hz
  have hbNorm : ‖coordPoint u v p (targetBridgeCoord z)‖ = 1 := by
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hz hρ
  have htNorm : ‖coordPoint u v p (targetPoleCoord z)‖ = 1 := by
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hzb : inner (𝕜 := ℂ)
      (coordPoint u v p z) (coordPoint u v p (targetBridgeCoord z)) = 0 := by
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have hzt : inner (𝕜 := ℂ)
      (coordPoint u v p z) (coordPoint u v p (targetPoleCoord z)) = 0 := by
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρ
  have hbt : inner (𝕜 := ℂ)
      (coordPoint u v p (targetBridgeCoord z))
      (coordPoint u v p (targetPoleCoord z)) = 0 := by
    have htmp := inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
    simpa [inner_eq_zero_symm] using htmp
  have hreprEq :
      coordPoint (coordPoint u v p z)
          (coordPoint u v p (targetBridgeCoord z))
          (coordPoint u v p (targetPoleCoord z))
          (targetFrameCoords z x) =
        coordPoint u v p x := by
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := targetFrameCoords z x)]
    rw [targetFrameReparam_targetFrameCoords (z := z) (x := x) hz hρ]
  have hnorm :
      ‖coordPoint (coordPoint u v p z)
          (coordPoint u v p (targetBridgeCoord z))
          (coordPoint u v p (targetPoleCoord z))
          (targetFrameCoords z x)‖ = 1 := by
    rw [hreprEq]
    exact coordPoint_norm hu hv hp huv hup hvp hx
  have hnorm' :
      ‖realFramePoint (coordPoint u v p z)
          (coordPoint u v p (targetBridgeCoord z))
          (coordPoint u v p (targetPoleCoord z))
          (targetFrameCoords z x).1
          (targetFrameCoords z x).2.1
          (targetFrameCoords z x).2.2‖ = 1 := by
    simpa [coordPoint_eq_realFramePoint] using hnorm
  have hsq :=
    norm_sq_realFramePoint hzNorm hbNorm htNorm hzb hzt hbt
      (targetFrameCoords z x).1 (targetFrameCoords z x).2.1 (targetFrameCoords z x).2.2
  rw [hnorm'] at hsq
  nlinarith

lemma target_oscillation_bound_of_targetPole_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hosc :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) (coordPoint u v p (targetPoleCoord z)) < ε →
        dist (coordPoint u v p y) (coordPoint u v p (targetPoleCoord z)) < ε →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
        x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x₁) (coordPoint u v p z) < δ →
        dist (coordPoint u v p x₂) (coordPoint u v p z) < δ →
        |frame_quadratic μ (coordPoint u v p x₁) -
            frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * a := by
  let q := coordPoint u v p z
  let b := coordPoint u v p (targetBridgeCoord z)
  let t := coordPoint u v p (targetPoleCoord z)
  have hqNorm : ‖q‖ = 1 := by
    dsimp [q]
    exact coordPoint_norm hu hv hp huv hup hvp hz
  have hbNorm : ‖b‖ = 1 := by
    dsimp [b]
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hz hρ
  have htNorm : ‖t‖ = 1 := by
    dsimp [t]
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hqb : inner (𝕜 := ℂ) q b = 0 := by
    dsimp [q, b]
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have hqt : inner (𝕜 := ℂ) q t = 0 := by
    dsimp [q, t]
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρ
  have hbt : inner (𝕜 := ℂ) b t = 0 := by
    dsimp [b, t]
    have htmp := inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
    simpa [inner_eq_zero_symm] using htmp
  have hoscTarget :
      ∀ {y₁ y₂ : ℝ × ℝ × ℝ},
        y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 →
        y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 →
        dist (coordPoint q b t y₁) t < ε →
        dist (coordPoint q b t y₂) t < ε →
        |frame_quadratic μ (coordPoint q b t y₁) -
            frame_quadratic μ (coordPoint q b t y₂)| ≤ a := by
    intro y₁ y₂ hy₁ hy₂ hdist₁ hdist₂
    have hrepr₁ :
        coordPoint q b t y₁ = coordPoint u v p (targetFrameReparam z y₁) := by
      simpa [q, b, t] using
        coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₁)
    have hrepr₂ :
        coordPoint q b t y₂ = coordPoint u v p (targetFrameReparam z y₂) := by
      simpa [q, b, t] using
        coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₂)
    calc
      |frame_quadratic μ (coordPoint q b t y₁) -
          frame_quadratic μ (coordPoint q b t y₂)|
          =
        |frame_quadratic μ (coordPoint u v p (targetFrameReparam z y₁)) -
            frame_quadratic μ (coordPoint u v p (targetFrameReparam z y₂))| := by
              rw [hrepr₁, hrepr₂]
      _ ≤ a := by
            apply hosc
            · exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hz hy₁ hρ
            · exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hz hy₂ hρ
            · simpa [t, hrepr₁] using hdist₁
            · simpa [t, hrepr₂] using hdist₂
  rcases ambient_oscillation_bound_of_cap_coords
      (hdim := hdim) (μ := μ) (u := q) (v := b) (p := t)
      hqNorm hbNorm htNorm hqb hqt hbt ha hε hoscTarget with
    ⟨α, δ, hα0, hαpi, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdist₁ hdist₂
  let y₁ := targetFrameCoords z x₁
  let y₂ := targetFrameCoords z x₂
  have hy₁ :
      y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 := by
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hz hx₁ hρ
  have hy₂ :
      y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 := by
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hz hx₂ hρ
  have hrepr₁ : coordPoint q b t y₁ = coordPoint u v p x₁ := by
    dsimp [y₁]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := targetFrameCoords z x₁)]
    rw [targetFrameReparam_targetFrameCoords (z := z) (x := x₁) hz hρ]
  have hrepr₂ : coordPoint q b t y₂ = coordPoint u v p x₂ := by
    dsimp [y₂]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := targetFrameCoords z x₂)]
    rw [targetFrameReparam_targetFrameCoords (z := z) (x := x₂) hz hρ]
  have hyDist₁H : dist (coordPoint q b t y₁) q < δ := by
    simpa [q, hrepr₁] using hdist₁
  have hyDist₂H : dist (coordPoint q b t y₂) q < δ := by
    simpa [q, hrepr₂] using hdist₂
  have hyDist₁ : dist y₁ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hbNorm htNorm hqb hqt hbt y₁) hyDist₁H
  have hyDist₂ : dist y₂ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hbNorm htNorm hqb hqt hbt y₂) hyDist₂H
  calc
    |frame_quadratic μ (coordPoint u v p x₁) -
        frame_quadratic μ (coordPoint u v p x₂)|
        =
      |frame_quadratic μ (coordPoint q b t y₁) -
          frame_quadratic μ (coordPoint q b t y₂)| := by
            rw [hrepr₁, hrepr₂]
    _ ≤ 2 * a := hlocal hy₁ hy₂ hyDist₁ hyDist₂

lemma target_oscillation_bound_of_targetPole_cap_uniform
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        ∀ {z : ℝ × ℝ × ℝ},
          z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
          horizontalRadius z ≠ 0 →
          (∀ {x y : ℝ × ℝ × ℝ},
            x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
            y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
            dist (coordPoint u v p x) (coordPoint u v p (targetPoleCoord z)) < ε →
            dist (coordPoint u v p y) (coordPoint u v p (targetPoleCoord z)) < ε →
            |frame_quadratic μ (coordPoint u v p x) -
                frame_quadratic μ (coordPoint u v p y)| ≤ a) →
          ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
            x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
            x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
            dist (coordPoint u v p x₁) (coordPoint u v p z) < δ →
            dist (coordPoint u v p x₂) (coordPoint u v p z) < δ →
            |frame_quadratic μ (coordPoint u v p x₁) -
                frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * a := by
  rcases ambient_oscillation_bound_of_cap_coords_uniform
      (hdim := hdim) (μ := μ) ha hε with
    ⟨α, δ, hα0, hαpi, hδ, hambient⟩
  refine ⟨δ, hδ, ?_⟩
  intro u v p hu hv hp huv hup hvp z hz hρ hosc x₁ x₂ hx₁ hx₂ hdist₁ hdist₂
  let q := coordPoint u v p z
  let b := coordPoint u v p (targetBridgeCoord z)
  let t := coordPoint u v p (targetPoleCoord z)
  have hqNorm : ‖q‖ = 1 := by
    dsimp [q]
    exact coordPoint_norm hu hv hp huv hup hvp hz
  have hbNorm : ‖b‖ = 1 := by
    dsimp [b]
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hz hρ
  have htNorm : ‖t‖ = 1 := by
    dsimp [t]
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hqb : inner (𝕜 := ℂ) q b = 0 := by
    dsimp [q, b]
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have hqt : inner (𝕜 := ℂ) q t = 0 := by
    dsimp [q, t]
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρ
  have hbt : inner (𝕜 := ℂ) b t = 0 := by
    dsimp [b, t]
    have htmp := inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
    simpa [inner_eq_zero_symm] using htmp
  have hoscTarget :
      ∀ {y₁ y₂ : ℝ × ℝ × ℝ},
        y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 →
        y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 →
        dist (coordPoint q b t y₁) t < ε →
        dist (coordPoint q b t y₂) t < ε →
        |frame_quadratic μ (coordPoint q b t y₁) -
            frame_quadratic μ (coordPoint q b t y₂)| ≤ a := by
    intro y₁ y₂ hy₁ hy₂ hdisty₁ hdisty₂
    have hrepr₁ :
        coordPoint q b t y₁ = coordPoint u v p (targetFrameReparam z y₁) := by
      simpa [q, b, t] using
        coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₁)
    have hrepr₂ :
        coordPoint q b t y₂ = coordPoint u v p (targetFrameReparam z y₂) := by
      simpa [q, b, t] using
        coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₂)
    calc
      |frame_quadratic μ (coordPoint q b t y₁) -
          frame_quadratic μ (coordPoint q b t y₂)|
          =
        |frame_quadratic μ (coordPoint u v p (targetFrameReparam z y₁)) -
            frame_quadratic μ (coordPoint u v p (targetFrameReparam z y₂))| := by
              rw [hrepr₁, hrepr₂]
      _ ≤ a := by
            apply hosc
            · exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hz hy₁ hρ
            · exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hz hy₂ hρ
            · simpa [t, hrepr₁] using hdisty₁
            · simpa [t, hrepr₂] using hdisty₂
  let y₁ := targetFrameCoords z x₁
  let y₂ := targetFrameCoords z x₂
  have hy₁ :
      y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 := by
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hz hx₁ hρ
  have hy₂ :
      y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 := by
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hz hx₂ hρ
  have hrepr₁ : coordPoint q b t y₁ = coordPoint u v p x₁ := by
    dsimp [y₁]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := targetFrameCoords z x₁)]
    rw [targetFrameReparam_targetFrameCoords (z := z) (x := x₁) hz hρ]
  have hrepr₂ : coordPoint q b t y₂ = coordPoint u v p x₂ := by
    dsimp [y₂]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := targetFrameCoords z x₂)]
    rw [targetFrameReparam_targetFrameCoords (z := z) (x := x₂) hz hρ]
  have hyDist₁H : dist (coordPoint q b t y₁) q < δ := by
    simpa [q, hrepr₁] using hdist₁
  have hyDist₂H : dist (coordPoint q b t y₂) q < δ := by
    simpa [q, hrepr₂] using hdist₂
  have hyDist₁ : dist y₁ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hbNorm htNorm hqb hqt hbt y₁) hyDist₁H
  have hyDist₂ : dist y₂ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hbNorm htNorm hqb hqt hbt y₂) hyDist₂H
  calc
    |frame_quadratic μ (coordPoint u v p x₁) -
        frame_quadratic μ (coordPoint u v p x₂)|
        =
      |frame_quadratic μ (coordPoint q b t y₁) -
          frame_quadratic μ (coordPoint q b t y₂)| := by
            rw [hrepr₁, hrepr₂]
    _ ≤ 2 * a := hambient hqNorm hbNorm htNorm hqb hqt hbt hoscTarget
      hy₁ hy₂ hyDist₁ hyDist₂

lemma nonpolar_oscillation_bound_of_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hosc :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < ε →
        dist (coordPoint u v p y) p < ε →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤ a)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
        x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x₁) (coordPoint u v p z) < δ →
        dist (coordPoint u v p x₂) (coordPoint u v p z) < δ →
        |frame_quadratic μ (coordPoint u v p x₁) -
            frame_quadratic μ (coordPoint u v p x₂)| ≤ 4 * a := by
  rcases targetPole_oscillation_bound_of_cap
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp ha hε hosc hz hρ with
    ⟨ε₁, hε₁, hpole⟩
  have h2a : 0 ≤ 2 * a := by nlinarith
  rcases target_oscillation_bound_of_targetPole_cap
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      (a := 2 * a) (ε := ε₁) h2a hε₁ hz hρ
      (hosc := by
        intro x y hx hy hdx hdy
        exact hpole hx hy hdx hdy) with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdx hdy
  have hbound := hlocal hx₁ hx₂ hdx hdy
  have hfour : 2 * (2 * a) = 4 * a := by ring
  simpa [hfour] using hbound

lemma target_oscillation_bound_of_targetPole_cap_uniform_any
    (hdim : 3 ≤ Module.finrank ℂ H)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (ν : FrameFunction H) {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        ∀ {z : ℝ × ℝ × ℝ},
          z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
          horizontalRadius z ≠ 0 →
          (∀ {x y : ℝ × ℝ × ℝ},
            x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
            y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
            dist (coordPoint u v p x) (coordPoint u v p (targetPoleCoord z)) < ε →
            dist (coordPoint u v p y) (coordPoint u v p (targetPoleCoord z)) < ε →
            |frame_quadratic ν (coordPoint u v p x) -
                frame_quadratic ν (coordPoint u v p y)| ≤ a) →
          ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
            x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
            x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
            dist (coordPoint u v p x₁) (coordPoint u v p z) < δ →
            dist (coordPoint u v p x₂) (coordPoint u v p z) < δ →
            |frame_quadratic ν (coordPoint u v p x₁) -
                frame_quadratic ν (coordPoint u v p x₂)| ≤ 2 * a := by
  rcases ambient_oscillation_bound_of_cap_coords_uniform_any
      (H := H) hdim ha hε with
    ⟨α, δ, hα0, hαpi, hδ, hambient⟩
  refine ⟨δ, hδ, ?_⟩
  intro ν u v p hu hv hp huv hup hvp z hz hρ hosc x₁ x₂ hx₁ hx₂ hdist₁ hdist₂
  let q := coordPoint u v p z
  let b := coordPoint u v p (targetBridgeCoord z)
  let t := coordPoint u v p (targetPoleCoord z)
  have hqNorm : ‖q‖ = 1 := by
    dsimp [q]
    exact coordPoint_norm hu hv hp huv hup hvp hz
  have hbNorm : ‖b‖ = 1 := by
    dsimp [b]
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hz hρ
  have htNorm : ‖t‖ = 1 := by
    dsimp [t]
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hqb : inner (𝕜 := ℂ) q b = 0 := by
    dsimp [q, b]
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have hqt : inner (𝕜 := ℂ) q t = 0 := by
    dsimp [q, t]
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρ
  have hbt : inner (𝕜 := ℂ) b t = 0 := by
    dsimp [b, t]
    have htmp := inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
    simpa [inner_eq_zero_symm] using htmp
  have hoscTarget :
      ∀ {y₁ y₂ : ℝ × ℝ × ℝ},
        y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 →
        y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 →
        dist (coordPoint q b t y₁) t < ε →
        dist (coordPoint q b t y₂) t < ε →
        |frame_quadratic ν (coordPoint q b t y₁) -
            frame_quadratic ν (coordPoint q b t y₂)| ≤ a := by
    intro y₁ y₂ hy₁ hy₂ hdisty₁ hdisty₂
    have hrepr₁ :
        coordPoint q b t y₁ = coordPoint u v p (targetFrameReparam z y₁) := by
      simpa [q, b, t] using
        coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₁)
    have hrepr₂ :
        coordPoint q b t y₂ = coordPoint u v p (targetFrameReparam z y₂) := by
      simpa [q, b, t] using
        coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y₂)
    calc
      |frame_quadratic ν (coordPoint q b t y₁) -
          frame_quadratic ν (coordPoint q b t y₂)|
          =
        |frame_quadratic ν (coordPoint u v p (targetFrameReparam z y₁)) -
            frame_quadratic ν (coordPoint u v p (targetFrameReparam z y₂))| := by
              rw [hrepr₁, hrepr₂]
      _ ≤ a := by
            apply hosc
            · exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hz hy₁ hρ
            · exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hz hy₂ hρ
            · simpa [t, hrepr₁] using hdisty₁
            · simpa [t, hrepr₂] using hdisty₂
  let y₁ := targetFrameCoords z x₁
  let y₂ := targetFrameCoords z x₂
  have hy₁ :
      y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 := by
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hz hx₁ hρ
  have hy₂ :
      y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 := by
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hz hx₂ hρ
  have hrepr₁ : coordPoint q b t y₁ = coordPoint u v p x₁ := by
    dsimp [y₁]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := targetFrameCoords z x₁)]
    rw [targetFrameReparam_targetFrameCoords (z := z) (x := x₁) hz hρ]
  have hrepr₂ : coordPoint q b t y₂ = coordPoint u v p x₂ := by
    dsimp [y₂]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := targetFrameCoords z x₂)]
    rw [targetFrameReparam_targetFrameCoords (z := z) (x := x₂) hz hρ]
  have hyDist₁H : dist (coordPoint q b t y₁) q < δ := by
    simpa [q, hrepr₁] using hdist₁
  have hyDist₂H : dist (coordPoint q b t y₂) q < δ := by
    simpa [q, hrepr₂] using hdist₂
  have hyDist₁ : dist y₁ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hbNorm htNorm hqb hqt hbt y₁) hyDist₁H
  have hyDist₂ : dist y₂ coordBase < δ := by
    exact lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hqNorm hbNorm htNorm hqb hqt hbt y₂) hyDist₂H
  calc
    |frame_quadratic ν (coordPoint u v p x₁) -
        frame_quadratic ν (coordPoint u v p x₂)|
        =
      |frame_quadratic ν (coordPoint q b t y₁) -
          frame_quadratic ν (coordPoint q b t y₂)| := by
            rw [hrepr₁, hrepr₂]
    _ ≤ 2 * a := hambient ν hqNorm hbNorm htNorm hqb hqt hbt hoscTarget
      hy₁ hy₂ hyDist₁ hyDist₂

lemma nonpolar_oscillation_bound_of_cap_uniform
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) p < ε →
          dist (coordPoint u v p y) p < ε →
          |frame_quadratic μ (coordPoint u v p x) -
              frame_quadratic μ (coordPoint u v p y)| ≤ a) →
        ∀ {z x₁ x₂ : ℝ × ℝ × ℝ},
          z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
          horizontalRadius z ≠ 0 →
          x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
          x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x₁) (coordPoint u v p z) < δ →
          dist (coordPoint u v p x₂) (coordPoint u v p z) < δ →
          |frame_quadratic μ (coordPoint u v p x₁) -
              frame_quadratic μ (coordPoint u v p x₂)| ≤ 4 * a := by
  rcases targetPole_oscillation_bound_of_cap_uniform
      (hdim := hdim) (μ := μ) ha hε with
    ⟨ε₁, hε₁, hpole⟩
  have h2a : 0 ≤ 2 * a := by nlinarith
  rcases target_oscillation_bound_of_targetPole_cap_uniform
      (hdim := hdim) (μ := μ) (a := 2 * a) (ε := ε₁) h2a hε₁ with
    ⟨δ, hδ, htarget⟩
  refine ⟨δ, hδ, ?_⟩
  intro u v p hu hv hp huv hup hvp hosc z x₁ x₂ hz hρ hx₁ hx₂ hdx hdy
  have hpole' :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) (coordPoint u v p (targetPoleCoord z)) < ε₁ →
        dist (coordPoint u v p y) (coordPoint u v p (targetPoleCoord z)) < ε₁ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤ 2 * a := by
    exact hpole hu hv hp huv hup hvp hosc hz hρ
  have hbound :=
    htarget hu hv hp huv hup hvp hz hρ hpole' hx₁ hx₂ hdx hdy
  have hfour : 2 * (2 * a) = 4 * a := by ring
  simpa [hfour] using hbound

lemma nonpolar_oscillation_bound_of_cap_uniform_any
    (hdim : 3 ≤ Module.finrank ℂ H)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (ν : FrameFunction H) {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) p < ε →
          dist (coordPoint u v p y) p < ε →
          |frame_quadratic ν (coordPoint u v p x) -
              frame_quadratic ν (coordPoint u v p y)| ≤ a) →
        ∀ {z x₁ x₂ : ℝ × ℝ × ℝ},
          z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
          horizontalRadius z ≠ 0 →
          x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
          x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x₁) (coordPoint u v p z) < δ →
          dist (coordPoint u v p x₂) (coordPoint u v p z) < δ →
          |frame_quadratic ν (coordPoint u v p x₁) -
              frame_quadratic ν (coordPoint u v p x₂)| ≤ 4 * a := by
  rcases targetPole_oscillation_bound_of_cap_uniform_any
      (H := H) hdim ha hε with
    ⟨ε₁, hε₁, hpole⟩
  have h2a : 0 ≤ 2 * a := by nlinarith
  rcases target_oscillation_bound_of_targetPole_cap_uniform_any
      (H := H) hdim (a := 2 * a) (ε := ε₁) h2a hε₁ with
    ⟨δ, hδ, htarget⟩
  refine ⟨δ, hδ, ?_⟩
  intro ν u v p hu hv hp huv hup hvp hosc z x₁ x₂ hz hρ hx₁ hx₂ hdx hdy
  have hpole' :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) (coordPoint u v p (targetPoleCoord z)) < ε₁ →
        dist (coordPoint u v p y) (coordPoint u v p (targetPoleCoord z)) < ε₁ →
        |frame_quadratic ν (coordPoint u v p x) -
            frame_quadratic ν (coordPoint u v p y)| ≤ 2 * a := by
    exact hpole ν hu hv hp huv hup hvp hosc hz hρ
  have hbound :=
    htarget ν hu hv hp huv hup hvp hz hρ hpole' hx₁ hx₂ hdx hdy
  have hfour : 2 * (2 * a) = 4 * a := by ring
  simpa [hfour] using hbound

lemma base_oscillation_bound_of_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hosc :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < ε →
        dist (coordPoint u v p y) p < ε →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
        x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x₁) u < δ →
        dist (coordPoint u v p x₂) u < δ →
        |frame_quadratic μ (coordPoint u v p x₁) -
            frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * a := by
  rcases ambient_oscillation_bound_of_cap_coords
      (hdim := hdim) (μ := μ) (u := u) (v := v) (p := p)
      hu hv hp huv hup hvp ha hε hosc with
    ⟨α, δ, hα0, hαpi, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdx hdy
  have hcoord₁ : dist x₁ coordBase < δ := by
    refine lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hu hv hp huv hup hvp x₁) ?_
    simpa [coordPoint_base] using hdx
  have hcoord₂ : dist x₂ coordBase < δ := by
    refine lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hu hv hp huv hup hvp x₂) ?_
    simpa [coordPoint_base] using hdy
  exact hlocal hx₁ hx₂ hcoord₁ hcoord₂

lemma base_oscillation_bound_of_cap_uniform
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) p < ε →
          dist (coordPoint u v p y) p < ε →
          |frame_quadratic μ (coordPoint u v p x) -
              frame_quadratic μ (coordPoint u v p y)| ≤ a) →
        ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
          x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
          x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x₁) u < δ →
          dist (coordPoint u v p x₂) u < δ →
          |frame_quadratic μ (coordPoint u v p x₁) -
              frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * a := by
  rcases ambient_oscillation_bound_of_cap_coords_uniform
      (hdim := hdim) (μ := μ) ha hε with
    ⟨α, δ, hα0, hαpi, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro u v p hu hv hp huv hup hvp hosc x₁ x₂ hx₁ hx₂ hdx hdy
  have hcoord₁ : dist x₁ coordBase < δ := by
    refine lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hu hv hp huv hup hvp x₁) ?_
    simpa [coordPoint_base] using hdx
  have hcoord₂ : dist x₂ coordBase < δ := by
    refine lt_of_le_of_lt
      (dist_coordBase_le_dist_coordPoint hu hv hp huv hup hvp x₂) ?_
    simpa [coordPoint_base] using hdy
  exact hlocal hu hv hp huv hup hvp hosc hx₁ hx₂ hcoord₁ hcoord₂

def antipodeFrameReparam (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (y.2.2, (y.2.1, -y.1))

def antipodeFrameCoords (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (-x.2.2, (x.2.1, x.1))

def negPoleCoord : ℝ × ℝ × ℝ :=
  (0, (0, -1))

lemma antipodeFrameReparam_sq_sum
    {y : ℝ × ℝ × ℝ}
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1) :
    (antipodeFrameReparam y).1 ^ 2 +
        (antipodeFrameReparam y).2.1 ^ 2 +
        (antipodeFrameReparam y).2.2 ^ 2 = 1 := by
  unfold antipodeFrameReparam
  nlinarith

lemma antipodeFrameCoords_sq_sum
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    (antipodeFrameCoords x).1 ^ 2 +
        (antipodeFrameCoords x).2.1 ^ 2 +
        (antipodeFrameCoords x).2.2 ^ 2 = 1 := by
  unfold antipodeFrameCoords
  nlinarith

lemma coordPoint_antipodeFrameReparam
    (u v p : H)
    (y : ℝ × ℝ × ℝ) :
    coordPoint (-p) v u y = coordPoint u v p (antipodeFrameReparam y) := by
  unfold coordPoint antipodeFrameReparam
  simp [realFramePoint, add_assoc, add_left_comm, add_comm, smul_neg, neg_add_rev]

lemma coordPoint_antipodeFrameCoords
    (u v p : H)
    (x : ℝ × ℝ × ℝ) :
    coordPoint (-p) v u (antipodeFrameCoords x) = coordPoint u v p x := by
  unfold coordPoint antipodeFrameCoords
  simp [realFramePoint, add_assoc, add_left_comm, add_comm, smul_neg, neg_add_rev]

lemma coordPoint_negPoleCoord
    (u v p : H) :
    coordPoint u v p negPoleCoord = -p := by
  simp [coordPoint, negPoleCoord]

lemma eq_pole_or_negPole_of_horizontalRadius_eq_zero
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z = 0) :
    z = poleCoord ∨ z = negPoleCoord := by
  have hρsq : z.1 ^ 2 + z.2.1 ^ 2 = 0 := by
    rw [← horizontalRadius_sq z, hρ]
    norm_num
  have hz1 : z.1 = 0 := by
    nlinarith [sq_nonneg z.2.1]
  have hz2 : z.2.1 = 0 := by
    nlinarith [sq_nonneg z.1]
  have hz3sq : z.2.2 ^ 2 = 1 := by
    nlinarith [hz, hz1, hz2]
  have hz3 : z.2.2 = 1 ∨ z.2.2 = -1 := by
    have hfactor : (z.2.2 - 1) * (z.2.2 + 1) = 0 := by
      nlinarith [hz3sq]
    rcases mul_eq_zero.mp hfactor with hminus | hplus
    · left
      linarith
    · right
      linarith
  rcases hz3 with hz3 | hz3
  · left
    ext <;> simp [poleCoord, hz1, hz2, hz3]
  · right
    ext <;> simp [negPoleCoord, hz1, hz2, hz3]

lemma eq_poleCoord_of_horizontalRadius_eq_zero_of_nonneg
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z = 0)
    (hz_nonneg : 0 ≤ z.2.2) :
    z = poleCoord := by
  rcases eq_pole_or_negPole_of_horizontalRadius_eq_zero hz hρ with h | h
  · exact h
  · have hzthird : z.2.2 = -1 := by
      simpa [h, negPoleCoord]
    exfalso
    linarith

lemma antipode_oscillation_bound_of_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hosc :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < ε →
        dist (coordPoint u v p y) p < ε →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
        x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x₁) (-p) < δ →
        dist (coordPoint u v p x₂) (-p) < δ →
        |frame_quadratic μ (coordPoint u v p x₁) -
            frame_quadratic μ (coordPoint u v p x₂)| ≤ 4 * a := by
  rcases base_oscillation_bound_of_cap
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp ha hε hosc with
    ⟨ε₁, hε₁, hbase⟩
  have h2a : 0 ≤ 2 * a := by nlinarith
  have hpv : inner (𝕜 := ℂ) p v = 0 := by
    simpa [inner_eq_zero_symm] using hvp
  have hpu : inner (𝕜 := ℂ) p u = 0 := by
    simpa [inner_eq_zero_symm] using hup
  have huv' : inner (𝕜 := ℂ) (-p) v = 0 := by
    rw [inner_neg_left, hpv, neg_zero]
  have hup' : inner (𝕜 := ℂ) (-p) u = 0 := by
    rw [inner_neg_left, hpu, neg_zero]
  have hvp' : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  rcases base_oscillation_bound_of_cap
      (hdim := hdim) (μ := μ) (u := -p) (v := v) (p := u)
      (by simpa using hp) hv hu huv' hup' hvp'
      (a := 2 * a) (ε := ε₁) h2a hε₁
      (hosc := by
        intro y₁ y₂ hy₁ hy₂ hdist₁ hdist₂
        calc
          |frame_quadratic μ (coordPoint (-p) v u y₁) -
              frame_quadratic μ (coordPoint (-p) v u y₂)|
              =
            |frame_quadratic μ (coordPoint u v p (antipodeFrameReparam y₁)) -
                frame_quadratic μ (coordPoint u v p (antipodeFrameReparam y₂))| := by
                  rw [coordPoint_antipodeFrameReparam, coordPoint_antipodeFrameReparam]
          _ ≤ 2 * a := by
                apply hbase
                · exact antipodeFrameReparam_sq_sum hy₁
                · exact antipodeFrameReparam_sq_sum hy₂
                · simpa [coordPoint_antipodeFrameReparam] using hdist₁
                · simpa [coordPoint_antipodeFrameReparam] using hdist₂) with
    ⟨δ, hδ, hanti⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdx hdy
  have hanti' :
      |frame_quadratic μ (coordPoint (-p) v u (antipodeFrameCoords x₁)) -
          frame_quadratic μ (coordPoint (-p) v u (antipodeFrameCoords x₂))| ≤
        2 * (2 * a) := by
    apply hanti
    · exact antipodeFrameCoords_sq_sum hx₁
    · exact antipodeFrameCoords_sq_sum hx₂
    · simpa [coordPoint_antipodeFrameCoords] using hdx
    · simpa [coordPoint_antipodeFrameCoords] using hdy
  have hanti'' :
      |frame_quadratic μ (coordPoint u v p x₁) -
          frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * (2 * a) := by
    simpa [coordPoint_antipodeFrameCoords] using hanti'
  nlinarith

lemma antipode_oscillation_bound_of_cap_uniform
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) p < ε →
          dist (coordPoint u v p y) p < ε →
          |frame_quadratic μ (coordPoint u v p x) -
              frame_quadratic μ (coordPoint u v p y)| ≤ a) →
        ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
          x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
          x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x₁) (-p) < δ →
          dist (coordPoint u v p x₂) (-p) < δ →
          |frame_quadratic μ (coordPoint u v p x₁) -
              frame_quadratic μ (coordPoint u v p x₂)| ≤ 4 * a := by
  rcases base_oscillation_bound_of_cap_uniform
      (hdim := hdim) (μ := μ) ha hε with
    ⟨ε₁, hε₁, hbase⟩
  have h2a : 0 ≤ 2 * a := by nlinarith
  rcases base_oscillation_bound_of_cap_uniform
      (hdim := hdim) (μ := μ) (a := 2 * a) (ε := ε₁) h2a hε₁ with
    ⟨δ, hδ, hantiBase⟩
  refine ⟨δ, hδ, ?_⟩
  intro u v p hu hv hp huv hup hvp hosc x₁ x₂ hx₁ hx₂ hdx hdy
  have hpv : inner (𝕜 := ℂ) p v = 0 := by
    simpa [inner_eq_zero_symm] using hvp
  have hpu : inner (𝕜 := ℂ) p u = 0 := by
    simpa [inner_eq_zero_symm] using hup
  have huv' : inner (𝕜 := ℂ) (-p) v = 0 := by
    rw [inner_neg_left, hpv, neg_zero]
  have hup' : inner (𝕜 := ℂ) (-p) u = 0 := by
    rw [inner_neg_left, hpu, neg_zero]
  have hvp' : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hbase' :
      ∀ {y₁ y₂ : ℝ × ℝ × ℝ},
        y₁.1 ^ 2 + y₁.2.1 ^ 2 + y₁.2.2 ^ 2 = 1 →
        y₂.1 ^ 2 + y₂.2.1 ^ 2 + y₂.2.2 ^ 2 = 1 →
        dist (coordPoint (-p) v u y₁) u < ε₁ →
        dist (coordPoint (-p) v u y₂) u < ε₁ →
        |frame_quadratic μ (coordPoint (-p) v u y₁) -
            frame_quadratic μ (coordPoint (-p) v u y₂)| ≤ 2 * a := by
    intro y₁ y₂ hy₁ hy₂ hdist₁ hdist₂
    calc
      |frame_quadratic μ (coordPoint (-p) v u y₁) -
          frame_quadratic μ (coordPoint (-p) v u y₂)|
          =
        |frame_quadratic μ (coordPoint u v p (antipodeFrameReparam y₁)) -
            frame_quadratic μ (coordPoint u v p (antipodeFrameReparam y₂))| := by
              rw [coordPoint_antipodeFrameReparam, coordPoint_antipodeFrameReparam]
      _ ≤ 2 * a := by
            apply hbase hu hv hp huv hup hvp hosc
            · exact antipodeFrameReparam_sq_sum hy₁
            · exact antipodeFrameReparam_sq_sum hy₂
            · simpa [coordPoint_antipodeFrameReparam] using hdist₁
            · simpa [coordPoint_antipodeFrameReparam] using hdist₂
  have hanti' :
      |frame_quadratic μ (coordPoint (-p) v u (antipodeFrameCoords x₁)) -
          frame_quadratic μ (coordPoint (-p) v u (antipodeFrameCoords x₂))| ≤
        2 * (2 * a) := by
    apply hantiBase (by simpa using hp) hv hu huv' hup' hvp' hbase'
    · exact antipodeFrameCoords_sq_sum hx₁
    · exact antipodeFrameCoords_sq_sum hx₂
    · simpa [coordPoint_antipodeFrameCoords] using hdx
    · simpa [coordPoint_antipodeFrameCoords] using hdy
  have hanti'' :
      |frame_quadratic μ (coordPoint u v p x₁) -
          frame_quadratic μ (coordPoint u v p x₂)| ≤ 2 * (2 * a) := by
    simpa [coordPoint_antipodeFrameCoords] using hanti'
  nlinarith

lemma sphere_oscillation_bound_of_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε)
    (hosc :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < ε →
        dist (coordPoint u v p y) p < ε →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤ a)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
        x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x₁) (coordPoint u v p z) < δ →
        dist (coordPoint u v p x₂) (coordPoint u v p z) < δ →
        |frame_quadratic μ (coordPoint u v p x₁) -
            frame_quadratic μ (coordPoint u v p x₂)| ≤ 4 * a := by
  by_cases hρ : horizontalRadius z = 0
  · rcases eq_pole_or_negPole_of_horizontalRadius_eq_zero hz hρ with rfl | rfl
    · refine ⟨ε, hε, ?_⟩
      intro x₁ x₂ hx₁ hx₂ hdx hdy
      have hmain :
          |frame_quadratic μ (coordPoint u v p x₁) -
              frame_quadratic μ (coordPoint u v p x₂)| ≤ a := by
        apply hosc hx₁ hx₂
        · simpa [coordPoint_poleCoord] using hdx
        · simpa [coordPoint_poleCoord] using hdy
      nlinarith
    · rcases antipode_oscillation_bound_of_cap
          (hdim := hdim) (μ := μ) hu hv hp huv hup hvp ha hε hosc with
        ⟨δ, hδ, hlocal⟩
      refine ⟨δ, hδ, ?_⟩
      intro x₁ x₂ hx₁ hx₂ hdx hdy
      exact hlocal hx₁ hx₂
        (by simpa [coordPoint_negPoleCoord] using hdx)
        (by simpa [coordPoint_negPoleCoord] using hdy)
  · exact nonpolar_oscillation_bound_of_cap
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp ha hε hosc hz hρ

lemma sphere_oscillation_bound_of_cap_uniform
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) p < ε →
          dist (coordPoint u v p y) p < ε →
          |frame_quadratic μ (coordPoint u v p x) -
              frame_quadratic μ (coordPoint u v p y)| ≤ a) →
        ∀ {z x₁ x₂ : ℝ × ℝ × ℝ},
          z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
          x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
          x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x₁) (coordPoint u v p z) < δ →
          dist (coordPoint u v p x₂) (coordPoint u v p z) < δ →
          |frame_quadratic μ (coordPoint u v p x₁) -
              frame_quadratic μ (coordPoint u v p x₂)| ≤ 4 * a := by
  rcases antipode_oscillation_bound_of_cap_uniform
      (hdim := hdim) (μ := μ) ha hε with
    ⟨δanti, hδanti, hanti⟩
  rcases nonpolar_oscillation_bound_of_cap_uniform
      (hdim := hdim) (μ := μ) ha hε with
    ⟨δnonpolar, hδnonpolar, hnonpolar⟩
  refine ⟨min ε (min δanti δnonpolar), lt_min hε (lt_min hδanti hδnonpolar), ?_⟩
  intro u v p hu hv hp huv hup hvp hosc z x₁ x₂ hz hx₁ hx₂ hdx hdy
  by_cases hρ : horizontalRadius z = 0
  · rcases eq_pole_or_negPole_of_horizontalRadius_eq_zero hz hρ with rfl | rfl
    · have hmain :
          |frame_quadratic μ (coordPoint u v p x₁) -
              frame_quadratic μ (coordPoint u v p x₂)| ≤ a := by
        apply hosc hx₁ hx₂
        · simpa [coordPoint_poleCoord] using lt_of_lt_of_le hdx (min_le_left _ _)
        · simpa [coordPoint_poleCoord] using lt_of_lt_of_le hdy (min_le_left _ _)
      nlinarith
    · have hdx' : dist (coordPoint u v p x₁) (-p) < δanti := by
        simpa [coordPoint_negPoleCoord] using
          lt_of_lt_of_le hdx ((min_le_right _ _).trans (min_le_left _ _))
      have hdy' : dist (coordPoint u v p x₂) (-p) < δanti := by
        simpa [coordPoint_negPoleCoord] using
          lt_of_lt_of_le hdy ((min_le_right _ _).trans (min_le_left _ _))
      exact hanti hu hv hp huv hup hvp hosc hx₁ hx₂ hdx' hdy'
  · have hdx' :
        dist (coordPoint u v p x₁) (coordPoint u v p z) < δnonpolar := by
      exact lt_of_lt_of_le hdx ((min_le_right _ _).trans (min_le_right _ _))
    have hdy' :
        dist (coordPoint u v p x₂) (coordPoint u v p z) < δnonpolar := by
      exact lt_of_lt_of_le hdy ((min_le_right _ _).trans (min_le_right _ _))
    exact hnonpolar hu hv hp huv hup hvp hosc hz hρ hx₁ hx₂ hdx' hdy'

end Thm27

namespace Thm25

def ewRadius (ξ η : ℝ) : ℝ :=
  Real.sqrt (ξ ^ 2 + η ^ 2)

def gleasonPsi (θ ξ η r : ℝ) : ℝ :=
  (ξ ^ 2 + η ^ 2) * Real.sin θ - ξ * r * Real.cos θ

def ewPathX (ξ η _r t : ℝ) : ℝ :=
  -(η / ewRadius ξ η) * Real.cos t + ξ * Real.sin t

def ewPathY (ξ η _r t : ℝ) : ℝ :=
  (ξ / ewRadius ξ η) * Real.cos t + η * Real.sin t

def ewPathR (_ξ _η r t : ℝ) : ℝ :=
  r * Real.sin t

lemma ewRadius_sq (ξ η : ℝ) :
    ewRadius ξ η ^ 2 = ξ ^ 2 + η ^ 2 := by
  unfold ewRadius
  rw [Real.sq_sqrt]
  positivity

lemma ewRadius_ne_zero_of_psi_neg
    {θ ξ η r : ℝ} (hneg : gleasonPsi θ ξ η r < 0) :
    ewRadius ξ η ≠ 0 := by
  intro hρ
  have hxy : ξ ^ 2 + η ^ 2 = 0 := by
    have := ewRadius_sq ξ η
    rw [hρ] at this
    nlinarith
  have hξ0 : ξ = 0 := by nlinarith [sq_nonneg ξ, sq_nonneg η, hxy]
  have hη0 : η = 0 := by nlinarith [sq_nonneg ξ, sq_nonneg η, hxy]
  unfold gleasonPsi at hneg
  rw [hξ0, hη0] at hneg
  linarith

lemma ewPath_sphere
    {ξ η r t : ℝ} (hρ : ewRadius ξ η ≠ 0)
    (hsphere : ξ ^ 2 + η ^ 2 + r ^ 2 = 1) :
    ewPathX ξ η r t ^ 2 + ewPathY ξ η r t ^ 2 + ewPathR ξ η r t ^ 2 = 1 := by
  have hρsq : ewRadius ξ η ^ 2 = ξ ^ 2 + η ^ 2 := ewRadius_sq ξ η
  unfold ewPathX ewPathY ewPathR
  have hxy :
      (-(η / ewRadius ξ η) * Real.cos t + ξ * Real.sin t) ^ 2 +
        ((ξ / ewRadius ξ η) * Real.cos t + η * Real.sin t) ^ 2 =
      Real.cos t ^ 2 + (ξ ^ 2 + η ^ 2) * Real.sin t ^ 2 := by
    field_simp [hρ]
    nlinarith [hρsq]
  calc
    (-(η / ewRadius ξ η) * Real.cos t + ξ * Real.sin t) ^ 2 +
        ((ξ / ewRadius ξ η) * Real.cos t + η * Real.sin t) ^ 2 +
        (r * Real.sin t) ^ 2
        =
      Real.cos t ^ 2 + (ξ ^ 2 + η ^ 2) * Real.sin t ^ 2 + r ^ 2 * Real.sin t ^ 2 := by
        rw [hxy]
        ring
    _ = Real.cos t ^ 2 + (ξ ^ 2 + η ^ 2 + r ^ 2) * Real.sin t ^ 2 := by
        ring
    _ = Real.cos t ^ 2 + Real.sin t ^ 2 := by rw [hsphere, one_mul]
    _ = 1 := by nlinarith [Real.sin_sq_add_cos_sq t]

lemma ewPath_plane
    {ξ η r t : ℝ} (hρ : ewRadius ξ η ≠ 0) :
    (ξ ^ 2 + η ^ 2) * ewPathR ξ η r t =
      r * (ξ * ewPathX ξ η r t + η * ewPathY ξ η r t) := by
  have hρsq : ewRadius ξ η ^ 2 = ξ ^ 2 + η ^ 2 := ewRadius_sq ξ η
  unfold ewPathX ewPathY ewPathR
  field_simp [hρ]
  nlinarith [hρsq]

lemma gleasonPsi_ewPath_zero_endpoint
    {θ ξ η r : ℝ} (hρ : ewRadius ξ η ≠ 0)
    (_hθ : 0 < θ) :
    gleasonPsi θ (ewPathX ξ η r 0) (ewPathY ξ η r 0) (ewPathR ξ η r 0) = Real.sin θ := by
  have hρsq : ewRadius ξ η ^ 2 = ξ ^ 2 + η ^ 2 := ewRadius_sq ξ η
  unfold gleasonPsi ewPathX ewPathY ewPathR
  rw [Real.sin_zero, Real.cos_zero]
  field_simp [hρ]
  rw [hρsq]
  ring

lemma gleasonPsi_ewPath_top
    {θ ξ η r : ℝ} :
    gleasonPsi θ (ewPathX ξ η r (Real.pi / 2)) (ewPathY ξ η r (Real.pi / 2))
      (ewPathR ξ η r (Real.pi / 2)) =
    gleasonPsi θ ξ η r := by
  unfold gleasonPsi ewPathX ewPathY ewPathR
  rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
  ring

theorem exists_ewPath_zero_of_gleasonPsi_neg
    {θ ξ η r : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hneg : gleasonPsi θ ξ η r < 0) :
    ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      gleasonPsi θ (ewPathX ξ η r t) (ewPathY ξ η r t) (ewPathR ξ η r t) = 0 := by
  have hρ : ewRadius ξ η ≠ 0 := ewRadius_ne_zero_of_psi_neg hneg
  let F : ℝ → ℝ := fun t =>
    gleasonPsi θ (ewPathX ξ η r t) (ewPathY ξ η r t) (ewPathR ξ η r t)
  have hFcont : Continuous F := by
    have hXcont : Continuous (ewPathX ξ η r) := by
      unfold ewPathX
      exact (continuous_const.mul Real.continuous_cos).add
        (continuous_const.mul Real.continuous_sin)
    have hYcont : Continuous (ewPathY ξ η r) := by
      unfold ewPathY
      exact (continuous_const.mul Real.continuous_cos).add
        (continuous_const.mul Real.continuous_sin)
    have hRcont : Continuous (ewPathR ξ η r) := by
      unfold ewPathR
      exact continuous_const.mul Real.continuous_sin
    unfold F gleasonPsi
    exact ((hXcont.pow 2).add (hYcont.pow 2)).mul continuous_const |>.sub
      ((hXcont.mul hRcont).mul continuous_const)
  have hF0 : 0 < F 0 := by
    have hθltπ : θ < Real.pi := by
      nlinarith [hθpi, Real.pi_pos]
    have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθltπ
    rw [show F 0 = Real.sin θ by
      unfold F
      exact gleasonPsi_ewPath_zero_endpoint hρ hθ0]
    exact hsin_pos
  have hFtop : F (Real.pi / 2) < 0 := by
    rw [show F (Real.pi / 2) = gleasonPsi θ ξ η r by
      unfold F
      exact gleasonPsi_ewPath_top]
    exact hneg
  have hzero_mem : (0 : ℝ) ∈ Set.uIcc (F 0) (F (Real.pi / 2)) := by
    rw [Set.mem_uIcc]
    right
    exact ⟨le_of_lt hFtop, le_of_lt hF0⟩
  rcases intermediate_value_uIcc hFcont.continuousOn hzero_mem with ⟨t, ht, hFt⟩
  have hpi_nonneg : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  exact ⟨t, by simpa [Set.uIcc_of_le hpi_nonneg] using ht, hFt⟩

theorem exists_two_step_ew_point_of_gleasonPsi_neg
    {θ ξ η r : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hsphere : ξ ^ 2 + η ^ 2 + r ^ 2 = 1)
    (hneg : gleasonPsi θ ξ η r < 0) :
    ∃ ξ' η' r',
      ξ' ^ 2 + η' ^ 2 + r' ^ 2 = 1 ∧
      (ξ ^ 2 + η ^ 2) * r' = r * (ξ * ξ' + η * η') ∧
      gleasonPsi θ ξ' η' r' = 0 := by
  have hρ : ewRadius ξ η ≠ 0 := ewRadius_ne_zero_of_psi_neg hneg
  rcases exists_ewPath_zero_of_gleasonPsi_neg hθ0 hθpi hneg with ⟨t, _ht, hzero⟩
  refine ⟨ewPathX ξ η r t, ewPathY ξ η r t, ewPathR ξ η r t, ?_, ?_, hzero⟩
  · exact ewPath_sphere hρ hsphere
  · exact ewPath_plane hρ

lemma gleasonPsi_meridian
    (θ φ : ℝ) :
    gleasonPsi θ (Real.cos φ) 0 (Real.sin φ) =
      Real.cos φ * Real.sin (θ - φ) := by
  unfold gleasonPsi
  rw [Real.sin_sub]
  ring

lemma ewRadius_cos_zero
    {φ : ℝ} (hcos : 0 < Real.cos φ) :
    ewRadius (Real.cos φ) 0 = Real.cos φ := by
  unfold ewRadius
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq_eq_abs]
  exact abs_of_pos hcos

lemma gleasonPsi_ewPath_meridian_eq
    {θ φ t : ℝ} (hcos : 0 < Real.cos φ) :
    gleasonPsi θ
        (ewPathX (Real.cos φ) 0 (Real.sin φ) t)
        (ewPathY (Real.cos φ) 0 (Real.sin φ) t)
        (ewPathR (Real.cos φ) 0 (Real.sin φ) t) =
      Real.sin θ * Real.cos t ^ 2 +
        Real.cos φ * Real.sin (θ - φ) * Real.sin t ^ 2 := by
  have hρ : ewRadius (Real.cos φ) 0 = Real.cos φ :=
    ewRadius_cos_zero hcos
  unfold gleasonPsi ewPathX ewPathY ewPathR
  rw [hρ]
  field_simp [ne_of_gt hcos]
  rw [Real.sin_sub]
  ring

lemma gleasonPsi_ewPath_meridian_zero_eq
    {θ φ t : ℝ}
    (hθ0 : 0 < θ) (hθφ : θ < φ) (hφpi : φ < Real.pi / 2)
    (hzero :
      gleasonPsi θ
          (ewPathX (Real.cos φ) 0 (Real.sin φ) t)
          (ewPathY (Real.cos φ) 0 (Real.sin φ) t)
          (ewPathR (Real.cos φ) 0 (Real.sin φ) t) = 0) :
    Real.sin θ * Real.cos t ^ 2 =
      -(Real.cos φ * Real.sin (θ - φ)) * Real.sin t ^ 2 := by
  have hcos : 0 < Real.cos φ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, hθ0, hθφ], hφpi⟩
  have hformula :=
    gleasonPsi_ewPath_meridian_eq (θ := θ) (φ := φ) (t := t) hcos
  rw [hformula] at hzero
  nlinarith

lemma gleasonPsi_ewPath_meridian_zero_cos_sq_le
    {θ φ t : ℝ}
    (hθ0 : 0 < θ) (hθφ : θ < φ) (hφpi : φ < Real.pi / 2)
    (hzero :
      gleasonPsi θ
          (ewPathX (Real.cos φ) 0 (Real.sin φ) t)
          (ewPathY (Real.cos φ) 0 (Real.sin φ) t)
          (ewPathR (Real.cos φ) 0 (Real.sin φ) t) = 0) :
    Real.cos t ^ 2 ≤
      -(Real.cos φ * Real.sin (θ - φ)) / Real.sin θ := by
  have hθltπ : θ < Real.pi := by nlinarith [Real.pi_pos, hθφ, hφpi]
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθltπ
  have hcosφ : 0 < Real.cos φ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, hθ0, hθφ], hφpi⟩
  have hgap_pos : 0 < -Real.sin (θ - φ) := by
    have hgap0 : 0 < φ - θ := by linarith
    have hgapπ : φ - θ < Real.pi := by nlinarith [Real.pi_pos, hφpi, hθ0]
    have hsin_gap : 0 < Real.sin (φ - θ) :=
      Real.sin_pos_of_pos_of_lt_pi hgap0 hgapπ
    have hrewrite : θ - φ = -(φ - θ) := by ring
    rw [hrewrite, Real.sin_neg]
    linarith
  have hcoeff_pos : 0 < -(Real.cos φ * Real.sin (θ - φ)) := by
    nlinarith
  have heq :=
    gleasonPsi_ewPath_meridian_zero_eq
      (θ := θ) (φ := φ) (t := t) hθ0 hθφ hφpi hzero
  have hsin_sq_le : Real.sin t ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_le_one t]
  have hmul :
      Real.sin θ * Real.cos t ^ 2 ≤
        -(Real.cos φ * Real.sin (θ - φ)) := by
    calc
      Real.sin θ * Real.cos t ^ 2
          = -(Real.cos φ * Real.sin (θ - φ)) * Real.sin t ^ 2 := heq
      _ ≤ -(Real.cos φ * Real.sin (θ - φ)) * 1 := by
          exact mul_le_mul_of_nonneg_left hsin_sq_le (le_of_lt hcoeff_pos)
      _ = -(Real.cos φ * Real.sin (θ - φ)) := by ring
  exact (le_div_iff₀ hsinθ).mpr (by simpa [mul_comm] using hmul)

lemma abs_one_sub_sin_le_cos_of_mem_Icc
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    |1 - Real.sin t| ≤ Real.cos t := by
  have hsin_nonneg : 0 ≤ Real.sin t := by
    exact Real.sin_nonneg_of_mem_Icc ⟨ht.1, by nlinarith [ht.2, Real.pi_pos]⟩
  have hsin_le_one : Real.sin t ≤ 1 := Real.sin_le_one t
  have hcos_nonneg : 0 ≤ Real.cos t := by
    exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [ht.1, Real.pi_pos], ht.2⟩
  have hleft_nonneg : 0 ≤ 1 - Real.sin t := by linarith
  have hsq :
      (1 - Real.sin t) ^ 2 ≤ Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hle := (sq_le_sq₀ hleft_nonneg hcos_nonneg).mp hsq
  simpa [abs_of_nonneg hleft_nonneg] using hle

lemma ewPath_meridian_dist_top_le_cos
    {φ t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    dist
        (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
          (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
            ewPathR (Real.cos φ) 0 (Real.sin φ) t))
        (Real.cos φ, (0, Real.sin φ)) ≤
      Real.cos t := by
  have hcos_t_nonneg : 0 ≤ Real.cos t := by
    exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [ht.1, Real.pi_pos], ht.2⟩
  have hsin_gap : |1 - Real.sin t| ≤ Real.cos t :=
    abs_one_sub_sin_le_cos_of_mem_Icc ht
  have hsin_gap' : |Real.sin t - 1| ≤ Real.cos t := by
    simpa [abs_sub_comm] using hsin_gap
  have hx :
      |ewPathX (Real.cos φ) 0 (Real.sin φ) t - Real.cos φ| ≤ Real.cos t := by
    have hbase :
        |Real.cos φ * Real.sin t - Real.cos φ| ≤ Real.cos t := by
      calc
        |Real.cos φ * Real.sin t - Real.cos φ|
            = |Real.cos φ| * |Real.sin t - 1| := by
                rw [← abs_mul]
                congr 1
                ring
        _ ≤ 1 * Real.cos t := by
            exact mul_le_mul (Real.abs_cos_le_one φ) hsin_gap'
              (abs_nonneg _) (by norm_num)
        _ = Real.cos t := by ring
    simpa [ewPathX, mul_comm] using hbase
  have hy :
      |ewPathY (Real.cos φ) 0 (Real.sin φ) t - 0| ≤ Real.cos t := by
    unfold ewPathY
    by_cases hcosφ : Real.cos φ = 0
    · simp [hcosφ, hcos_t_nonneg]
    · have hρ : ewRadius (Real.cos φ) 0 = |Real.cos φ| := by
        unfold ewRadius
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq_eq_abs]
      rw [hρ]
      have hratio_abs : |Real.cos φ / (|Real.cos φ|)| = 1 := by
        rw [abs_div, abs_abs, div_self]
        exact abs_ne_zero.mpr hcosφ
      have heq :
          |Real.cos φ / (|Real.cos φ|) * Real.cos t + 0 * Real.sin t - 0| =
            Real.cos t := by
        calc
          |Real.cos φ / (|Real.cos φ|) * Real.cos t + 0 * Real.sin t - 0|
              = |Real.cos φ / (|Real.cos φ|)| * |Real.cos t| := by
                  rw [zero_mul, add_zero, sub_zero, abs_mul]
          _ = Real.cos t := by
              rw [hratio_abs, one_mul, abs_of_nonneg hcos_t_nonneg]
      exact le_of_eq heq
  have hz :
      |ewPathR (Real.cos φ) 0 (Real.sin φ) t - Real.sin φ| ≤ Real.cos t := by
    have hbase :
        |Real.sin φ * Real.sin t - Real.sin φ| ≤ Real.cos t := by
      calc
        |Real.sin φ * Real.sin t - Real.sin φ|
            = |Real.sin φ| * |Real.sin t - 1| := by
                rw [← abs_mul]
                congr 1
                ring
        _ ≤ 1 * Real.cos t := by
            exact mul_le_mul (Real.abs_sin_le_one φ) hsin_gap'
              (abs_nonneg _) (by norm_num)
        _ = Real.cos t := by ring
    simpa [ewPathR] using hbase
  simpa [Prod.dist_eq, Prod.norm_def, Real.dist_eq, Real.norm_eq_abs] using
    (max_le hx (max_le hy hz))

lemma gleasonPsi_meridian_neg
    {θ φ : ℝ}
    (hθ0 : 0 < θ) (hφθ : θ < φ) (hφpi : φ < Real.pi / 2) :
    gleasonPsi θ (Real.cos φ) 0 (Real.sin φ) < 0 := by
  have hcos_pos : 0 < Real.cos φ := by
    refine Real.cos_pos_of_mem_Ioo ?_
    constructor
    · nlinarith [Real.pi_pos]
    · exact hφpi
  have hsin_neg : Real.sin (θ - φ) < 0 := by
    have hneg : θ - φ < 0 := by linarith
    have hneg_pi : -Real.pi < θ - φ := by
      nlinarith [hθ0, hφpi, Real.pi_pos]
    exact Real.sin_neg_of_neg_of_neg_pi_lt hneg hneg_pi
  rw [gleasonPsi_meridian]
  nlinarith

theorem exists_ewPath_meridian_zero_dist_top_sq_le
    {θ φ : ℝ}
    (hθ0 : 0 < θ) (hθφ : θ < φ) (hφpi : φ < Real.pi / 2) :
    ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      gleasonPsi θ
          (ewPathX (Real.cos φ) 0 (Real.sin φ) t)
          (ewPathY (Real.cos φ) 0 (Real.sin φ) t)
          (ewPathR (Real.cos φ) 0 (Real.sin φ) t) = 0 ∧
      dist
          (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
            (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
              ewPathR (Real.cos φ) 0 (Real.sin φ) t))
          (Real.cos φ, (0, Real.sin φ)) ^ 2 ≤
        -(Real.cos φ * Real.sin (θ - φ)) / Real.sin θ := by
  have hθpi : θ < Real.pi / 2 := by linarith
  have hneg :
      gleasonPsi θ (Real.cos φ) 0 (Real.sin φ) < 0 :=
    gleasonPsi_meridian_neg hθ0 hθφ hφpi
  rcases exists_ewPath_zero_of_gleasonPsi_neg
      (θ := θ) (ξ := Real.cos φ) (η := 0) (r := Real.sin φ)
      hθ0 hθpi hneg with
    ⟨t, ht, hzero⟩
  have hdist :
      dist
          (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
            (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
              ewPathR (Real.cos φ) 0 (Real.sin φ) t))
          (Real.cos φ, (0, Real.sin φ)) ≤
        Real.cos t :=
    ewPath_meridian_dist_top_le_cos (φ := φ) (t := t) ht
  have hdist_nonneg :
      0 ≤
        dist
          (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
            (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
              ewPathR (Real.cos φ) 0 (Real.sin φ) t))
          (Real.cos φ, (0, Real.sin φ)) :=
    dist_nonneg
  have hcos_t_nonneg : 0 ≤ Real.cos t := by
    exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [ht.1, Real.pi_pos], ht.2⟩
  have hdist_sq :
      dist
          (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
            (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
              ewPathR (Real.cos φ) 0 (Real.sin φ) t))
          (Real.cos φ, (0, Real.sin φ)) ^ 2 ≤
        Real.cos t ^ 2 :=
    (sq_le_sq₀ hdist_nonneg hcos_t_nonneg).mpr hdist
  have hcos_sq :
      Real.cos t ^ 2 ≤
        -(Real.cos φ * Real.sin (θ - φ)) / Real.sin θ :=
    gleasonPsi_ewPath_meridian_zero_cos_sq_le hθ0 hθφ hφpi hzero
  exact ⟨t, ht, hzero, le_trans hdist_sq hcos_sq⟩

theorem exists_ewPath_meridian_zero_dist_top_sq_lt
    {θ ε : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) (hε : 0 < ε) :
    ∃ φ t,
      θ < φ ∧ φ < Real.pi / 2 ∧
      t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) ∧
      gleasonPsi θ
          (ewPathX (Real.cos φ) 0 (Real.sin φ) t)
          (ewPathY (Real.cos φ) 0 (Real.sin φ) t)
          (ewPathR (Real.cos φ) 0 (Real.sin φ) t) = 0 ∧
      dist
          (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
            (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
              ewPathR (Real.cos φ) 0 (Real.sin φ) t))
          (Real.cos φ, (0, Real.sin φ)) ^ 2 < ε := by
  have hθltπ : θ < Real.pi := by nlinarith [hθpi, Real.pi_pos]
  have hsinθ_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθltπ
  let α : ℝ := min ((Real.pi / 2 - θ) / 2) ((ε * Real.sin θ) / 2)
  have hgap_pos : 0 < (Real.pi / 2 - θ) / 2 := by nlinarith
  have hscale_pos : 0 < (ε * Real.sin θ) / 2 := by nlinarith
  have hα_pos : 0 < α := by
    exact lt_min hgap_pos hscale_pos
  have hα_le_gap : α ≤ (Real.pi / 2 - θ) / 2 := by
    exact min_le_left _ _
  have hα_lt_gap : α < Real.pi / 2 - θ := by
    nlinarith [hgap_pos, hα_le_gap]
  have hα_le_scale : α ≤ (ε * Real.sin θ) / 2 := by
    exact min_le_right _ _
  have hα_lt_scale : α < ε * Real.sin θ := by
    nlinarith [hscale_pos, hα_le_scale]
  let φ : ℝ := Real.pi / 2 - α
  have hθφ : θ < φ := by
    dsimp [φ]
    linarith
  have hφpi : φ < Real.pi / 2 := by
    dsimp [φ]
    linarith
  rcases exists_ewPath_meridian_zero_dist_top_sq_le
      (θ := θ) (φ := φ) hθ0 hθφ hφpi with
    ⟨t, ht, hzero, hdist_le⟩
  have hcoeff_lt :
      -(Real.cos φ * Real.sin (θ - φ)) / Real.sin θ < ε := by
    have hcos_eq : Real.cos φ = Real.sin α := by
      dsimp [φ]
      rw [Real.cos_pi_div_two_sub]
    have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
    have hsinα_le : Real.sin α ≤ α := Real.sin_le hα_nonneg
    have hcosφ_nonneg : 0 ≤ Real.cos φ := by
      rw [hcos_eq]
      have hα_ltπ : α < Real.pi := by nlinarith [hα_le_gap, hθ0, Real.pi_pos]
      exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi hα_pos hα_ltπ)
    have hneg_sin_le : -Real.sin (θ - φ) ≤ 1 := by
      nlinarith [Real.neg_one_le_sin (θ - φ)]
    have hnum_le :
        -(Real.cos φ * Real.sin (θ - φ)) ≤ Real.cos φ := by
      have hmul :
          Real.cos φ * (-Real.sin (θ - φ)) ≤ Real.cos φ * 1 := by
        exact mul_le_mul_of_nonneg_left hneg_sin_le hcosφ_nonneg
      nlinarith
    have hcos_lt : Real.cos φ < ε * Real.sin θ := by
      rw [hcos_eq]
      exact lt_of_le_of_lt hsinα_le hα_lt_scale
    have hnum_lt :
        -(Real.cos φ * Real.sin (θ - φ)) < ε * Real.sin θ :=
      lt_of_le_of_lt hnum_le hcos_lt
    exact (div_lt_iff₀ hsinθ_pos).mpr (by simpa [mul_comm] using hnum_lt)
  exact ⟨φ, t, hθφ, hφpi, ht, hzero, lt_of_le_of_lt hdist_le hcoeff_lt⟩

theorem exists_sphere_point_with_gleasonPsi_neg
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) :
    ∃ ξ η r, ξ ^ 2 + η ^ 2 + r ^ 2 = 1 ∧ gleasonPsi θ ξ η r < 0 := by
  let φ : ℝ := (θ + Real.pi / 2) / 2
  have hφθ : θ < φ := by
    dsimp [φ]
    linarith
  have hφpi : φ < Real.pi / 2 := by
    dsimp [φ]
    linarith
  refine ⟨Real.cos φ, 0, Real.sin φ, ?_, ?_⟩
  · nlinarith [Real.sin_sq_add_cos_sq φ]
  · exact gleasonPsi_meridian_neg hθ0 hφθ hφpi

def gleasonPsiSwap (θ ξ η r : ℝ) : ℝ :=
  gleasonPsi θ η ξ r

theorem exists_ewPath_meridian_swap_zero_dist_top_sq_lt
    {θ ε : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) (hε : 0 < ε) :
    ∃ φ t,
      θ < φ ∧ φ < Real.pi / 2 ∧
      t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) ∧
      gleasonPsiSwap θ
          (ewPathY (Real.cos φ) 0 (Real.sin φ) t)
          (ewPathX (Real.cos φ) 0 (Real.sin φ) t)
          (ewPathR (Real.cos φ) 0 (Real.sin φ) t) = 0 ∧
      dist
          (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
            (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
              ewPathR (Real.cos φ) 0 (Real.sin φ) t))
          (0, (Real.cos φ, Real.sin φ)) ^ 2 < ε := by
  rcases exists_ewPath_meridian_zero_dist_top_sq_lt
      (θ := θ) (ε := ε) hθ0 hθpi hε with
    ⟨φ, t, hθφ, hφpi, ht, hzero, hdist⟩
  refine ⟨φ, t, hθφ, hφpi, ht, ?_, ?_⟩
  · simpa [gleasonPsiSwap] using hzero
  · have hdist_eq :
        dist
            (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
              (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
                ewPathR (Real.cos φ) 0 (Real.sin φ) t))
            (0, (Real.cos φ, Real.sin φ)) =
          dist
            (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
              (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
                ewPathR (Real.cos φ) 0 (Real.sin φ) t))
            (Real.cos φ, (0, Real.sin φ)) := by
      simp [Prod.dist_eq, Real.dist_eq, Real.norm_eq_abs, max_assoc, max_left_comm, max_comm]
    simpa [hdist_eq] using hdist

theorem exists_gleasonPsiSwap_zero_near_high_meridian
    {θ ε : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) (hε : 0 < ε) :
    ∃ φ x,
      θ < φ ∧ φ < Real.pi / 2 ∧
      x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 ∧
      gleasonPsiSwap θ x.1 x.2.1 x.2.2 = 0 ∧
      dist x (0, (Real.cos φ, Real.sin φ)) ^ 2 < ε := by
  rcases exists_ewPath_meridian_swap_zero_dist_top_sq_lt
      (θ := θ) (ε := ε) hθ0 hθpi hε with
    ⟨φ, t, hθφ, hφpi, ht, hzero, hdist⟩
  let x : ℝ × ℝ × ℝ :=
    (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
      (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
        ewPathR (Real.cos φ) 0 (Real.sin φ) t))
  have hcosφ : 0 < Real.cos φ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, hθ0, hθφ], hφpi⟩
  have hρ : ewRadius (Real.cos φ) 0 ≠ 0 := by
    rw [ewRadius_cos_zero hcosφ]
    exact ne_of_gt hcosφ
  have hsphere_base : Real.cos φ ^ 2 + 0 ^ 2 + Real.sin φ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq φ]
  have hsphere_path :
      ewPathX (Real.cos φ) 0 (Real.sin φ) t ^ 2 +
          ewPathY (Real.cos φ) 0 (Real.sin φ) t ^ 2 +
            ewPathR (Real.cos φ) 0 (Real.sin φ) t ^ 2 = 1 :=
    ewPath_sphere hρ hsphere_base
  refine ⟨φ, x, hθφ, hφpi, ?_, ?_, ?_⟩
  · dsimp [x]
    nlinarith
  · simpa [x] using hzero
  · simpa [x] using hdist

lemma horizontalRadius_ewPath_meridian_swap_ne_zero
    {φ t : ℝ} (hcosφ : 0 < Real.cos φ) :
    horizontalRadius
        (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
          (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
            ewPathR (Real.cos φ) 0 (Real.sin φ) t)) ≠ 0 := by
  intro hρ
  let x : ℝ × ℝ × ℝ :=
    (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
      (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
        ewPathR (Real.cos φ) 0 (Real.sin φ) t))
  have hρsq := horizontalRadius_sq x
  have hsum :
      ewPathY (Real.cos φ) 0 (Real.sin φ) t ^ 2 +
          ewPathX (Real.cos φ) 0 (Real.sin φ) t ^ 2 = 0 := by
    rw [hρ] at hρsq
    simpa [x] using hρsq.symm
  have hrad : ewRadius (Real.cos φ) 0 = Real.cos φ :=
    ewRadius_cos_zero hcosφ
  have hy :
      ewPathY (Real.cos φ) 0 (Real.sin φ) t = Real.cos t := by
    unfold ewPathY
    rw [hrad]
    field_simp [ne_of_gt hcosφ]
    ring
  have hx :
      ewPathX (Real.cos φ) 0 (Real.sin φ) t = Real.cos φ * Real.sin t := by
    simp [ewPathX]
  rw [hy, hx] at hsum
  have hcos_t_zero : Real.cos t = 0 := by
    nlinarith [sq_nonneg (Real.cos t), sq_nonneg (Real.cos φ * Real.sin t)]
  have hmul_zero : Real.cos φ * Real.sin t = 0 := by
    have hs : (Real.cos φ * Real.sin t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (Real.cos t), sq_nonneg (Real.cos φ * Real.sin t)]
    exact sq_eq_zero_iff.mp hs
  have hsin_t_zero : Real.sin t = 0 := by
    exact (mul_eq_zero.mp hmul_zero).resolve_left (ne_of_gt hcosφ)
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem exists_gleasonPsiSwap_zero_near_high_meridian_nonpolar
    {θ ε : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) (hε : 0 < ε) :
    ∃ φ x,
      θ < φ ∧ φ < Real.pi / 2 ∧
      x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 ∧
      horizontalRadius x ≠ 0 ∧
      gleasonPsiSwap θ x.1 x.2.1 x.2.2 = 0 ∧
      dist x (0, (Real.cos φ, Real.sin φ)) ^ 2 < ε := by
  rcases exists_ewPath_meridian_swap_zero_dist_top_sq_lt
      (θ := θ) (ε := ε) hθ0 hθpi hε with
    ⟨φ, t, hθφ, hφpi, ht, hzero, hdist⟩
  let x : ℝ × ℝ × ℝ :=
    (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
      (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
        ewPathR (Real.cos φ) 0 (Real.sin φ) t))
  have hcosφ : 0 < Real.cos φ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, hθ0, hθφ], hφpi⟩
  have hρ : horizontalRadius x ≠ 0 := by
    simpa [x] using
      (horizontalRadius_ewPath_meridian_swap_ne_zero (φ := φ) (t := t) hcosφ)
  refine ⟨φ, x, hθφ, hφpi, ?_, hρ, ?_, ?_⟩
  · have hρew : ewRadius (Real.cos φ) 0 ≠ 0 := by
      rw [ewRadius_cos_zero hcosφ]
      exact ne_of_gt hcosφ
    have hsphere_base : Real.cos φ ^ 2 + 0 ^ 2 + Real.sin φ ^ 2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    have hsphere_path :
        ewPathX (Real.cos φ) 0 (Real.sin φ) t ^ 2 +
            ewPathY (Real.cos φ) 0 (Real.sin φ) t ^ 2 +
              ewPathR (Real.cos φ) 0 (Real.sin φ) t ^ 2 = 1 :=
      ewPath_sphere hρew hsphere_base
    dsimp [x]
    nlinarith
  · simpa [x] using hzero
  · simpa [x] using hdist

set_option maxHeartbeats 800000 in
theorem exists_gleasonPsiSwap_zero_near_pole_nonpolar
    {θ ε : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) (hε : 0 < ε) :
    ∃ φ x,
      θ < φ ∧ φ < Real.pi / 2 ∧
      x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 ∧
      horizontalRadius x ≠ 0 ∧
      gleasonPsiSwap θ x.1 x.2.1 x.2.2 = 0 ∧
      dist x poleCoord < ε := by
  have hθltπ : θ < Real.pi := by nlinarith [hθpi, Real.pi_pos]
  have hsinθ_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθltπ
  let εpath : ℝ := (ε / 2) ^ 2
  have hεpath : 0 < εpath := by
    dsimp [εpath]
    positivity
  let α : ℝ :=
    min ((Real.pi / 2 - θ) / 2)
      (min ((εpath * Real.sin θ) / 2) (ε / 4))
  have hgap_pos : 0 < (Real.pi / 2 - θ) / 2 := by nlinarith
  have hscale_pos : 0 < (εpath * Real.sin θ) / 2 := by positivity
  have hquarter_pos : 0 < ε / 4 := by positivity
  have hα_pos : 0 < α := by
    exact lt_min hgap_pos (lt_min hscale_pos hquarter_pos)
  have hα_le_gap : α ≤ (Real.pi / 2 - θ) / 2 := by
    exact min_le_left _ _
  have hα_lt_gap : α < Real.pi / 2 - θ := by
    nlinarith [hgap_pos, hα_le_gap]
  have hα_le_scale : α ≤ (εpath * Real.sin θ) / 2 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hα_lt_scale : α < εpath * Real.sin θ := by
    nlinarith [hscale_pos, hα_le_scale]
  have hα_le_quarter : α ≤ ε / 4 := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hα_lt_half : α < ε / 2 := by
    nlinarith [hquarter_pos, hα_le_quarter]
  let φ : ℝ := Real.pi / 2 - α
  have hθφ : θ < φ := by
    dsimp [φ]
    linarith
  have hφpi : φ < Real.pi / 2 := by
    dsimp [φ]
    linarith
  rcases exists_ewPath_meridian_zero_dist_top_sq_le
      (θ := θ) (φ := φ) hθ0 hθφ hφpi with
    ⟨t, ht, hzero, hdist_le⟩
  let x : ℝ × ℝ × ℝ :=
    (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
      (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
        ewPathR (Real.cos φ) 0 (Real.sin φ) t))
  have hcosφ : 0 < Real.cos φ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, hθ0, hθφ], hφpi⟩
  have hρ : horizontalRadius x ≠ 0 := by
    simpa [x] using
      (horizontalRadius_ewPath_meridian_swap_ne_zero (φ := φ) (t := t) hcosφ)
  have hsphere : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 := by
    have hρew : ewRadius (Real.cos φ) 0 ≠ 0 := by
      rw [ewRadius_cos_zero hcosφ]
      exact ne_of_gt hcosφ
    have hsphere_base : Real.cos φ ^ 2 + 0 ^ 2 + Real.sin φ ^ 2 = 1 := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    have hsphere_path :
        ewPathX (Real.cos φ) 0 (Real.sin φ) t ^ 2 +
            ewPathY (Real.cos φ) 0 (Real.sin φ) t ^ 2 +
              ewPathR (Real.cos φ) 0 (Real.sin φ) t ^ 2 = 1 :=
      ewPath_sphere hρew hsphere_base
    dsimp [x]
    nlinarith
  have hψ : gleasonPsiSwap θ x.1 x.2.1 x.2.2 = 0 := by
    simpa [x, gleasonPsiSwap] using hzero
  have hcoeff_lt :
      -(Real.cos φ * Real.sin (θ - φ)) / Real.sin θ < εpath := by
    have hcos_eq : Real.cos φ = Real.sin α := by
      dsimp [φ]
      rw [Real.cos_pi_div_two_sub]
    have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
    have hsinα_le : Real.sin α ≤ α := Real.sin_le hα_nonneg
    have hcosφ_nonneg : 0 ≤ Real.cos φ := le_of_lt hcosφ
    have hneg_sin_le : -Real.sin (θ - φ) ≤ 1 := by
      nlinarith [Real.neg_one_le_sin (θ - φ)]
    have hnum_le :
        -(Real.cos φ * Real.sin (θ - φ)) ≤ Real.cos φ := by
      have hmul :
          Real.cos φ * (-Real.sin (θ - φ)) ≤ Real.cos φ * 1 := by
        exact mul_le_mul_of_nonneg_left hneg_sin_le hcosφ_nonneg
      nlinarith
    have hcos_lt : Real.cos φ < εpath * Real.sin θ := by
      rw [hcos_eq]
      exact lt_of_le_of_lt hsinα_le hα_lt_scale
    have hnum_lt :
        -(Real.cos φ * Real.sin (θ - φ)) < εpath * Real.sin θ :=
      lt_of_le_of_lt hnum_le hcos_lt
    exact (div_lt_iff₀ hsinθ_pos).mpr (by simpa [mul_comm] using hnum_lt)
  have hdist_top_sq :
      dist x (0, (Real.cos φ, Real.sin φ)) ^ 2 < εpath := by
    have hdist_eq :
        dist x (0, (Real.cos φ, Real.sin φ)) =
          dist
            (ewPathX (Real.cos φ) 0 (Real.sin φ) t,
              (ewPathY (Real.cos φ) 0 (Real.sin φ) t,
                ewPathR (Real.cos φ) 0 (Real.sin φ) t))
            (Real.cos φ, (0, Real.sin φ)) := by
      simp only [x, Prod.dist_eq, Real.dist_eq, Real.norm_eq_abs]
      ac_rfl
    rw [hdist_eq]
    exact lt_of_le_of_lt hdist_le hcoeff_lt
  have hdist_top : dist x (0, (Real.cos φ, Real.sin φ)) < ε / 2 := by
    have hdist_nonneg : 0 ≤ dist x (0, (Real.cos φ, Real.sin φ)) := dist_nonneg
    dsimp [εpath] at hdist_top_sq
    nlinarith
  have htop_pole_le : dist (0, (Real.cos φ, Real.sin φ)) poleCoord ≤ α := by
    have hgap_abs : |φ - Real.pi / 2| = α := by
      dsimp [φ]
      rw [sub_right_comm, sub_self, zero_sub, abs_neg, abs_of_nonneg (le_of_lt hα_pos)]
    have hcos_bound : |Real.cos φ - Real.cos (Real.pi / 2)| ≤ α := by
      simpa [hgap_abs] using Real.abs_cos_sub_cos_le φ (Real.pi / 2)
    have hsin_bound : |Real.sin φ - Real.sin (Real.pi / 2)| ≤ α := by
      simpa [hgap_abs] using Real.abs_sin_sub_sin_le φ (Real.pi / 2)
    have hzero : |(0 : ℝ) - 0| ≤ α := by
      simpa using (le_of_lt hα_pos : 0 ≤ α)
    have hcos0 : |Real.cos φ - 0| ≤ α := by
      simpa using hcos_bound
    have hsin1 : |Real.sin φ - 1| ≤ α := by
      simpa using hsin_bound
    simp only [poleCoord, Prod.dist_eq, Real.dist_eq, Real.norm_eq_abs]
    exact max_le hzero (max_le hcos0 hsin1)
  have htop_pole : dist (0, (Real.cos φ, Real.sin φ)) poleCoord < ε / 2 :=
    lt_of_le_of_lt htop_pole_le hα_lt_half
  have hnear_pole : dist x poleCoord < ε := by
    have htri := dist_triangle x (0, (Real.cos φ, Real.sin φ)) poleCoord
    nlinarith
  exact ⟨φ, x, hθφ, hφpi, hsphere, hρ, hψ, hnear_pole⟩

theorem exists_two_step_ew_point_of_gleasonPsiSwap_neg
    {θ ξ η r : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hsphere : ξ ^ 2 + η ^ 2 + r ^ 2 = 1)
    (hneg : gleasonPsiSwap θ ξ η r < 0) :
    ∃ ξ' η' r',
      ξ' ^ 2 + η' ^ 2 + r' ^ 2 = 1 ∧
      (ξ ^ 2 + η ^ 2) * r' = r * (ξ * ξ' + η * η') ∧
      gleasonPsiSwap θ ξ' η' r' = 0 := by
  rcases exists_two_step_ew_point_of_gleasonPsi_neg
      (θ := θ) (ξ := η) (η := ξ) (r := r) hθ0 hθpi
      (by simpa [add_comm] using hsphere) hneg with
    ⟨η', ξ', r', hsphere', hplane, hpsi⟩
  refine ⟨ξ', η', r', ?_, ?_, ?_⟩
  · simpa [add_comm, add_left_comm, add_assoc] using hsphere'
  · simpa [mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc] using hplane
  · simpa [gleasonPsiSwap] using hpsi

theorem exists_sphere_point_with_gleasonPsiSwap_neg
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) :
    ∃ ξ η r, ξ ^ 2 + η ^ 2 + r ^ 2 = 1 ∧ gleasonPsiSwap θ ξ η r < 0 := by
  rcases exists_sphere_point_with_gleasonPsi_neg hθ0 hθpi with
    ⟨η, ξ, r, hsphere, hneg⟩
  exact ⟨ξ, η, r, by simpa [add_comm, add_left_comm, add_assoc] using hsphere,
    by simpa [gleasonPsiSwap] using hneg⟩

theorem exists_sphere_point_with_gleasonPsiSwap_neg_pos
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) :
    ∃ ξ η r, ξ ^ 2 + η ^ 2 + r ^ 2 = 1 ∧ 0 < r ∧ gleasonPsiSwap θ ξ η r < 0 := by
  rcases exists_sphere_point_with_gleasonPsiSwap_neg hθ0 hθpi with
    ⟨ξ, η, r, hsphere, hneg⟩
  by_cases hr : 0 < r
  · exact ⟨ξ, η, r, hsphere, hr, hneg⟩
  · have hsin : 0 < Real.sin θ := by
      have hθpi' : θ < Real.pi := by
        linarith [Real.pi_pos, hθpi]
      exact Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi'
    have hr_ne : r ≠ 0 := by
      intro hr0
      have : 0 ≤ gleasonPsiSwap θ ξ η r := by
        subst hr0
        unfold gleasonPsiSwap gleasonPsi
        nlinarith [hsphere, hsin]
      linarith
    have hrneg : 0 < -r := by
      have : r < 0 := lt_of_le_of_ne (le_of_not_gt hr) hr_ne
      linarith
    refine ⟨-ξ, -η, -r, ?_, hrneg, ?_⟩
    · nlinarith [hsphere]
    · simpa [gleasonPsiSwap, gleasonPsi, mul_comm, mul_left_comm, mul_assoc]
        using hneg

end Thm25

section Thm28

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

def vCoord : ℝ × ℝ × ℝ :=
  (0, (1, 0))

def polarQuarterTurnCoord (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (-x.2.1, (x.1, x.2.2))

def coordSphereSet : Set (ℝ × ℝ × ℝ) :=
  {x | x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1}

def coordSphereImage (u v p : H) : Set H :=
  coordPoint u v p '' coordSphereSet

lemma exists_unit_phase_mul_eq_nonneg_real (z : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ r : ℝ, 0 ≤ r ∧ c * z = (r : ℂ) := by
  by_cases hz : z = 0
  · refine ⟨1, by simp, 0, le_rfl, ?_⟩
    simp [hz]
  · refine ⟨(‖z‖ : ℂ) / z, ?_, ‖z‖, norm_nonneg _, ?_⟩
    · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact div_self (ne_of_gt hzpos)
    · have hz0 : z ≠ 0 := hz
      calc
        ((‖z‖ : ℂ) / z) * z = ((‖z‖ : ℂ) * z) / z := by
          rw [div_mul_eq_mul_div]
        _ = (‖z‖ : ℂ) := by
          field_simp [hz0]

lemma exists_unit_phase_inner_eq_nonneg_real (p x : H) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ r : ℝ, 0 ≤ r ∧ inner (𝕜 := ℂ) p (c • x) = (r : ℂ) := by
  rcases exists_unit_phase_mul_eq_nonneg_real (inner (𝕜 := ℂ) p x) with
    ⟨c, hc, r, hr0, hmul⟩
  refine ⟨c, hc, r, hr0, ?_⟩
  rw [inner_smul_right]
  simpa [mul_comm] using hmul

lemma quarterTurnCLM_coordPoint
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (x : ℝ × ℝ × ℝ) :
    quarterTurnCLM u v (coordPoint u v p x) =
      coordPoint u v p (polarQuarterTurnCoord x) := by
  have hucoord :
      inner (𝕜 := ℂ) u (coordPoint u v p x) = (x.1 : ℂ) := by
    simpa [coordPoint, coordDot] using
      (inner_coordPoint_coordPoint hu hv hp huv hup hvp (1, (0, 0)) x)
  have hvcoord :
      inner (𝕜 := ℂ) v (coordPoint u v p x) = (x.2.1 : ℂ) := by
    simpa [coordPoint, coordDot] using
      (inner_coordPoint_coordPoint hu hv hp huv hup hvp (0, (1, 0)) x)
  rw [quarterTurnCLM_apply, hucoord, hvcoord]
  unfold coordPoint polarQuarterTurnCoord
  abel_nf
  simp [smul_smul, Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc]

def northMeridianCoord (θ : ℝ) : ℝ × ℝ × ℝ :=
  (0, (Real.cos θ, Real.sin θ))

def coordTraceValue
    (μ : FrameFunction H) (u v p : H) : ℝ :=
  μ.μ (GleasonRankOne.projectionOntoSpan (H := H) ({u, v, p} : Set H))

def polarSumValue
    (μ : FrameFunction H) (u v p : H)
    (x : ℝ × ℝ × ℝ) : ℝ :=
  frame_quadratic μ (coordPoint u v p x) +
    frame_quadratic μ (coordPoint u v p (polarQuarterTurnCoord x))

lemma coordPoint_neg_coord
    (u v p : H) (x : ℝ × ℝ × ℝ) :
    coordPoint u v p (-x) = -coordPoint u v p x := by
  simp [coordPoint, neg_smul, add_comm]

lemma polarQuarterTurnCoord_neg
    (x : ℝ × ℝ × ℝ) :
    polarQuarterTurnCoord (-x) = -polarQuarterTurnCoord x := by
  ext <;> simp [polarQuarterTurnCoord]

lemma polarSumValue_neg_coord
    (μ : FrameFunction H) (u v p : H)
    (x : ℝ × ℝ × ℝ) :
    polarSumValue μ u v p (-x) = polarSumValue μ u v p x := by
  unfold polarSumValue
  rw [coordPoint_neg_coord, polarQuarterTurnCoord_neg, coordPoint_neg_coord]
  simp [frame_quadratic_neg]

lemma polarSumValue_neg_neg_frame
    (μ : FrameFunction H) (u v p : H)
    (x : ℝ × ℝ × ℝ) :
    polarSumValue μ (-u) (-v) p x =
      polarSumValue μ u v p (-x.1, (-x.2.1, x.2.2)) := by
  unfold polarSumValue
  congr 1
  · simp [coordPoint, add_assoc, add_left_comm, add_comm]
  · simp [coordPoint, polarQuarterTurnCoord, add_assoc, add_left_comm, add_comm]

lemma polarSumValue_nonneg
    (μ : FrameFunction H) (u v p : H)
    (x : ℝ × ℝ × ℝ) :
    0 ≤ polarSumValue μ u v p x := by
  unfold polarSumValue
  have hx := frame_quadratic_nonneg μ (coordPoint u v p x)
  have hy := frame_quadratic_nonneg μ (coordPoint u v p (polarQuarterTurnCoord x))
  linarith

def northOpenPolarSumSet
    (μ : FrameFunction H) (u v p : H) : Set ℝ :=
  {r : ℝ | ∃ x : ℝ × ℝ × ℝ,
      x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 ∧
      0 < x.2.2 ∧
      polarSumValue μ u v p x = r}

lemma northOpenPolarSumSet_nonempty
    (μ : FrameFunction H) (u v p : H) :
    (northOpenPolarSumSet μ u v p).Nonempty := by
  refine ⟨polarSumValue μ u v p (northMeridianCoord (Real.pi / 4)), ?_⟩
  refine ⟨northMeridianCoord (Real.pi / 4), by
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      norm_num
    norm_num [northMeridianCoord, Real.sin_pi_div_four, Real.cos_pi_div_four]
    nlinarith, ?_, rfl⟩
  have hquarter : 0 < Real.pi / 4 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  have hquarter_lt_pi : Real.pi / 4 < Real.pi := by
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  simpa [northMeridianCoord] using Real.sin_pos_of_pos_of_lt_pi hquarter hquarter_lt_pi

lemma northOpenPolarSumSet_bddBelow
    (μ : FrameFunction H) (u v p : H) :
    BddBelow (northOpenPolarSumSet μ u v p) := by
  refine ⟨0, ?_⟩
  intro r hr
  rcases hr with ⟨x, -, -, rfl⟩
  exact polarSumValue_nonneg μ u v p x

lemma exists_northOpenPolarSum_near_infimum
    (μ : FrameFunction H) (u v p : H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℝ × ℝ × ℝ,
      z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 ∧
      0 < z.2.2 ∧
      polarSumValue μ u v p z <
        sInf (northOpenPolarSumSet μ u v p) + ε := by
  have hne := northOpenPolarSumSet_nonempty μ u v p
  obtain ⟨r, hr_mem, hr_lt⟩ := exists_lt_of_csInf_lt hne
    (by linarith : sInf (northOpenPolarSumSet μ u v p) <
      sInf (northOpenPolarSumSet μ u v p) + ε)
  rcases hr_mem with ⟨z, hz, hzpos, rfl⟩
  exact ⟨z, hz, hzpos, hr_lt⟩

def northOpenNonpolePolarSumSet
    (μ : FrameFunction H) (u v p : H) : Set ℝ :=
  {r : ℝ | ∃ x : ℝ × ℝ × ℝ,
      x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 ∧
      0 < x.2.2 ∧
      horizontalRadius x ≠ 0 ∧
      polarSumValue μ u v p x = r}

lemma northOpenNonpolePolarSumSet_nonempty
    (μ : FrameFunction H) (u v p : H) :
    (northOpenNonpolePolarSumSet μ u v p).Nonempty := by
  refine ⟨polarSumValue μ u v p (northMeridianCoord (Real.pi / 4)), ?_⟩
  refine ⟨northMeridianCoord (Real.pi / 4), by
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      norm_num
    norm_num [northMeridianCoord, Real.sin_pi_div_four, Real.cos_pi_div_four]
    nlinarith, ?_, ?_, rfl⟩
  · have hquarter : 0 < Real.pi / 4 := by
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith
    have hquarter_lt_pi : Real.pi / 4 < Real.pi := by
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith
    simpa [northMeridianCoord] using Real.sin_pos_of_pos_of_lt_pi hquarter hquarter_lt_pi
  · have hcos_pos : 0 < Real.cos (Real.pi / 4) := by
      rw [Real.cos_pi_div_four]
      positivity
    have hpos : 0 < (Real.cos (Real.pi / 4)) ^ 2 := by
      nlinarith
    have hsq :
        horizontalRadius (northMeridianCoord (Real.pi / 4)) ^ 2 =
          (Real.cos (Real.pi / 4)) ^ 2 := by
      rw [horizontalRadius_sq]
      simp [northMeridianCoord]
    intro hzero
    have hsq0 : horizontalRadius (northMeridianCoord (Real.pi / 4)) ^ 2 = 0 := by
      nlinarith
    rw [hsq] at hsq0
    linarith

lemma northOpenNonpolePolarSumSet_bddBelow
    (μ : FrameFunction H) (u v p : H) :
    BddBelow (northOpenNonpolePolarSumSet μ u v p) := by
  refine ⟨0, ?_⟩
  intro r hr
  rcases hr with ⟨x, -, -, -, rfl⟩
  exact polarSumValue_nonneg μ u v p x

lemma exists_northOpenNonpolePolarSum_near_infimum
    (μ : FrameFunction H) (u v p : H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ℝ × ℝ × ℝ,
      z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 ∧
      0 < z.2.2 ∧
      horizontalRadius z ≠ 0 ∧
      polarSumValue μ u v p z <
        sInf (northOpenNonpolePolarSumSet μ u v p) + ε := by
  have hne := northOpenNonpolePolarSumSet_nonempty μ u v p
  obtain ⟨r, hr_mem, hr_lt⟩ := exists_lt_of_csInf_lt hne
    (by linarith : sInf (northOpenNonpolePolarSumSet μ u v p) <
      sInf (northOpenNonpolePolarSumSet μ u v p) + ε)
  rcases hr_mem with ⟨z, hz, hzpos, hρz, rfl⟩
  exact ⟨z, hz, hzpos, hρz, hr_lt⟩

lemma coordPoint_vCoord
    (u v p : H) :
    coordPoint u v p vCoord = v := by
  simp [coordPoint, vCoord]

lemma quarterTurnCLM_u
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0) :
    quarterTurnCLM u v u = v := by
  simpa [coordPoint, coordBase, vCoord, polarQuarterTurnCoord] using
    (quarterTurnCLM_coordPoint hu hv hp huv hup hvp coordBase)

lemma quarterTurnCLM_v
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0) :
    quarterTurnCLM u v v = -u := by
  simpa [coordPoint, vCoord, coordBase, polarQuarterTurnCoord] using
    (quarterTurnCLM_coordPoint hu hv hp huv hup hvp vCoord)

lemma quarterTurnCLM_p
    {u v p : H}
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0) :
    quarterTurnCLM u v p = p := by
  exact quarterTurnCLM_eq_self_of_orthogonal hup hvp

def quarterTurnInvCLM (u v : H) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H
    - (ContinuousLinearMap.smulRight (innerSL ℂ u) u)
    - (ContinuousLinearMap.smulRight (innerSL ℂ v) v)
    - (ContinuousLinearMap.smulRight (innerSL ℂ u) v)
    + (ContinuousLinearMap.smulRight (innerSL ℂ v) u)

lemma quarterTurnInvCLM_apply
    (u v : H) (x : H) :
    quarterTurnInvCLM u v x =
      x - (inner (𝕜 := ℂ) u x : ℂ) • u - (inner (𝕜 := ℂ) v x : ℂ) • v -
        (inner (𝕜 := ℂ) u x : ℂ) • v + (inner (𝕜 := ℂ) v x : ℂ) • u := by
  simp [quarterTurnInvCLM, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

def quarterTurnResidual (u v : H) (x : H) : H :=
  x - (inner (𝕜 := ℂ) u x : ℂ) • u - (inner (𝕜 := ℂ) v x : ℂ) • v

lemma inner_quarterTurnResidual_left
    {u v x : H}
    (hu : ‖u‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    inner (𝕜 := ℂ) u (quarterTurnResidual u v x) = 0 := by
  rw [quarterTurnResidual]
  have huvu : inner (𝕜 := ℂ) u v = 0 := huv
  simp [inner_sub_right, inner_smul_right, huvu, hu, inner_self_eq_norm_sq_to_K]

lemma inner_quarterTurnResidual_right
    {u v x : H}
    (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    inner (𝕜 := ℂ) v (quarterTurnResidual u v x) = 0 := by
  rw [quarterTurnResidual]
  have hvu : inner (𝕜 := ℂ) v u = 0 := by simpa [inner_eq_zero_symm] using huv
  simp [inner_sub_right, inner_smul_right, hvu, hv, inner_self_eq_norm_sq_to_K]

lemma quarterTurnCLM_eq_residual_rotate
    (u v : H) (x : H) :
    quarterTurnCLM u v x =
      quarterTurnResidual u v x +
        (inner (𝕜 := ℂ) u x : ℂ) • v - (inner (𝕜 := ℂ) v x : ℂ) • u := by
  rw [quarterTurnCLM_apply, quarterTurnResidual]

lemma quarterTurnInvCLM_eq_residual_rotate
    (u v : H) (x : H) :
    quarterTurnInvCLM u v x =
      quarterTurnResidual u v x -
        (inner (𝕜 := ℂ) u x : ℂ) • v + (inner (𝕜 := ℂ) v x : ℂ) • u := by
  rw [quarterTurnInvCLM_apply, quarterTurnResidual]

lemma inner_quarterTurnResidual_quarterTurnResidual
    {u v x y : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) :
    inner (𝕜 := ℂ) (quarterTurnResidual u v x) (quarterTurnResidual u v y) =
      inner (𝕜 := ℂ) x y -
        star (inner (𝕜 := ℂ) u x) * inner (𝕜 := ℂ) u y -
        star (inner (𝕜 := ℂ) v x) * inner (𝕜 := ℂ) v y := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by simpa [inner_eq_zero_symm] using huv
  have hres_u : inner (𝕜 := ℂ) (quarterTurnResidual u v x) u = 0 := by
    simpa [inner_eq_zero_symm] using
      (inner_quarterTurnResidual_left (x := x) hu huv)
  have hres_v : inner (𝕜 := ℂ) (quarterTurnResidual u v x) v = 0 := by
    simpa [inner_eq_zero_symm] using
      (inner_quarterTurnResidual_right (x := x) hv huv)
  calc
    inner (𝕜 := ℂ) (quarterTurnResidual u v x) (quarterTurnResidual u v y)
        = inner (𝕜 := ℂ) (quarterTurnResidual u v x)
            (y - (inner (𝕜 := ℂ) u y : ℂ) • u - (inner (𝕜 := ℂ) v y : ℂ) • v) := rfl
    _ = inner (𝕜 := ℂ) (quarterTurnResidual u v x) y := by
          simp [inner_sub_right, inner_smul_right, hres_u, hres_v]
    _ = inner (𝕜 := ℂ) x y -
          star (inner (𝕜 := ℂ) u x) * inner (𝕜 := ℂ) u y -
          star (inner (𝕜 := ℂ) v x) * inner (𝕜 := ℂ) v y := by
          simp [quarterTurnResidual, inner_sub_left, inner_smul_left, huv, hvu, hu, hv,
            inner_self_eq_norm_sq_to_K, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc, mul_left_comm, mul_comm]

lemma inner_quarterTurnCLM_map
    {u v : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (x y : H) :
    inner (𝕜 := ℂ) (quarterTurnCLM u v x) (quarterTurnCLM u v y) =
      inner (𝕜 := ℂ) x y := by
  have hvu : inner (𝕜 := ℂ) v u = 0 := by simpa [inner_eq_zero_symm] using huv
  have hres_u : inner (𝕜 := ℂ) (quarterTurnResidual u v x) u = 0 := by
    simpa [inner_eq_zero_symm] using
      (inner_quarterTurnResidual_left (x := x) hu huv)
  have hres_v : inner (𝕜 := ℂ) (quarterTurnResidual u v x) v = 0 := by
    simpa [inner_eq_zero_symm] using
      (inner_quarterTurnResidual_right (x := x) hv huv)
  have hmain :
      inner (𝕜 := ℂ) (quarterTurnCLM u v x) (quarterTurnCLM u v y) =
        inner (𝕜 := ℂ) (quarterTurnResidual u v x) (quarterTurnResidual u v y) +
          star (inner (𝕜 := ℂ) u x) * inner (𝕜 := ℂ) u y +
          star (inner (𝕜 := ℂ) v x) * inner (𝕜 := ℂ) v y := by
    simp [quarterTurnCLM_eq_residual_rotate, sub_eq_add_neg, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, huv, hvu, hu, hv, hres_u, hres_v,
      inner_self_eq_norm_sq_to_K, add_assoc, add_left_comm, add_comm, mul_assoc,
      mul_left_comm, mul_comm, inner_quarterTurnResidual_left, inner_quarterTurnResidual_right]
  have hu_res : inner (𝕜 := ℂ) u (quarterTurnResidual u v y) = 0 :=
    inner_quarterTurnResidual_left hu huv
  have hv_res : inner (𝕜 := ℂ) v (quarterTurnResidual u v y) = 0 :=
    inner_quarterTurnResidual_right hv huv
  rw [hmain, inner_quarterTurnResidual_quarterTurnResidual hu hv huv]
  ring

lemma inner_u_quarterTurnCLM
    {u v x : H}
    (hu : ‖u‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    inner (𝕜 := ℂ) u (quarterTurnCLM u v x) = - inner (𝕜 := ℂ) v x := by
  rw [quarterTurnCLM_eq_residual_rotate]
  have hu_res : inner (𝕜 := ℂ) u (quarterTurnResidual u v x) = 0 :=
    inner_quarterTurnResidual_left hu huv
  simp [inner_add_right, inner_sub_right, inner_smul_right, hu_res, huv, hu,
    inner_self_eq_norm_sq_to_K]

lemma inner_v_quarterTurnCLM
    {u v x : H}
    (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    inner (𝕜 := ℂ) v (quarterTurnCLM u v x) = inner (𝕜 := ℂ) u x := by
  rw [quarterTurnCLM_eq_residual_rotate]
  have hvu : inner (𝕜 := ℂ) v u = 0 := by simpa [inner_eq_zero_symm] using huv
  have hv_res : inner (𝕜 := ℂ) v (quarterTurnResidual u v x) = 0 :=
    inner_quarterTurnResidual_right hv huv
  simp [inner_add_right, inner_sub_right, inner_smul_right, hv_res, hvu, hv,
    inner_self_eq_norm_sq_to_K]

lemma inner_u_quarterTurnInvCLM
    {u v x : H}
    (hu : ‖u‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    inner (𝕜 := ℂ) u (quarterTurnInvCLM u v x) = inner (𝕜 := ℂ) v x := by
  rw [quarterTurnInvCLM_eq_residual_rotate]
  have hu_res : inner (𝕜 := ℂ) u (quarterTurnResidual u v x) = 0 :=
    inner_quarterTurnResidual_left hu huv
  simp [inner_sub_right, inner_add_right, inner_smul_right, hu_res, huv, hu,
    inner_self_eq_norm_sq_to_K]

lemma inner_v_quarterTurnInvCLM
    {u v x : H}
    (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    inner (𝕜 := ℂ) v (quarterTurnInvCLM u v x) = - inner (𝕜 := ℂ) u x := by
  rw [quarterTurnInvCLM_eq_residual_rotate]
  have hvu : inner (𝕜 := ℂ) v u = 0 := by simpa [inner_eq_zero_symm] using huv
  have hv_res : inner (𝕜 := ℂ) v (quarterTurnResidual u v x) = 0 :=
    inner_quarterTurnResidual_right hv huv
  simp [inner_sub_right, inner_add_right, inner_smul_right, hv_res, hvu, hv,
    inner_self_eq_norm_sq_to_K]

lemma quarterTurnResidual_quarterTurnCLM
    {u v x : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) :
    quarterTurnResidual u v (quarterTurnCLM u v x) = quarterTurnResidual u v x := by
  have huJ : inner (𝕜 := ℂ) u
      (quarterTurnResidual u v x + (inner (𝕜 := ℂ) u x : ℂ) • v -
        (inner (𝕜 := ℂ) v x : ℂ) • u) = - inner (𝕜 := ℂ) v x := by
    simpa [quarterTurnCLM_eq_residual_rotate] using
      (inner_u_quarterTurnCLM (x := x) hu huv)
  have hvJ : inner (𝕜 := ℂ) v
      (quarterTurnResidual u v x + (inner (𝕜 := ℂ) u x : ℂ) • v -
        (inner (𝕜 := ℂ) v x : ℂ) • u) = inner (𝕜 := ℂ) u x := by
    simpa [quarterTurnCLM_eq_residual_rotate] using
      (inner_v_quarterTurnCLM (x := x) hv huv)
  rw [quarterTurnResidual, quarterTurnCLM_eq_residual_rotate, huJ, hvJ, quarterTurnResidual]
  simp [sub_eq_add_neg, smul_smul, mul_assoc]

lemma quarterTurnResidual_quarterTurnInvCLM
    {u v x : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) :
    quarterTurnResidual u v (quarterTurnInvCLM u v x) = quarterTurnResidual u v x := by
  have huJ : inner (𝕜 := ℂ) u
      (quarterTurnResidual u v x - (inner (𝕜 := ℂ) u x : ℂ) • v +
        (inner (𝕜 := ℂ) v x : ℂ) • u) = inner (𝕜 := ℂ) v x := by
    simpa [quarterTurnInvCLM_eq_residual_rotate] using
      (inner_u_quarterTurnInvCLM (x := x) hu huv)
  have hvJ : inner (𝕜 := ℂ) v
      (quarterTurnResidual u v x - (inner (𝕜 := ℂ) u x : ℂ) • v +
        (inner (𝕜 := ℂ) v x : ℂ) • u) = - inner (𝕜 := ℂ) u x := by
    simpa [quarterTurnInvCLM_eq_residual_rotate] using
      (inner_v_quarterTurnInvCLM (x := x) hv huv)
  rw [quarterTurnResidual, quarterTurnInvCLM_eq_residual_rotate, huJ, hvJ, quarterTurnResidual]
  simp [sub_eq_add_neg, smul_smul, mul_assoc]

lemma quarterTurnCLM_quarterTurnInvCLM
    {u v x : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) :
    quarterTurnCLM u v (quarterTurnInvCLM u v x) = x := by
  rw [quarterTurnCLM_eq_residual_rotate]
  have huinv :
      inner (𝕜 := ℂ) u (quarterTurnInvCLM u v x) = inner (𝕜 := ℂ) v x := by
    exact inner_u_quarterTurnInvCLM hu huv
  have hvinv :
      inner (𝕜 := ℂ) v (quarterTurnInvCLM u v x) = - inner (𝕜 := ℂ) u x := by
    exact inner_v_quarterTurnInvCLM hv huv
  rw [quarterTurnResidual_quarterTurnInvCLM hu hv huv, huinv, hvinv]
  simp [quarterTurnResidual, sub_eq_add_neg, smul_smul, mul_assoc]

def quarterTurnLinearIsometryEquiv
    (u v : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) :
    H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective
    ((quarterTurnCLM u v).toLinearMap.isometryOfInner
      (inner_quarterTurnCLM_map hu hv huv))
    (by
      intro x
      refine ⟨quarterTurnInvCLM u v x, ?_⟩
      exact quarterTurnCLM_quarterTurnInvCLM hu hv huv)

lemma quarterTurnLinearIsometryEquiv_apply
    {u v : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (x : H) :
    quarterTurnLinearIsometryEquiv u v hu hv huv x = quarterTurnCLM u v x := by
  rfl

namespace Projection

def conjLIE (e : H ≃ₗᵢ[ℂ] H) (P : Projection H) : Projection H := by
  let eCLM : H →L[ℂ] H := e.toContinuousLinearEquiv.toContinuousLinearMap
  let eSymmCLM : H →L[ℂ] H := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨
    (eCLM.comp P.1).comp eSymmCLM,
    ?_, ?_⟩
  ·
    ext x
    have hPP : P.1 (P.1 (e.symm x)) = P.1 (e.symm x) := by
      change ((P.1 * P.1) (e.symm x)) = P.1 (e.symm x)
      rw [P.2.1]
    simpa [eCLM, eSymmCLM, ContinuousLinearMap.mul_apply, hPP]
  ·
    intro x y
    have h := P.inner_err (e.symm x) (e.symm y)
    have hsub : y - e (P.1 (e.symm y)) = e (e.symm y - P.1 (e.symm y)) := by
      simpa using (e.map_sub (e.symm y) (P.1 (e.symm y)))
    calc
      inner (𝕜 := ℂ)
          (e (P.1 (e.symm x)))
          (y - e (P.1 (e.symm y)))
          =
        inner (𝕜 := ℂ)
          (e (P.1 (e.symm x)))
          (e (e.symm y - P.1 (e.symm y))) := by
            rw [hsub]
      _ =
        inner (𝕜 := ℂ)
          (P.1 (e.symm x))
          (e.symm y - P.1 (e.symm y)) := by
            exact
              (LinearIsometryEquiv.inner_map_map e
                (P.1 (e.symm x)) (e.symm y - P.1 (e.symm y)))
      _ = 0 := h

lemma conjLIE_apply
    (e : H ≃ₗᵢ[ℂ] H) (P : Projection H) (x : H) :
    (conjLIE e P).1 x = e (P.1 (e.symm x)) := by
  rfl

lemma orthogonal_conjLIE
    (e : H ≃ₗᵢ[ℂ] H) {P Q : Projection H}
    (h : Projection.orthogonal P Q) :
    Projection.orthogonal (conjLIE e P) (conjLIE e Q) := by
  ext x
  have h0 := congrArg (fun T : H →L[ℂ] H => e (T (e.symm x))) h
  simpa [conjLIE, ContinuousLinearMap.mul_apply] using h0

lemma conjLIE_add
    (e : H ≃ₗᵢ[ℂ] H) (P Q : Projection H)
    (h : Projection.orthogonal P Q) :
    conjLIE e (Projection.add P Q h) =
      Projection.add (conjLIE e P) (conjLIE e Q) (orthogonal_conjLIE e h) := by
  apply Subtype.ext
  ext x
  simp [conjLIE, Projection.add, ContinuousLinearMap.comp_apply]

lemma conjLIE_one
    (e : H ≃ₗᵢ[ℂ] H) :
    conjLIE e Projection.one = Projection.one := by
  apply Subtype.ext
  ext x
  simp [conjLIE, Projection.one]

lemma conjLIE_projectionOntoSubmodule
    (e : H ≃ₗᵢ[ℂ] H) (K : Submodule ℂ H) :
    conjLIE e (GleasonRankOne.projectionOntoSubmodule (H := H) K) =
      GleasonRankOne.projectionOntoSubmodule (H := H)
        (K.map (e.toLinearEquiv : H →ₗ[ℂ] H)) := by
  apply Subtype.ext
  ext x
  simpa [conjLIE, GleasonRankOne.projectionOntoSubmodule,
    ContinuousLinearMap.comp_apply] using
    (Submodule.starProjection_map_apply (f := e) (p := K) (x := x)).symm

lemma conjLIE_rankOneProjection
    (e : H ≃ₗᵢ[ℂ] H) (x : H) (hx : x ≠ 0) :
    conjLIE e (RankOne.rankOneProjection (H := H) x hx) =
      RankOne.rankOneProjection (H := H) (e x)
        (by
          intro h0
          have hx0 : x = 0 := (e.map_eq_zero_iff).mp h0
          exact hx hx0) := by
  apply Subtype.ext
  ext y
  have hmap :
      ((ℂ ∙ x : Submodule ℂ H).map (e.toLinearEquiv : H →ₗ[ℂ] H)) =
        (ℂ ∙ e x : Submodule ℂ H) := by
    simpa [Set.image_singleton] using
      (Submodule.map_span (f := (e.toLinearEquiv : H →ₗ[ℂ] H)) ({x} : Set H))
  calc
    (Projection.conjLIE e (RankOne.rankOneProjection (H := H) x hx)).1 y
        = e (((ℂ ∙ x : Submodule ℂ H).starProjection) (e.symm y)) := by
            simp [Projection.conjLIE, RankOne.rankOneProjection, ContinuousLinearMap.comp_apply]
    _ = (((ℂ ∙ x : Submodule ℂ H).map (e.toLinearEquiv : H →ₗ[ℂ] H)).starProjection y) := by
          simpa using
            (Submodule.starProjection_map_apply (f := e) (p := (ℂ ∙ x : Submodule ℂ H))
              (x := y)).symm
    _ = ((ℂ ∙ e x : Submodule ℂ H).starProjection y) := by
          simpa [hmap]
    _ = (RankOne.rankOneProjection (H := H) (e x)
          (by
            intro h0
            exact hx ((e.map_eq_zero_iff).mp h0))).1 y := by
          simp [RankOne.rankOneProjection]

end Projection

def rotatedFrameFunction
    (μ : FrameFunction H) (e : H ≃ₗᵢ[ℂ] H) : FrameFunction H where
  μ := fun P => μ.μ (Projection.conjLIE e P)
  nonneg := by
    intro P
    exact μ.nonneg _
  additive := by
    intro P Q h
    simpa [Projection.conjLIE_add (H := H) e P Q h] using
      μ.additive (Projection.conjLIE e P) (Projection.conjLIE e Q)
        (Projection.orthogonal_conjLIE (H := H) e h)
  normalized := by
    simpa [Projection.conjLIE_one (H := H) e] using μ.normalized

def averageFrameFunction
    (μ ν : FrameFunction H) : FrameFunction H where
  μ := fun P => (μ.μ P + ν.μ P) / 2
  nonneg := by
    intro P
    have hμ := μ.nonneg P
    have hν := ν.nonneg P
    linarith
  additive := by
    intro P Q h
    rw [μ.additive P Q h, ν.additive P Q h]
    ring
  normalized := by
    change (μ.μ Projection.one + ν.μ Projection.one) / 2 = 1
    simp [μ.normalized, ν.normalized]

lemma frame_quadratic_rotatedFrameFunction
    (μ : FrameFunction H) (e : H ≃ₗᵢ[ℂ] H) (x : H) :
    frame_quadratic (H := H) (rotatedFrameFunction μ e) x =
      frame_quadratic (H := H) μ (e x) := by
  by_cases hx : x = 0
  · simp [frame_quadratic, hx]
  · have hex : e x ≠ 0 := by
      intro h0
      exact hx (e.injective (by simpa using h0))
    simp [frame_quadratic, hx, hex, rotatedFrameFunction,
      Projection.conjLIE_rankOneProjection, e.norm_map]

lemma frame_quadratic_averageFrameFunction
    (μ ν : FrameFunction H) (x : H) :
    frame_quadratic (H := H) (averageFrameFunction μ ν) x =
      (frame_quadratic (H := H) μ x + frame_quadratic (H := H) ν x) / 2 := by
  by_cases hx : x = 0
  · simp [frame_quadratic, hx, averageFrameFunction]
  · rw [frame_quadratic, frame_quadratic, frame_quadratic]
    simp [hx, averageFrameFunction]
    ring

def quarterTurnRotatedFrameFunction
    (μ : FrameFunction H) (u v : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) : FrameFunction H :=
  rotatedFrameFunction μ (quarterTurnLinearIsometryEquiv u v hu hv huv)

def quarterTurnAverageFrameFunction
    (μ : FrameFunction H) (u v : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) : FrameFunction H :=
  averageFrameFunction μ (quarterTurnRotatedFrameFunction μ u v hu hv huv)

lemma frame_quadratic_quarterTurnRotated_coordPoint
    (μ : FrameFunction H) {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (x : ℝ × ℝ × ℝ) :
    frame_quadratic (H := H)
        (quarterTurnRotatedFrameFunction μ u v hu hv huv)
        (coordPoint u v p x) =
      frame_quadratic (H := H) μ
        (coordPoint u v p (polarQuarterTurnCoord x)) := by
  have hrot :=
    frame_quadratic_rotatedFrameFunction
      (μ := μ)
      (e := quarterTurnLinearIsometryEquiv u v hu hv huv)
      (x := coordPoint u v p x)
  calc
    frame_quadratic (H := H)
        (quarterTurnRotatedFrameFunction μ u v hu hv huv)
        (coordPoint u v p x)
        =
      frame_quadratic (H := H) μ
        ((quarterTurnLinearIsometryEquiv u v hu hv huv)
          (coordPoint u v p x)) := by
            simpa [quarterTurnRotatedFrameFunction] using hrot
    _ = frame_quadratic (H := H) μ
          (quarterTurnCLM u v (coordPoint u v p x)) := by
            rw [quarterTurnLinearIsometryEquiv_apply hu hv huv]
    _ = frame_quadratic (H := H) μ
          (coordPoint u v p (polarQuarterTurnCoord x)) := by
            rw [quarterTurnCLM_coordPoint hu hv hp huv hup hvp x]

lemma two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
    (μ : FrameFunction H) {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (x : ℝ × ℝ × ℝ) :
    2 * frame_quadratic (H := H)
        (quarterTurnAverageFrameFunction μ u v hu hv huv)
        (coordPoint u v p x) =
      polarSumValue μ u v p x := by
  have havg :=
    frame_quadratic_averageFrameFunction
      (μ := μ)
      (ν := quarterTurnRotatedFrameFunction μ u v hu hv huv)
      (x := coordPoint u v p x)
  have havg' :
      frame_quadratic (H := H)
          (quarterTurnAverageFrameFunction μ u v hu hv huv)
          (coordPoint u v p x) =
        (frame_quadratic (H := H) μ (coordPoint u v p x) +
          frame_quadratic (H := H)
            (quarterTurnRotatedFrameFunction μ u v hu hv huv)
            (coordPoint u v p x)) / 2 := by
    simpa [quarterTurnAverageFrameFunction] using havg
  calc
    2 * frame_quadratic (H := H)
        (quarterTurnAverageFrameFunction μ u v hu hv huv)
        (coordPoint u v p x)
        =
      2 * ((frame_quadratic (H := H) μ (coordPoint u v p x) +
          frame_quadratic (H := H)
            (quarterTurnRotatedFrameFunction μ u v hu hv huv)
            (coordPoint u v p x)) / 2) := by
              rw [havg']
    _ = polarSumValue μ u v p x := by
          rw [frame_quadratic_quarterTurnRotated_coordPoint
            (μ := μ) hu hv hp huv hup hvp x]
          unfold polarSumValue
          ring

lemma coordPoint_mem_span
    (u v p : H) (x : ℝ × ℝ × ℝ) :
    coordPoint u v p x ∈ Submodule.span ℂ ({u, v, p} : Set H) := by
  let K : Submodule ℂ H := Submodule.span ℂ ({u, v, p} : Set H)
  have hu_mem : ((x.1 : ℂ) • u) ∈ K := by
    exact K.smul_mem _
      (Submodule.subset_span (by simp [Set.mem_insert_iff]))
  have hv_mem : ((x.2.1 : ℂ) • v) ∈ K := by
    exact K.smul_mem _
      (Submodule.subset_span (by simp [Set.mem_insert_iff]))
  have hp_mem : ((x.2.2 : ℂ) • p) ∈ K := by
    exact K.smul_mem _
      (Submodule.subset_span (by simp [Set.mem_insert_iff]))
  have huv_mem : ((x.1 : ℂ) • u + (x.2.1 : ℂ) • v) ∈ K := K.add_mem hu_mem hv_mem
  simpa [coordPoint, add_assoc] using K.add_mem huv_mem hp_mem

lemma polarQuarterTurnCoord_sq_sum
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    (polarQuarterTurnCoord x).1 ^ 2 +
        (polarQuarterTurnCoord x).2.1 ^ 2 +
        (polarQuarterTurnCoord x).2.2 ^ 2 = 1 := by
  unfold polarQuarterTurnCoord
  nlinarith

lemma horizontalRadius_polarQuarterTurnCoord
    (x : ℝ × ℝ × ℝ) :
    horizontalRadius (polarQuarterTurnCoord x) = horizontalRadius x := by
  unfold horizontalRadius polarQuarterTurnCoord
  congr 1
  ring

lemma northMeridianCoord_sq_sum
    (θ : ℝ) :
    (northMeridianCoord θ).1 ^ 2 +
        (northMeridianCoord θ).2.1 ^ 2 +
        (northMeridianCoord θ).2.2 ^ 2 = 1 := by
  simp [northMeridianCoord, Real.sin_sq_add_cos_sq θ]

lemma northMeridianCoord_horizontalRadius_ne_zero
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) :
    horizontalRadius (northMeridianCoord θ) ≠ 0 := by
  intro hρ
  have hcos_pos : 0 < Real.cos θ := by
    refine Real.cos_pos_of_mem_Ioo ?_
    constructor
    · nlinarith [Real.pi_pos]
    · exact hθpi
  have hsq :
      horizontalRadius (northMeridianCoord θ) ^ 2 = 0 := by
    rw [hρ]
    ring
  have hcos_sq : Real.cos θ ^ 2 = 0 := by
    simpa [northMeridianCoord, horizontalRadius_sq] using hsq
  nlinarith

def psiCenterCoord (θ : ℝ) : ℝ × ℝ × ℝ :=
  (0, (Real.cos θ / 2, Real.sqrt (1 - (Real.cos θ / 2) ^ 2)))

lemma psiCenterCoord_sq_sum
    (θ : ℝ) :
    (psiCenterCoord θ).1 ^ 2 +
        (psiCenterCoord θ).2.1 ^ 2 +
        (psiCenterCoord θ).2.2 ^ 2 = 1 := by
  have hnonneg : 0 ≤ 1 - (Real.cos θ / 2) ^ 2 := by
    have hcos_sq := Real.cos_sq_le_one θ
    nlinarith
  dsimp [psiCenterCoord]
  rw [Real.sq_sqrt hnonneg]
  ring

lemma psiCenterCoord_third_pos
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) :
    0 < (psiCenterCoord θ).2.2 := by
  have harg_pos : 0 < 1 - (Real.cos θ / 2) ^ 2 := by
    have hcos_sq := Real.cos_sq_le_one θ
    nlinarith
  dsimp [psiCenterCoord]
  exact Real.sqrt_pos.2 harg_pos

lemma psiCenterCoord_third_gt_half
    (θ : ℝ) :
    (1 : ℝ) / 2 < (psiCenterCoord θ).2.2 := by
  have harg : ((1 : ℝ) / 2) ^ 2 < 1 - (Real.cos θ / 2) ^ 2 := by
    have hcos_sq := Real.cos_sq_le_one θ
    nlinarith
  dsimp [psiCenterCoord]
  exact (Real.lt_sqrt (by norm_num : 0 ≤ (1 : ℝ) / 2)).mpr harg

lemma horizontalRadius_psiCenterCoord_ne_zero
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) :
    horizontalRadius (psiCenterCoord θ) ≠ 0 := by
  have hcos_pos : 0 < Real.cos θ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθpi⟩
  intro hρ
  have hsq : horizontalRadius (psiCenterCoord θ) ^ 2 = 0 := by rw [hρ]; ring
  have hcos_sq : (Real.cos θ / 2) ^ 2 = 0 := by
    simpa [psiCenterCoord, horizontalRadius_sq] using hsq
  nlinarith

lemma gleasonPsiSwap_psiCenterCoord_neg
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) :
    Thm25.gleasonPsiSwap θ (psiCenterCoord θ).1
      (psiCenterCoord θ).2.1 (psiCenterCoord θ).2.2 < 0 := by
  have hθltπ : θ < Real.pi := by linarith [Real.pi_pos, hθpi]
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθltπ
  have hcos_pos : 0 < Real.cos θ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθpi⟩
  let c : ℝ := Real.cos θ
  let s : ℝ := Real.sin θ
  let r : ℝ := Real.sqrt (1 - (c / 2) ^ 2)
  have hcpos : 0 < c := hcos_pos
  have hspos : 0 < s := hsin_pos
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.sqrt_nonneg _
  have harg_nonneg : 0 ≤ 1 - (c / 2) ^ 2 := by
    have hcos_sq := Real.cos_sq_le_one θ
    dsimp [c]
    nlinarith
  have hr_sq : r ^ 2 = 1 - (c / 2) ^ 2 := by
    dsimp [r]
    exact Real.sq_sqrt harg_nonneg
  have hs_sq : s ^ 2 + c ^ 2 = 1 := by
    dsimp [s, c]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hs_half_lt_r : s / 2 < r := by
    by_contra hnot
    have hr_le : r ≤ s / 2 := le_of_not_gt hnot
    have hsq_le : r ^ 2 ≤ (s / 2) ^ 2 := by nlinarith
    have hsq_gt : (s / 2) ^ 2 < r ^ 2 := by
      rw [hr_sq]
      nlinarith [hs_sq]
    linarith
  dsimp [psiCenterCoord, Thm25.gleasonPsiSwap, Thm25.gleasonPsi, c, s, r] at *
  nlinarith

lemma gleasonPsiSwap_psiCenterCoord_le_neg_cos_sq
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) :
    Thm25.gleasonPsiSwap θ (psiCenterCoord θ).1
      (psiCenterCoord θ).2.1 (psiCenterCoord θ).2.2 ≤
        -(Real.cos θ ^ 2) / 16 := by
  have hθltπ : θ < Real.pi := by linarith [Real.pi_pos, hθpi]
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθltπ
  have hcos_pos : 0 < Real.cos θ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθpi⟩
  let c : ℝ := Real.cos θ
  let s : ℝ := Real.sin θ
  let r : ℝ := Real.sqrt (1 - (c / 2) ^ 2)
  have hcpos : 0 < c := hcos_pos
  have hspos : 0 < s := hsin_pos
  have hsle : s ≤ 1 := by
    simpa [s] using Real.sin_le_one θ
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.sqrt_nonneg _
  have harg_nonneg : 0 ≤ 1 - (c / 2) ^ 2 := by
    have hcos_sq := Real.cos_sq_le_one θ
    dsimp [c]
    nlinarith
  have hr_sq : r ^ 2 = 1 - (c / 2) ^ 2 := by
    dsimp [r]
    exact Real.sq_sqrt harg_nonneg
  have hs_sq : s ^ 2 + c ^ 2 = 1 := by
    dsimp [s, c]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hgap : s / 2 + (1 : ℝ) / 8 < r := by
    by_contra hnot
    have hr_le : r ≤ s / 2 + (1 : ℝ) / 8 := le_of_not_gt hnot
    have hlhs_nonneg : 0 ≤ s / 2 + (1 : ℝ) / 8 := by nlinarith
    have hsq_le : r ^ 2 ≤ (s / 2 + (1 : ℝ) / 8) ^ 2 := by nlinarith
    have hsq_gt : (s / 2 + (1 : ℝ) / 8) ^ 2 < r ^ 2 := by
      rw [hr_sq]
      nlinarith [hs_sq, hsle]
    linarith
  have hcoeff : s / 4 - r / 2 ≤ -(1 : ℝ) / 16 := by
    nlinarith
  dsimp [psiCenterCoord, Thm25.gleasonPsiSwap, Thm25.gleasonPsi, c, s, r] at *
  nlinarith

lemma gleasonPsiSwap_midMeridianCoord_eq
    (θ : ℝ) :
    Thm25.gleasonPsiSwap θ
        (northMeridianCoord ((θ + Real.pi / 2) / 2)).1
        (northMeridianCoord ((θ + Real.pi / 2) / 2)).2.1
        (northMeridianCoord ((θ + Real.pi / 2) / 2)).2.2 =
      -Real.sin ((Real.pi / 2 - θ) / 2) ^ 2 := by
  let φ : ℝ := (θ + Real.pi / 2) / 2
  have hphi :
      Thm25.gleasonPsiSwap θ
          (northMeridianCoord φ).1
          (northMeridianCoord φ).2.1
          (northMeridianCoord φ).2.2 =
        Real.cos φ * Real.sin (θ - φ) := by
    simpa [Thm25.gleasonPsiSwap, northMeridianCoord] using
      Thm25.gleasonPsi_meridian θ φ
  have hcos :
      Real.cos φ = Real.sin ((Real.pi / 2 - θ) / 2) := by
    dsimp [φ]
    rw [show (θ + Real.pi / 2) / 2 = Real.pi / 2 - ((Real.pi / 2 - θ) / 2) by ring]
    rw [Real.cos_pi_div_two_sub]
  have hsin :
      Real.sin (θ - φ) = -Real.sin ((Real.pi / 2 - θ) / 2) := by
    dsimp [φ]
    have hrewrite : θ - (θ + Real.pi / 2) / 2 = -((Real.pi / 2 - θ) / 2) := by ring
    rw [hrewrite, Real.sin_neg]
  rw [show ((θ + Real.pi / 2) / 2) = φ by rfl]
  rw [hphi, hcos, hsin]
  ring

lemma gleasonPsiSwap_midMeridianCoord_le_neg_gap_sq
    {θ τ : ℝ}
    (hθ0 : 0 < θ)
    (hτ0 : 0 < τ)
    (hθτ : θ ≤ Real.pi / 2 - τ) :
    Thm25.gleasonPsiSwap θ
        (northMeridianCoord ((θ + Real.pi / 2) / 2)).1
        (northMeridianCoord ((θ + Real.pi / 2) / 2)).2.1
        (northMeridianCoord ((θ + Real.pi / 2) / 2)).2.2 ≤
      -(Real.sin (τ / 2)) ^ 2 := by
  rw [gleasonPsiSwap_midMeridianCoord_eq θ]
  have harg_ge : τ / 2 ≤ (Real.pi / 2 - θ) / 2 := by
    nlinarith
  have htheta_le : θ ≤ Real.pi / 2 := by linarith
  have hmem1 : τ / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have hnonneg : 0 ≤ τ / 2 := by positivity
      nlinarith [Real.pi_pos]
    · have htau_le : τ ≤ Real.pi / 2 := by linarith
      nlinarith [htau_le]
  have hmem2 : (Real.pi / 2 - θ) / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have hnonneg : 0 ≤ (Real.pi / 2 - θ) / 2 := by nlinarith
      nlinarith [Real.pi_pos, hnonneg]
    · nlinarith [Real.pi_pos, htheta_le]
  have hsin_mono :
      Real.sin (τ / 2) ≤ Real.sin ((Real.pi / 2 - θ) / 2) := by
    exact Real.monotoneOn_sin hmem1 hmem2 harg_ge
  have hsin_nonneg : 0 ≤ Real.sin (τ / 2) := by
    have htau_le : τ ≤ Real.pi / 2 := by linarith
    have hlt_pi : τ / 2 < Real.pi := by
      nlinarith [htau_le, Real.pi_pos]
    exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by positivity) hlt_pi)
  have hsq :
      Real.sin (τ / 2) ^ 2 ≤ Real.sin ((Real.pi / 2 - θ) / 2) ^ 2 := by
    nlinarith
  linarith

lemma coord_fst_abs_sub_lt_of_dist_lt
    {x y : ℝ × ℝ × ℝ} {δ : ℝ} (h : dist x y < δ) :
    |x.1 - y.1| < δ := by
  have hdist :
      dist x y =
        max |x.1 - y.1| (max |x.2.1 - y.2.1| |x.2.2 - y.2.2|) := by
    rcases x with ⟨x1, x23⟩
    rcases x23 with ⟨x2, x3⟩
    rcases y with ⟨y1, y23⟩
    rcases y23 with ⟨y2, y3⟩
    simp [Prod.dist_eq, Prod.norm_def, Real.dist_eq, Real.norm_eq_abs]
  exact lt_of_le_of_lt (by rw [hdist]; exact le_max_left _ _) h

lemma coord_snd_fst_abs_sub_lt_of_dist_lt
    {x y : ℝ × ℝ × ℝ} {δ : ℝ} (h : dist x y < δ) :
    |x.2.1 - y.2.1| < δ := by
  have hdist :
      dist x y =
        max |x.1 - y.1| (max |x.2.1 - y.2.1| |x.2.2 - y.2.2|) := by
    rcases x with ⟨x1, x23⟩
    rcases x23 with ⟨x2, x3⟩
    rcases y with ⟨y1, y23⟩
    rcases y23 with ⟨y2, y3⟩
    simp [Prod.dist_eq, Prod.norm_def, Real.dist_eq, Real.norm_eq_abs]
  exact lt_of_le_of_lt (by
    rw [hdist]
    exact le_trans (le_max_left _ _) (le_max_right _ _)) h

lemma coord_snd_snd_abs_sub_lt_of_dist_lt
    {x y : ℝ × ℝ × ℝ} {δ : ℝ} (h : dist x y < δ) :
    |x.2.2 - y.2.2| < δ := by
  have hdist :
      dist x y =
        max |x.1 - y.1| (max |x.2.1 - y.2.1| |x.2.2 - y.2.2|) := by
    rcases x with ⟨x1, x23⟩
    rcases x23 with ⟨x2, x3⟩
    rcases y with ⟨y1, y23⟩
    rcases y23 with ⟨y2, y3⟩
    simp [Prod.dist_eq, Prod.norm_def, Real.dist_eq, Real.norm_eq_abs]
  exact lt_of_le_of_lt (by
    rw [hdist]
    exact le_trans (le_max_right _ _) (le_max_right _ _)) h

lemma abs_coord_le_one_of_sq_sum
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    |x.1| ≤ 1 ∧ |x.2.1| ≤ 1 ∧ |x.2.2| ≤ 1 := by
  have hx1sq : x.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.2.1, sq_nonneg x.2.2, hx]
  have hx2sq : x.2.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2.2, hx]
  have hx3sq : x.2.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2.1, hx]
  exact ⟨(sq_le_one_iff_abs_le_one x.1).mp hx1sq,
    (sq_le_one_iff_abs_le_one x.2.1).mp hx2sq,
    (sq_le_one_iff_abs_le_one x.2.2).mp hx3sq⟩

lemma abs_sq_sub_sq_le_two_mul_of_abs_sub_le
    {a b δ : ℝ} (hδ : 0 ≤ δ)
    (hab : |a - b| ≤ δ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    |a ^ 2 - b ^ 2| ≤ 2 * δ := by
  have hsum : |a + b| ≤ 2 := by
    calc
      |a + b| ≤ |a| + |b| := abs_add_le a b
      _ ≤ 1 + 1 := add_le_add ha hb
      _ = 2 := by norm_num
  have hfactor : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  calc
    |a ^ 2 - b ^ 2| = |a - b| * |a + b| := by
      rw [hfactor, abs_mul]
    _ ≤ δ * 2 := mul_le_mul hab hsum (abs_nonneg _) hδ
    _ = 2 * δ := by ring

lemma abs_mul_sub_mul_le_two_mul_of_abs_sub_le
    {a b a₀ b₀ δ : ℝ} (hδ : 0 ≤ δ)
    (ha : |a| ≤ 1) (hb₀ : |b₀| ≤ 1)
    (ha_close : |a - a₀| ≤ δ) (hb_close : |b - b₀| ≤ δ) :
    |a * b - a₀ * b₀| ≤ 2 * δ := by
  have hdecomp : a * b - a₀ * b₀ = a * (b - b₀) + b₀ * (a - a₀) := by ring
  calc
    |a * b - a₀ * b₀|
        = |a * (b - b₀) + b₀ * (a - a₀)| := by rw [hdecomp]
    _ ≤ |a * (b - b₀)| + |b₀ * (a - a₀)| := abs_add_le _ _
    _ = |a| * |b - b₀| + |b₀| * |a - a₀| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * δ + 1 * δ := by
      refine add_le_add ?_ ?_
      · exact mul_le_mul ha hb_close (abs_nonneg _) (by norm_num)
      · exact mul_le_mul hb₀ ha_close (abs_nonneg _) (by norm_num)
    _ = 2 * δ := by ring

lemma abs_sq_sub_sq_le_mul_abs_sum
    {a b δ M : ℝ} (hδ : 0 ≤ δ)
    (hab : |a - b| ≤ δ) (hsum : |a + b| ≤ M) :
    |a ^ 2 - b ^ 2| ≤ δ * M := by
  have hfactor : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  calc
    |a ^ 2 - b ^ 2| = |a - b| * |a + b| := by
      rw [hfactor, abs_mul]
    _ ≤ δ * M := mul_le_mul hab hsum (abs_nonneg _) hδ

lemma gleasonPsiSwap_le_ref_add_six_mul_delta
    {θ δ : ℝ} {x y : ℝ × ℝ × ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hδ0 : 0 ≤ δ)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hdist : dist x y < δ) :
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 ≤
      Thm25.gleasonPsiSwap θ y.1 y.2.1 y.2.2 + 6 * δ := by
  have hxabs := abs_coord_le_one_of_sq_sum hx
  have hyabs := abs_coord_le_one_of_sq_sum hy
  have hx1_close : |x.1 - y.1| ≤ δ :=
    le_of_lt (coord_fst_abs_sub_lt_of_dist_lt (x := x) (y := y) hdist)
  have hx2_close : |x.2.1 - y.2.1| ≤ δ :=
    le_of_lt (coord_snd_fst_abs_sub_lt_of_dist_lt (x := x) (y := y) hdist)
  have hx3_close : |x.2.2 - y.2.2| ≤ δ :=
    le_of_lt (coord_snd_snd_abs_sub_lt_of_dist_lt (x := x) (y := y) hdist)
  have hsq1 :
      |x.1 ^ 2 - y.1 ^ 2| ≤ 2 * δ :=
    abs_sq_sub_sq_le_two_mul_of_abs_sub_le hδ0 hx1_close hxabs.1 hyabs.1
  have hsq2 :
      |x.2.1 ^ 2 - y.2.1 ^ 2| ≤ 2 * δ :=
    abs_sq_sub_sq_le_two_mul_of_abs_sub_le hδ0 hx2_close hxabs.2.1 hyabs.2.1
  have hsum_sq :
      |(x.1 ^ 2 + x.2.1 ^ 2) - (y.1 ^ 2 + y.2.1 ^ 2)| ≤ 4 * δ := by
    have hdecomp :
        (x.1 ^ 2 + x.2.1 ^ 2) - (y.1 ^ 2 + y.2.1 ^ 2) =
          (x.1 ^ 2 - y.1 ^ 2) + (x.2.1 ^ 2 - y.2.1 ^ 2) := by ring
    calc
      |(x.1 ^ 2 + x.2.1 ^ 2) - (y.1 ^ 2 + y.2.1 ^ 2)|
          = |(x.1 ^ 2 - y.1 ^ 2) + (x.2.1 ^ 2 - y.2.1 ^ 2)| := by rw [hdecomp]
      _ ≤ |x.1 ^ 2 - y.1 ^ 2| + |x.2.1 ^ 2 - y.2.1 ^ 2| := abs_add_le _ _
      _ ≤ 2 * δ + 2 * δ := add_le_add hsq1 hsq2
      _ = 4 * δ := by ring
  have hprod :
      |x.2.1 * x.2.2 - y.2.1 * y.2.2| ≤ 2 * δ :=
    abs_mul_sub_mul_le_two_mul_of_abs_sub_le hδ0 hxabs.2.1 hyabs.2.2
      hx2_close hx3_close
  have hθltπ : θ < Real.pi := by linarith [Real.pi_pos, hθpi]
  have hsin_nonneg : 0 ≤ Real.sin θ := le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ0 hθltπ)
  have hsin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hcos_nonneg : 0 ≤ Real.cos θ := by
    exact le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθpi⟩)
  have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hsum_upper :
      ((x.1 ^ 2 + x.2.1 ^ 2) - (y.1 ^ 2 + y.2.1 ^ 2)) * Real.sin θ ≤
        4 * δ := by
    have hupper := (abs_le.mp hsum_sq).2
    have hmul :
        ((x.1 ^ 2 + x.2.1 ^ 2) - (y.1 ^ 2 + y.2.1 ^ 2)) * Real.sin θ ≤
          (4 * δ) * Real.sin θ :=
      mul_le_mul_of_nonneg_right hupper hsin_nonneg
    have hright : (4 * δ) * Real.sin θ ≤ 4 * δ := by
      have h4δ : 0 ≤ 4 * δ := by nlinarith
      have := mul_le_mul_of_nonneg_left hsin_le h4δ
      nlinarith
    exact le_trans hmul hright
  have hprod_upper :
      -((x.2.1 * x.2.2 - y.2.1 * y.2.2) * Real.cos θ) ≤ 2 * δ := by
    have hlower := (abs_le.mp hprod).1
    have hneg : -(x.2.1 * x.2.2 - y.2.1 * y.2.2) ≤ 2 * δ := by
      linarith
    have hmul :
        -(x.2.1 * x.2.2 - y.2.1 * y.2.2) * Real.cos θ ≤
          (2 * δ) * Real.cos θ :=
      mul_le_mul_of_nonneg_right hneg hcos_nonneg
    have hright : (2 * δ) * Real.cos θ ≤ 2 * δ := by
      have h2δ : 0 ≤ 2 * δ := by nlinarith
      have := mul_le_mul_of_nonneg_left hcos_le h2δ
      nlinarith
    have hleft :
        -((x.2.1 * x.2.2 - y.2.1 * y.2.2) * Real.cos θ) =
          -(x.2.1 * x.2.2 - y.2.1 * y.2.2) * Real.cos θ := by
      ring
    rw [hleft]
    exact le_trans hmul hright
  have hdiff :
      Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 -
        Thm25.gleasonPsiSwap θ y.1 y.2.1 y.2.2 ≤ 6 * δ := by
    have hrewrite :
        Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 -
          Thm25.gleasonPsiSwap θ y.1 y.2.1 y.2.2 =
            ((x.1 ^ 2 + x.2.1 ^ 2) - (y.1 ^ 2 + y.2.1 ^ 2)) * Real.sin θ -
              ((x.2.1 * x.2.2 - y.2.1 * y.2.2) * Real.cos θ) := by
      dsimp [Thm25.gleasonPsiSwap, Thm25.gleasonPsi]
      ring
    rw [hrewrite]
    calc
      ((x.1 ^ 2 + x.2.1 ^ 2) - (y.1 ^ 2 + y.2.1 ^ 2)) * Real.sin θ -
          ((x.2.1 * x.2.2 - y.2.1 * y.2.2) * Real.cos θ)
          =
        ((x.1 ^ 2 + x.2.1 ^ 2) - (y.1 ^ 2 + y.2.1 ^ 2)) * Real.sin θ +
          -((x.2.1 * x.2.2 - y.2.1 * y.2.2) * Real.cos θ) := by ring
      _ ≤ 4 * δ + 2 * δ := add_le_add hsum_upper hprod_upper
      _ = 6 * δ := by ring
  simpa [add_comm] using (sub_le_iff_le_add.mp hdiff)

lemma gleasonPsiSwap_le_center_add_six_mul_delta
    {θ δ : ℝ} {x : ℝ × ℝ × ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hδ0 : 0 ≤ δ)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hdist : dist x (psiCenterCoord θ) < δ) :
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 ≤
      Thm25.gleasonPsiSwap θ (psiCenterCoord θ).1
        (psiCenterCoord θ).2.1 (psiCenterCoord θ).2.2 + 6 * δ := by
  exact gleasonPsiSwap_le_ref_add_six_mul_delta
    (θ := θ) (δ := δ) hθ0 hθpi hδ0 hx
    (psiCenterCoord_sq_sum θ) hdist

set_option maxHeartbeats 1200000 in
lemma gleasonPsiSwap_le_center_add_four_cos_mul_delta
    {θ δ : ℝ} {x : ℝ × ℝ × ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hδ0 : 0 ≤ δ) (hδle : δ ≤ Real.cos θ / 16)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hdist : dist x (psiCenterCoord θ) < δ) :
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 ≤
      Thm25.gleasonPsiSwap θ (psiCenterCoord θ).1
        (psiCenterCoord θ).2.1 (psiCenterCoord θ).2.2 +
          4 * Real.cos θ * δ := by
  let c : ℝ := Real.cos θ
  let s : ℝ := Real.sin θ
  let r : ℝ := Real.sqrt (1 - (c / 2) ^ 2)
  let y : ℝ × ℝ × ℝ := psiCenterCoord θ
  have hcpos : 0 < c := by
    dsimp [c]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθpi⟩
  have hc_nonneg : 0 ≤ c := le_of_lt hcpos
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos, hθpi]))
  have hs_le : s ≤ 1 := by
    dsimp [s]
    exact Real.sin_le_one θ
  have hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 := by
    simpa [y] using psiCenterCoord_sq_sum θ
  have hxabs := abs_coord_le_one_of_sq_sum hx
  have hyabs := abs_coord_le_one_of_sq_sum hy
  have hx1_close : |x.1 - 0| ≤ δ := by
    simpa [y, psiCenterCoord] using
      le_of_lt (coord_fst_abs_sub_lt_of_dist_lt (x := x) (y := y) hdist)
  have hx2_close : |x.2.1 - c / 2| ≤ δ := by
    simpa [y, psiCenterCoord, c] using
      le_of_lt (coord_snd_fst_abs_sub_lt_of_dist_lt (x := x) (y := y) hdist)
  have hx3_close : |x.2.2 - r| ≤ δ := by
    simpa [y, psiCenterCoord, c, r] using
      le_of_lt (coord_snd_snd_abs_sub_lt_of_dist_lt (x := x) (y := y) hdist)
  have hx1_bounds : -δ ≤ x.1 ∧ x.1 ≤ δ := by
    simpa using (abs_le.mp hx1_close)
  have hx1_sq_le_delta_sq : x.1 ^ 2 ≤ δ ^ 2 := by
    nlinarith [hx1_bounds.1, hx1_bounds.2]
  have hx1_sq_le : x.1 ^ 2 ≤ c * δ / 16 := by
    nlinarith [hx1_sq_le_delta_sq, hδle, hδ0, hcpos]
  have hsq1 : |x.1 ^ 2 - (0 : ℝ) ^ 2| ≤ c * δ / 16 := by
    simpa using hx1_sq_le
  have hx2_sum : |x.2.1 + c / 2| ≤ c + δ := by
    calc
      |x.2.1 + c / 2|
          = |(x.2.1 - c / 2) + c| := by ring_nf
      _ ≤ |x.2.1 - c / 2| + |c| := abs_add_le _ _
      _ ≤ δ + c := by
          exact add_le_add hx2_close (by simpa [abs_of_nonneg hc_nonneg])
      _ = c + δ := by ring
  have hsq2_raw :
      |x.2.1 ^ 2 - (c / 2) ^ 2| ≤ δ * (c + δ) :=
    abs_sq_sub_sq_le_mul_abs_sum hδ0 hx2_close hx2_sum
  have hsq2 : |x.2.1 ^ 2 - (c / 2) ^ 2| ≤ (17 / 16) * c * δ := by
    have hraw := hsq2_raw
    nlinarith [hraw, hδle, hδ0, hcpos]
  have hsum_sq :
      |(x.1 ^ 2 + x.2.1 ^ 2) - (0 ^ 2 + (c / 2) ^ 2)| ≤
        2 * c * δ := by
    have hdecomp :
        (x.1 ^ 2 + x.2.1 ^ 2) - (0 ^ 2 + (c / 2) ^ 2) =
          (x.1 ^ 2 - 0 ^ 2) + (x.2.1 ^ 2 - (c / 2) ^ 2) := by ring
    calc
      |(x.1 ^ 2 + x.2.1 ^ 2) - (0 ^ 2 + (c / 2) ^ 2)|
          = |(x.1 ^ 2 - 0 ^ 2) + (x.2.1 ^ 2 - (c / 2) ^ 2)| := by rw [hdecomp]
      _ ≤ |x.1 ^ 2 - 0 ^ 2| + |x.2.1 ^ 2 - (c / 2) ^ 2| := abs_add_le _ _
      _ ≤ c * δ / 16 + (17 / 16) * c * δ := add_le_add hsq1 hsq2
      _ = (9 / 8) * c * δ := by ring
      _ ≤ 2 * c * δ := by
          have hcd_nonneg : 0 ≤ c * δ := mul_nonneg hc_nonneg hδ0
          nlinarith
  have hprod_decomp :
      x.2.1 * x.2.2 - (c / 2) * r =
        x.2.1 * (x.2.2 - r) + r * (x.2.1 - c / 2) := by ring
  have hprod :
      |x.2.1 * x.2.2 - (c / 2) * r| ≤ 2 * δ := by
    calc
      |x.2.1 * x.2.2 - (c / 2) * r|
          = |x.2.1 * (x.2.2 - r) + r * (x.2.1 - c / 2)| := by rw [hprod_decomp]
      _ ≤ |x.2.1 * (x.2.2 - r)| + |r * (x.2.1 - c / 2)| := abs_add_le _ _
      _ = |x.2.1| * |x.2.2 - r| + |r| * |x.2.1 - c / 2| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * δ + 1 * δ := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul hxabs.2.1 hx3_close (abs_nonneg _) (by norm_num)
          · have hr_abs : |r| ≤ 1 := by
              simpa [y, psiCenterCoord, c, r] using hyabs.2.2
            exact mul_le_mul hr_abs hx2_close (abs_nonneg _) (by norm_num)
      _ = 2 * δ := by ring
  have hsum_upper :
      ((x.1 ^ 2 + x.2.1 ^ 2) - (0 ^ 2 + (c / 2) ^ 2)) * s ≤
        2 * c * δ := by
    have hupper := (abs_le.mp hsum_sq).2
    have hmul :
        ((x.1 ^ 2 + x.2.1 ^ 2) - (0 ^ 2 + (c / 2) ^ 2)) * s ≤
          (2 * c * δ) * s :=
      mul_le_mul_of_nonneg_right hupper hs_nonneg
    have hright : (2 * c * δ) * s ≤ 2 * c * δ := by
      have hnonneg : 0 ≤ 2 * c * δ := by nlinarith
      exact mul_le_of_le_one_right hnonneg hs_le
    exact le_trans hmul hright
  have hprod_upper :
      -((x.2.1 * x.2.2 - (c / 2) * r) * c) ≤ 2 * c * δ := by
    have hprod_abs : |(x.2.1 * x.2.2 - (c / 2) * r) * c| ≤ 2 * c * δ := by
      calc
        |(x.2.1 * x.2.2 - (c / 2) * r) * c|
            = |x.2.1 * x.2.2 - (c / 2) * r| * c := by
                rw [abs_mul, abs_of_nonneg hc_nonneg]
        _ ≤ (2 * δ) * c := mul_le_mul_of_nonneg_right hprod hc_nonneg
        _ = 2 * c * δ := by ring
    exact le_trans (neg_le_abs _) hprod_abs
  have hdiff :
      Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 -
        Thm25.gleasonPsiSwap θ (psiCenterCoord θ).1
          (psiCenterCoord θ).2.1 (psiCenterCoord θ).2.2 ≤
          4 * c * δ := by
    have hrewrite :
        Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 -
          Thm25.gleasonPsiSwap θ (psiCenterCoord θ).1
            (psiCenterCoord θ).2.1 (psiCenterCoord θ).2.2 =
            ((x.1 ^ 2 + x.2.1 ^ 2) - (0 ^ 2 + (c / 2) ^ 2)) * s -
              ((x.2.1 * x.2.2 - (c / 2) * r) * c) := by
      dsimp [Thm25.gleasonPsiSwap, Thm25.gleasonPsi, psiCenterCoord, c, s, r]
      ring
    rw [hrewrite]
    calc
      ((x.1 ^ 2 + x.2.1 ^ 2) - (0 ^ 2 + (c / 2) ^ 2)) * s -
          ((x.2.1 * x.2.2 - (c / 2) * r) * c)
          =
        ((x.1 ^ 2 + x.2.1 ^ 2) - (0 ^ 2 + (c / 2) ^ 2)) * s +
          -((x.2.1 * x.2.2 - (c / 2) * r) * c) := by ring
      _ ≤ 2 * c * δ + 2 * c * δ := add_le_add hsum_upper hprod_upper
      _ = 4 * c * δ := by ring
  have hle := sub_le_iff_le_add.mp (by simpa [c] using hdiff)
  linarith

lemma gleasonPsiSwap_lt_zero_of_dist_midMeridianCoord_away_from_pole
    {θ τ : ℝ}
    (hθ0 : 0 < θ)
    (hτ0 : 0 < τ)
    (hθτ : θ ≤ Real.pi / 2 - τ)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hdist :
      dist x (northMeridianCoord ((θ + Real.pi / 2) / 2)) <
        (Real.sin (τ / 2)) ^ 2 / 12) :
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 := by
  have hθpi : θ < Real.pi / 2 := by linarith
  have hδ0 : 0 ≤ (Real.sin (τ / 2)) ^ 2 / 12 := by positivity
  have hcenter :=
    gleasonPsiSwap_midMeridianCoord_le_neg_gap_sq
      (θ := θ) (τ := τ) hθ0 hτ0 hθτ
  have hnear :=
    gleasonPsiSwap_le_ref_add_six_mul_delta
      (θ := θ) (δ := (Real.sin (τ / 2)) ^ 2 / 12)
      hθ0 hθpi hδ0 hx
      (northMeridianCoord_sq_sum ((θ + Real.pi / 2) / 2))
      hdist
  calc
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2
        ≤ Thm25.gleasonPsiSwap θ
            (northMeridianCoord ((θ + Real.pi / 2) / 2)).1
            (northMeridianCoord ((θ + Real.pi / 2) / 2)).2.1
            (northMeridianCoord ((θ + Real.pi / 2) / 2)).2.2 +
          6 * ((Real.sin (τ / 2)) ^ 2 / 12) := hnear
    _ ≤ -(Real.sin (τ / 2)) ^ 2 + 6 * ((Real.sin (τ / 2)) ^ 2 / 12) := by
        linarith
    _ < 0 := by
        have hsin_pos : 0 < Real.sin (τ / 2) := by
          have htau_le : τ ≤ Real.pi / 2 := by linarith [hθ0, hθτ]
          have htau_lt_pi : τ / 2 < Real.pi := by
            nlinarith [htau_le, Real.pi_pos]
          exact Real.sin_pos_of_pos_of_lt_pi (by positivity) htau_lt_pi
        nlinarith [sq_pos_of_pos hsin_pos]

lemma gleasonPsiSwap_lt_zero_of_dist_psiCenterCoord_linear
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hdist : dist x (psiCenterCoord θ) < Real.cos θ / 256) :
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 := by
  have hcos_pos : 0 < Real.cos θ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθpi⟩
  have hδ0 : 0 ≤ Real.cos θ / 256 := by positivity
  have hδle : Real.cos θ / 256 ≤ Real.cos θ / 16 := by
    nlinarith
  have hcenter :=
    gleasonPsiSwap_psiCenterCoord_le_neg_cos_sq (θ := θ) hθ0 hθpi
  have hnear :=
    gleasonPsiSwap_le_center_add_four_cos_mul_delta
      (θ := θ) (δ := Real.cos θ / 256) hθ0 hθpi hδ0 hδle hx hdist
  calc
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2
        ≤ Thm25.gleasonPsiSwap θ (psiCenterCoord θ).1
            (psiCenterCoord θ).2.1 (psiCenterCoord θ).2.2 +
          4 * Real.cos θ * (Real.cos θ / 256) := hnear
    _ ≤ -(Real.cos θ ^ 2) / 16 + 4 * Real.cos θ * (Real.cos θ / 256) := by
        linarith
    _ < 0 := by
        nlinarith [sq_pos_of_pos hcos_pos]

lemma gleasonPsiSwap_lt_zero_of_dist_psiCenterCoord_low_uniform
    {θ : ℝ} (hθ0 : 0 < θ) (hθle : θ ≤ Real.pi / 3)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hdist : dist x (psiCenterCoord θ) < (1 : ℝ) / 512) :
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 := by
  have hθpi : θ < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hcos_ge : (1 : ℝ) / 2 ≤ Real.cos θ := by
    have hcos :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        (le_of_lt hθ0)
        (by nlinarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi)
        hθle
    simpa [Real.cos_pi_div_three] using hcos
  have hdist' : dist x (psiCenterCoord θ) < Real.cos θ / 256 := by
    nlinarith
  exact gleasonPsiSwap_lt_zero_of_dist_psiCenterCoord_linear
    (θ := θ) hθ0 hθpi hx hdist'

lemma gleasonPsiSwap_lt_zero_of_dist_psiCenterCoord
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hdist : dist x (psiCenterCoord θ) < Real.cos θ ^ 2 / 256) :
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 := by
  have hcos_pos : 0 < Real.cos θ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθpi⟩
  have hδ0 : 0 ≤ Real.cos θ ^ 2 / 256 := by positivity
  have hcenter :=
    gleasonPsiSwap_psiCenterCoord_le_neg_cos_sq (θ := θ) hθ0 hθpi
  have hnear :=
    gleasonPsiSwap_le_center_add_six_mul_delta
      (θ := θ) (δ := Real.cos θ ^ 2 / 256) hθ0 hθpi hδ0 hx hdist
  have hcos_sq_pos : 0 < Real.cos θ ^ 2 := sq_pos_of_pos hcos_pos
  calc
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2
        ≤ Thm25.gleasonPsiSwap θ (psiCenterCoord θ).1
            (psiCenterCoord θ).2.1 (psiCenterCoord θ).2.2 +
          6 * (Real.cos θ ^ 2 / 256) := hnear
    _ ≤ -(Real.cos θ ^ 2) / 16 + 6 * (Real.cos θ ^ 2 / 256) := by
        linarith
    _ < 0 := by
        nlinarith

lemma arcsin_mem_open_quarter
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 < Real.arcsin r ∧ Real.arcsin r < Real.pi / 2 := by
  constructor
  · simpa using (Real.arcsin_pos.mpr hr0)
  · simpa using (Real.arcsin_lt_pi_div_two.mpr hr1)

lemma northMeridianCoord_arcsin
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hznonneg : 0 ≤ z.2.2) :
    northMeridianCoord (Real.arcsin z.2.2) =
      (0, (horizontalRadius z, z.2.2)) := by
  have hzm1 : -1 ≤ z.2.2 := by linarith
  have hzle : z.2.2 ≤ 1 := by
    nlinarith [hz, sq_nonneg z.1, sq_nonneg z.2.1]
  have hρsq := horizontalRadius_sq z
  ext <;> dsimp [northMeridianCoord]
  · rw [Real.cos_arcsin]
    have hEq : 1 - z.2.2 ^ 2 = horizontalRadius z ^ 2 := by
      nlinarith [hz, hρsq]
    rw [hEq, Real.sqrt_sq_eq_abs]
    have hρnonneg : 0 ≤ horizontalRadius z := by
      unfold horizontalRadius
      exact Real.sqrt_nonneg _
    exact abs_of_nonneg hρnonneg
  · rw [Real.sin_arcsin hzm1 hzle]

lemma coordDot_target_horizontalUnitCoord
    {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    coordDot z (horizontalUnitCoord z) = horizontalRadius z := by
  have hρsq := horizontalRadius_sq z
  unfold coordDot horizontalUnitCoord
  field_simp [hρ]
  rw [hρsq]
  ring

lemma equatorFrameCoords_self
    {z : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    equatorFrameCoords z z = (0, (horizontalRadius z, z.2.2)) := by
  ext <;> simp [equatorFrameCoords, coordDot_target_targetPoleCoord,
    coordDot_target_horizontalUnitCoord, hρ]

lemma equatorFrameCoords_self_eq_northMeridian
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hznonneg : 0 ≤ z.2.2) :
    equatorFrameCoords z z = northMeridianCoord (Real.arcsin z.2.2) := by
  rw [equatorFrameCoords_self hρ]
  symm
  exact northMeridianCoord_arcsin hz hznonneg

def meridianFlip (y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (-y.1, (y.2.1, y.2.2))

def meridianFrameReparam
    (z y : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  coordLinearCombo y.1 y.2.1 y.2.2
    (-targetPoleCoord z) (horizontalUnitCoord z) poleCoord

def meridianFrameCoords
    (z x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (-coordDot x (targetPoleCoord z),
    (coordDot x (horizontalUnitCoord z), x.2.2))

lemma meridianFrameReparam_eq_equatorFrameReparam
    (z y : ℝ × ℝ × ℝ) :
    meridianFrameReparam z y = equatorFrameReparam z (meridianFlip y) := by
  ext <;> simp [meridianFrameReparam, equatorFrameReparam, meridianFlip,
    coordLinearCombo, sub_eq_add_neg, add_assoc]
  all_goals ring

lemma meridianFrameCoords_eq_meridianFlip
    (z x : ℝ × ℝ × ℝ) :
    meridianFrameCoords z x = meridianFlip (equatorFrameCoords z x) := by
  rfl

lemma meridianFlip_sq_sum
    {y : ℝ × ℝ × ℝ}
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1) :
    (meridianFlip y).1 ^ 2 +
        (meridianFlip y).2.1 ^ 2 +
        (meridianFlip y).2.2 ^ 2 = 1 := by
  dsimp [meridianFlip]
  nlinarith

lemma meridianFrameReparam_sq_sum
    {z y : ℝ × ℝ × ℝ}
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    (meridianFrameReparam z y).1 ^ 2 +
        (meridianFrameReparam z y).2.1 ^ 2 +
        (meridianFrameReparam z y).2.2 ^ 2 = 1 := by
  rw [meridianFrameReparam_eq_equatorFrameReparam z y]
  exact equatorFrameReparam_sq_sum (meridianFlip_sq_sum hy) hρ

lemma meridianFrameReparam_explicit
    {z y : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    meridianFrameReparam z y =
      ((y.1 * z.2.1 + y.2.1 * z.1) / horizontalRadius z,
        ((-y.1 * z.1 + y.2.1 * z.2.1) / horizontalRadius z, y.2.2)) := by
  ext <;> simp [meridianFrameReparam, coordLinearCombo, targetPoleCoord,
    horizontalUnitCoord, poleCoord]
  · field_simp [hρ]
  · field_simp [hρ]

def lowHorizontalMeridianCoord (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  meridianFrameReparam z (0, (Real.cos (Real.pi / 6), Real.sin (Real.pi / 6)))

lemma lowHorizontalMeridianCoord_third
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    (lowHorizontalMeridianCoord z).2.2 = (1 : ℝ) / 2 := by
  dsimp [lowHorizontalMeridianCoord]
  rw [meridianFrameReparam_explicit hρ]
  simp [Real.sin_pi_div_six]

lemma lowHorizontalMeridianCoord_sq_sum
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    (lowHorizontalMeridianCoord z).1 ^ 2 +
      (lowHorizontalMeridianCoord z).2.1 ^ 2 +
        (lowHorizontalMeridianCoord z).2.2 ^ 2 = 1 := by
  dsimp [lowHorizontalMeridianCoord]
  apply meridianFrameReparam_sq_sum
  · rw [Real.sin_pi_div_six, Real.cos_pi_div_six]
    have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    nlinarith
  · exact hρ

lemma lowHorizontalMeridianCoord_pos
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    0 < (lowHorizontalMeridianCoord z).2.2 := by
  rw [lowHorizontalMeridianCoord_third hρ]
  norm_num

lemma lowHorizontalMeridianCoord_low
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    Real.arcsin (lowHorizontalMeridianCoord z).2.2 ≤ Real.pi / 3 := by
  rw [lowHorizontalMeridianCoord_third hρ]
  have hmemx : ((1 : ℝ) / 2) ∈ Set.Icc (-(1 : ℝ)) 1 := by norm_num
  have hmemy : (Real.pi / 3) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith [Real.pi_pos]
  rw [Real.arcsin_le_iff_le_sin hmemx hmemy]
  rw [Real.sin_pi_div_three]
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  nlinarith [Real.sqrt_nonneg 3, hsqrt_sq]

lemma lowHorizontalMeridianCoord_horizontalRadius_ne_zero
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    horizontalRadius (lowHorizontalMeridianCoord z) ≠ 0 := by
  intro hzero
  have hρsq :
      horizontalRadius (lowHorizontalMeridianCoord z) ^ 2 =
        (lowHorizontalMeridianCoord z).1 ^ 2 +
          (lowHorizontalMeridianCoord z).2.1 ^ 2 := by
    rw [horizontalRadius_sq]
  have hxy_zero :
      (lowHorizontalMeridianCoord z).1 ^ 2 +
        (lowHorizontalMeridianCoord z).2.1 ^ 2 = 0 := by
    nlinarith
  have hthird_sq : (lowHorizontalMeridianCoord z).2.2 ^ 2 = 1 := by
    nlinarith [lowHorizontalMeridianCoord_sq_sum hρ]
  rw [lowHorizontalMeridianCoord_third hρ] at hthird_sq
  norm_num at hthird_sq

lemma targetPoleCoord_lowHorizontalMeridianCoord
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    targetPoleCoord (lowHorizontalMeridianCoord z) = targetPoleCoord z := by
  have hcos_pos : 0 < Real.cos (Real.pi / 6) := by
    rw [Real.cos_pi_div_six]
    positivity
  have hρsq : horizontalRadius z ^ 2 = z.1 ^ 2 + z.2.1 ^ 2 := by
    rw [horizontalRadius_sq]
  have hρpos : 0 < horizontalRadius z := by
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hρ)
  have hρa_eq :
      horizontalRadius (lowHorizontalMeridianCoord z) =
        Real.cos (Real.pi / 6) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (le_of_lt hcos_pos)).1
    change
      Real.sqrt
          ((lowHorizontalMeridianCoord z).1 ^ 2 +
            (lowHorizontalMeridianCoord z).2.1 ^ 2) ^ 2 =
        Real.cos (Real.pi / 6) ^ 2
    rw [Real.sq_sqrt]
    · dsimp [lowHorizontalMeridianCoord]
      rw [meridianFrameReparam_explicit hρ]
      field_simp [hρ]
      rw [hρsq]
      ring
    · positivity
  ext
  · simp only [targetPoleCoord]
    rw [hρa_eq]
    dsimp [lowHorizontalMeridianCoord]
    rw [meridianFrameReparam_explicit hρ]
    field_simp [hρ, ne_of_gt hcos_pos]
    ring
  · simp only [targetPoleCoord]
    rw [hρa_eq]
    dsimp [lowHorizontalMeridianCoord]
    rw [meridianFrameReparam_explicit hρ]
    field_simp [hρ, ne_of_gt hcos_pos]
    ring
  · simp [targetPoleCoord]

lemma targetBridgeCoord_lowHorizontalMeridianCoord
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    targetBridgeCoord (lowHorizontalMeridianCoord z) =
      meridianFrameReparam z (0, ((1 : ℝ) / 2, -Real.cos (Real.pi / 6))) := by
  have hcos_pos : 0 < Real.cos (Real.pi / 6) := by
    rw [Real.cos_pi_div_six]
    positivity
  have hρsq : horizontalRadius z ^ 2 = z.1 ^ 2 + z.2.1 ^ 2 := by
    rw [horizontalRadius_sq]
  have hlowρ :
      horizontalRadius (lowHorizontalMeridianCoord z) =
        Real.cos (Real.pi / 6) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (le_of_lt hcos_pos)).1
    change
      Real.sqrt
          ((lowHorizontalMeridianCoord z).1 ^ 2 +
            (lowHorizontalMeridianCoord z).2.1 ^ 2) ^ 2 =
        Real.cos (Real.pi / 6) ^ 2
    rw [Real.sq_sqrt]
    · dsimp [lowHorizontalMeridianCoord]
      rw [meridianFrameReparam_explicit hρ]
      field_simp [hρ]
      rw [hρsq]
      ring
    · positivity
  ext <;> simp only [targetBridgeCoord, lowHorizontalMeridianCoord_third hρ,
    hlowρ, meridianFrameReparam_explicit hρ]
  · dsimp [lowHorizontalMeridianCoord]
    rw [meridianFrameReparam_explicit hρ, Real.cos_pi_div_six]
    field_simp [hρ]
    ring
  · dsimp [lowHorizontalMeridianCoord]
    rw [meridianFrameReparam_explicit hρ, Real.cos_pi_div_six]
    field_simp [hρ]
    ring

lemma polarQuarterTurnCoord_meridianFrameReparam
    {z y : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    polarQuarterTurnCoord (meridianFrameReparam z y) =
      meridianFrameReparam z (polarQuarterTurnCoord y) := by
  rw [meridianFrameReparam_explicit hρ, meridianFrameReparam_explicit hρ]
  ext <;> simp [polarQuarterTurnCoord]
  · field_simp [hρ]
    ring
  · field_simp [hρ]
    ring

lemma coordPoint_meridianFrameReparam
    (u v p : H)
    (z y : ℝ × ℝ × ℝ) :
    coordPoint
        (coordPoint u v p (-targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z))
        p y =
      coordPoint u v p (meridianFrameReparam z y) := by
  have hflip :
      coordPoint
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p y =
        coordPoint
          (coordPoint u v p (targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p (meridianFlip y) := by
    simp [coordPoint, meridianFlip, sub_eq_add_neg, add_assoc]
  rw [hflip]
  rw [coordPoint_equatorFrameReparam (u := u) (v := v) (p := p) (z := z)
    (y := meridianFlip y)]
  rw [← meridianFrameReparam_eq_equatorFrameReparam z y]

lemma dist_coordPoint_meridianFrameReparam_pole_lt
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z y : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0)
    {ε : ℝ} (hdist : dist y poleCoord < ε) :
    dist (coordPoint u v p (meridianFrameReparam z y)) p < 3 * ε := by
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hle :
      dist (coordPoint u' w p y) (coordPoint u' w p poleCoord) ≤
        3 * dist y poleCoord :=
    dist_coordPoint_le_three_mul_dist_coords hu' hw hp y poleCoord
  have hlt : 3 * dist y poleCoord < 3 * ε := by
    nlinarith
  calc
    dist (coordPoint u v p (meridianFrameReparam z y)) p
        = dist (coordPoint u' w p y) (coordPoint u' w p poleCoord) := by
            dsimp [u', w]
            rw [coordPoint_meridianFrameReparam, coordPoint_poleCoord]
    _ < 3 * ε := lt_of_le_of_lt hle hlt

lemma polarSumValue_meridianFrameReparam
    (μ : FrameFunction H) (u v p : H)
    {z y : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    polarSumValue μ
        (coordPoint u v p (-targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z))
        p y =
      polarSumValue μ u v p (meridianFrameReparam z y) := by
  unfold polarSumValue
  rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z) (y := y)]
  rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
    (y := polarQuarterTurnCoord y)]
  rw [polarQuarterTurnCoord_meridianFrameReparam (z := z) (y := y) hρ]

lemma polarSumValue_meridianFrameCoords
    (μ : FrameFunction H) (u v p : H)
    {z x : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius z ≠ 0) :
    polarSumValue μ
        (coordPoint u v p (-targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z))
        p (meridianFrameCoords z x) =
      polarSumValue μ u v p x := by
  have hcoord :
      meridianFrameReparam z (meridianFrameCoords z x) = x := by
    rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z x)]
    rw [meridianFrameCoords_eq_meridianFlip z x]
    simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
  rw [polarSumValue_meridianFrameReparam (μ := μ) (u := u) (v := v) (p := p) hρ]
  simpa [hcoord]

lemma meridianFrameCoords_self_eq_northMeridian
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hznonneg : 0 ≤ z.2.2) :
    meridianFrameCoords z z = northMeridianCoord (Real.arcsin z.2.2) := by
  have h0 : coordDot z (targetPoleCoord z) = 0 :=
    coordDot_target_targetPoleCoord hρ
  rw [← equatorFrameCoords_self_eq_northMeridian (z := z) hz hρ hznonneg]
  rw [meridianFrameCoords_eq_meridianFlip z z]
  simp [meridianFlip, equatorFrameCoords, h0]

lemma coordPoint_meridianFrameCoords_self_eq_northMeridian
    (u v p : H)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hznonneg : 0 ≤ z.2.2) :
    coordPoint
        (coordPoint u v p (-targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z))
        p
        (northMeridianCoord (Real.arcsin z.2.2)) =
      coordPoint u v p z := by
  rw [← meridianFrameCoords_self_eq_northMeridian (z := z) hz hρ hznonneg]
  rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
    (y := meridianFrameCoords z z)]
  have hcoord :
      meridianFrameReparam z (meridianFrameCoords z z) = z := by
    rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z z)]
    rw [meridianFrameCoords_eq_meridianFlip z z]
    simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
  simpa [hcoord]

lemma targetFrameCoordsSwap_sq_sum
    {u v p : H} {z x : ℝ × ℝ × ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    (targetFrameCoordsSwap z x).1 ^ 2 +
        (targetFrameCoordsSwap z x).2.1 ^ 2 +
        (targetFrameCoordsSwap z x).2.2 ^ 2 = 1 := by
  have hmain :=
    targetFrameCoords_sq_sum hu hv hp huv hup hvp hz hx hρ
  unfold targetFrameCoordsSwap targetFrameCoords at *
  nlinarith

lemma coordDot_targetBridgeCoord_zero_of_ew_plane
    {x y : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius x ≠ 0)
    (hplane :
      (x.1 ^ 2 + x.2.1 ^ 2) * y.2.2 =
        x.2.2 * (x.1 * y.1 + x.2.1 * y.2.1)) :
    coordDot y (targetBridgeCoord x) = 0 := by
  have hρsq := horizontalRadius_sq x
  unfold coordDot targetBridgeCoord
  field_simp [hρ]
  ring_nf
  have hplane' :
      horizontalRadius x ^ 2 * y.2.2 =
        x.2.2 * y.1 * x.1 + x.2.2 * y.2.1 * x.2.1 := by
    rw [hρsq]
    nlinarith [hplane]
  linarith

lemma coordDot_northMeridianCoord_targetBridge
    {θ : ℝ} {y : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius y ≠ 0) :
    coordDot (northMeridianCoord θ) (targetBridgeCoord y) =
      -Thm25.gleasonPsiSwap θ y.1 y.2.1 y.2.2 / horizontalRadius y := by
  have hρsq := horizontalRadius_sq y
  unfold coordDot targetBridgeCoord northMeridianCoord Thm25.gleasonPsiSwap Thm25.gleasonPsi
  field_simp [hρ]
  ring_nf
  have hsq :
      horizontalRadius y ^ 2 * Real.sin θ =
        y.1 ^ 2 * Real.sin θ + y.2.1 ^ 2 * Real.sin θ := by
    rw [hρsq]
    ring
  linarith

lemma horizontalRadius_ne_zero_of_gleasonPsiSwap_neg
    {θ : ℝ} {x : ℝ × ℝ × ℝ}
    (hneg : Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0) :
    horizontalRadius x ≠ 0 := by
  simpa [horizontalRadius, Thm25.ewRadius, Thm25.gleasonPsiSwap, add_comm] using
    (Thm25.ewRadius_ne_zero_of_psi_neg
      (θ := θ) (ξ := x.2.1) (η := x.1) (r := x.2.2) hneg)

lemma horizontalRadius_ne_zero_of_ew_plane_on_sphere
    {x y : ℝ × ℝ × ℝ}
    (hρx : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hplane :
      (x.1 ^ 2 + x.2.1 ^ 2) * y.2.2 =
        x.2.2 * (x.1 * y.1 + x.2.1 * y.2.1)) :
    horizontalRadius y ≠ 0 := by
  intro hρy
  have hyρsq : y.1 ^ 2 + y.2.1 ^ 2 = 0 := by
    rw [← horizontalRadius_sq y, hρy]
    norm_num
  have hy10 : y.1 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2.1, hyρsq]
  have hy20 : y.2.1 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2.1, hyρsq]
  have hy2 : y.2.2 ^ 2 = 1 := by
    nlinarith [hy, hy10, hy20]
  have hy2_ne : y.2.2 ≠ 0 := by
    intro hy20'
    nlinarith [hy2]
  have hxρsq : x.1 ^ 2 + x.2.1 ^ 2 ≠ 0 := by
    intro hxρsq0
    have hsq0 : horizontalRadius x ^ 2 = 0 := by
      rw [horizontalRadius_sq x, hxρsq0]
    have : horizontalRadius x = 0 := by
      nlinarith
    exact hρx this
  have hzero :
      (x.1 ^ 2 + x.2.1 ^ 2) * y.2.2 = 0 := by
    rw [hplane]
    simp [hy10, hy20]
  have hxsum0 : x.1 ^ 2 + x.2.1 ^ 2 = 0 := by
    rcases mul_eq_zero.mp hzero with hxsum0 | hy20'
    · exact hxsum0
    · exact (hy2_ne hy20').elim
  exact hxρsq hxsum0

lemma exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {θ : ℝ} {x : ℝ × ℝ × ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hneg : Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0) :
    ∃ y s t : ℝ × ℝ × ℝ,
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      horizontalRadius y ≠ 0 ∧
      s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 = 1 ∧
      s.2.2 = 0 ∧
      t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 1 ∧
      t.2.2 = 0 ∧
      y = targetFrameReparamSwap x s ∧
      northMeridianCoord θ = targetFrameReparamSwap y t := by
  have hρx : horizontalRadius x ≠ 0 := by
    exact horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hneg
  rcases Thm25.exists_two_step_ew_point_of_gleasonPsiSwap_neg hθ0 hθpi hx hneg with
    ⟨ξ', η', r', hy, hplane, hpsi⟩
  let y : ℝ × ℝ × ℝ := (ξ', (η', r'))
  let s : ℝ × ℝ × ℝ := targetFrameCoordsSwap x y
  have hsphere_y :
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 := by
    simpa [y] using hy
  have hs0 : s.2.2 = 0 := by
    unfold s targetFrameCoordsSwap
    change coordDot y (targetBridgeCoord x) = 0
    exact coordDot_targetBridgeCoord_zero_of_ew_plane hρx (by simpa [y] using hplane)
  have hs :
      s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 = 1 := by
    exact targetFrameCoordsSwap_sq_sum
      hu hv hp huv hup hvp hx hsphere_y hρx
  have hρy : horizontalRadius y ≠ 0 := by
    exact horizontalRadius_ne_zero_of_ew_plane_on_sphere
      hρx hsphere_y (by simpa [y] using hplane)
  let t : ℝ × ℝ × ℝ := targetFrameCoordsSwap y (northMeridianCoord θ)
  have ht0 : t.2.2 = 0 := by
    unfold t targetFrameCoordsSwap
    have hdot := coordDot_northMeridianCoord_targetBridge (θ := θ) (y := y) hρy
    have hpsi' : Thm25.gleasonPsiSwap θ y.1 y.2.1 y.2.2 = 0 := by
      simpa [y] using hpsi
    rw [hpsi'] at hdot
    simpa using hdot
  have ht :
      t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 1 := by
    exact targetFrameCoordsSwap_sq_sum
      hu hv hp huv hup hvp hsphere_y (northMeridianCoord_sq_sum θ) hρy
  have hy_repr : y = targetFrameReparamSwap x s := by
    symm
    exact targetFrameReparamSwap_targetFrameCoordsSwap (z := x) (x := y) hx hρx
  have hz_repr : northMeridianCoord θ = targetFrameReparamSwap y t := by
    symm
    exact targetFrameReparamSwap_targetFrameCoordsSwap
      (z := y) (x := northMeridianCoord θ) hsphere_y hρy
  exact ⟨y, s, t, hsphere_y, hρy, hs, hs0, ht, ht0, hy_repr, hz_repr⟩

lemma exists_targetFrameSwap_northMeridian_of_gleasonPsiSwap_zero
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {θ : ℝ} {y : ℝ × ℝ × ℝ}
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hρy : horizontalRadius y ≠ 0)
    (hψ : Thm25.gleasonPsiSwap θ y.1 y.2.1 y.2.2 = 0) :
    ∃ t : ℝ × ℝ × ℝ,
      t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 1 ∧
      t.2.2 = 0 ∧
      northMeridianCoord θ = targetFrameReparamSwap y t := by
  let t : ℝ × ℝ × ℝ := targetFrameCoordsSwap y (northMeridianCoord θ)
  have ht0 : t.2.2 = 0 := by
    unfold t targetFrameCoordsSwap
    have hdot := coordDot_northMeridianCoord_targetBridge (θ := θ) (y := y) hρy
    rw [hψ] at hdot
    simpa using hdot
  have ht :
      t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 1 := by
    exact targetFrameCoordsSwap_sq_sum
      hu hv hp huv hup hvp hy (northMeridianCoord_sq_sum θ) hρy
  have hrepr : northMeridianCoord θ = targetFrameReparamSwap y t := by
    symm
    exact targetFrameReparamSwap_targetFrameCoordsSwap
      (z := y) (x := northMeridianCoord θ) hy hρy
  exact ⟨t, ht, ht0, hrepr⟩


lemma targetPoleCoord_polarQuarterTurnCoord
    {x : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius x ≠ 0) :
    targetPoleCoord (polarQuarterTurnCoord x) =
      polarQuarterTurnCoord (targetPoleCoord x) := by
  have hrad :
      horizontalRadius (-x.2.1, (x.1, x.2.2)) = horizontalRadius x := by
    simpa [polarQuarterTurnCoord] using horizontalRadius_polarQuarterTurnCoord x
  ext <;> simp [targetPoleCoord, polarQuarterTurnCoord]
  · rw [hrad]
    simp [neg_div]
  · rw [hrad]

lemma targetBridgeCoord_polarQuarterTurnCoord
    {x : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius x ≠ 0) :
    targetBridgeCoord (polarQuarterTurnCoord x) =
      polarQuarterTurnCoord (targetBridgeCoord x) := by
  have hrad :
      horizontalRadius (-x.2.1, (x.1, x.2.2)) = horizontalRadius x := by
    simpa [polarQuarterTurnCoord] using horizontalRadius_polarQuarterTurnCoord x
  ext <;> simp [targetBridgeCoord, polarQuarterTurnCoord]
  · rw [hrad]
    simp [neg_div]
  · rw [hrad]
  · rw [hrad]

lemma horizontalUnitCoord_polarQuarterTurnCoord
    {x : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius x ≠ 0) :
    horizontalUnitCoord (polarQuarterTurnCoord x) =
      polarQuarterTurnCoord (horizontalUnitCoord x) := by
  have hrad :
      horizontalRadius (-x.2.1, (x.1, x.2.2)) = horizontalRadius x := by
    simpa [polarQuarterTurnCoord] using horizontalRadius_polarQuarterTurnCoord x
  ext <;> simp [horizontalUnitCoord, polarQuarterTurnCoord]
  · rw [hrad]
    simp [neg_div]
  · rw [hrad]

lemma polarSumValue_eq_trace_on_equator
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hr : x.2.2 = 0) :
    polarSumValue μ u v p x =
      coordTraceValue μ u v p - frame_quadratic μ p := by
  have hab : x.1 ^ 2 + x.2.1 ^ 2 = 1 := by
    nlinarith [hx, hr]
  have hgc :=
    GleasonBridge.great_circle_constancy hdim μ u v hu hv huv x.1 x.2.1 hab
  have hsum :=
    GleasonRankOne.three_vector_sum (H := H) μ u v p hu hv hp huv hup hvp
  have hturn :
      coordPoint u v p (polarQuarterTurnCoord x) =
        -(((x.2.1 : ℂ) • u) - ((x.1 : ℂ) • v)) := by
    simp [coordPoint, polarQuarterTurnCoord, hr, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]
  have hturnQ :
      frame_quadratic μ (coordPoint u v p (polarQuarterTurnCoord x)) =
        frame_quadratic μ (((x.2.1 : ℂ) • u) - ((x.1 : ℂ) • v)) := by
    rw [hturn, frame_quadratic_neg]
  unfold polarSumValue coordTraceValue
  have hmain :
      frame_quadratic μ (coordPoint u v p x) +
        frame_quadratic μ (coordPoint u v p (polarQuarterTurnCoord x)) =
      frame_quadratic μ u + frame_quadratic μ v := by
    rw [hturnQ]
    simpa [coordPoint, hr] using hgc
  linarith

lemma coordPoint_mem_targetFrameSpan
    (u v p : H)
    {z y : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    coordPoint u v p y ∈
      Submodule.span ℂ ({coordPoint u v p z,
        coordPoint u v p (targetBridgeCoord z),
        coordPoint u v p (targetPoleCoord z)} : Set H) := by
  have hrepr :
      coordPoint u v p y =
        coordPoint (coordPoint u v p z)
          (coordPoint u v p (targetBridgeCoord z))
          (coordPoint u v p (targetPoleCoord z))
          (targetFrameCoords z y) := by
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := z)
        (y := targetFrameCoords z y)]
    rw [targetFrameReparam_targetFrameCoords (z := z) (x := y) hz hρ]
  have hmem :
      coordPoint u v p y ∈
        Submodule.span ℂ ({coordPoint u v p z,
          coordPoint u v p (targetBridgeCoord z),
          coordPoint u v p (targetPoleCoord z)} : Set H) := by
    rw [hrepr]
    exact coordPoint_mem_span
      (coordPoint u v p z)
      (coordPoint u v p (targetBridgeCoord z))
      (coordPoint u v p (targetPoleCoord z))
      (targetFrameCoords z y)
  exact hmem

lemma targetFrame_span_eq_original
    (u v p : H)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    Submodule.span ℂ ({coordPoint u v p z,
      coordPoint u v p (targetBridgeCoord z),
      coordPoint u v p (targetPoleCoord z)} : Set H) =
      Submodule.span ℂ ({u, v, p} : Set H) := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.2 ?_
    intro x hx
    have hx' :
        x = coordPoint u v p z ∨
          x = coordPoint u v p (targetBridgeCoord z) ∨
          x = coordPoint u v p (targetPoleCoord z) := by
      simpa using hx
    rcases hx' with rfl | rfl | rfl
    · exact coordPoint_mem_span u v p z
    · exact coordPoint_mem_span u v p (targetBridgeCoord z)
    · exact coordPoint_mem_span u v p (targetPoleCoord z)
  · refine Submodule.span_le.2 ?_
    have hu_mem :
        u ∈
          Submodule.span ℂ ({coordPoint u v p z,
            coordPoint u v p (targetBridgeCoord z),
            coordPoint u v p (targetPoleCoord z)} : Set H) := by
      simpa [coordPoint_base] using
        (coordPoint_mem_targetFrameSpan (u := u) (v := v) (p := p)
          (z := z) (y := coordBase) hz hρ)
    have hv_mem :
        v ∈
          Submodule.span ℂ ({coordPoint u v p z,
            coordPoint u v p (targetBridgeCoord z),
            coordPoint u v p (targetPoleCoord z)} : Set H) := by
      simpa [coordPoint_vCoord] using
        (coordPoint_mem_targetFrameSpan (u := u) (v := v) (p := p)
          (z := z) (y := vCoord) hz hρ)
    have hp_mem :
        p ∈
          Submodule.span ℂ ({coordPoint u v p z,
            coordPoint u v p (targetBridgeCoord z),
            coordPoint u v p (targetPoleCoord z)} : Set H) := by
      simpa [coordPoint_poleCoord] using
        (coordPoint_mem_targetFrameSpan (u := u) (v := v) (p := p)
          (z := z) (y := poleCoord) hz hρ)
    intro x hx
    have hx' : x = u ∨ x = v ∨ x = p := by
      simpa using hx
    rcases hx' with rfl | rfl | rfl
    · exact hu_mem
    · exact hv_mem
    · exact hp_mem

lemma coordTraceValue_targetFrame
    (μ : FrameFunction H) (u v p : H)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    coordTraceValue μ (coordPoint u v p z)
        (coordPoint u v p (targetBridgeCoord z))
        (coordPoint u v p (targetPoleCoord z)) =
      coordTraceValue μ u v p := by
  have hspan := targetFrame_span_eq_original (u := u) (v := v) (p := p) hz hρ
  simp [coordTraceValue, GleasonRankOne.projectionOntoSpan,
    GleasonRankOne.projectionOntoSubmodule, hspan]

lemma polarSumValue_le_trace_add_p
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0) :
    polarSumValue μ u v p x ≤
      coordTraceValue μ u v p + frame_quadratic μ p := by
  let xH := coordPoint u v p x
  let qH := coordPoint u v p (targetPoleCoord x)
  let bH := coordPoint u v p (targetBridgeCoord x)
  let ux : ℝ × ℝ × ℝ := polarQuarterTurnCoord x
  let uq : ℝ × ℝ × ℝ := polarQuarterTurnCoord (targetPoleCoord x)
  let ub : ℝ × ℝ × ℝ := polarQuarterTurnCoord (targetBridgeCoord x)
  have huq_def : uq = targetPoleCoord ux := by
    simpa [ux, uq] using (targetPoleCoord_polarQuarterTurnCoord (x := x) hρ).symm
  have hub_def : ub = targetBridgeCoord ux := by
    simpa [ux, ub] using (targetBridgeCoord_polarQuarterTurnCoord (x := x) hρ).symm
  have hux : ux.1 ^ 2 + ux.2.1 ^ 2 + ux.2.2 ^ 2 = 1 := by
    exact polarQuarterTurnCoord_sq_sum hx
  have hρux : horizontalRadius ux ≠ 0 := by
    simpa [ux, horizontalRadius_polarQuarterTurnCoord x] using hρ
  have hxH : ‖xH‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hx
  have hqH : ‖qH‖ = 1 := by
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hbH : ‖bH‖ = 1 := by
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hx hρ
  have huxH : ‖coordPoint u v p ux‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hux
  have huqH : ‖coordPoint u v p uq‖ = 1 := by
    rw [huq_def]
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρux
  have hubH : ‖coordPoint u v p ub‖ = 1 := by
    rw [hub_def]
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hux hρux
  have hxq : inner (𝕜 := ℂ) xH qH = 0 := by
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρ
  have hxb : inner (𝕜 := ℂ) xH bH = 0 := by
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have hqb : inner (𝕜 := ℂ) qH bH = 0 := by
    exact inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have huxq : inner (𝕜 := ℂ) (coordPoint u v p ux) (coordPoint u v p uq) = 0 := by
    rw [huq_def]
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρux
  have huxb : inner (𝕜 := ℂ) (coordPoint u v p ux) (coordPoint u v p ub) = 0 := by
    rw [hub_def]
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρux
  have huqb :
      inner (𝕜 := ℂ) (coordPoint u v p uq) (coordPoint u v p ub) = 0 := by
    rw [huq_def, hub_def]
    exact inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρux
  have hsum₁ :
      frame_quadratic μ xH + frame_quadratic μ qH + frame_quadratic μ bH =
        coordTraceValue μ u v p := by
    have hsum :=
      GleasonRankOne.three_vector_sum (H := H) μ xH qH bH
        hxH hqH hbH hxq hxb hqb
    have hset :
        ({coordPoint u v p x,
            coordPoint u v p (targetBridgeCoord x),
            coordPoint u v p (targetPoleCoord x)} : Set H) =
          ({coordPoint u v p x,
            coordPoint u v p (targetPoleCoord x),
            coordPoint u v p (targetBridgeCoord x)} : Set H) := by
      ext t
      constructor <;> intro ht
      · rcases ht with rfl | rfl | rfl <;> simp
      · rcases ht with rfl | rfl | rfl <;> simp
    have htrace :
        coordTraceValue μ xH qH bH = coordTraceValue μ u v p := by
      simpa [coordTraceValue, xH, qH, bH, hset] using
        coordTraceValue_targetFrame (μ := μ) (u := u) (v := v) (p := p) hx hρ
    have hsum' :
        frame_quadratic μ xH + frame_quadratic μ qH + frame_quadratic μ bH =
          coordTraceValue μ xH qH bH := by
      simpa [coordTraceValue] using hsum
    linarith
  have hsum₂ :
      frame_quadratic μ (coordPoint u v p ux) +
          frame_quadratic μ (coordPoint u v p uq) +
          frame_quadratic μ (coordPoint u v p ub) =
        coordTraceValue μ u v p := by
    have hsum :=
      GleasonRankOne.three_vector_sum (H := H) μ
        (coordPoint u v p ux) (coordPoint u v p uq) (coordPoint u v p ub)
        huxH huqH hubH huxq huxb huqb
    have hset :
        ({coordPoint u v p ux,
            coordPoint u v p (targetBridgeCoord ux),
            coordPoint u v p (targetPoleCoord ux)} : Set H) =
          ({coordPoint u v p ux,
            coordPoint u v p uq,
            coordPoint u v p ub} : Set H) := by
      ext t
      constructor <;> intro ht
      · rcases ht with rfl | rfl | rfl <;> simp [huq_def, hub_def]
      · rcases ht with rfl | rfl | rfl <;> simp [huq_def, hub_def]
    have htrace :
        coordTraceValue μ (coordPoint u v p ux)
            (coordPoint u v p uq)
            (coordPoint u v p ub) =
          coordTraceValue μ u v p := by
      simpa [coordTraceValue, ux, uq, ub, hset] using
        coordTraceValue_targetFrame (μ := μ) (u := u) (v := v) (p := p) hux hρux
    have hsum' :
        frame_quadratic μ (coordPoint u v p ux) +
            frame_quadratic μ (coordPoint u v p uq) +
            frame_quadratic μ (coordPoint u v p ub) =
          coordTraceValue μ (coordPoint u v p ux)
            (coordPoint u v p uq)
            (coordPoint u v p ub) := by
      simpa [coordTraceValue] using hsum
    linarith
  have hqeq :
      polarSumValue μ u v p (targetPoleCoord x) =
        coordTraceValue μ u v p - frame_quadratic μ p := by
    apply polarSumValue_eq_trace_on_equator
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
    · exact targetPoleCoord_sq_sum hρ
    · simp [targetPoleCoord]
  have hb_nonneg : 0 ≤ frame_quadratic μ bH := frame_quadratic_nonneg μ bH
  have hub_nonneg : 0 ≤ frame_quadratic μ (coordPoint u v p ub) :=
    frame_quadratic_nonneg μ (coordPoint u v p ub)
  have hbound :
      polarSumValue μ u v p x + polarSumValue μ u v p (targetPoleCoord x) ≤
        2 * coordTraceValue μ u v p := by
    unfold polarSumValue at *
    linarith
  linarith

lemma frame_quadratic_p_le_coordTraceValue
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0) :
    frame_quadratic μ p ≤ coordTraceValue μ u v p := by
  have hsum :=
    GleasonRankOne.three_vector_sum (H := H) μ u v p hu hv hp huv hup hvp
  have hsum' :
      frame_quadratic μ u + frame_quadratic μ v + frame_quadratic μ p =
        coordTraceValue μ u v p := by
    simpa [coordTraceValue] using hsum
  have hu_nonneg : 0 ≤ frame_quadratic μ u := frame_quadratic_nonneg μ u
  have hv_nonneg : 0 ≤ frame_quadratic μ v := frame_quadratic_nonneg μ v
  linarith

lemma polarSumValue_le_trace_add_p_all
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    polarSumValue μ u v p x ≤
      coordTraceValue μ u v p + frame_quadratic μ p := by
  by_cases hρ : horizontalRadius x = 0
  · rcases eq_pole_or_negPole_of_horizontalRadius_eq_zero hx hρ with rfl | rfl
    · have hp_le :
        frame_quadratic μ p ≤ coordTraceValue μ u v p := by
        exact frame_quadratic_p_le_coordTraceValue (μ := μ) hu hv hp huv hup hvp
      have hpole :
          polarSumValue μ u v p poleCoord = 2 * frame_quadratic μ p := by
        simp [polarSumValue, poleCoord, polarQuarterTurnCoord, coordPoint]
        ring
      rw [hpole]
      linarith
    · have hp_le :
        frame_quadratic μ p ≤ coordTraceValue μ u v p := by
        exact frame_quadratic_p_le_coordTraceValue (μ := μ) hu hv hp huv hup hvp
      have hnegpole :
          polarSumValue μ u v p negPoleCoord = 2 * frame_quadratic μ p := by
        simp [polarSumValue, negPoleCoord, polarQuarterTurnCoord, coordPoint,
          frame_quadratic_neg]
        ring
      rw [hnegpole]
      linarith
  · exact polarSumValue_le_trace_add_p
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hx hρ

lemma coordTraceValue_targetFrameSwap
    (μ : FrameFunction H) (u v p : H)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    coordTraceValue μ (coordPoint u v p z)
        (coordPoint u v p (targetPoleCoord z))
        (coordPoint u v p (targetBridgeCoord z)) =
      coordTraceValue μ u v p := by
  have hset :
      ({coordPoint u v p z,
          coordPoint u v p (targetBridgeCoord z),
          coordPoint u v p (targetPoleCoord z)} : Set H) =
        ({coordPoint u v p z,
          coordPoint u v p (targetPoleCoord z),
          coordPoint u v p (targetBridgeCoord z)} : Set H) := by
    ext t
    constructor <;> intro ht
    · rcases ht with rfl | rfl | rfl <;> simp
    · rcases ht with rfl | rfl | rfl <;> simp
  simpa [coordTraceValue, hset] using
    coordTraceValue_targetFrame (μ := μ) (u := u) (v := v) (p := p) hz hρ

lemma polarQuarterTurnCoord_coordLinearCombo
    (a b c : ℝ) (x y z : ℝ × ℝ × ℝ) :
    polarQuarterTurnCoord (coordLinearCombo a b c x y z) =
      coordLinearCombo a b c
        (polarQuarterTurnCoord x)
        (polarQuarterTurnCoord y)
        (polarQuarterTurnCoord z) := by
  ext <;> unfold polarQuarterTurnCoord coordLinearCombo <;> ring

lemma targetFrameReparamSwap_polarQuarterTurn
    {x y : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius x ≠ 0) :
    polarQuarterTurnCoord (targetFrameReparamSwap x y) =
      targetFrameReparamSwap (polarQuarterTurnCoord x) y := by
  rw [targetFrameReparamSwap, targetFrameReparamSwap,
    polarQuarterTurnCoord_coordLinearCombo]
  simp [targetPoleCoord_polarQuarterTurnCoord hρ,
    targetBridgeCoord_polarQuarterTurnCoord hρ]

lemma targetFrameReparam_polarQuarterTurn
    {x y : ℝ × ℝ × ℝ}
    (hρ : horizontalRadius x ≠ 0) :
    polarQuarterTurnCoord (targetFrameReparam x y) =
      targetFrameReparam (polarQuarterTurnCoord x) y := by
  rw [targetFrameReparam, targetFrameReparam,
    polarQuarterTurnCoord_coordLinearCombo]
  simp [targetPoleCoord_polarQuarterTurnCoord hρ,
    targetBridgeCoord_polarQuarterTurnCoord hρ]

lemma ew_pair_sum_eq_base_targetPole
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0) :
    frame_quadratic μ (coordPoint u v p (targetFrameReparamSwap x y)) +
      frame_quadratic μ
        (coordPoint u v p (targetFrameReparamSwap x (polarQuarterTurnCoord y))) =
    frame_quadratic μ (coordPoint u v p x) +
      frame_quadratic μ (coordPoint u v p (targetPoleCoord x)) := by
  let xH := coordPoint u v p x
  let qH := coordPoint u v p (targetPoleCoord x)
  let bH := coordPoint u v p (targetBridgeCoord x)
  have hxH : ‖xH‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hx
  have hqH : ‖qH‖ = 1 := by
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hbH : ‖bH‖ = 1 := by
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hx hρ
  have hxq : inner (𝕜 := ℂ) xH qH = 0 := by
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρ
  have hxb : inner (𝕜 := ℂ) xH bH = 0 := by
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have hqb : inner (𝕜 := ℂ) qH bH = 0 := by
    exact inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have htrace :
      coordTraceValue μ xH qH bH = coordTraceValue μ u v p := by
    simpa [xH, qH, bH] using
      coordTraceValue_targetFrameSwap (μ := μ) (u := u) (v := v) (p := p) hx hρ
  have hlocal_y₀ :=
    polarSumValue_eq_trace_on_equator
      (hdim := hdim) (μ := μ)
      (u := xH) (v := qH) (p := bH)
      hxH hqH hbH hxq hxb hqb hy hy0
  have hlocal_y :
      frame_quadratic μ (coordPoint u v p (targetFrameReparamSwap x y)) +
        frame_quadratic μ
          (coordPoint u v p (targetFrameReparamSwap x (polarQuarterTurnCoord y))) =
      coordTraceValue μ u v p - frame_quadratic μ bH := by
    have htmp :
        polarSumValue μ xH qH bH y =
          coordTraceValue μ u v p - frame_quadratic μ bH := by
      linarith
    simpa [polarSumValue, xH, qH, bH, coordPoint_targetFrameReparamSwap] using htmp
  have hbase₀ :=
    polarSumValue_eq_trace_on_equator
      (hdim := hdim) (μ := μ)
      (u := xH) (v := qH) (p := bH)
      hxH hqH hbH hxq hxb hqb
      (x := coordBase) (by simp [coordBase]) (by simp [coordBase])
  have hbase :
      frame_quadratic μ (coordPoint u v p x) +
        frame_quadratic μ (coordPoint u v p (targetPoleCoord x)) =
      coordTraceValue μ u v p - frame_quadratic μ bH := by
    have htmp :
        polarSumValue μ xH qH bH coordBase =
          coordTraceValue μ u v p - frame_quadratic μ bH := by
      linarith
    have hcoord :
        polarQuarterTurnCoord coordBase = vCoord := by
      simp [coordBase, vCoord, polarQuarterTurnCoord]
    rw [polarSumValue, hcoord, coordPoint_base, coordPoint_vCoord] at htmp
    simpa [xH, qH, bH] using htmp
  linarith

lemma polarSumValue_pair_sum_eq_base_targetPole
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0) :
    polarSumValue μ u v p (targetFrameReparamSwap x y) +
      polarSumValue μ u v p (targetFrameReparamSwap x (polarQuarterTurnCoord y)) =
    polarSumValue μ u v p x + polarSumValue μ u v p (targetPoleCoord x) := by
  have hfirst :=
    ew_pair_sum_eq_base_targetPole
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hx hρ hy hy0
  have hux : (polarQuarterTurnCoord x).1 ^ 2 +
      (polarQuarterTurnCoord x).2.1 ^ 2 +
      (polarQuarterTurnCoord x).2.2 ^ 2 = 1 := by
    exact polarQuarterTurnCoord_sq_sum hx
  have hρux : horizontalRadius (polarQuarterTurnCoord x) ≠ 0 := by
    simpa [horizontalRadius_polarQuarterTurnCoord x] using hρ
  have hsecond₀ :=
    ew_pair_sum_eq_base_targetPole
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hux hρux hy hy0
      (x := polarQuarterTurnCoord x) (y := y)
  have hcomm₁ :
      polarQuarterTurnCoord (targetFrameReparamSwap x y) =
        targetFrameReparamSwap (polarQuarterTurnCoord x) y := by
    exact targetFrameReparamSwap_polarQuarterTurn (x := x) (y := y) hρ
  have hcomm₂ :
      polarQuarterTurnCoord (targetFrameReparamSwap x (polarQuarterTurnCoord y)) =
        targetFrameReparamSwap (polarQuarterTurnCoord x) (polarQuarterTurnCoord y) := by
    exact targetFrameReparamSwap_polarQuarterTurn
      (x := x) (y := polarQuarterTurnCoord y) hρ
  have hpole_comm :
      targetPoleCoord (polarQuarterTurnCoord x) =
        polarQuarterTurnCoord (targetPoleCoord x) := by
    exact targetPoleCoord_polarQuarterTurnCoord (x := x) hρ
  have hsecond :
      frame_quadratic μ
          (coordPoint u v p (polarQuarterTurnCoord (targetFrameReparamSwap x y))) +
        frame_quadratic μ
          (coordPoint u v p
            (polarQuarterTurnCoord (targetFrameReparamSwap x (polarQuarterTurnCoord y)))) =
      frame_quadratic μ (coordPoint u v p (polarQuarterTurnCoord x)) +
        frame_quadratic μ
          (coordPoint u v p (polarQuarterTurnCoord (targetPoleCoord x))) := by
    simpa [hcomm₁, hcomm₂, hpole_comm] using hsecond₀
  unfold polarSumValue
  linarith

lemma ew_pair_sum_eq_base_targetBridge
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0) :
    frame_quadratic μ (coordPoint u v p (targetFrameReparam x y)) +
      frame_quadratic μ
        (coordPoint u v p (targetFrameReparam x (polarQuarterTurnCoord y))) =
    frame_quadratic μ (coordPoint u v p x) +
      frame_quadratic μ (coordPoint u v p (targetBridgeCoord x)) := by
  let xH := coordPoint u v p x
  let bH := coordPoint u v p (targetBridgeCoord x)
  let qH := coordPoint u v p (targetPoleCoord x)
  have hxH : ‖xH‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hx
  have hbH : ‖bH‖ = 1 := by
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hx hρ
  have hqH : ‖qH‖ = 1 := by
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρ
  have hxb : inner (𝕜 := ℂ) xH bH = 0 := by
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
  have hxq : inner (𝕜 := ℂ) xH qH = 0 := by
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρ
  have hbq : inner (𝕜 := ℂ) bH qH = 0 := by
    have htmp := inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρ
    simpa [inner_eq_zero_symm, bH, qH] using htmp
  have hlocal_y₀ :=
    polarSumValue_eq_trace_on_equator
      (hdim := hdim) (μ := μ)
      (u := xH) (v := bH) (p := qH)
      hxH hbH hqH hxb hxq hbq hy hy0
  have hlocal_y :
      frame_quadratic μ (coordPoint u v p (targetFrameReparam x y)) +
        frame_quadratic μ
          (coordPoint u v p (targetFrameReparam x (polarQuarterTurnCoord y))) =
      coordTraceValue μ u v p - frame_quadratic μ qH := by
    have htmp :
        polarSumValue μ xH bH qH y =
          coordTraceValue μ u v p - frame_quadratic μ qH := by
      have htrace :
          coordTraceValue μ xH bH qH = coordTraceValue μ u v p := by
        simpa [xH, bH, qH] using
          coordTraceValue_targetFrame (μ := μ) (u := u) (v := v) (p := p) hx hρ
      linarith
    simpa [polarSumValue, xH, bH, qH, coordPoint_targetFrameReparam] using htmp
  have hbase₀ :=
    polarSumValue_eq_trace_on_equator
      (hdim := hdim) (μ := μ)
      (u := xH) (v := bH) (p := qH)
      hxH hbH hqH hxb hxq hbq
      (x := coordBase) (by simp [coordBase]) (by simp [coordBase])
  have hbase :
      frame_quadratic μ (coordPoint u v p x) +
        frame_quadratic μ (coordPoint u v p (targetBridgeCoord x)) =
      coordTraceValue μ u v p - frame_quadratic μ qH := by
    have htmp :
        polarSumValue μ xH bH qH coordBase =
          coordTraceValue μ u v p - frame_quadratic μ qH := by
      have htrace :
          coordTraceValue μ xH bH qH = coordTraceValue μ u v p := by
        simpa [xH, bH, qH] using
          coordTraceValue_targetFrame (μ := μ) (u := u) (v := v) (p := p) hx hρ
      linarith
    have hcoord :
        polarQuarterTurnCoord coordBase = vCoord := by
      simp [coordBase, vCoord, polarQuarterTurnCoord]
    rw [polarSumValue, hcoord, coordPoint_base, coordPoint_vCoord] at htmp
    simpa [xH, bH, qH] using htmp
  linarith

lemma polarSumValue_pair_sum_eq_base_targetBridge
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0) :
    polarSumValue μ u v p (targetFrameReparam x y) +
      polarSumValue μ u v p (targetFrameReparam x (polarQuarterTurnCoord y)) =
    polarSumValue μ u v p x + polarSumValue μ u v p (targetBridgeCoord x) := by
  have hfirst :=
    ew_pair_sum_eq_base_targetBridge
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hx hρ hy hy0
  have hux : (polarQuarterTurnCoord x).1 ^ 2 +
      (polarQuarterTurnCoord x).2.1 ^ 2 +
      (polarQuarterTurnCoord x).2.2 ^ 2 = 1 := by
    exact polarQuarterTurnCoord_sq_sum hx
  have hρux : horizontalRadius (polarQuarterTurnCoord x) ≠ 0 := by
    simpa [horizontalRadius_polarQuarterTurnCoord x] using hρ
  have hsecond₀ :=
    ew_pair_sum_eq_base_targetBridge
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hux hρux hy hy0
      (x := polarQuarterTurnCoord x) (y := y)
  have hcomm₁ :
      polarQuarterTurnCoord (targetFrameReparam x y) =
        targetFrameReparam (polarQuarterTurnCoord x) y := by
    exact targetFrameReparam_polarQuarterTurn (x := x) (y := y) hρ
  have hcomm₂ :
      polarQuarterTurnCoord (targetFrameReparam x (polarQuarterTurnCoord y)) =
        targetFrameReparam (polarQuarterTurnCoord x) (polarQuarterTurnCoord y) := by
    exact targetFrameReparam_polarQuarterTurn
      (x := x) (y := polarQuarterTurnCoord y) hρ
  have hbridge_comm :
      targetBridgeCoord (polarQuarterTurnCoord x) =
        polarQuarterTurnCoord (targetBridgeCoord x) := by
    exact targetBridgeCoord_polarQuarterTurnCoord (x := x) hρ
  have hsecond :
      frame_quadratic μ
          (coordPoint u v p (polarQuarterTurnCoord (targetFrameReparam x y))) +
        frame_quadratic μ
          (coordPoint u v p
            (polarQuarterTurnCoord (targetFrameReparam x (polarQuarterTurnCoord y)))) =
      frame_quadratic μ (coordPoint u v p (polarQuarterTurnCoord x)) +
        frame_quadratic μ
          (coordPoint u v p (polarQuarterTurnCoord (targetBridgeCoord x))) := by
    simpa [hcomm₁, hcomm₂, hbridge_comm] using hsecond₀
  unfold polarSumValue
  linarith

lemma polarSumValue_targetBridgeCoord_le_targetFrameReparam_pair_sum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0) :
    polarSumValue μ u v p (targetBridgeCoord x) ≤
      polarSumValue μ u v p (targetFrameReparam x y) +
        polarSumValue μ u v p (targetFrameReparam x (polarQuarterTurnCoord y)) := by
  have hpair :=
    polarSumValue_pair_sum_eq_base_targetBridge
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hx hρ hy hy0
  have hx_nonneg :
      0 ≤ polarSumValue μ u v p x := by
    unfold polarSumValue
    have hq₁ : 0 ≤ frame_quadratic μ (coordPoint u v p x) :=
      frame_quadratic_nonneg μ _
    have hq₂ :
        0 ≤ frame_quadratic μ (coordPoint u v p (polarQuarterTurnCoord x)) :=
      frame_quadratic_nonneg μ _
    linarith
  linarith

lemma polarSumValue_targetBridgeCoord_le_of_targetFrameReparam_pair_le
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {A B : ℝ}
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0)
    (hA : polarSumValue μ u v p (targetFrameReparam x y) ≤ A)
    (hB :
      polarSumValue μ u v p (targetFrameReparam x (polarQuarterTurnCoord y)) ≤ B) :
    polarSumValue μ u v p (targetBridgeCoord x) ≤ A + B := by
  have hbridge :=
    polarSumValue_targetBridgeCoord_le_targetFrameReparam_pair_sum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hx hρ hy hy0
  linarith

lemma polarSumValue_targetBridgeCoord_le_of_targetFrameReparam_pair_near_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η C₁ C₂ : ℝ}
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0)
    (hA : polarSumValue μ u v p (targetFrameReparam x y) ≤ C₁ * η)
    (hB :
      polarSumValue μ u v p (targetFrameReparam x (polarQuarterTurnCoord y)) ≤
        C₂ * η) :
    polarSumValue μ u v p (targetBridgeCoord x) ≤ (C₁ + C₂) * η := by
  have hbridge :=
    polarSumValue_targetBridgeCoord_le_of_targetFrameReparam_pair_le
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hx hρ hy hy0 hA hB
  nlinarith

lemma polarSumValue_add_targetBridgeCoord_eq_trace_add_p
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0) :
    polarSumValue μ u v p x +
      polarSumValue μ u v p (targetBridgeCoord x) =
    coordTraceValue μ u v p + frame_quadratic μ p := by
  have hxq : (polarQuarterTurnCoord x).1 ^ 2 +
      (polarQuarterTurnCoord x).2.1 ^ 2 +
      (polarQuarterTurnCoord x).2.2 ^ 2 = 1 := by
    exact polarQuarterTurnCoord_sq_sum hx
  have hρq : horizontalRadius (polarQuarterTurnCoord x) ≠ 0 := by
    simpa [horizontalRadius_polarQuarterTurnCoord x] using hρ
  have hbridge₁ :=
    frame_quadratic_targetBridge_identity
      (H := H) hdim μ hu hv hp huv hup hvp hx hρ
  have hbridge₂ :=
    frame_quadratic_targetBridge_identity
      (H := H) hdim μ hu hv hp huv hup hvp hxq hρq
      (z := polarQuarterTurnCoord x)
  have hunit_equator :
      (horizontalUnitCoord x).2.2 = 0 := by
    simp [horizontalUnitCoord]
  have hunit_sum :
      (horizontalUnitCoord x).1 ^ 2 +
      (horizontalUnitCoord x).2.1 ^ 2 +
      (horizontalUnitCoord x).2.2 ^ 2 = 1 := by
    exact horizontalUnitCoord_sq_sum hρ
  have hunit_trace :
      polarSumValue μ u v p (horizontalUnitCoord x) =
        coordTraceValue μ u v p - frame_quadratic μ p := by
    exact polarSumValue_eq_trace_on_equator
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hunit_sum hunit_equator
  have hbridge₂' :
      frame_quadratic μ
          (coordPoint u v p (polarQuarterTurnCoord x)) +
        frame_quadratic μ
          (coordPoint u v p (polarQuarterTurnCoord (targetBridgeCoord x))) =
      frame_quadratic μ
          (coordPoint u v p (polarQuarterTurnCoord (horizontalUnitCoord x))) +
        frame_quadratic μ p := by
    simpa [targetBridgeCoord_polarQuarterTurnCoord hρ,
      horizontalUnitCoord_polarQuarterTurnCoord hρ] using hbridge₂
  unfold polarSumValue at *
  linarith

lemma polarSumValue_lowHorizontalMeridianCoord_sub_eq_targetBridge_sub
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    polarSumValue μ u v p (lowHorizontalMeridianCoord z) -
      polarSumValue μ u v p z =
    polarSumValue μ u v p (targetBridgeCoord z) -
      polarSumValue μ u v p (targetBridgeCoord (lowHorizontalMeridianCoord z)) := by
  have hlow :
      (lowHorizontalMeridianCoord z).1 ^ 2 +
        (lowHorizontalMeridianCoord z).2.1 ^ 2 +
          (lowHorizontalMeridianCoord z).2.2 ^ 2 = 1 :=
    lowHorizontalMeridianCoord_sq_sum hρ
  have hρlow : horizontalRadius (lowHorizontalMeridianCoord z) ≠ 0 :=
    lowHorizontalMeridianCoord_horizontalRadius_ne_zero hρ
  have hz_id :=
    polarSumValue_add_targetBridgeCoord_eq_trace_add_p
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hz hρ
  have hlow_id :=
    polarSumValue_add_targetBridgeCoord_eq_trace_add_p
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hlow hρlow
  linarith

lemma polarSumValue_le_targetFrameReparamSwap_add_two_p
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0) :
    polarSumValue μ u v p x ≤
      polarSumValue μ u v p (targetFrameReparamSwap x y) +
        2 * frame_quadratic μ p := by
  let t : ℝ × ℝ × ℝ := targetFrameReparamSwap x (polarQuarterTurnCoord y)
  have hconst :=
    polarSumValue_pair_sum_eq_base_targetPole
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hx hρ hy hy0
  have ht :
      t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 1 := by
    have hyq : (polarQuarterTurnCoord y).1 ^ 2 +
        (polarQuarterTurnCoord y).2.1 ^ 2 +
        (polarQuarterTurnCoord y).2.2 ^ 2 = 1 := by
      exact polarQuarterTurnCoord_sq_sum hy
    simpa [t] using
      targetFrameReparamSwap_sq_sum hu hv hp huv hup hvp hx hyq hρ
  have ht_bound :
      polarSumValue μ u v p t ≤
        coordTraceValue μ u v p + frame_quadratic μ p := by
    exact polarSumValue_le_trace_add_p_all
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp ht
  have hqeq :
      polarSumValue μ u v p (targetPoleCoord x) =
        coordTraceValue μ u v p - frame_quadratic μ p := by
    apply polarSumValue_eq_trace_on_equator
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
    · exact targetPoleCoord_sq_sum hρ
    · simp [targetPoleCoord]
  simpa [t] using (by linarith [hconst, ht_bound, hqeq] :
    polarSumValue μ u v p x ≤
      polarSumValue μ u v p (targetFrameReparamSwap x y) +
        2 * frame_quadratic μ p)

lemma polarSumValue_le_targetFrameReparamSwap_add_two_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0) :
    polarSumValue μ u v p x ≤
      polarSumValue μ u v p (targetFrameReparamSwap x y) + 2 * η := by
  have hmain :=
    polarSumValue_le_targetFrameReparamSwap_add_two_p
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hx hρ hy hy0
  linarith

lemma polarSumValue_le_northMeridian_of_gleasonPsiSwap_zero_add_two_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {θ : ℝ} {y : ℝ × ℝ × ℝ}
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hρy : horizontalRadius y ≠ 0)
    (hψ : Thm25.gleasonPsiSwap θ y.1 y.2.1 y.2.2 = 0) :
    polarSumValue μ u v p y ≤
      polarSumValue μ u v p (northMeridianCoord θ) + 2 * η := by
  rcases exists_targetFrameSwap_northMeridian_of_gleasonPsiSwap_zero
      hu hv hp huv hup hvp hy hρy hψ with
    ⟨t, ht, ht0, ht_repr⟩
  have hmain :=
    polarSumValue_le_targetFrameReparamSwap_add_two_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hy hρy ht ht0
  simpa [ht_repr] using hmain

theorem exists_high_meridian_near_with_polarSum_le_north_add_two_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η θ ε : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) (hε : 0 < ε) :
    ∃ φ y,
      θ < φ ∧ φ < Real.pi / 2 ∧
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      horizontalRadius y ≠ 0 ∧
      dist y (0, (Real.cos φ, Real.sin φ)) ^ 2 < ε ∧
      polarSumValue μ u v p y ≤
        polarSumValue μ u v p (northMeridianCoord θ) + 2 * η := by
  rcases Thm25.exists_gleasonPsiSwap_zero_near_high_meridian_nonpolar
      (θ := θ) (ε := ε) hθ0 hθpi hε with
    ⟨φ, y, hθφ, hφpi, hy, hρy, hψ, hdist⟩
  have hle :
      polarSumValue μ u v p y ≤
        polarSumValue μ u v p (northMeridianCoord θ) + 2 * η :=
    polarSumValue_le_northMeridian_of_gleasonPsiSwap_zero_add_two_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hy hρy hψ
  exact ⟨φ, y, hθφ, hφpi, hy, hρy, hdist, hle⟩

theorem exists_near_pole_with_polarSum_le_north_add_two_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η θ ε : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) (hε : 0 < ε) :
    ∃ φ y,
      θ < φ ∧ φ < Real.pi / 2 ∧
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      horizontalRadius y ≠ 0 ∧
      dist y poleCoord < ε ∧
      polarSumValue μ u v p y ≤
        polarSumValue μ u v p (northMeridianCoord θ) + 2 * η := by
  rcases Thm25.exists_gleasonPsiSwap_zero_near_pole_nonpolar
      (θ := θ) (ε := ε) hθ0 hθpi hε with
    ⟨φ, y, hθφ, hφpi, hy, hρy, hψ, hdist⟩
  have hle :
      polarSumValue μ u v p y ≤
        polarSumValue μ u v p (northMeridianCoord θ) + 2 * η :=
    polarSumValue_le_northMeridian_of_gleasonPsiSwap_zero_add_two_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hy hρy hψ
  exact ⟨φ, y, hθφ, hφpi, hy, hρy, hdist, hle⟩

lemma exists_rotated_high_meridian_near_with_polarSum_le_positive_point_add_two_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ y,
      Real.arcsin z.2.2 < φ ∧ φ < Real.pi / 2 ∧
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      horizontalRadius y ≠ 0 ∧
      dist y (northMeridianCoord φ) ^ 2 < ε ∧
      polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p y ≤
        polarSumValue μ u v p z + 2 * η := by
  have hzlt1 : z.2.2 < 1 := by
    by_contra hznot
    have hge : 1 ≤ z.2.2 := le_of_not_gt hznot
    have hsq : 1 ≤ z.2.2 ^ 2 := by
      nlinarith
    have hsum : z.1 ^ 2 + z.2.1 ^ 2 = 0 := by
      nlinarith [hz, hsq]
    have hz1 : z.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have hz2 : z.2.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have hρ0 : horizontalRadius z = 0 := by
      have hsq0 : horizontalRadius z ^ 2 = 0 := by
        rw [horizontalRadius_sq z]
        nlinarith [hz1, hz2]
      nlinarith [sq_nonneg (horizontalRadius z), hsq0]
    exact hρ hρ0
  rcases arcsin_mem_open_quarter hzpos hzlt1 with ⟨hθ0, hθpi⟩
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'w : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc]
        using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    dsimp [w]
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [coordPoint_poleCoord u v p] using hwp'
  rcases exists_high_meridian_near_with_polarSum_le_north_add_two_eta
      (hdim := hdim) (μ := μ)
      (u := u') (v := w) (p := p)
      hu' hw hp hu'w hu'p hwp hη hθ0 hθpi hε with
    ⟨φ, y, hθφ, hφpi, hy, hρy, hdist, hpolar⟩
  have hreparam :
      polarSumValue μ u' w p (northMeridianCoord (Real.arcsin z.2.2)) =
        polarSumValue μ u v p z := by
    rw [← meridianFrameCoords_self_eq_northMeridian (z := z) hz hρ (le_of_lt hzpos)]
    dsimp [u', w]
    rw [polarSumValue_meridianFrameCoords
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (x := z) hρ]
  refine ⟨φ, y, hθφ, hφpi, hy, hρy, ?_, ?_⟩
  · simpa [northMeridianCoord] using hdist
  · dsimp [u', w] at hpolar hreparam ⊢
    linarith

lemma exists_rotated_high_near_pole_with_polarSum_le_positive_point_add_two_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ y,
      Real.arcsin z.2.2 < φ ∧ φ < Real.pi / 2 ∧
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      horizontalRadius y ≠ 0 ∧
      dist y poleCoord < ε ∧
      polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p y ≤
        polarSumValue μ u v p z + 2 * η := by
  have hzlt1 : z.2.2 < 1 := by
    by_contra hznot
    have hge : 1 ≤ z.2.2 := le_of_not_gt hznot
    have hsq : 1 ≤ z.2.2 ^ 2 := by
      nlinarith
    have hsum : z.1 ^ 2 + z.2.1 ^ 2 = 0 := by
      nlinarith [hz, hsq]
    have hz1 : z.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have hz2 : z.2.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have hρ0 : horizontalRadius z = 0 := by
      have hsq0 : horizontalRadius z ^ 2 = 0 := by
        rw [horizontalRadius_sq z]
        nlinarith [hz1, hz2]
      nlinarith [sq_nonneg (horizontalRadius z), hsq0]
    exact hρ hρ0
  rcases arcsin_mem_open_quarter hzpos hzlt1 with ⟨hθ0, hθpi⟩
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'w : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc]
        using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    dsimp [w]
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [coordPoint_poleCoord u v p] using hwp'
  rcases exists_near_pole_with_polarSum_le_north_add_two_eta
      (hdim := hdim) (μ := μ)
      (u := u') (v := w) (p := p)
      hu' hw hp hu'w hu'p hwp hη hθ0 hθpi hε with
    ⟨φ, y, hθφ, hφpi, hy, hρy, hdist, hpolar⟩
  have hreparam :
      polarSumValue μ u' w p (northMeridianCoord (Real.arcsin z.2.2)) =
        polarSumValue μ u v p z := by
    rw [← meridianFrameCoords_self_eq_northMeridian (z := z) hz hρ (le_of_lt hzpos)]
    dsimp [u', w]
    rw [polarSumValue_meridianFrameCoords
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (x := z) hρ]
  refine ⟨φ, y, hθφ, hφpi, hy, hρy, hdist, ?_⟩
  dsimp [u', w] at hpolar hreparam ⊢
  linarith

lemma exists_rotated_high_meridian_near_nonpole_infimum_add_three_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ y,
      Real.arcsin z.2.2 < φ ∧ φ < Real.pi / 2 ∧
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      horizontalRadius y ≠ 0 ∧
      dist y (northMeridianCoord φ) ^ 2 < ε ∧
      polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p y ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
  rcases exists_rotated_high_meridian_near_with_polarSum_le_positive_point_add_two_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos hε with
    ⟨φ, y, hθφ, hφpi, hy, hρy, hdist, hpolar⟩
  refine ⟨φ, y, hθφ, hφpi, hy, hρy, hdist, ?_⟩
  linarith

lemma exists_rotated_high_near_pole_nonpole_infimum_add_three_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ y,
      Real.arcsin z.2.2 < φ ∧ φ < Real.pi / 2 ∧
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      horizontalRadius y ≠ 0 ∧
      dist y poleCoord < ε ∧
      polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p y ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
  rcases exists_rotated_high_near_pole_with_polarSum_le_positive_point_add_two_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos hε with
    ⟨φ, y, hθφ, hφpi, hy, hρy, hdist, hpolar⟩
  refine ⟨φ, y, hθφ, hφpi, hy, hρy, hdist, ?_⟩
  linarith

lemma nonpole_infimum_le_rotated_nonpole_infimum
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    sInf (northOpenNonpolePolarSumSet μ u v p) ≤
      sInf (northOpenNonpolePolarSumSet μ
        (coordPoint u v p (-targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z))
        p) := by
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  apply le_csInf
    (northOpenNonpolePolarSumSet_nonempty μ u' w p)
  intro r hr
  rcases hr with ⟨a, ha, hapos, hρa, rfl⟩
  have ha' :
      (meridianFrameReparam z a).1 ^ 2 +
        (meridianFrameReparam z a).2.1 ^ 2 +
          (meridianFrameReparam z a).2.2 ^ 2 = 1 :=
    meridianFrameReparam_sq_sum ha hρ
  have hapos' : 0 < (meridianFrameReparam z a).2.2 := by
    simpa [meridianFrameReparam_explicit hρ] using hapos
  have halt : a.2.2 < 1 := by
    by_contra hnot
    have hge : 1 ≤ a.2.2 := le_of_not_gt hnot
    have hsq : 1 ≤ a.2.2 ^ 2 := by
      nlinarith
    have hsum : a.1 ^ 2 + a.2.1 ^ 2 = 0 := by
      nlinarith [ha, hsq]
    have hzero : horizontalRadius a = 0 := by
      have hsq0 : horizontalRadius a ^ 2 = 0 := by
        rw [horizontalRadius_sq a]
        nlinarith [hsum]
      nlinarith [sq_nonneg (horizontalRadius a), hsq0]
    exact hρa hzero
  have halt' : (meridianFrameReparam z a).2.2 < 1 := by
    simpa [meridianFrameReparam_explicit hρ] using halt
  have hρa' : horizontalRadius (meridianFrameReparam z a) ≠ 0 := by
    intro hzero
    have hsq0 : horizontalRadius (meridianFrameReparam z a) ^ 2 = 0 := by
      nlinarith
    rw [horizontalRadius_sq (meridianFrameReparam z a)] at hsq0
    have hthird_one : (meridianFrameReparam z a).2.2 ^ 2 = 1 := by
      nlinarith [ha', hsq0]
    nlinarith
  have hle :
      sInf (northOpenNonpolePolarSumSet μ u v p) ≤
        polarSumValue μ u v p (meridianFrameReparam z a) :=
    csInf_le
      (northOpenNonpolePolarSumSet_bddBelow μ u v p)
      ⟨meridianFrameReparam z a, ha', hapos', hρa', rfl⟩
  dsimp [u', w]
  rwa [polarSumValue_meridianFrameReparam
    (μ := μ) (u := u) (v := v) (p := p) (z := z) (y := a) hρ]

lemma rotated_nonpole_infimum_le_nonpole_infimum_add_three_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    sInf (northOpenNonpolePolarSumSet μ
        (coordPoint u v p (-targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z))
        p) ≤
      sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
  let ε : ℝ := (1 : ℝ) / 4
  have hε : 0 < ε := by norm_num [ε]
  rcases exists_rotated_high_near_pole_nonpole_infimum_add_three_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos hzβ hε with
    ⟨φ, y, _hθφ, _hφpi, hy, hρy, hdist, hpolar⟩
  have hypos : 0 < y.2.2 := by
    have hthird_close :
        |y.2.2 - poleCoord.2.2| < ε :=
      coord_snd_snd_abs_sub_lt_of_dist_lt (x := y) (y := poleCoord) hdist
    have hlow := (abs_lt.mp hthird_close).1
    dsimp [poleCoord, ε] at hlow
    linarith
  have hle :
      sInf (northOpenNonpolePolarSumSet μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p) ≤
        polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p y :=
    csInf_le
      (northOpenNonpolePolarSumSet_bddBelow μ
        (coordPoint u v p (-targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z))
        p)
      ⟨y, hy, hypos, hρy, rfl⟩
  linarith

lemma rotated_nonpole_infimum_band
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    sInf (northOpenNonpolePolarSumSet μ u v p) ≤
        sInf (northOpenNonpolePolarSumSet μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p) ∧
      sInf (northOpenNonpolePolarSumSet μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p) ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
  exact ⟨
    nonpole_infimum_le_rotated_nonpole_infimum
      (μ := μ) hu hv hp huv hup hvp hz hρ,
    rotated_nonpole_infimum_le_nonpole_infimum_add_three_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos hzβ⟩

lemma exists_rotated_high_positive_meridian_near_nonpole_infimum_add_three_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    ∃ φ y,
      Real.arcsin z.2.2 < φ ∧ φ < Real.pi / 2 ∧
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      0 < y.2.2 ∧
      horizontalRadius y ≠ 0 ∧
      polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p y ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
  let ε : ℝ := (z.2.2 / 2) ^ 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  rcases exists_rotated_high_meridian_near_nonpole_infimum_add_three_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos hzβ hε with
    ⟨φ, y, hθφ, hφpi, hy, hρy, hdist, hpolar⟩
  have hzle1 : z.2.2 ≤ 1 := by
    nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, sq_nonneg (z.2.2 - 1), hz]
  have hsin_gt : z.2.2 < Real.sin φ := by
    have hθ_nonneg : -(Real.pi / 2) ≤ Real.arcsin z.2.2 := by
      have hθ0 : 0 < Real.arcsin z.2.2 :=
        Real.arcsin_pos.mpr hzpos
      nlinarith [Real.pi_pos]
    have hsin_lt :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        hθ_nonneg (le_of_lt hφpi) hθφ
    rwa [Real.sin_arcsin (by linarith : -1 ≤ z.2.2) hzle1] at hsin_lt
  have hdist_lt : dist y (northMeridianCoord φ) < z.2.2 / 2 := by
    have hdist_nonneg : 0 ≤ dist y (northMeridianCoord φ) := dist_nonneg
    have hhalf_pos : 0 < z.2.2 / 2 := by positivity
    dsimp [ε] at hdist
    nlinarith
  have hthird_close :
      |y.2.2 - (northMeridianCoord φ).2.2| < z.2.2 / 2 :=
    coord_snd_snd_abs_sub_lt_of_dist_lt (x := y) (y := northMeridianCoord φ) hdist_lt
  have hypos : 0 < y.2.2 := by
    have hlow := (abs_lt.mp hthird_close).1
    simp [northMeridianCoord] at hlow
    nlinarith
  exact ⟨φ, y, hθφ, hφpi, hy, hypos, hρy, hpolar⟩

lemma exists_rotated_high_positive_meridian_near_nonpole_infimum_add_three_eta_with_third
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    ∃ φ y,
      Real.arcsin z.2.2 < φ ∧ φ < Real.pi / 2 ∧
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      z.2.2 / 2 < y.2.2 ∧
      0 < y.2.2 ∧
      horizontalRadius y ≠ 0 ∧
      polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p y ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
  let ε : ℝ := (z.2.2 / 2) ^ 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  rcases exists_rotated_high_meridian_near_nonpole_infimum_add_three_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos hzβ hε with
    ⟨φ, y, hθφ, hφpi, hy, hρy, hdist, hpolar⟩
  have hzle1 : z.2.2 ≤ 1 := by
    nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, sq_nonneg (z.2.2 - 1), hz]
  have hsin_gt : z.2.2 < Real.sin φ := by
    have hθ_nonneg : -(Real.pi / 2) ≤ Real.arcsin z.2.2 := by
      have hθ0 : 0 < Real.arcsin z.2.2 :=
        Real.arcsin_pos.mpr hzpos
      nlinarith [Real.pi_pos]
    have hsin_lt :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two
        hθ_nonneg (le_of_lt hφpi) hθφ
    rwa [Real.sin_arcsin (by linarith : -1 ≤ z.2.2) hzle1] at hsin_lt
  have hdist_lt : dist y (northMeridianCoord φ) < z.2.2 / 2 := by
    have hdist_nonneg : 0 ≤ dist y (northMeridianCoord φ) := dist_nonneg
    have hhalf_pos : 0 < z.2.2 / 2 := by positivity
    dsimp [ε] at hdist
    nlinarith
  have hthird_close :
      |y.2.2 - (northMeridianCoord φ).2.2| < z.2.2 / 2 :=
    coord_snd_snd_abs_sub_lt_of_dist_lt (x := y) (y := northMeridianCoord φ) hdist_lt
  have hygt : z.2.2 / 2 < y.2.2 := by
    have hlow := (abs_lt.mp hthird_close).1
    simp [northMeridianCoord] at hlow
    nlinarith
  have hypos : 0 < y.2.2 := by
    nlinarith
  exact ⟨φ, y, hθφ, hφpi, hy, hygt, hypos, hρy, hpolar⟩

lemma polarSumValue_le_two_step_targetFrame_add_four_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {x y z s t : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρx : horizontalRadius x ≠ 0)
    (hs : s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 = 1)
    (hs0 : s.2.2 = 0)
    (hy_def : y = targetFrameReparamSwap x s)
    (hρy : horizontalRadius y ≠ 0)
    (ht : t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 1)
    (ht0 : t.2.2 = 0)
    (hz_def : z = targetFrameReparamSwap y t) :
    polarSumValue μ u v p x ≤ polarSumValue μ u v p z + 4 * η := by
  have hy :
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 := by
    rw [hy_def]
    exact targetFrameReparamSwap_sq_sum hu hv hp huv hup hvp hx hs hρx
  have hxy :
      polarSumValue μ u v p x ≤ polarSumValue μ u v p y + 2 * η := by
    simpa [hy_def] using
      polarSumValue_le_targetFrameReparamSwap_add_two_eta
        (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hx hρx hs hs0
  have hyz :
      polarSumValue μ u v p y ≤ polarSumValue μ u v p z + 2 * η := by
    simpa [hz_def] using
      polarSumValue_le_targetFrameReparamSwap_add_two_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hy hρy ht ht0
  linarith

lemma polarSumValue_northMeridian_le_lower_northMeridian_add_four_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η θ φ : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    (hθ0 : 0 < θ) (hθφ : θ < φ) (hφpi : φ < Real.pi / 2) :
    polarSumValue μ u v p (northMeridianCoord φ) ≤
      polarSumValue μ u v p (northMeridianCoord θ) + 4 * η := by
  have hθpi : θ < Real.pi / 2 := by linarith
  have hx : (northMeridianCoord φ).1 ^ 2 +
      (northMeridianCoord φ).2.1 ^ 2 +
      (northMeridianCoord φ).2.2 ^ 2 = 1 :=
    northMeridianCoord_sq_sum φ
  have hρx : horizontalRadius (northMeridianCoord φ) ≠ 0 := by
    exact northMeridianCoord_horizontalRadius_ne_zero
      (lt_trans hθ0 hθφ) hφpi
  have hneg :
      Thm25.gleasonPsiSwap θ (northMeridianCoord φ).1
        (northMeridianCoord φ).2.1 (northMeridianCoord φ).2.2 < 0 := by
    simpa [northMeridianCoord, Thm25.gleasonPsiSwap] using
      (Thm25.gleasonPsi_meridian_neg
        (θ := θ) (φ := φ) hθ0 hθφ hφpi)
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hx hneg with
    ⟨y, s, t, _hy, hρy, hs, hs0, ht, ht0, hy_def, hz_def⟩
  exact polarSumValue_le_two_step_targetFrame_add_four_eta
    (hdim := hdim) (μ := μ) (z := northMeridianCoord θ)
    hu hv hp huv hup hvp hη hx hρx hs hs0 hy_def hρy ht ht0 hz_def

lemma polarSumValue_rotated_northMeridian_le_positive_point_add_four_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η θ : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    (hθpi : θ < Real.pi / 2)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hφθ : Real.arcsin z.2.2 < θ) :
    polarSumValue μ
        (coordPoint u v p (-targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z))
        p (northMeridianCoord θ) ≤
      polarSumValue μ u v p z + 4 * η := by
  have hzlt1 : z.2.2 < 1 := by
    by_contra hznot
    have hge : 1 ≤ z.2.2 := le_of_not_gt hznot
    have hsq : 1 ≤ z.2.2 ^ 2 := by nlinarith
    have hsum : z.1 ^ 2 + z.2.1 ^ 2 = 0 := by
      nlinarith [hz, hsq]
    have hz1 : z.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have hz2 : z.2.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have hρ0 : horizontalRadius z = 0 := by
      have hsq0 : horizontalRadius z ^ 2 = 0 := by
        rw [horizontalRadius_sq z]
        nlinarith [hz1, hz2]
      nlinarith [sq_nonneg (horizontalRadius z), hsq0]
    exact hρ hρ0
  rcases arcsin_mem_open_quarter hzpos hzlt1 with ⟨hφ0, hφpi⟩
  have hθ0 : 0 < θ := lt_trans hφ0 hφθ
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'w : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc]
        using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    dsimp [w]
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [coordPoint_poleCoord u v p] using hwp'
  have hmeridian :
      polarSumValue μ u' w p (northMeridianCoord θ) ≤
        polarSumValue μ u' w p
          (northMeridianCoord (Real.arcsin z.2.2)) + 4 * η := by
    exact polarSumValue_northMeridian_le_lower_northMeridian_add_four_eta
      (hdim := hdim) (μ := μ) hu' hw hp hu'w hu'p hwp hη
      hφ0 hφθ hθpi
  have hreparam :
      polarSumValue μ u' w p (northMeridianCoord (Real.arcsin z.2.2)) =
        polarSumValue μ u v p z := by
    rw [← meridianFrameCoords_self_eq_northMeridian (z := z) hz hρ (le_of_lt hzpos)]
    dsimp [u', w]
    rw [polarSumValue_meridianFrameCoords
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (x := z) hρ]
  dsimp [u', w] at hmeridian
  linarith

lemma polarSumValue_high_point_le_lowHorizontalMeridianCoord_add_four_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hhigh : Real.pi / 6 < Real.arcsin z.2.2) :
    polarSumValue μ u v p z ≤
      polarSumValue μ u v p (lowHorizontalMeridianCoord z) + 4 * η := by
  have hzlt1 : z.2.2 < 1 := by
    by_contra hznot
    have hge : 1 ≤ z.2.2 := le_of_not_gt hznot
    have hsq : 1 ≤ z.2.2 ^ 2 := by nlinarith
    have hsum : z.1 ^ 2 + z.2.1 ^ 2 = 0 := by
      nlinarith [hz, hsq]
    have hz1 : z.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have hz2 : z.2.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have hρ0 : horizontalRadius z = 0 := by
      have hsq0 : horizontalRadius z ^ 2 = 0 := by
        rw [horizontalRadius_sq z]
        nlinarith [hz1, hz2]
      nlinarith [sq_nonneg (horizontalRadius z), hsq0]
    exact hρ hρ0
  rcases arcsin_mem_open_quarter hzpos hzlt1 with ⟨hφ0, hφpi⟩
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'w : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc]
        using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    dsimp [w]
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [coordPoint_poleCoord u v p] using hwp'
  have hsix_pos : 0 < Real.pi / 6 := by positivity
  have hlow_high :
      polarSumValue μ u' w p (northMeridianCoord (Real.arcsin z.2.2)) ≤
        polarSumValue μ u' w p (northMeridianCoord (Real.pi / 6)) + 4 * η := by
    exact polarSumValue_northMeridian_le_lower_northMeridian_add_four_eta
      (hdim := hdim) (μ := μ) hu' hw hp hu'w hu'p hwp hη
      hsix_pos hhigh hφpi
  have hz_reparam :
      polarSumValue μ u' w p (northMeridianCoord (Real.arcsin z.2.2)) =
        polarSumValue μ u v p z := by
    rw [← meridianFrameCoords_self_eq_northMeridian (z := z) hz hρ (le_of_lt hzpos)]
    dsimp [u', w]
    rw [polarSumValue_meridianFrameCoords
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (x := z) hρ]
  have hlow_reparam :
      polarSumValue μ u' w p (northMeridianCoord (Real.pi / 6)) =
        polarSumValue μ u v p (lowHorizontalMeridianCoord z) := by
    dsimp [u', w, lowHorizontalMeridianCoord]
    rw [polarSumValue_meridianFrameReparam
      (μ := μ) (u := u) (v := v) (p := p) (z := z)
      (y := northMeridianCoord (Real.pi / 6)) hρ]
    simp [northMeridianCoord]
  linarith

lemma polarSumValue_band_of_two_step_near_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    {x y z s t : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρx : horizontalRadius x ≠ 0)
    (hs : s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 = 1)
    (hs0 : s.2.2 = 0)
    (hy_def : y = targetFrameReparamSwap x s)
    (hρy : horizontalRadius y ≠ 0)
    (ht : t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 1)
    (ht0 : t.2.2 = 0)
    (hz_def : z = targetFrameReparamSwap y t)
    (hzβ : polarSumValue μ u v p z ≤ β + η) :
    β ≤ polarSumValue μ u v p x ∧
      polarSumValue μ u v p x ≤ β + 5 * η := by
  have hlow : β ≤ polarSumValue μ u v p x := hβ hx
  have hstep :
      polarSumValue μ u v p x ≤ polarSumValue μ u v p z + 4 * η := by
    exact polarSumValue_le_two_step_targetFrame_add_four_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη
      hx hρx hs hs0 hy_def hρy ht ht0 hz_def
  constructor
  · exact hlow
  · linarith

lemma continuous_gleasonPsiSwap
    (θ : ℝ) :
    Continuous (fun x : ℝ × ℝ × ℝ =>
      Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2) := by
  have hξ : Continuous (fun x : ℝ × ℝ × ℝ => x.1) := continuous_fst
  have hη : Continuous (fun x : ℝ × ℝ × ℝ => x.2.1) := continuous_snd.fst
  have hr : Continuous (fun x : ℝ × ℝ × ℝ => x.2.2) := continuous_snd.snd
  unfold Thm25.gleasonPsiSwap Thm25.gleasonPsi
  exact ((hη.pow 2).add (hξ.pow 2)).mul continuous_const |>.sub
    ((hη.mul hr).mul continuous_const)

lemma exists_local_band_neighborhood_of_meridian_near_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      ∀ {x : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        dist x x0 < δ →
        β ≤ polarSumValue μ u v p x ∧
          polarSumValue μ u v p x ≤ β + 5 * η := by
  rcases Thm25.exists_sphere_point_with_gleasonPsiSwap_neg hθ0 hθpi with
    ⟨ξ0, η0, r0, hx0, hneg0⟩
  let x0 : ℝ × ℝ × ℝ := (ξ0, (η0, r0))
  let ψ : ℝ × ℝ × ℝ → ℝ := fun x =>
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2
  have hcont : Continuous ψ := by
    simpa [ψ] using continuous_gleasonPsiSwap θ
  have hopen : IsOpen {x : ℝ × ℝ × ℝ | ψ x < 0} :=
    hcont.isOpen_preimage _ isOpen_Iio
  have hx0mem : x0 ∈ {x : ℝ × ℝ × ℝ | ψ x < 0} := by
    simpa [x0, ψ] using hneg0
  have hnhds : {x : ℝ × ℝ × ℝ | ψ x < 0} ∈ nhds x0 := hopen.mem_nhds hx0mem
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδ, hball⟩
  refine ⟨x0, δ, hδ, by simpa [x0] using hx0, ?_⟩
  intro x hx hdist
  have hneg : Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 := by
    exact hball hdist
  have hρx : horizontalRadius x ≠ 0 := by
    exact horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hneg
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hx hneg with
    ⟨y, s, t, hy, hρy, hs, hs0, ht, ht0, hy_def, hz_def⟩
  exact polarSumValue_band_of_two_step_near_infimum
    (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
    hβ hη hx hρx hs hs0 hy_def hρy ht ht0 hz_def hzβ

lemma exists_local_band_neighborhood_of_meridian_near_infimum_on_north
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      0 < x0.2.2 ∧
      ∀ {x : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        dist x x0 < δ →
        0 < x.2.2 ∧
        β ≤ polarSumValue μ u v p x ∧
          polarSumValue μ u v p x ≤ β + 5 * η := by
  rcases Thm25.exists_sphere_point_with_gleasonPsiSwap_neg_pos hθ0 hθpi with
    ⟨ξ0, η0, r0, hx0, hx0pos, hneg0⟩
  let x0 : ℝ × ℝ × ℝ := (ξ0, (η0, r0))
  let ψ : ℝ × ℝ × ℝ → ℝ := fun x =>
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2
  have hcont : Continuous ψ := by
    simpa [ψ] using continuous_gleasonPsiSwap θ
  have hopenψ : IsOpen {x : ℝ × ℝ × ℝ | ψ x < 0} :=
    hcont.isOpen_preimage _ isOpen_Iio
  have hopenr : IsOpen {x : ℝ × ℝ × ℝ | 0 < x.2.2} :=
    continuous_snd.snd.isOpen_preimage _ isOpen_Ioi
  have hx0memψ : x0 ∈ {x : ℝ × ℝ × ℝ | ψ x < 0} := by
    simpa [x0, ψ] using hneg0
  have hx0memr : x0 ∈ {x : ℝ × ℝ × ℝ | 0 < x.2.2} := by
    simpa [x0] using hx0pos
  have hnhds :
      {x : ℝ × ℝ × ℝ | ψ x < 0 ∧ 0 < x.2.2} ∈ nhds x0 := by
    exact Filter.inter_mem (hopenψ.mem_nhds hx0memψ) (hopenr.mem_nhds hx0memr)
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδ, hball⟩
  refine ⟨x0, δ, hδ, by simpa [x0] using hx0, by simpa [x0] using hx0pos, ?_⟩
  intro x hx hdist
  have hxball : x ∈ {x : ℝ × ℝ × ℝ | ψ x < 0 ∧ 0 < x.2.2} := hball hdist
  have hneg : Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 := hxball.1
  have hxpos : 0 < x.2.2 := hxball.2
  have hρx : horizontalRadius x ≠ 0 := by
    exact horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hneg
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hx hneg with
    ⟨y, s, t, hy, hρy, hs, hs0, ht, ht0, hy_def, hz_def⟩
  have hstep :
      polarSumValue μ u v p x ≤
        polarSumValue μ u v p (northMeridianCoord θ) + 4 * η := by
    exact polarSumValue_le_two_step_targetFrame_add_four_eta
      (hdim := hdim) (μ := μ) (z := northMeridianCoord θ) hu hv hp huv hup hvp hη
      hx hρx hs hs0 hy_def hρy ht ht0 hz_def
  have hlow : β ≤ polarSumValue μ u v p x := hβ (w := x) hx hxpos hρx
  have hhigh : polarSumValue μ u v p x ≤ β + 5 * η := by
    linarith
  exact ⟨hxpos, hlow, hhigh⟩

lemma exists_local_band_neighborhood_of_meridian_near_infimum_on_north_uniform
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      0 < x0.2.2 ∧
      horizontalRadius x0 ≠ 0 ∧
      ∀ {H : Type*}
        [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        [FiniteDimensional ℂ H],
        3 ≤ Module.finrank ℂ H →
        ∀ (μ : FrameFunction H) {u v p : H},
          (hu : ‖u‖ = 1) → (hv : ‖v‖ = 1) → (hp : ‖p‖ = 1) →
          (huv : inner (𝕜 := ℂ) u v = 0) →
          inner (𝕜 := ℂ) u p = 0 →
          inner (𝕜 := ℂ) v p = 0 →
          ∀ {β η : ℝ},
            (∀ {w : ℝ × ℝ × ℝ},
              w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
              0 < w.2.2 →
              horizontalRadius w ≠ 0 →
              β ≤ polarSumValue μ u v p w) →
            frame_quadratic μ p ≤ η →
            polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η →
            ∀ {x : ℝ × ℝ × ℝ},
              x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
              dist x x0 < δ →
              0 < x.2.2 ∧
              β ≤ polarSumValue μ u v p x ∧
                polarSumValue μ u v p x ≤ β + 5 * η := by
  let x0 : ℝ × ℝ × ℝ := psiCenterCoord θ
  let δ : ℝ := Real.cos θ / 256
  have hcos_pos : 0 < Real.cos θ := by
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθpi⟩
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hx0 : x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 := by
    simpa [x0] using psiCenterCoord_sq_sum θ
  have hx0pos : 0 < x0.2.2 := by
    simpa [x0] using psiCenterCoord_third_pos hθ0 hθpi
  have hρx0 : horizontalRadius x0 ≠ 0 := by
    simpa [x0] using horizontalRadius_psiCenterCoord_ne_zero hθ0 hθpi
  refine ⟨x0, δ, hδ, hx0, hx0pos, hρx0, ?_⟩
  intro H _ _ _ _ hdim μ u v p hu hv hp huv hup hvp β η hβ hη hzβ x hx hdist
  have hneg : Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 := by
    simpa [x0, δ] using
      (gleasonPsiSwap_lt_zero_of_dist_psiCenterCoord_linear
        (θ := θ) hθ0 hθpi hx hdist)
  have hxpos : 0 < x.2.2 := by
    have hthird_close :
        |x.2.2 - x0.2.2| < δ :=
      coord_snd_snd_abs_sub_lt_of_dist_lt (x := x) (y := x0) hdist
    have hthird_low : -δ < x.2.2 - x0.2.2 := (abs_lt.mp hthird_close).1
    have hx0_gt_half : (1 : ℝ) / 2 < x0.2.2 := by
      simpa [x0] using psiCenterCoord_third_gt_half θ
    have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hδ_lt_half : δ < (1 : ℝ) / 2 := by
      dsimp [δ]
      nlinarith
    linarith
  have hρx : horizontalRadius x ≠ 0 :=
    horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hneg
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hx hneg with
    ⟨y, s, t, hy, hρy, hs, hs0, ht, ht0, hy_def, hz_def⟩
  have hstep :
      polarSumValue μ u v p x ≤
        polarSumValue μ u v p (northMeridianCoord θ) + 4 * η := by
    exact polarSumValue_le_two_step_targetFrame_add_four_eta
      (hdim := hdim) (μ := μ) (z := northMeridianCoord θ) hu hv hp huv hup hvp hη
      hx hρx hs hs0 hy_def hρy ht ht0 hz_def
  have hlow : β ≤ polarSumValue μ u v p x := hβ hx hxpos hρx
  have hhigh : polarSumValue μ u v p x ≤ β + 5 * η := by
    linarith
  exact ⟨hxpos, hlow, hhigh⟩

lemma exists_local_oscillation_neighborhood_of_meridian_near_infimum_on_north_uniform
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      0 < x0.2.2 ∧
      horizontalRadius x0 ≠ 0 ∧
      ∀ {H : Type*}
        [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        [FiniteDimensional ℂ H],
        3 ≤ Module.finrank ℂ H →
        ∀ (μ : FrameFunction H) {u v p : H},
          (hu : ‖u‖ = 1) → (hv : ‖v‖ = 1) → (hp : ‖p‖ = 1) →
          (huv : inner (𝕜 := ℂ) u v = 0) →
          inner (𝕜 := ℂ) u p = 0 →
          inner (𝕜 := ℂ) v p = 0 →
          ∀ {β η : ℝ},
            (∀ {w : ℝ × ℝ × ℝ},
              w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
              0 < w.2.2 →
              horizontalRadius w ≠ 0 →
              β ≤ polarSumValue μ u v p w) →
            frame_quadratic μ p ≤ η →
            polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η →
            ∀ {x y : ℝ × ℝ × ℝ},
              x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
              y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
              dist x x0 < δ →
              dist y x0 < δ →
              0 < x.2.2 ∧
              0 < y.2.2 ∧
              |polarSumValue μ u v p x - polarSumValue μ u v p y| ≤ 5 * η := by
  rcases exists_local_band_neighborhood_of_meridian_near_infimum_on_north_uniform
      hθ0 hθpi with
    ⟨x0, δ, hδ, hx0, hx0pos, hρx0, hlocal⟩
  refine ⟨x0, δ, hδ, hx0, hx0pos, hρx0, ?_⟩
  intro H _ _ _ _ hdim μ u v p hu hv hp huv hup hvp β η hβ hη hzβ x y hx hy hdx hdy
  rcases hlocal hdim μ hu hv hp huv hup hvp hβ hη hzβ hx hdx with
    ⟨hxpos, hxlo, hxhi⟩
  rcases hlocal hdim μ hu hv hp huv hup hvp hβ hη hzβ hy hdy with
    ⟨hypos, hylo, hyhi⟩
  have hxy :
      polarSumValue μ u v p x - polarSumValue μ u v p y ≤ 5 * η := by
    linarith
  have hyx :
      polarSumValue μ u v p y - polarSumValue μ u v p x ≤ 5 * η := by
    linarith
  exact ⟨hxpos, hypos, abs_le.mpr ⟨by linarith, hxy⟩⟩

lemma psiCenterCoord_band_of_northMeridian_near_nonpole_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η θ : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hθβ :
      polarSumValue μ u v p (northMeridianCoord θ) ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    0 < (psiCenterCoord θ).2.2 ∧
      horizontalRadius (psiCenterCoord θ) ≠ 0 ∧
      sInf (northOpenNonpolePolarSumSet μ u v p) ≤
        polarSumValue μ u v p (psiCenterCoord θ) ∧
      polarSumValue μ u v p (psiCenterCoord θ) ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 5 * η := by
  let β : ℝ := sInf (northOpenNonpolePolarSumSet μ u v p)
  have hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w := by
    intro w hw hwpos hρw
    dsimp [β]
    exact csInf_le
      (northOpenNonpolePolarSumSet_bddBelow μ u v p)
      ⟨w, hw, hwpos, hρw, rfl⟩
  let x : ℝ × ℝ × ℝ := psiCenterCoord θ
  have hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 := by
    simpa [x] using psiCenterCoord_sq_sum θ
  have hxpos : 0 < x.2.2 := by
    simpa [x] using psiCenterCoord_third_pos hθ0 hθpi
  have hρx : horizontalRadius x ≠ 0 := by
    simpa [x] using horizontalRadius_psiCenterCoord_ne_zero hθ0 hθpi
  have hneg : Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 := by
    simpa [x] using gleasonPsiSwap_psiCenterCoord_neg hθ0 hθpi
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hx hneg with
    ⟨y, s, t, hy, hρy, hs, hs0, ht, ht0, hy_def, hz_def⟩
  have hstep :
      polarSumValue μ u v p x ≤
        polarSumValue μ u v p (northMeridianCoord θ) + 4 * η := by
    exact polarSumValue_le_two_step_targetFrame_add_four_eta
      (hdim := hdim) (μ := μ) (z := northMeridianCoord θ)
      hu hv hp huv hup hvp hη hx hρx hs hs0 hy_def hρy ht ht0 hz_def
  have hlo : β ≤ polarSumValue μ u v p x := hβ hx hxpos hρx
  have hhi : polarSumValue μ u v p x ≤ β + 5 * η := by
    linarith
  exact ⟨by simpa [x] using hxpos, by simpa [x] using hρx,
    by simpa [x, β] using hlo, by simpa [x, β] using hhi⟩

lemma local_band_neighborhood_of_meridian_near_infimum_on_north_low_uniform
    {θ : ℝ} (hθ0 : 0 < θ) (hθle : θ ≤ Real.pi / 3)
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H) {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hdist : dist x (psiCenterCoord θ) < (1 : ℝ) / 512) :
    0 < x.2.2 ∧
      β ≤ polarSumValue μ u v p x ∧
        polarSumValue μ u v p x ≤ β + 5 * η := by
  have hθpi : θ < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hneg : Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 :=
    gleasonPsiSwap_lt_zero_of_dist_psiCenterCoord_low_uniform
      (θ := θ) hθ0 hθle hx hdist
  have hxpos : 0 < x.2.2 := by
    have hthird_close :
        |x.2.2 - (psiCenterCoord θ).2.2| < (1 : ℝ) / 512 :=
      coord_snd_snd_abs_sub_lt_of_dist_lt (x := x) (y := psiCenterCoord θ) hdist
    have hthird_low : -((1 : ℝ) / 512) < x.2.2 - (psiCenterCoord θ).2.2 :=
      (abs_lt.mp hthird_close).1
    have hx0_gt_half : (1 : ℝ) / 2 < (psiCenterCoord θ).2.2 :=
      psiCenterCoord_third_gt_half θ
    nlinarith
  have hρx : horizontalRadius x ≠ 0 :=
    horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hneg
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hx hneg with
    ⟨y, s, t, hy, hρy, hs, hs0, ht, ht0, hy_def, hz_def⟩
  have hstep :
      polarSumValue μ u v p x ≤
        polarSumValue μ u v p (northMeridianCoord θ) + 4 * η := by
    exact polarSumValue_le_two_step_targetFrame_add_four_eta
      (hdim := hdim) (μ := μ) (z := northMeridianCoord θ)
      hu hv hp huv hup hvp hη hx hρx hs hs0 hy_def hρy ht ht0 hz_def
  have hlow : β ≤ polarSumValue μ u v p x := hβ hx hxpos hρx
  have hhigh : polarSumValue μ u v p x ≤ β + 5 * η := by
    linarith
  exact ⟨hxpos, hlow, hhigh⟩

lemma local_oscillation_neighborhood_of_meridian_near_infimum_on_north_low_uniform
    {θ : ℝ} (hθ0 : 0 < θ) (hθle : θ ≤ Real.pi / 3)
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H) {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hdx : dist x (psiCenterCoord θ) < (1 : ℝ) / 512)
    (hdy : dist y (psiCenterCoord θ) < (1 : ℝ) / 512) :
    0 < x.2.2 ∧
      0 < y.2.2 ∧
        |polarSumValue μ u v p x - polarSumValue μ u v p y| ≤ 5 * η := by
  rcases local_band_neighborhood_of_meridian_near_infimum_on_north_low_uniform
      (θ := θ) hθ0 hθle hdim μ hu hv hp huv hup hvp hβ hη hzβ hx hdx with
    ⟨hxpos, hxlo, hxhi⟩
  rcases local_band_neighborhood_of_meridian_near_infimum_on_north_low_uniform
      (θ := θ) hθ0 hθle hdim μ hu hv hp huv hup hvp hβ hη hzβ hy hdy with
    ⟨hypos, hylo, hyhi⟩
  have hxy :
      polarSumValue μ u v p x - polarSumValue μ u v p y ≤ 5 * η := by
    linarith
  have hyx :
      polarSumValue μ u v p y - polarSumValue μ u v p x ≤ 5 * η := by
    linarith
  exact ⟨hxpos, hypos, abs_le.mpr ⟨by linarith, hxy⟩⟩

lemma local_band_neighborhood_of_meridian_near_infimum_on_north_away_uniform
    {θ τ : ℝ} (hθ0 : 0 < θ) (hτ0 : 0 < τ)
    (hθτ : θ ≤ Real.pi / 2 - τ)
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H) {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hdist : dist x (psiCenterCoord θ) < Real.sin τ / 256) :
    0 < x.2.2 ∧
      β ≤ polarSumValue μ u v p x ∧
        polarSumValue μ u v p x ≤ β + 5 * η := by
  have hθpi : θ < Real.pi / 2 := by
    linarith
  have hτltpi : τ < Real.pi := by
    nlinarith [hθ0, hθτ, Real.pi_pos]
  have hsin_pos : 0 < Real.sin τ :=
    Real.sin_pos_of_pos_of_lt_pi hτ0 hτltpi
  have hsin_le_cos : Real.sin τ ≤ Real.cos θ := by
    have hy_nonneg : 0 ≤ Real.pi / 2 - τ := le_trans (le_of_lt hθ0) hθτ
    have hy_le_pi : Real.pi / 2 - τ ≤ Real.pi := by
      nlinarith [hθ0, hθτ, Real.pi_pos]
    have hcos :=
      Real.cos_le_cos_of_nonneg_of_le_pi
        (le_of_lt hθ0) hy_le_pi hθτ
    simpa [Real.cos_pi_div_two_sub] using hcos
  have hdist' : dist x (psiCenterCoord θ) < Real.cos θ / 256 := by
    nlinarith
  have hneg : Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 :=
    gleasonPsiSwap_lt_zero_of_dist_psiCenterCoord_linear
      (θ := θ) hθ0 hθpi hx hdist'
  have hxpos : 0 < x.2.2 := by
    have hthird_close :
        |x.2.2 - (psiCenterCoord θ).2.2| < Real.sin τ / 256 :=
      coord_snd_snd_abs_sub_lt_of_dist_lt (x := x) (y := psiCenterCoord θ) hdist
    have hthird_low : -(Real.sin τ / 256) < x.2.2 - (psiCenterCoord θ).2.2 :=
      (abs_lt.mp hthird_close).1
    have hx0_gt_half : (1 : ℝ) / 2 < (psiCenterCoord θ).2.2 :=
      psiCenterCoord_third_gt_half θ
    have hsin_le_one : Real.sin τ ≤ 1 := Real.sin_le_one τ
    have hdelta_lt_half : Real.sin τ / 256 < (1 : ℝ) / 2 := by
      nlinarith
    linarith
  have hρx : horizontalRadius x ≠ 0 :=
    horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hneg
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hx hneg with
    ⟨y, s, t, hy, hρy, hs, hs0, ht, ht0, hy_def, hz_def⟩
  have hstep :
      polarSumValue μ u v p x ≤
        polarSumValue μ u v p (northMeridianCoord θ) + 4 * η := by
    exact polarSumValue_le_two_step_targetFrame_add_four_eta
      (hdim := hdim) (μ := μ) (z := northMeridianCoord θ)
      hu hv hp huv hup hvp hη hx hρx hs hs0 hy_def hρy ht ht0 hz_def
  have hlow : β ≤ polarSumValue μ u v p x := hβ hx hxpos hρx
  have hhigh : polarSumValue μ u v p x ≤ β + 5 * η := by
    linarith
  exact ⟨hxpos, hlow, hhigh⟩

lemma local_oscillation_neighborhood_of_meridian_near_infimum_on_north_away_uniform
    {θ τ : ℝ} (hθ0 : 0 < θ) (hτ0 : 0 < τ)
    (hθτ : θ ≤ Real.pi / 2 - τ)
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H) {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hdx : dist x (psiCenterCoord θ) < Real.sin τ / 256)
    (hdy : dist y (psiCenterCoord θ) < Real.sin τ / 256) :
    0 < x.2.2 ∧
      0 < y.2.2 ∧
        |polarSumValue μ u v p x - polarSumValue μ u v p y| ≤ 5 * η := by
  rcases local_band_neighborhood_of_meridian_near_infimum_on_north_away_uniform
      (θ := θ) (τ := τ) hθ0 hτ0 hθτ hdim μ hu hv hp huv hup hvp hβ hη hzβ hx hdx with
    ⟨hxpos, hxlo, hxhi⟩
  rcases local_band_neighborhood_of_meridian_near_infimum_on_north_away_uniform
      (θ := θ) (τ := τ) hθ0 hτ0 hθτ hdim μ hu hv hp huv hup hvp hβ hη hzβ hy hdy with
    ⟨hypos, hylo, hyhi⟩
  have hxy :
      polarSumValue μ u v p x - polarSumValue μ u v p y ≤ 5 * η := by
    linarith
  have hyx :
      polarSumValue μ u v p y - polarSumValue μ u v p x ≤ 5 * η := by
    linarith
  exact ⟨hxpos, hypos, abs_le.mpr ⟨by linarith, hxy⟩⟩

lemma targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum_on_north_low_uniform
    {θ : ℝ} (hθ0 : 0 < θ) (hθle : θ ≤ Real.pi / 3)
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H) {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hdx :
      dist (coordPoint (coordPoint u v p (psiCenterCoord θ))
          (coordPoint u v p (targetBridgeCoord (psiCenterCoord θ)))
          (coordPoint u v p (targetPoleCoord (psiCenterCoord θ))) x)
        (coordPoint u v p (psiCenterCoord θ)) < (1 : ℝ) / 512)
    (hdy :
      dist (coordPoint (coordPoint u v p (psiCenterCoord θ))
          (coordPoint u v p (targetBridgeCoord (psiCenterCoord θ)))
          (coordPoint u v p (targetPoleCoord (psiCenterCoord θ))) y)
        (coordPoint u v p (psiCenterCoord θ)) < (1 : ℝ) / 512) :
    |frame_quadratic (H := H)
        (quarterTurnAverageFrameFunction μ u v hu hv huv)
        (coordPoint (coordPoint u v p (psiCenterCoord θ))
          (coordPoint u v p (targetBridgeCoord (psiCenterCoord θ)))
          (coordPoint u v p (targetPoleCoord (psiCenterCoord θ))) x) -
      frame_quadratic (H := H)
        (quarterTurnAverageFrameFunction μ u v hu hv huv)
        (coordPoint (coordPoint u v p (psiCenterCoord θ))
          (coordPoint u v p (targetBridgeCoord (psiCenterCoord θ)))
          (coordPoint u v p (targetPoleCoord (psiCenterCoord θ))) y)| ≤
      5 * η / 2 := by
  let x0 : ℝ × ℝ × ℝ := psiCenterCoord θ
  have hθpi : θ < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  have hx0 : x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 := by
    simpa [x0] using psiCenterCoord_sq_sum θ
  have hρx0 : horizontalRadius x0 ≠ 0 := by
    simpa [x0] using horizontalRadius_psiCenterCoord_ne_zero hθ0 hθpi
  let xH : H := coordPoint u v p x0
  let bH : H := coordPoint u v p (targetBridgeCoord x0)
  let qH : H := coordPoint u v p (targetPoleCoord x0)
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have hx' :
      (targetFrameReparam x0 x).1 ^ 2 +
          (targetFrameReparam x0 x).2.1 ^ 2 +
          (targetFrameReparam x0 x).2.2 ^ 2 = 1 := by
    exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hx0 hx hρx0
  have hy' :
      (targetFrameReparam x0 y).1 ^ 2 +
          (targetFrameReparam x0 y).2.1 ^ 2 +
          (targetFrameReparam x0 y).2.2 ^ 2 = 1 := by
    exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hx0 hy hρx0
  have hdx' : dist (targetFrameReparam x0 x) x0 < (1 : ℝ) / 512 := by
    have hle :=
      dist_coords_le_dist_coordPoint hu hv hp huv hup hvp
        (targetFrameReparam x0 x) x0
    have hdistH :
        dist (coordPoint u v p (targetFrameReparam x0 x))
            (coordPoint u v p x0) < (1 : ℝ) / 512 := by
      simpa [x0, xH, bH, qH, coordPoint_targetFrameReparam] using hdx
    exact lt_of_le_of_lt hle hdistH
  have hdy' : dist (targetFrameReparam x0 y) x0 < (1 : ℝ) / 512 := by
    have hle :=
      dist_coords_le_dist_coordPoint hu hv hp huv hup hvp
        (targetFrameReparam x0 y) x0
    have hdistH :
        dist (coordPoint u v p (targetFrameReparam x0 y))
            (coordPoint u v p x0) < (1 : ℝ) / 512 := by
      simpa [x0, xH, bH, qH, coordPoint_targetFrameReparam] using hdy
    exact lt_of_le_of_lt hle hdistH
  have hmain :
      |polarSumValue μ u v p (targetFrameReparam x0 x) -
          polarSumValue μ u v p (targetFrameReparam x0 y)| ≤ 5 * η := by
    rcases local_oscillation_neighborhood_of_meridian_near_infimum_on_north_low_uniform
        (θ := θ) hθ0 hθle hdim μ hu hv hp huv hup hvp hβ hη hzβ
        hx' hy' hdx' hdy' with
      ⟨_, _, hmain⟩
    exact hmain
  have hxAvg :
      2 * frame_quadratic (H := H) μavg
          (coordPoint xH bH qH x) =
        polarSumValue μ u v p (targetFrameReparam x0 x) := by
    simpa [μavg, xH, bH, qH, coordPoint_targetFrameReparam] using
      (two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp
        (targetFrameReparam x0 x))
  have hyAvg :
      2 * frame_quadratic (H := H) μavg
          (coordPoint xH bH qH y) =
        polarSumValue μ u v p (targetFrameReparam x0 y) := by
    simpa [μavg, xH, bH, qH, coordPoint_targetFrameReparam] using
      (two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp
        (targetFrameReparam x0 y))
  let A : ℝ := frame_quadratic (H := H) μavg (coordPoint xH bH qH x)
  let B : ℝ := frame_quadratic (H := H) μavg (coordPoint xH bH qH y)
  have hmain' : |2 * A - 2 * B| ≤ 5 * η := by
    simpa [A, B, hxAvg, hyAvg] using hmain
  have hfactor : |2 * A - 2 * B| = 2 * |A - B| := by
    rw [show 2 * A - 2 * B = 2 * (A - B) by ring]
    rw [abs_mul, abs_of_nonneg (by norm_num)]
  have hscaled : 2 * |A - B| ≤ 5 * η := by
    simpa [hfactor] using hmain'
  have hab : |A - B| ≤ 5 * η / 2 := by
    nlinarith [abs_nonneg (A - B), hηnonneg]
  simpa [A, B, μavg, x0, xH, bH, qH, sub_eq_add_neg] using hab

lemma targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum_on_north_away_uniform
    {θ τ : ℝ} (hθ0 : 0 < θ) (hτ0 : 0 < τ)
    (hθτ : θ ≤ Real.pi / 2 - τ)
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H) {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hdx :
      dist (coordPoint (coordPoint u v p (psiCenterCoord θ))
          (coordPoint u v p (targetBridgeCoord (psiCenterCoord θ)))
          (coordPoint u v p (targetPoleCoord (psiCenterCoord θ))) x)
        (coordPoint u v p (psiCenterCoord θ)) < Real.sin τ / 256)
    (hdy :
      dist (coordPoint (coordPoint u v p (psiCenterCoord θ))
          (coordPoint u v p (targetBridgeCoord (psiCenterCoord θ)))
          (coordPoint u v p (targetPoleCoord (psiCenterCoord θ))) y)
        (coordPoint u v p (psiCenterCoord θ)) < Real.sin τ / 256) :
    |frame_quadratic (H := H)
        (quarterTurnAverageFrameFunction μ u v hu hv huv)
        (coordPoint (coordPoint u v p (psiCenterCoord θ))
          (coordPoint u v p (targetBridgeCoord (psiCenterCoord θ)))
          (coordPoint u v p (targetPoleCoord (psiCenterCoord θ))) x) -
      frame_quadratic (H := H)
        (quarterTurnAverageFrameFunction μ u v hu hv huv)
        (coordPoint (coordPoint u v p (psiCenterCoord θ))
          (coordPoint u v p (targetBridgeCoord (psiCenterCoord θ)))
          (coordPoint u v p (targetPoleCoord (psiCenterCoord θ))) y)| ≤
      5 * η / 2 := by
  let x0 : ℝ × ℝ × ℝ := psiCenterCoord θ
  have hθpi : θ < Real.pi / 2 := by
    linarith
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  have hx0 : x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 := by
    simpa [x0] using psiCenterCoord_sq_sum θ
  have hρx0 : horizontalRadius x0 ≠ 0 := by
    simpa [x0] using horizontalRadius_psiCenterCoord_ne_zero hθ0 hθpi
  let xH : H := coordPoint u v p x0
  let bH : H := coordPoint u v p (targetBridgeCoord x0)
  let qH : H := coordPoint u v p (targetPoleCoord x0)
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have hx' :
      (targetFrameReparam x0 x).1 ^ 2 +
          (targetFrameReparam x0 x).2.1 ^ 2 +
          (targetFrameReparam x0 x).2.2 ^ 2 = 1 := by
    exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hx0 hx hρx0
  have hy' :
      (targetFrameReparam x0 y).1 ^ 2 +
          (targetFrameReparam x0 y).2.1 ^ 2 +
          (targetFrameReparam x0 y).2.2 ^ 2 = 1 := by
    exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hx0 hy hρx0
  have hdx' : dist (targetFrameReparam x0 x) x0 < Real.sin τ / 256 := by
    have hle :=
      dist_coords_le_dist_coordPoint hu hv hp huv hup hvp
        (targetFrameReparam x0 x) x0
    have hdistH :
        dist (coordPoint u v p (targetFrameReparam x0 x))
            (coordPoint u v p x0) < Real.sin τ / 256 := by
      simpa [x0, xH, bH, qH, coordPoint_targetFrameReparam] using hdx
    exact lt_of_le_of_lt hle hdistH
  have hdy' : dist (targetFrameReparam x0 y) x0 < Real.sin τ / 256 := by
    have hle :=
      dist_coords_le_dist_coordPoint hu hv hp huv hup hvp
        (targetFrameReparam x0 y) x0
    have hdistH :
        dist (coordPoint u v p (targetFrameReparam x0 y))
            (coordPoint u v p x0) < Real.sin τ / 256 := by
      simpa [x0, xH, bH, qH, coordPoint_targetFrameReparam] using hdy
    exact lt_of_le_of_lt hle hdistH
  have hmain :
      |polarSumValue μ u v p (targetFrameReparam x0 x) -
          polarSumValue μ u v p (targetFrameReparam x0 y)| ≤ 5 * η := by
    rcases local_oscillation_neighborhood_of_meridian_near_infimum_on_north_away_uniform
        (θ := θ) (τ := τ) hθ0 hτ0 hθτ hdim μ hu hv hp huv hup hvp hβ hη hzβ
        hx' hy' hdx' hdy' with
      ⟨_, _, hmain⟩
    exact hmain
  have hxAvg :
      2 * frame_quadratic (H := H) μavg
          (coordPoint xH bH qH x) =
        polarSumValue μ u v p (targetFrameReparam x0 x) := by
    simpa [μavg, xH, bH, qH, coordPoint_targetFrameReparam] using
      (two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp
        (targetFrameReparam x0 x))
  have hyAvg :
      2 * frame_quadratic (H := H) μavg
          (coordPoint xH bH qH y) =
        polarSumValue μ u v p (targetFrameReparam x0 y) := by
    simpa [μavg, xH, bH, qH, coordPoint_targetFrameReparam] using
      (two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp
        (targetFrameReparam x0 y))
  let A : ℝ := frame_quadratic (H := H) μavg (coordPoint xH bH qH x)
  let B : ℝ := frame_quadratic (H := H) μavg (coordPoint xH bH qH y)
  have hmain' : |2 * A - 2 * B| ≤ 5 * η := by
    simpa [A, B, hxAvg, hyAvg] using hmain
  have hfactor : |2 * A - 2 * B| = 2 * |A - B| := by
    rw [show 2 * A - 2 * B = 2 * (A - B) by ring]
    rw [abs_mul, abs_of_nonneg (by norm_num)]
  have hscaled : 2 * |A - B| ≤ 5 * η := by
    simpa [hfactor] using hmain'
  have hab : |A - B| ≤ 5 * η / 2 := by
    nlinarith [abs_nonneg (A - B), hηnonneg]
  simpa [A, B, μavg, x0, xH, bH, qH, sub_eq_add_neg] using hab

lemma exists_targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum_on_north_low_uniform
    {θ : ℝ} (hθ0 : 0 < θ) (hθle : θ ≤ Real.pi / 3) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      0 < x0.2.2 ∧
      horizontalRadius x0 ≠ 0 ∧
      ∀ {H : Type*}
        [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        [FiniteDimensional ℂ H],
        3 ≤ Module.finrank ℂ H →
        ∀ (μ : FrameFunction H) {u v p : H},
          (hu : ‖u‖ = 1) → (hv : ‖v‖ = 1) → (hp : ‖p‖ = 1) →
          (huv : inner (𝕜 := ℂ) u v = 0) →
          inner (𝕜 := ℂ) u p = 0 →
          inner (𝕜 := ℂ) v p = 0 →
          ∀ {β η : ℝ},
            (∀ {w : ℝ × ℝ × ℝ},
              w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
              0 < w.2.2 →
              horizontalRadius w ≠ 0 →
              β ≤ polarSumValue μ u v p w) →
            frame_quadratic μ p ≤ η →
            polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η →
            ∀ {x y : ℝ × ℝ × ℝ},
              x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
              y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
              dist (coordPoint (coordPoint u v p x0)
                  (coordPoint u v p (targetBridgeCoord x0))
                  (coordPoint u v p (targetPoleCoord x0)) x)
                (coordPoint u v p x0) < δ →
              dist (coordPoint (coordPoint u v p x0)
                  (coordPoint u v p (targetBridgeCoord x0))
                  (coordPoint u v p (targetPoleCoord x0)) y)
                (coordPoint u v p x0) < δ →
              |frame_quadratic (H := H)
                  (quarterTurnAverageFrameFunction μ u v hu hv huv)
                  (coordPoint (coordPoint u v p x0)
                    (coordPoint u v p (targetBridgeCoord x0))
                    (coordPoint u v p (targetPoleCoord x0)) x) -
                frame_quadratic (H := H)
                  (quarterTurnAverageFrameFunction μ u v hu hv huv)
                  (coordPoint (coordPoint u v p x0)
                    (coordPoint u v p (targetBridgeCoord x0))
                    (coordPoint u v p (targetPoleCoord x0)) y)| ≤
                5 * η / 2 := by
  let x0 : ℝ × ℝ × ℝ := psiCenterCoord θ
  let δ : ℝ := (1 : ℝ) / 512
  have hθpi : θ < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  refine ⟨x0, δ, by norm_num [δ], ?_, ?_, ?_, ?_⟩
  · simpa [x0] using psiCenterCoord_sq_sum θ
  · simpa [x0] using psiCenterCoord_third_pos hθ0 hθpi
  · simpa [x0] using horizontalRadius_psiCenterCoord_ne_zero hθ0 hθpi
  · intro H _ _ _ _ hdim μ u v p hu hv hp huv hup hvp β η hβ hη hzβ x y hx hy hdx hdy
    simpa [x0, δ] using
      targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum_on_north_low_uniform
        (θ := θ) hθ0 hθle hdim μ hu hv hp huv hup hvp hβ hη hzβ hx hy hdx hdy

lemma exists_targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum_on_north_uniform
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      0 < x0.2.2 ∧
      horizontalRadius x0 ≠ 0 ∧
      ∀ {H : Type*}
        [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        [FiniteDimensional ℂ H],
        3 ≤ Module.finrank ℂ H →
        ∀ (μ : FrameFunction H) {u v p : H},
          (hu : ‖u‖ = 1) → (hv : ‖v‖ = 1) → (hp : ‖p‖ = 1) →
          (huv : inner (𝕜 := ℂ) u v = 0) →
          inner (𝕜 := ℂ) u p = 0 →
          inner (𝕜 := ℂ) v p = 0 →
          ∀ {β η : ℝ},
            (∀ {w : ℝ × ℝ × ℝ},
              w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
              0 < w.2.2 →
              horizontalRadius w ≠ 0 →
              β ≤ polarSumValue μ u v p w) →
            frame_quadratic μ p ≤ η →
            polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η →
            ∀ {x y : ℝ × ℝ × ℝ},
              x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
              y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
              dist (coordPoint (coordPoint u v p x0)
                  (coordPoint u v p (targetBridgeCoord x0))
                  (coordPoint u v p (targetPoleCoord x0)) x)
                (coordPoint u v p x0) < δ →
              dist (coordPoint (coordPoint u v p x0)
                  (coordPoint u v p (targetBridgeCoord x0))
                  (coordPoint u v p (targetPoleCoord x0)) y)
                (coordPoint u v p x0) < δ →
              |frame_quadratic (H := H)
                  (quarterTurnAverageFrameFunction μ u v hu hv huv)
                  (coordPoint (coordPoint u v p x0)
                    (coordPoint u v p (targetBridgeCoord x0))
                    (coordPoint u v p (targetPoleCoord x0)) x) -
                frame_quadratic (H := H)
                  (quarterTurnAverageFrameFunction μ u v hu hv huv)
                  (coordPoint (coordPoint u v p x0)
                    (coordPoint u v p (targetBridgeCoord x0))
                    (coordPoint u v p (targetPoleCoord x0)) y)| ≤
                5 * η / 2 := by
  rcases exists_local_oscillation_neighborhood_of_meridian_near_infimum_on_north_uniform
      hθ0 hθpi with
    ⟨x0, δ, hδ, hx0, hx0pos, hρx0, hlocal⟩
  refine ⟨x0, δ, hδ, hx0, hx0pos, hρx0, ?_⟩
  intro H _ _ _ _ hdim μ u v p hu hv hp huv hup hvp β η hβ hη hzβ x y hx hy hdx hdy
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  let xH : H := coordPoint u v p x0
  let bH : H := coordPoint u v p (targetBridgeCoord x0)
  let qH : H := coordPoint u v p (targetPoleCoord x0)
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have hx' :
      (targetFrameReparam x0 x).1 ^ 2 +
          (targetFrameReparam x0 x).2.1 ^ 2 +
          (targetFrameReparam x0 x).2.2 ^ 2 = 1 := by
    exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hx0 hx hρx0
  have hy' :
      (targetFrameReparam x0 y).1 ^ 2 +
          (targetFrameReparam x0 y).2.1 ^ 2 +
          (targetFrameReparam x0 y).2.2 ^ 2 = 1 := by
    exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hx0 hy hρx0
  have hdx' : dist (targetFrameReparam x0 x) x0 < δ := by
    have hle :=
      dist_coords_le_dist_coordPoint hu hv hp huv hup hvp
        (targetFrameReparam x0 x) x0
    have hdistH :
        dist (coordPoint u v p (targetFrameReparam x0 x))
            (coordPoint u v p x0) < δ := by
      simpa [xH, bH, qH, coordPoint_targetFrameReparam] using hdx
    exact lt_of_le_of_lt hle hdistH
  have hdy' : dist (targetFrameReparam x0 y) x0 < δ := by
    have hle :=
      dist_coords_le_dist_coordPoint hu hv hp huv hup hvp
        (targetFrameReparam x0 y) x0
    have hdistH :
        dist (coordPoint u v p (targetFrameReparam x0 y))
            (coordPoint u v p x0) < δ := by
      simpa [xH, bH, qH, coordPoint_targetFrameReparam] using hdy
    exact lt_of_le_of_lt hle hdistH
  have hmain :
      |polarSumValue μ u v p (targetFrameReparam x0 x) -
          polarSumValue μ u v p (targetFrameReparam x0 y)| ≤ 5 * η := by
    rcases hlocal hdim μ hu hv hp huv hup hvp hβ hη hzβ hx' hy' hdx' hdy' with
      ⟨_, _, hmain⟩
    exact hmain
  have hxAvg :
      2 * frame_quadratic (H := H) μavg
          (coordPoint xH bH qH x) =
        polarSumValue μ u v p (targetFrameReparam x0 x) := by
    simpa [μavg, xH, bH, qH, coordPoint_targetFrameReparam] using
      (two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp
        (targetFrameReparam x0 x))
  have hyAvg :
      2 * frame_quadratic (H := H) μavg
          (coordPoint xH bH qH y) =
        polarSumValue μ u v p (targetFrameReparam x0 y) := by
    simpa [μavg, xH, bH, qH, coordPoint_targetFrameReparam] using
      (two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp
        (targetFrameReparam x0 y))
  let A : ℝ := frame_quadratic (H := H) μavg (coordPoint xH bH qH x)
  let B : ℝ := frame_quadratic (H := H) μavg (coordPoint xH bH qH y)
  have hmain' : |2 * A - 2 * B| ≤ 5 * η := by
    simpa [A, B, hxAvg, hyAvg] using hmain
  have hfactor : |2 * A - 2 * B| = 2 * |A - B| := by
    rw [show 2 * A - 2 * B = 2 * (A - B) by ring]
    rw [abs_mul, abs_of_nonneg (by norm_num)]
  have hscaled : 2 * |A - B| ≤ 5 * η := by
    simpa [hfactor] using hmain'
  have hab : |A - B| ≤ 5 * η / 2 := by
    nlinarith [abs_nonneg (A - B), hηnonneg]
  simpa [A, B, μavg, xH, bH, qH, sub_eq_add_neg] using hab

lemma exists_local_oscillation_neighborhood_of_meridian_near_infimum_on_north
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      0 < x0.2.2 ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist x x0 < δ →
        dist y x0 < δ →
        0 < x.2.2 ∧
        0 < y.2.2 ∧
        |polarSumValue μ u v p x - polarSumValue μ u v p y| ≤ 5 * η := by
  rcases exists_local_band_neighborhood_of_meridian_near_infimum_on_north
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hθ0 hθpi hβ hη hzβ with
    ⟨x0, δ, hδ, hx0, hx0pos, hlocal⟩
  refine ⟨x0, δ, hδ, hx0, hx0pos, ?_⟩
  intro x y hx hy hdx hdy
  rcases hlocal hx hdx with ⟨hxpos, hxlo, hxhi⟩
  rcases hlocal hy hdy with ⟨hypos, hylo, hyhi⟩
  have hxy :
      polarSumValue μ u v p x - polarSumValue μ u v p y ≤ 5 * η := by
    linarith
  have hyx :
      polarSumValue μ u v p y - polarSumValue μ u v p x ≤ 5 * η := by
    linarith
  exact ⟨hxpos, hypos, abs_le.mpr ⟨by linarith, hxy⟩⟩

lemma exists_local_oscillation_neighborhood_of_meridian_near_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist x x0 < δ →
        dist y x0 < δ →
        |polarSumValue μ u v p x - polarSumValue μ u v p y| ≤ 5 * η := by
  rcases exists_local_band_neighborhood_of_meridian_near_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hθ0 hθpi hβ hη hzβ with
    ⟨x0, δ, hδ, hx0, hlocal⟩
  refine ⟨x0, δ, hδ, hx0, ?_⟩
  intro x y hx hy hdx hdy
  rcases hlocal hx hdx with ⟨hxlo, hxhi⟩
  rcases hlocal hy hdy with ⟨hylo, hyhi⟩
  have hxy :
      polarSumValue μ u v p x - polarSumValue μ u v p y ≤ 5 * η := by
    linarith
  have hyx :
      polarSumValue μ u v p y - polarSumValue μ u v p x ≤ 5 * η := by
    linarith
  exact abs_le.mpr ⟨by linarith, hxy⟩

lemma exists_nonpolar_local_oscillation_neighborhood_of_meridian_near_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      horizontalRadius x0 ≠ 0 ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist x x0 < δ →
        dist y x0 < δ →
        |polarSumValue μ u v p x - polarSumValue μ u v p y| ≤ 5 * η := by
  rcases Thm25.exists_sphere_point_with_gleasonPsiSwap_neg hθ0 hθpi with
    ⟨ξ0, η0, r0, hx0, hneg0⟩
  let x0 : ℝ × ℝ × ℝ := (ξ0, (η0, r0))
  let ψ : ℝ × ℝ × ℝ → ℝ := fun x =>
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2
  have hcont : Continuous ψ := by
    simpa [ψ] using continuous_gleasonPsiSwap θ
  have hopen : IsOpen {x : ℝ × ℝ × ℝ | ψ x < 0} :=
    hcont.isOpen_preimage _ isOpen_Iio
  have hx0mem : x0 ∈ {x : ℝ × ℝ × ℝ | ψ x < 0} := by
    simpa [x0, ψ] using hneg0
  have hρx0 : horizontalRadius x0 ≠ 0 := by
    simpa [x0] using horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hneg0
  have hnhds : {x : ℝ × ℝ × ℝ | ψ x < 0} ∈ nhds x0 := hopen.mem_nhds hx0mem
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδ, hball⟩
  refine ⟨x0, δ, hδ, by simpa [x0] using hx0, hρx0, ?_⟩
  intro x y hx hy hdx hdy
  have hnegx : Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 := by
    exact hball hdx
  have hnegy : Thm25.gleasonPsiSwap θ y.1 y.2.1 y.2.2 < 0 := by
    exact hball hdy
  have hρx : horizontalRadius x ≠ 0 := by
    exact horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hnegx
  have hρy : horizontalRadius y ≠ 0 := by
    exact horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hnegy
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hx hnegx with
    ⟨x1, sx, tx, hx1, hρx1, hsx, hsx0, htx, htx0, hx1_def, hx2_def⟩
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hy hnegy with
    ⟨y1, sy, ty, hy1, hρy1, hsy, hsy0, hty, hty0, hy1_def, hy2_def⟩
  have hbandx :=
    polarSumValue_band_of_two_step_near_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hβ hη hx hρx hsx hsx0 hx1_def hρx1 htx htx0 hx2_def hzβ
  have hbandy :=
    polarSumValue_band_of_two_step_near_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hβ hη hy hρy hsy hsy0 hy1_def hρy1 hty hty0 hy2_def hzβ
  rcases hbandx with ⟨hxlo, hxhi⟩
  rcases hbandy with ⟨hylo, hyhi⟩
  have hxy :
      polarSumValue μ u v p x - polarSumValue μ u v p y ≤ 5 * η := by
    linarith
  have hyx :
      polarSumValue μ u v p y - polarSumValue μ u v p x ≤ 5 * η := by
    linarith
  exact abs_le.mpr ⟨by linarith, hxy⟩

lemma exists_targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      horizontalRadius x0 ≠ 0 ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint (coordPoint u v p x0)
            (coordPoint u v p (targetBridgeCoord x0))
            (coordPoint u v p (targetPoleCoord x0)) x)
          (coordPoint u v p x0) < δ →
        dist (coordPoint (coordPoint u v p x0)
            (coordPoint u v p (targetBridgeCoord x0))
            (coordPoint u v p (targetPoleCoord x0)) y)
          (coordPoint u v p x0) < δ →
        |frame_quadratic (H := H)
            (quarterTurnAverageFrameFunction μ u v hu hv huv)
            (coordPoint (coordPoint u v p x0)
              (coordPoint u v p (targetBridgeCoord x0))
              (coordPoint u v p (targetPoleCoord x0)) x) -
          frame_quadratic (H := H)
            (quarterTurnAverageFrameFunction μ u v hu hv huv)
            (coordPoint (coordPoint u v p x0)
              (coordPoint u v p (targetBridgeCoord x0))
              (coordPoint u v p (targetPoleCoord x0)) y)| ≤
          5 * η / 2 := by
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  rcases exists_nonpolar_local_oscillation_neighborhood_of_meridian_near_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hθ0 hθpi hβ hη hzβ with
    ⟨x0, δ, hδ, hx0, hρx0, hlocal⟩
  refine ⟨x0, δ, hδ, hx0, hρx0, ?_⟩
  intro x y hx hy hdx hdy
  let xH : H := coordPoint u v p x0
  let bH : H := coordPoint u v p (targetBridgeCoord x0)
  let qH : H := coordPoint u v p (targetPoleCoord x0)
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have hx' :
      (targetFrameReparam x0 x).1 ^ 2 +
          (targetFrameReparam x0 x).2.1 ^ 2 +
          (targetFrameReparam x0 x).2.2 ^ 2 = 1 := by
    exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hx0 hx hρx0
  have hy' :
      (targetFrameReparam x0 y).1 ^ 2 +
          (targetFrameReparam x0 y).2.1 ^ 2 +
          (targetFrameReparam x0 y).2.2 ^ 2 = 1 := by
    exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hx0 hy hρx0
  have hdx' : dist (targetFrameReparam x0 x) x0 < δ := by
    have hle :=
      dist_coords_le_dist_coordPoint hu hv hp huv hup hvp
        (targetFrameReparam x0 x) x0
    have hdistH :
        dist (coordPoint u v p (targetFrameReparam x0 x))
            (coordPoint u v p x0) < δ := by
      simpa [xH, bH, qH, coordPoint_targetFrameReparam] using hdx
    exact lt_of_le_of_lt hle hdistH
  have hdy' : dist (targetFrameReparam x0 y) x0 < δ := by
    have hle :=
      dist_coords_le_dist_coordPoint hu hv hp huv hup hvp
        (targetFrameReparam x0 y) x0
    have hdistH :
        dist (coordPoint u v p (targetFrameReparam x0 y))
            (coordPoint u v p x0) < δ := by
      simpa [xH, bH, qH, coordPoint_targetFrameReparam] using hdy
    exact lt_of_le_of_lt hle hdistH
  have hmain :
      |polarSumValue μ u v p (targetFrameReparam x0 x) -
          polarSumValue μ u v p (targetFrameReparam x0 y)| ≤ 5 * η := by
    exact hlocal hx' hy' hdx' hdy'
  have hxAvg :
      2 * frame_quadratic (H := H) μavg
          (coordPoint xH bH qH x) =
        polarSumValue μ u v p (targetFrameReparam x0 x) := by
    simpa [μavg, xH, bH, qH, coordPoint_targetFrameReparam] using
      (two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp
        (targetFrameReparam x0 x))
  have hyAvg :
      2 * frame_quadratic (H := H) μavg
          (coordPoint xH bH qH y) =
        polarSumValue μ u v p (targetFrameReparam x0 y) := by
    simpa [μavg, xH, bH, qH, coordPoint_targetFrameReparam] using
      (two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp
        (targetFrameReparam x0 y))
  let A : ℝ := frame_quadratic (H := H) μavg (coordPoint xH bH qH x)
  let B : ℝ := frame_quadratic (H := H) μavg (coordPoint xH bH qH y)
  have hmain' : |2 * A - 2 * B| ≤ 5 * η := by
    simpa [A, B, hxAvg, hyAvg] using hmain
  have hfactor : |2 * A - 2 * B| = 2 * |A - B| := by
    rw [show 2 * A - 2 * B = 2 * (A - B) by ring]
    rw [abs_mul, abs_of_nonneg (by norm_num)]
  have hscaled : 2 * |A - B| ≤ 5 * η := by
    simpa [hfactor] using hmain'
  have hab : |A - B| ≤ 5 * η / 2 := by
    nlinarith
  simpa [A, B, sub_eq_add_neg] using hab

lemma exists_local_oscillation_neighborhood_of_quarterTurnAverage_at_p_near_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic (H := H)
            (quarterTurnAverageFrameFunction μ u v hu hv huv)
            (coordPoint u v p x) -
          frame_quadratic (H := H)
            (quarterTurnAverageFrameFunction μ u v hu hv huv)
            (coordPoint u v p y)| ≤
          10 * η := by
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  rcases exists_targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hθ0 hθpi hβ hη hzβ with
    ⟨x0, ε, hε, hx0, hρx0, hcap⟩
  let xH : H := coordPoint u v p x0
  let bH : H := coordPoint u v p (targetBridgeCoord x0)
  let qH : H := coordPoint u v p (targetPoleCoord x0)
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have hxH : ‖xH‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hx0
  have hbH : ‖bH‖ = 1 := by
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hx0 hρx0
  have hqH : ‖qH‖ = 1 := by
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρx0
  have hxb : inner (𝕜 := ℂ) xH bH = 0 := by
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρx0
  have hxq : inner (𝕜 := ℂ) xH qH = 0 := by
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρx0
  have hbq : inner (𝕜 := ℂ) bH qH = 0 := by
    have htmp := inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρx0
    simpa [xH, bH, qH, inner_eq_zero_symm] using htmp
  have hbx : inner (𝕜 := ℂ) bH xH = 0 := by
    simpa [inner_eq_zero_symm] using hxb
  have hqx : inner (𝕜 := ℂ) qH xH = 0 := by
    simpa [inner_eq_zero_symm] using hxq
  have hosc' :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint bH qH xH x) xH < ε →
        dist (coordPoint bH qH xH y) xH < ε →
        |frame_quadratic (H := H) μavg (coordPoint bH qH xH x) -
            frame_quadratic (H := H) μavg (coordPoint bH qH xH y)| ≤
          5 * η / 2 := by
    intro x y hx hy hdx hdy
    have hx' := cycleCoord_sq_sum hx
    have hy' := cycleCoord_sq_sum hy
    have hxc :
        coordPoint bH qH xH x = coordPoint xH bH qH (cycleCoord x) := by
      exact coordPoint_cycle xH bH qH x
    have hyc :
        coordPoint bH qH xH y = coordPoint xH bH qH (cycleCoord y) := by
      exact coordPoint_cycle xH bH qH y
    have hdx' :
        dist (coordPoint xH bH qH (cycleCoord x)) xH < ε := by
      simpa [hxc] using hdx
    have hdy' :
        dist (coordPoint xH bH qH (cycleCoord y)) xH < ε := by
      simpa [hyc] using hdy
    have hmain := hcap hx' hy' hdx' hdy'
    simpa [hxc, hyc] using hmain
  let z : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 poleCoord)
  have hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 := by
    apply cycleCoordInv_sq_sum
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 (by simp [poleCoord]) hρx0
  have ha : 0 ≤ 5 * η / 2 := by
    nlinarith
  rcases sphere_oscillation_bound_of_cap
      (hdim := hdim) (μ := μavg)
      (u := bH) (v := qH) (p := xH)
      hbH hqH hxH hbq hbx hqx
      (a := 5 * η / 2) (ε := ε) ha hε
      (hosc := hosc') (z := z) hz with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hdx hdy
  let tx : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 x)
  let ty : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 y)
  have htx : tx.1 ^ 2 + tx.2.1 ^ 2 + tx.2.2 ^ 2 = 1 := by
    apply cycleCoordInv_sq_sum
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 hx hρx0
  have hty : ty.1 ^ 2 + ty.2.1 ^ 2 + ty.2.2 ^ 2 = 1 := by
    apply cycleCoordInv_sq_sum
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 hy hρx0
  have htxPoint :
      coordPoint bH qH xH tx = coordPoint u v p x := by
    rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH) (x := targetFrameCoords x0 x)]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
      (y := targetFrameCoords x0 x)]
    rw [targetFrameReparam_targetFrameCoords (z := x0) (x := x) hx0 hρx0]
  have htyPoint :
      coordPoint bH qH xH ty = coordPoint u v p y := by
    rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH) (x := targetFrameCoords x0 y)]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
      (y := targetFrameCoords x0 y)]
    rw [targetFrameReparam_targetFrameCoords (z := x0) (x := y) hx0 hρx0]
  have hzPoint :
      coordPoint bH qH xH z = p := by
    rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH) (x := targetFrameCoords x0 poleCoord)]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
      (y := targetFrameCoords x0 poleCoord)]
    rw [targetFrameReparam_targetFrameCoords (z := x0) (x := poleCoord) hx0 hρx0]
    exact coordPoint_poleCoord u v p
  have htxDist :
      dist (coordPoint bH qH xH tx) (coordPoint bH qH xH z) < δ := by
    simpa [htxPoint, hzPoint] using hdx
  have htyDist :
      dist (coordPoint bH qH xH ty) (coordPoint bH qH xH z) < δ := by
    simpa [htyPoint, hzPoint] using hdy
  have hmain :
      |frame_quadratic (H := H) μavg (coordPoint bH qH xH tx) -
          frame_quadratic (H := H) μavg (coordPoint bH qH xH ty)| ≤
        4 * (5 * η / 2) := by
    exact hlocal htx hty htxDist htyDist
  have hmain' :
      |frame_quadratic (H := H) μavg (coordPoint u v p x) -
          frame_quadratic (H := H) μavg (coordPoint u v p y)| ≤
        4 * (5 * η / 2) := by
    simpa [μavg, htxPoint, htyPoint] using hmain
  have hfinal :
      |frame_quadratic (H := H) μavg (coordPoint u v p x) -
          frame_quadratic (H := H) μavg (coordPoint u v p y)| ≤
        10 * η := by
    nlinarith
  simpa [μavg] using hfinal

lemma exists_local_oscillation_neighborhood_of_quarterTurnAverage_at_p_near_infimum_on_north_low_uniform
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθle : θ ≤ Real.pi / 3)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic (H := H)
            (quarterTurnAverageFrameFunction μ u v hu hv huv)
            (coordPoint u v p x) -
          frame_quadratic (H := H)
            (quarterTurnAverageFrameFunction μ u v hu hv huv)
            (coordPoint u v p y)| ≤
          10 * η := by
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  rcases exists_targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum_on_north_low_uniform
      (θ := θ) hθ0 hθle with
    ⟨x0, ε, hε, hx0, _hx0pos, hρx0, hcap⟩
  let xH : H := coordPoint u v p x0
  let bH : H := coordPoint u v p (targetBridgeCoord x0)
  let qH : H := coordPoint u v p (targetPoleCoord x0)
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have hxH : ‖xH‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hx0
  have hbH : ‖bH‖ = 1 := by
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hx0 hρx0
  have hqH : ‖qH‖ = 1 := by
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρx0
  have hxb : inner (𝕜 := ℂ) xH bH = 0 := by
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρx0
  have hxq : inner (𝕜 := ℂ) xH qH = 0 := by
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρx0
  have hbq : inner (𝕜 := ℂ) bH qH = 0 := by
    have htmp := inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρx0
    simpa [xH, bH, qH, inner_eq_zero_symm] using htmp
  have hbx : inner (𝕜 := ℂ) bH xH = 0 := by
    simpa [inner_eq_zero_symm] using hxb
  have hqx : inner (𝕜 := ℂ) qH xH = 0 := by
    simpa [inner_eq_zero_symm] using hxq
  have hosc' :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint bH qH xH x) xH < ε →
        dist (coordPoint bH qH xH y) xH < ε →
        |frame_quadratic (H := H) μavg (coordPoint bH qH xH x) -
            frame_quadratic (H := H) μavg (coordPoint bH qH xH y)| ≤
          5 * η / 2 := by
    intro x y hx hy hdx hdy
    have hx' := cycleCoord_sq_sum hx
    have hy' := cycleCoord_sq_sum hy
    have hxc :
        coordPoint bH qH xH x = coordPoint xH bH qH (cycleCoord x) := by
      exact coordPoint_cycle xH bH qH x
    have hyc :
        coordPoint bH qH xH y = coordPoint xH bH qH (cycleCoord y) := by
      exact coordPoint_cycle xH bH qH y
    have hdx' :
        dist (coordPoint xH bH qH (cycleCoord x)) xH < ε := by
      simpa [hxc] using hdx
    have hdy' :
        dist (coordPoint xH bH qH (cycleCoord y)) xH < ε := by
      simpa [hyc] using hdy
    have hmain :=
      hcap hdim μ hu hv hp huv hup hvp hβ hη hzβ hx' hy' hdx' hdy'
    simpa [μavg, hxc, hyc] using hmain
  let z : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 poleCoord)
  have hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 := by
    dsimp [z]
    apply cycleCoordInv_sq_sum
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 (by simp [poleCoord]) hρx0
  have hρz : horizontalRadius z ≠ 0 := by
    dsimp [z]
    exact horizontalRadius_cycleCoordInv_targetFrameCoords_poleCoord_ne_zero hρx0
  have ha : 0 ≤ 5 * η / 2 := by
    nlinarith
  rcases nonpolar_oscillation_bound_of_cap_uniform_any
      (H := H) hdim (a := 5 * η / 2) (ε := ε) ha hε with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hdx hdy
  let tx : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 x)
  let ty : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 y)
  have htx : tx.1 ^ 2 + tx.2.1 ^ 2 + tx.2.2 ^ 2 = 1 := by
    dsimp [tx]
    apply cycleCoordInv_sq_sum
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 hx hρx0
  have hty : ty.1 ^ 2 + ty.2.1 ^ 2 + ty.2.2 ^ 2 = 1 := by
    dsimp [ty]
    apply cycleCoordInv_sq_sum
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 hy hρx0
  have htxPoint :
      coordPoint bH qH xH tx = coordPoint u v p x := by
    rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH) (x := targetFrameCoords x0 x)]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
      (y := targetFrameCoords x0 x)]
    rw [targetFrameReparam_targetFrameCoords (z := x0) (x := x) hx0 hρx0]
  have htyPoint :
      coordPoint bH qH xH ty = coordPoint u v p y := by
    rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH) (x := targetFrameCoords x0 y)]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
      (y := targetFrameCoords x0 y)]
    rw [targetFrameReparam_targetFrameCoords (z := x0) (x := y) hx0 hρx0]
  have hzPoint :
      coordPoint bH qH xH z = p := by
    dsimp [z]
    rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH) (x := targetFrameCoords x0 poleCoord)]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
      (y := targetFrameCoords x0 poleCoord)]
    rw [targetFrameReparam_targetFrameCoords (z := x0) (x := poleCoord) hx0 hρx0]
    exact coordPoint_poleCoord u v p
  have htxDist :
      dist (coordPoint bH qH xH tx) (coordPoint bH qH xH z) < δ := by
    simpa [htxPoint, hzPoint] using hdx
  have htyDist :
      dist (coordPoint bH qH xH ty) (coordPoint bH qH xH z) < δ := by
    simpa [htyPoint, hzPoint] using hdy
  have hmain :
      |frame_quadratic (H := H) μavg (coordPoint bH qH xH tx) -
          frame_quadratic (H := H) μavg (coordPoint bH qH xH ty)| ≤
        4 * (5 * η / 2) := by
    exact hlocal μavg hbH hqH hxH hbq hbx hqx hosc' hz hρz htx hty htxDist htyDist
  have hmain' :
      |frame_quadratic (H := H) μavg (coordPoint u v p x) -
          frame_quadratic (H := H) μavg (coordPoint u v p y)| ≤
        4 * (5 * η / 2) := by
    simpa [μavg, htxPoint, htyPoint] using hmain
  have hfinal :
      |frame_quadratic (H := H) μavg (coordPoint u v p x) -
          frame_quadratic (H := H) μavg (coordPoint u v p y)| ≤
        10 * η := by
    nlinarith
  simpa [μavg] using hfinal

lemma exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum_on_north_low_uniform
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθle : θ ≤ Real.pi / 3)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          22 * η := by
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  rcases exists_local_oscillation_neighborhood_of_quarterTurnAverage_at_p_near_infimum_on_north_low_uniform
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hθ0 hθle hβ hη hzβ with
    ⟨δ, hδ, hlocal⟩
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have havgp_eq :
      frame_quadratic (H := H) μavg p = frame_quadratic μ p := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp poleCoord
    have hpole :
        polarSumValue μ u v p poleCoord = 2 * frame_quadratic μ p := by
      have hturn : polarQuarterTurnCoord poleCoord = poleCoord := by
        simp [polarQuarterTurnCoord, poleCoord]
      rw [polarSumValue, hturn, coordPoint_poleCoord]
      ring
    have htwo' :
        2 * frame_quadratic (H := H) μavg p = 2 * frame_quadratic μ p := by
      simpa [μavg, coordPoint_poleCoord] using htwo.trans hpole
    nlinarith
  have havgp_le : frame_quadratic (H := H) μavg p ≤ η := by
    rw [havgp_eq]
    exact hη
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hdx hdy
  have hpdist : dist (coordPoint u v p poleCoord) p < δ := by
    simpa [coordPoint_poleCoord] using hδ
  have hlocx :
      |frame_quadratic (H := H) μavg (coordPoint u v p x) -
          frame_quadratic (H := H) μavg p| ≤ 10 * η := by
    simpa [μavg, coordPoint_poleCoord] using
      (hlocal hx (by simp [poleCoord]) hdx hpdist)
  have hlocy :
      |frame_quadratic (H := H) μavg (coordPoint u v p y) -
          frame_quadratic (H := H) μavg p| ≤ 10 * η := by
    simpa [μavg, coordPoint_poleCoord] using
      (hlocal hy (by simp [poleCoord]) hdy hpdist)
  have havgx_le :
      frame_quadratic (H := H) μavg (coordPoint u v p x) ≤ 11 * η := by
    have hupperx :
        frame_quadratic (H := H) μavg (coordPoint u v p x) -
            frame_quadratic (H := H) μavg p ≤ 10 * η := by
      exact (abs_le.mp hlocx).2
    nlinarith
  have havgy_le :
      frame_quadratic (H := H) μavg (coordPoint u v p y) ≤ 11 * η := by
    have huppery :
        frame_quadratic (H := H) μavg (coordPoint u v p y) -
            frame_quadratic (H := H) μavg p ≤ 10 * η := by
      exact (abs_le.mp hlocy).2
    nlinarith
  have hGx_le :
      polarSumValue μ u v p x ≤ 22 * η := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp x
    have htwo' :
        2 * frame_quadratic (H := H) μavg (coordPoint u v p x) ≤ 22 * η := by
      nlinarith
    linarith
  have hGy_le :
      polarSumValue μ u v p y ≤ 22 * η := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp y
    have htwo' :
        2 * frame_quadratic (H := H) μavg (coordPoint u v p y) ≤ 22 * η := by
      nlinarith
    linarith
  have hx_le :
      frame_quadratic μ (coordPoint u v p x) ≤ 22 * η := by
    have hnonneg_rot := frame_quadratic_nonneg μ (coordPoint u v p (polarQuarterTurnCoord x))
    unfold polarSumValue at hGx_le
    linarith
  have hy_le :
      frame_quadratic μ (coordPoint u v p y) ≤ 22 * η := by
    have hnonneg_rot := frame_quadratic_nonneg μ (coordPoint u v p (polarQuarterTurnCoord y))
    unfold polarSumValue at hGy_le
    linarith
  have hx_nonneg : 0 ≤ frame_quadratic μ (coordPoint u v p x) :=
    frame_quadratic_nonneg μ (coordPoint u v p x)
  have hy_nonneg : 0 ≤ frame_quadratic μ (coordPoint u v p y) :=
    frame_quadratic_nonneg μ (coordPoint u v p y)
  have hxy :
      frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y) ≤ 22 * η := by
    linarith
  have hyx :
      frame_quadratic μ (coordPoint u v p y) -
          frame_quadratic μ (coordPoint u v p x) ≤ 22 * η := by
    linarith
  exact abs_le.mpr ⟨by linarith, hxy⟩

set_option maxHeartbeats 800000 in
lemma exists_uniform_pole_cap_oscillation_of_low_north_near_infimum
    (hdim : 3 ≤ Module.finrank ℂ H)
    {η : ℝ} (hηpos : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {θ : ℝ}, 0 < θ → θ ≤ Real.pi / 3 →
      ∀ (μ : FrameFunction H) {u v p : H} {β : ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {w : ℝ × ℝ × ℝ},
          w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
          0 < w.2.2 →
          horizontalRadius w ≠ 0 →
          β ≤ polarSumValue μ u v p w) →
        frame_quadratic μ p ≤ η →
        polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η →
        ∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) p < δ →
          dist (coordPoint u v p y) p < δ →
          |frame_quadratic μ (coordPoint u v p x) -
              frame_quadratic μ (coordPoint u v p y)| ≤
            22 * η := by
  let ε : ℝ := (1 : ℝ) / 512
  have hε : 0 < ε := by
    norm_num [ε]
  have ha : 0 ≤ 5 * η / 2 := by
    nlinarith
  rcases nonpolar_oscillation_bound_of_cap_uniform_any
      (H := H) hdim (a := 5 * η / 2) (ε := ε) ha hε with
    ⟨δ, hδ, hnonpolar⟩
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ0 hθle μ u v p β hu hv hp huv hup hvp hβ hpη hzβ x y hx hy hdx hdy
  let x0 : ℝ × ℝ × ℝ := psiCenterCoord θ
  have hθpi : θ < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hx0 : x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 := by
    simpa [x0] using psiCenterCoord_sq_sum θ
  have hρx0 : horizontalRadius x0 ≠ 0 := by
    simpa [x0] using horizontalRadius_psiCenterCoord_ne_zero hθ0 hθpi
  let xH : H := coordPoint u v p x0
  let bH : H := coordPoint u v p (targetBridgeCoord x0)
  let qH : H := coordPoint u v p (targetPoleCoord x0)
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have hxH : ‖xH‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hx0
  have hbH : ‖bH‖ = 1 := by
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hx0 hρx0
  have hqH : ‖qH‖ = 1 := by
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρx0
  have hxb : inner (𝕜 := ℂ) xH bH = 0 := by
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρx0
  have hxq : inner (𝕜 := ℂ) xH qH = 0 := by
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρx0
  have hbq : inner (𝕜 := ℂ) bH qH = 0 := by
    have htmp := inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρx0
    simpa [xH, bH, qH, inner_eq_zero_symm] using htmp
  have hbx : inner (𝕜 := ℂ) bH xH = 0 := by
    simpa [inner_eq_zero_symm] using hxb
  have hqx : inner (𝕜 := ℂ) qH xH = 0 := by
    simpa [inner_eq_zero_symm] using hxq
  have hosc' :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint bH qH xH x) xH < ε →
        dist (coordPoint bH qH xH y) xH < ε →
        |frame_quadratic (H := H) μavg (coordPoint bH qH xH x) -
            frame_quadratic (H := H) μavg (coordPoint bH qH xH y)| ≤
          5 * η / 2 := by
    intro a b ha' hb' hda hdb
    have ha_cycle := cycleCoord_sq_sum ha'
    have hb_cycle := cycleCoord_sq_sum hb'
    have ha_point :
        coordPoint bH qH xH a = coordPoint xH bH qH (cycleCoord a) := by
      exact coordPoint_cycle xH bH qH a
    have hb_point :
        coordPoint bH qH xH b = coordPoint xH bH qH (cycleCoord b) := by
      exact coordPoint_cycle xH bH qH b
    have hda' :
        dist (coordPoint xH bH qH (cycleCoord a)) xH < ε := by
      simpa [ha_point] using hda
    have hdb' :
        dist (coordPoint xH bH qH (cycleCoord b)) xH < ε := by
      simpa [hb_point] using hdb
    have hmain :=
      targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum_on_north_low_uniform
        (θ := θ) hθ0 hθle hdim μ hu hv hp huv hup hvp hβ hpη hzβ
        ha_cycle hb_cycle hda' hdb'
    simpa [μavg, ha_point, hb_point] using hmain
  let z : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 poleCoord)
  have hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 := by
    dsimp [z]
    apply cycleCoordInv_sq_sum
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 (by simp [poleCoord]) hρx0
  have hρz : horizontalRadius z ≠ 0 := by
    dsimp [z]
    exact horizontalRadius_cycleCoordInv_targetFrameCoords_poleCoord_ne_zero hρx0
  have hlocal_avg :
      ∀ {a b : ℝ × ℝ × ℝ},
        a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 = 1 →
        b.1 ^ 2 + b.2.1 ^ 2 + b.2.2 ^ 2 = 1 →
        dist (coordPoint u v p a) p < δ →
        dist (coordPoint u v p b) p < δ →
        |frame_quadratic (H := H) μavg (coordPoint u v p a) -
            frame_quadratic (H := H) μavg (coordPoint u v p b)| ≤
          10 * η := by
    intro a b ha' hb' hda hdb
    let ta : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 a)
    let tb : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 b)
    have hta : ta.1 ^ 2 + ta.2.1 ^ 2 + ta.2.2 ^ 2 = 1 := by
      dsimp [ta]
      apply cycleCoordInv_sq_sum
      exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 ha' hρx0
    have htb : tb.1 ^ 2 + tb.2.1 ^ 2 + tb.2.2 ^ 2 = 1 := by
      dsimp [tb]
      apply cycleCoordInv_sq_sum
      exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 hb' hρx0
    have hta_point :
        coordPoint bH qH xH ta = coordPoint u v p a := by
      dsimp [ta]
      rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH)
        (x := targetFrameCoords x0 a)]
      rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
        (y := targetFrameCoords x0 a)]
      rw [targetFrameReparam_targetFrameCoords (z := x0) (x := a) hx0 hρx0]
    have htb_point :
        coordPoint bH qH xH tb = coordPoint u v p b := by
      dsimp [tb]
      rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH)
        (x := targetFrameCoords x0 b)]
      rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
        (y := targetFrameCoords x0 b)]
      rw [targetFrameReparam_targetFrameCoords (z := x0) (x := b) hx0 hρx0]
    have hz_point :
        coordPoint bH qH xH z = p := by
      dsimp [z]
      rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH)
        (x := targetFrameCoords x0 poleCoord)]
      rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
        (y := targetFrameCoords x0 poleCoord)]
      rw [targetFrameReparam_targetFrameCoords (z := x0) (x := poleCoord) hx0 hρx0]
      exact coordPoint_poleCoord u v p
    have hda' :
        dist (coordPoint bH qH xH ta) (coordPoint bH qH xH z) < δ := by
      simpa [hta_point, hz_point] using hda
    have hdb' :
        dist (coordPoint bH qH xH tb) (coordPoint bH qH xH z) < δ := by
      simpa [htb_point, hz_point] using hdb
    have hmain :
        |frame_quadratic (H := H) μavg (coordPoint bH qH xH ta) -
            frame_quadratic (H := H) μavg (coordPoint bH qH xH tb)| ≤
          4 * (5 * η / 2) := by
      exact hnonpolar μavg hbH hqH hxH hbq hbx hqx hosc' hz hρz hta htb hda' hdb'
    have hmain' :
        |frame_quadratic (H := H) μavg (coordPoint u v p a) -
            frame_quadratic (H := H) μavg (coordPoint u v p b)| ≤
          4 * (5 * η / 2) := by
      simpa [μavg, hta_point, htb_point] using hmain
    have hfinal :
        |frame_quadratic (H := H) μavg (coordPoint u v p a) -
            frame_quadratic (H := H) μavg (coordPoint u v p b)| ≤
          10 * η := by
      nlinarith
    exact hfinal
  have havgp_eq :
      frame_quadratic (H := H) μavg p = frame_quadratic μ p := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp poleCoord
    have hpole :
        polarSumValue μ u v p poleCoord = 2 * frame_quadratic μ p := by
      have hturn : polarQuarterTurnCoord poleCoord = poleCoord := by
        simp [polarQuarterTurnCoord, poleCoord]
      rw [polarSumValue, hturn, coordPoint_poleCoord]
      ring
    have htwo' :
        2 * frame_quadratic (H := H) μavg p = 2 * frame_quadratic μ p := by
      simpa [μavg, coordPoint_poleCoord] using htwo.trans hpole
    nlinarith
  have hpdist : dist (coordPoint u v p poleCoord) p < δ := by
    simpa [coordPoint_poleCoord] using hδ
  have hlocx :
      |frame_quadratic (H := H) μavg (coordPoint u v p x) -
          frame_quadratic (H := H) μavg p| ≤ 10 * η := by
    simpa [μavg, coordPoint_poleCoord] using
      (hlocal_avg hx (by simp [poleCoord]) hdx hpdist)
  have hlocy :
      |frame_quadratic (H := H) μavg (coordPoint u v p y) -
          frame_quadratic (H := H) μavg p| ≤ 10 * η := by
    simpa [μavg, coordPoint_poleCoord] using
      (hlocal_avg hy (by simp [poleCoord]) hdy hpdist)
  have havgx_le :
      frame_quadratic (H := H) μavg (coordPoint u v p x) ≤ 11 * η := by
    have hupperx :
        frame_quadratic (H := H) μavg (coordPoint u v p x) -
            frame_quadratic (H := H) μavg p ≤ 10 * η := by
      exact (abs_le.mp hlocx).2
    nlinarith
  have havgy_le :
      frame_quadratic (H := H) μavg (coordPoint u v p y) ≤ 11 * η := by
    have huppery :
        frame_quadratic (H := H) μavg (coordPoint u v p y) -
            frame_quadratic (H := H) μavg p ≤ 10 * η := by
      exact (abs_le.mp hlocy).2
    nlinarith
  have hGx_le :
      polarSumValue μ u v p x ≤ 22 * η := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp x
    have htwo' :
        2 * frame_quadratic (H := H) μavg (coordPoint u v p x) ≤ 22 * η := by
      nlinarith
    linarith
  have hGy_le :
      polarSumValue μ u v p y ≤ 22 * η := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp y
    have htwo' :
        2 * frame_quadratic (H := H) μavg (coordPoint u v p y) ≤ 22 * η := by
      nlinarith
    linarith
  have hx_le :
      frame_quadratic μ (coordPoint u v p x) ≤ 22 * η := by
    have hnonneg_rot := frame_quadratic_nonneg μ (coordPoint u v p (polarQuarterTurnCoord x))
    unfold polarSumValue at hGx_le
    linarith
  have hy_le :
      frame_quadratic μ (coordPoint u v p y) ≤ 22 * η := by
    have hnonneg_rot := frame_quadratic_nonneg μ (coordPoint u v p (polarQuarterTurnCoord y))
    unfold polarSumValue at hGy_le
    linarith
  have hx_nonneg : 0 ≤ frame_quadratic μ (coordPoint u v p x) :=
    frame_quadratic_nonneg μ (coordPoint u v p x)
  have hy_nonneg : 0 ≤ frame_quadratic μ (coordPoint u v p y) :=
    frame_quadratic_nonneg μ (coordPoint u v p y)
  have hxy :
      frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y) ≤ 22 * η := by
    linarith
  have hyx :
      frame_quadratic μ (coordPoint u v p y) -
          frame_quadratic μ (coordPoint u v p x) ≤ 22 * η := by
    linarith
  exact abs_le.mpr ⟨by linarith, hxy⟩

set_option maxHeartbeats 800000 in
lemma exists_uniform_pole_cap_oscillation_of_away_north_near_infimum
    (hdim : 3 ≤ Module.finrank ℂ H)
    {η τ : ℝ} (hηpos : 0 < η) (hτ0 : 0 < τ) (hτpi : τ < Real.pi) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {θ : ℝ}, 0 < θ → θ ≤ Real.pi / 2 - τ →
      ∀ (μ : FrameFunction H) {u v p : H} {β : ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {w : ℝ × ℝ × ℝ},
          w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
          0 < w.2.2 →
          horizontalRadius w ≠ 0 →
          β ≤ polarSumValue μ u v p w) →
        frame_quadratic μ p ≤ η →
        polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η →
        ∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) p < δ →
          dist (coordPoint u v p y) p < δ →
          |frame_quadratic μ (coordPoint u v p x) -
              frame_quadratic μ (coordPoint u v p y)| ≤
            22 * η := by
  let ε : ℝ := Real.sin τ / 256
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hτ0 hτpi) (by norm_num)
  have ha : 0 ≤ 5 * η / 2 := by
    nlinarith
  rcases nonpolar_oscillation_bound_of_cap_uniform_any
      (H := H) hdim (a := 5 * η / 2) (ε := ε) ha hε with
    ⟨δ, hδ, hnonpolar⟩
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ0 hθτ μ u v p β hu hv hp huv hup hvp hβ hpη hzβ x y hx hy hdx hdy
  let x0 : ℝ × ℝ × ℝ := psiCenterCoord θ
  have hθpi : θ < Real.pi / 2 := by
    linarith
  have hx0 : x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 := by
    simpa [x0] using psiCenterCoord_sq_sum θ
  have hρx0 : horizontalRadius x0 ≠ 0 := by
    simpa [x0] using horizontalRadius_psiCenterCoord_ne_zero hθ0 hθpi
  let xH : H := coordPoint u v p x0
  let bH : H := coordPoint u v p (targetBridgeCoord x0)
  let qH : H := coordPoint u v p (targetPoleCoord x0)
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have hxH : ‖xH‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hx0
  have hbH : ‖bH‖ = 1 := by
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hx0 hρx0
  have hqH : ‖qH‖ = 1 := by
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρx0
  have hxb : inner (𝕜 := ℂ) xH bH = 0 := by
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρx0
  have hxq : inner (𝕜 := ℂ) xH qH = 0 := by
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρx0
  have hbq : inner (𝕜 := ℂ) bH qH = 0 := by
    have htmp := inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρx0
    simpa [xH, bH, qH, inner_eq_zero_symm] using htmp
  have hbx : inner (𝕜 := ℂ) bH xH = 0 := by
    simpa [inner_eq_zero_symm] using hxb
  have hqx : inner (𝕜 := ℂ) qH xH = 0 := by
    simpa [inner_eq_zero_symm] using hxq
  have hosc' :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint bH qH xH x) xH < ε →
        dist (coordPoint bH qH xH y) xH < ε →
        |frame_quadratic (H := H) μavg (coordPoint bH qH xH x) -
            frame_quadratic (H := H) μavg (coordPoint bH qH xH y)| ≤
          5 * η / 2 := by
    intro a b ha' hb' hda hdb
    have ha_cycle := cycleCoord_sq_sum ha'
    have hb_cycle := cycleCoord_sq_sum hb'
    have ha_point :
        coordPoint bH qH xH a = coordPoint xH bH qH (cycleCoord a) := by
      exact coordPoint_cycle xH bH qH a
    have hb_point :
        coordPoint bH qH xH b = coordPoint xH bH qH (cycleCoord b) := by
      exact coordPoint_cycle xH bH qH b
    have hda' :
        dist (coordPoint xH bH qH (cycleCoord a)) xH < ε := by
      simpa [ha_point] using hda
    have hdb' :
        dist (coordPoint xH bH qH (cycleCoord b)) xH < ε := by
      simpa [hb_point] using hdb
    have hmain :=
      targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum_on_north_away_uniform
        (θ := θ) (τ := τ) hθ0 hτ0 hθτ
        hdim μ hu hv hp huv hup hvp hβ hpη hzβ
        ha_cycle hb_cycle hda' hdb'
    simpa [μavg, ha_point, hb_point] using hmain
  let z : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 poleCoord)
  have hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 := by
    dsimp [z]
    apply cycleCoordInv_sq_sum
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 (by simp [poleCoord]) hρx0
  have hρz : horizontalRadius z ≠ 0 := by
    dsimp [z]
    exact horizontalRadius_cycleCoordInv_targetFrameCoords_poleCoord_ne_zero hρx0
  have hlocal_avg :
      ∀ {a b : ℝ × ℝ × ℝ},
        a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 = 1 →
        b.1 ^ 2 + b.2.1 ^ 2 + b.2.2 ^ 2 = 1 →
        dist (coordPoint u v p a) p < δ →
        dist (coordPoint u v p b) p < δ →
        |frame_quadratic (H := H) μavg (coordPoint u v p a) -
            frame_quadratic (H := H) μavg (coordPoint u v p b)| ≤
          10 * η := by
    intro a b ha' hb' hda hdb
    let ta : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 a)
    let tb : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 b)
    have hta : ta.1 ^ 2 + ta.2.1 ^ 2 + ta.2.2 ^ 2 = 1 := by
      dsimp [ta]
      apply cycleCoordInv_sq_sum
      exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 ha' hρx0
    have htb : tb.1 ^ 2 + tb.2.1 ^ 2 + tb.2.2 ^ 2 = 1 := by
      dsimp [tb]
      apply cycleCoordInv_sq_sum
      exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 hb' hρx0
    have hta_point :
        coordPoint bH qH xH ta = coordPoint u v p a := by
      dsimp [ta]
      rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH)
        (x := targetFrameCoords x0 a)]
      rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
        (y := targetFrameCoords x0 a)]
      rw [targetFrameReparam_targetFrameCoords (z := x0) (x := a) hx0 hρx0]
    have htb_point :
        coordPoint bH qH xH tb = coordPoint u v p b := by
      dsimp [tb]
      rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH)
        (x := targetFrameCoords x0 b)]
      rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
        (y := targetFrameCoords x0 b)]
      rw [targetFrameReparam_targetFrameCoords (z := x0) (x := b) hx0 hρx0]
    have hz_point :
        coordPoint bH qH xH z = p := by
      dsimp [z]
      rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH)
        (x := targetFrameCoords x0 poleCoord)]
      rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
        (y := targetFrameCoords x0 poleCoord)]
      rw [targetFrameReparam_targetFrameCoords (z := x0) (x := poleCoord) hx0 hρx0]
      exact coordPoint_poleCoord u v p
    have hda' :
        dist (coordPoint bH qH xH ta) (coordPoint bH qH xH z) < δ := by
      simpa [hta_point, hz_point] using hda
    have hdb' :
        dist (coordPoint bH qH xH tb) (coordPoint bH qH xH z) < δ := by
      simpa [htb_point, hz_point] using hdb
    have hmain :
        |frame_quadratic (H := H) μavg (coordPoint bH qH xH ta) -
            frame_quadratic (H := H) μavg (coordPoint bH qH xH tb)| ≤
          4 * (5 * η / 2) := by
      exact hnonpolar μavg hbH hqH hxH hbq hbx hqx hosc' hz hρz hta htb hda' hdb'
    have hmain' :
        |frame_quadratic (H := H) μavg (coordPoint u v p a) -
            frame_quadratic (H := H) μavg (coordPoint u v p b)| ≤
          4 * (5 * η / 2) := by
      simpa [μavg, hta_point, htb_point] using hmain
    have hfinal :
        |frame_quadratic (H := H) μavg (coordPoint u v p a) -
            frame_quadratic (H := H) μavg (coordPoint u v p b)| ≤
          10 * η := by
      nlinarith
    exact hfinal
  have havgp_eq :
      frame_quadratic (H := H) μavg p = frame_quadratic μ p := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp poleCoord
    have hpole :
        polarSumValue μ u v p poleCoord = 2 * frame_quadratic μ p := by
      have hturn : polarQuarterTurnCoord poleCoord = poleCoord := by
        simp [polarQuarterTurnCoord, poleCoord]
      rw [polarSumValue, hturn, coordPoint_poleCoord]
      ring
    have htwo' :
        2 * frame_quadratic (H := H) μavg p = 2 * frame_quadratic μ p := by
      simpa [μavg, coordPoint_poleCoord] using htwo.trans hpole
    nlinarith
  have hpdist : dist (coordPoint u v p poleCoord) p < δ := by
    simpa [coordPoint_poleCoord] using hδ
  have hlocx :
      |frame_quadratic (H := H) μavg (coordPoint u v p x) -
          frame_quadratic (H := H) μavg p| ≤ 10 * η := by
    simpa [μavg, coordPoint_poleCoord] using
      (hlocal_avg hx (by simp [poleCoord]) hdx hpdist)
  have hlocy :
      |frame_quadratic (H := H) μavg (coordPoint u v p y) -
          frame_quadratic (H := H) μavg p| ≤ 10 * η := by
    simpa [μavg, coordPoint_poleCoord] using
      (hlocal_avg hy (by simp [poleCoord]) hdy hpdist)
  have havgx_le :
      frame_quadratic (H := H) μavg (coordPoint u v p x) ≤ 11 * η := by
    have hupperx :
        frame_quadratic (H := H) μavg (coordPoint u v p x) -
            frame_quadratic (H := H) μavg p ≤ 10 * η := by
      exact (abs_le.mp hlocx).2
    nlinarith
  have havgy_le :
      frame_quadratic (H := H) μavg (coordPoint u v p y) ≤ 11 * η := by
    have huppery :
        frame_quadratic (H := H) μavg (coordPoint u v p y) -
            frame_quadratic (H := H) μavg p ≤ 10 * η := by
      exact (abs_le.mp hlocy).2
    nlinarith
  have hGx_le :
      polarSumValue μ u v p x ≤ 22 * η := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp x
    have htwo' :
        2 * frame_quadratic (H := H) μavg (coordPoint u v p x) ≤ 22 * η := by
      nlinarith
    linarith
  have hGy_le :
      polarSumValue μ u v p y ≤ 22 * η := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp y
    have htwo' :
        2 * frame_quadratic (H := H) μavg (coordPoint u v p y) ≤ 22 * η := by
      nlinarith
    linarith
  have hx_le :
      frame_quadratic μ (coordPoint u v p x) ≤ 22 * η := by
    have hnonneg_rot := frame_quadratic_nonneg μ (coordPoint u v p (polarQuarterTurnCoord x))
    unfold polarSumValue at hGx_le
    linarith
  have hy_le :
      frame_quadratic μ (coordPoint u v p y) ≤ 22 * η := by
    have hnonneg_rot := frame_quadratic_nonneg μ (coordPoint u v p (polarQuarterTurnCoord y))
    unfold polarSumValue at hGy_le
    linarith
  have hx_nonneg : 0 ≤ frame_quadratic μ (coordPoint u v p x) :=
    frame_quadratic_nonneg μ (coordPoint u v p x)
  have hy_nonneg : 0 ≤ frame_quadratic μ (coordPoint u v p y) :=
    frame_quadratic_nonneg μ (coordPoint u v p y)
  have hxy :
      frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y) ≤ 22 * η := by
    linarith
  have hyx :
      frame_quadratic μ (coordPoint u v p y) -
          frame_quadratic μ (coordPoint u v p x) ≤ 22 * η := by
    linarith
  exact abs_le.mpr ⟨by linarith, hxy⟩

lemma exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          22 * η := by
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  rcases exists_local_oscillation_neighborhood_of_quarterTurnAverage_at_p_near_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hθ0 hθpi hβ hη hzβ with
    ⟨δ, hδ, hlocal⟩
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have havgp_eq :
      frame_quadratic (H := H) μavg p = frame_quadratic μ p := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp poleCoord
    have hpole :
        polarSumValue μ u v p poleCoord = 2 * frame_quadratic μ p := by
      have hturn : polarQuarterTurnCoord poleCoord = poleCoord := by
        simp [polarQuarterTurnCoord, poleCoord]
      rw [polarSumValue, hturn, coordPoint_poleCoord]
      ring
    have htwo' :
        2 * frame_quadratic (H := H) μavg p = 2 * frame_quadratic μ p := by
      simpa [μavg, coordPoint_poleCoord] using htwo.trans hpole
    nlinarith
  have havgp_le : frame_quadratic (H := H) μavg p ≤ η := by
    rw [havgp_eq]
    exact hη
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hdx hdy
  have hpdist : dist (coordPoint u v p poleCoord) p < δ := by
    simpa [coordPoint_poleCoord] using hδ
  have hlocx :
      |frame_quadratic (H := H) μavg (coordPoint u v p x) -
          frame_quadratic (H := H) μavg p| ≤ 10 * η := by
    simpa [μavg, coordPoint_poleCoord] using
      (hlocal hx (by simp [poleCoord]) hdx hpdist)
  have hlocy :
      |frame_quadratic (H := H) μavg (coordPoint u v p y) -
          frame_quadratic (H := H) μavg p| ≤ 10 * η := by
    simpa [μavg, coordPoint_poleCoord] using
      (hlocal hy (by simp [poleCoord]) hdy hpdist)
  have havgx_le :
      frame_quadratic (H := H) μavg (coordPoint u v p x) ≤ 11 * η := by
    have hupperx :
        frame_quadratic (H := H) μavg (coordPoint u v p x) -
            frame_quadratic (H := H) μavg p ≤ 10 * η := by
      exact (abs_le.mp hlocx).2
    nlinarith
  have havgy_le :
      frame_quadratic (H := H) μavg (coordPoint u v p y) ≤ 11 * η := by
    have huppery :
        frame_quadratic (H := H) μavg (coordPoint u v p y) -
            frame_quadratic (H := H) μavg p ≤ 10 * η := by
      exact (abs_le.mp hlocy).2
    nlinarith
  have hGx_le :
      polarSumValue μ u v p x ≤ 22 * η := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp x
    have htwo' :
        2 * frame_quadratic (H := H) μavg (coordPoint u v p x) ≤ 22 * η := by
      nlinarith
    linarith
  have hGy_le :
      polarSumValue μ u v p y ≤ 22 * η := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp y
    have htwo' :
        2 * frame_quadratic (H := H) μavg (coordPoint u v p y) ≤ 22 * η := by
      nlinarith
    linarith
  have hx_le :
      frame_quadratic μ (coordPoint u v p x) ≤ 22 * η := by
    have hnonneg_rot := frame_quadratic_nonneg μ (coordPoint u v p (polarQuarterTurnCoord x))
    unfold polarSumValue at hGx_le
    linarith
  have hy_le :
      frame_quadratic μ (coordPoint u v p y) ≤ 22 * η := by
    have hnonneg_rot := frame_quadratic_nonneg μ (coordPoint u v p (polarQuarterTurnCoord y))
    unfold polarSumValue at hGy_le
    linarith
  have hx_nonneg : 0 ≤ frame_quadratic μ (coordPoint u v p x) :=
    frame_quadratic_nonneg μ (coordPoint u v p x)
  have hy_nonneg : 0 ≤ frame_quadratic μ (coordPoint u v p y) :=
    frame_quadratic_nonneg μ (coordPoint u v p y)
  have hxy :
      frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y) ≤ 22 * η := by
    linarith
  have hyx :
      frame_quadratic μ (coordPoint u v p y) -
          frame_quadratic μ (coordPoint u v p x) ≤ 22 * η := by
    linarith
  exact abs_le.mpr ⟨by linarith, hxy⟩

lemma exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum_of_positive_point
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ : polarSumValue μ u v p z ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p x)
            p < δ →
        dist
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p y)
            p < δ →
        |frame_quadratic μ
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p x) -
            frame_quadratic μ
              (coordPoint
                (coordPoint u v p (-targetPoleCoord z))
                (coordPoint u v p (horizontalUnitCoord z))
                p y)| ≤
          22 * η := by
  have hzlt1 : z.2.2 < 1 := by
    by_contra hznot
    have hge : 1 ≤ z.2.2 := le_of_not_gt hznot
    have hsq : 1 ≤ z.2.2 ^ 2 := by
      nlinarith
    have hsum : z.1 ^ 2 + z.2.1 ^ 2 = 0 := by
      nlinarith [hz, hsq]
    have hz1 : z.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have hz2 : z.2.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have : horizontalRadius z = 0 := by
      have hsq0 : horizontalRadius z ^ 2 = 0 := by
        rw [horizontalRadius_sq z]
        nlinarith [hz1, hz2]
      nlinarith [sq_nonneg (horizontalRadius z), hsq0]
    exact hρ this
  rcases arcsin_mem_open_quarter hzpos hzlt1 with ⟨hθ0, hθpi⟩
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'v' : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc] using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  have hβ' :
      ∀ {y : ℝ × ℝ × ℝ},
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        β ≤ polarSumValue μ u' w p y := by
    intro y hy
    have hy' :
        (meridianFrameReparam z y).1 ^ 2 +
        (meridianFrameReparam z y).2.1 ^ 2 +
            (meridianFrameReparam z y).2.2 ^ 2 = 1 := by
      exact meridianFrameReparam_sq_sum hy hρ
    dsimp [u', w]
    rw [polarSumValue_meridianFrameReparam
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (y := y) hρ]
    exact hβ hy'
  have hzβ' :
      polarSumValue μ u' w p (northMeridianCoord (Real.arcsin z.2.2)) ≤ β + η := by
    rw [← meridianFrameCoords_self_eq_northMeridian (z := z) hz hρ (le_of_lt hzpos)]
    dsimp [u', w]
    rw [polarSumValue_meridianFrameCoords
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (x := z) hρ]
    exact hzβ
  simpa [u', w] using
    exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum
      (hdim := hdim) (μ := μ)
      (u := u') (v := w) (p := p)
      hu' hwNorm hp hu'v' hu'p hwp
      hθ0 hθpi hβ' hη hzβ'

lemma exists_local_oscillation_neighborhood_of_positive_point_near_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ : polarSumValue μ u v p z ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) (coordPoint u v p z) < δ →
        dist (coordPoint u v p y) (coordPoint u v p z) < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          88 * η := by
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'v' : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc] using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  rcases exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum_of_positive_point
      (hdim := hdim) (μ := μ)
      (u := u) (v := v) (p := p)
      hu hv hp huv hup hvp hβ hη hz hρ hzpos hzβ with
    ⟨ε, hε, hosc⟩
  have hseed :
      (northMeridianCoord (Real.arcsin z.2.2)).1 ^ 2 +
          (northMeridianCoord (Real.arcsin z.2.2)).2.1 ^ 2 +
          (northMeridianCoord (Real.arcsin z.2.2)).2.2 ^ 2 = 1 := by
    simp [northMeridianCoord]
  have ha : 0 ≤ 22 * η := by
    nlinarith
  rcases sphere_oscillation_bound_of_cap
      (hdim := hdim) (μ := μ)
      (u := u') (v := w) (p := p)
      hu' hwNorm hp hu'v' hu'p hwp
      ha hε hosc hseed with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hdx hdy
  let tx : ℝ × ℝ × ℝ := meridianFrameCoords z x
  let ty : ℝ × ℝ × ℝ := meridianFrameCoords z y
  have htx :
      tx.1 ^ 2 + tx.2.1 ^ 2 + tx.2.2 ^ 2 = 1 := by
    dsimp [tx]
    rw [meridianFrameCoords_eq_meridianFlip z x]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := x) hx hρ)
  have hty :
      ty.1 ^ 2 + ty.2.1 ^ 2 + ty.2.2 ^ 2 = 1 := by
    dsimp [ty]
    rw [meridianFrameCoords_eq_meridianFlip z y]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := y) hy hρ)
  have htxPoint :
      coordPoint u' w p tx = coordPoint u v p x := by
    dsimp [tx, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z x)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z x) = x := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z x)]
      rw [meridianFrameCoords_eq_meridianFlip z x]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have htyPoint :
      coordPoint u' w p ty = coordPoint u v p y := by
    dsimp [ty, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z y)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z y) = y := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z y)]
      rw [meridianFrameCoords_eq_meridianFlip z y]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have hzPoint :
      coordPoint u' w p (northMeridianCoord (Real.arcsin z.2.2)) =
        coordPoint u v p z := by
    dsimp [u', w]
    exact coordPoint_meridianFrameCoords_self_eq_northMeridian
      (u := u) (v := v) (p := p) hz hρ (le_of_lt hzpos)
  have htxDist :
      dist (coordPoint u' w p tx)
          (coordPoint u' w p (northMeridianCoord (Real.arcsin z.2.2))) < δ := by
    simpa [htxPoint, hzPoint] using hdx
  have htyDist :
      dist (coordPoint u' w p ty)
          (coordPoint u' w p (northMeridianCoord (Real.arcsin z.2.2))) < δ := by
    simpa [htyPoint, hzPoint] using hdy
  have hmain :
      |frame_quadratic μ (coordPoint u' w p tx) -
          frame_quadratic μ (coordPoint u' w p ty)| ≤
        4 * (22 * η) := by
    exact hlocal htx hty htxDist htyDist
  have hmain' :
      |frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y)| ≤
        4 * (22 * η) := by
    simpa [htxPoint, htyPoint] using hmain
  have hfinal :
      |frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y)| ≤
        88 * η := by
    nlinarith
  exact hfinal

lemma exists_nonpolar_local_oscillation_neighborhood_of_meridian_near_infimum_on_north
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      0 < x0.2.2 ∧
      horizontalRadius x0 ≠ 0 ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist x x0 < δ →
        dist y x0 < δ →
        0 < x.2.2 ∧
        0 < y.2.2 ∧
        |polarSumValue μ u v p x - polarSumValue μ u v p y| ≤ 5 * η := by
  rcases Thm25.exists_sphere_point_with_gleasonPsiSwap_neg_pos hθ0 hθpi with
    ⟨ξ0, η0, r0, hx0, hx0pos, hneg0⟩
  let x0 : ℝ × ℝ × ℝ := (ξ0, (η0, r0))
  let ψ : ℝ × ℝ × ℝ → ℝ := fun x =>
    Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2
  have hcont : Continuous ψ := by
    simpa [ψ] using continuous_gleasonPsiSwap θ
  have hopenψ : IsOpen {x : ℝ × ℝ × ℝ | ψ x < 0} :=
    hcont.isOpen_preimage _ isOpen_Iio
  have hopenr : IsOpen {x : ℝ × ℝ × ℝ | 0 < x.2.2} :=
    continuous_snd.snd.isOpen_preimage _ isOpen_Ioi
  have hx0memψ : x0 ∈ {x : ℝ × ℝ × ℝ | ψ x < 0} := by
    simpa [x0, ψ] using hneg0
  have hx0memr : x0 ∈ {x : ℝ × ℝ × ℝ | 0 < x.2.2} := by
    simpa [x0] using hx0pos
  have hρx0 : horizontalRadius x0 ≠ 0 := by
    simpa [x0] using horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hneg0
  have hnhds :
      {x : ℝ × ℝ × ℝ | ψ x < 0 ∧ 0 < x.2.2} ∈ nhds x0 := by
    exact Filter.inter_mem (hopenψ.mem_nhds hx0memψ) (hopenr.mem_nhds hx0memr)
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδ, hball⟩
  refine ⟨x0, δ, hδ, by simpa [x0] using hx0, by simpa [x0] using hx0pos, hρx0, ?_⟩
  intro x y hx hy hdx hdy
  have hxball : x ∈ {x : ℝ × ℝ × ℝ | ψ x < 0 ∧ 0 < x.2.2} := hball hdx
  have hyball : y ∈ {x : ℝ × ℝ × ℝ | ψ x < 0 ∧ 0 < x.2.2} := hball hdy
  have hnegx : Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 := hxball.1
  have hnegy : Thm25.gleasonPsiSwap θ y.1 y.2.1 y.2.2 < 0 := hyball.1
  have hxpos : 0 < x.2.2 := hxball.2
  have hypos : 0 < y.2.2 := hyball.2
  have hρx : horizontalRadius x ≠ 0 := by
    exact horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hnegx
  have hρy : horizontalRadius y ≠ 0 := by
    exact horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hnegy
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hx hnegx with
    ⟨x1, sx, tx, hx1, hρx1, hsx, hsx0, htx, htx0, hx1_def, hx2_def⟩
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hy hnegy with
    ⟨y1, sy, ty, hy1, hρy1, hsy, hsy0, hty, hty0, hy1_def, hy2_def⟩
  have hstepx :
      polarSumValue μ u v p x ≤ polarSumValue μ u v p (northMeridianCoord θ) + 4 * η := by
    exact polarSumValue_le_two_step_targetFrame_add_four_eta
      (hdim := hdim) (μ := μ) (z := northMeridianCoord θ) hu hv hp huv hup hvp hη
      hx hρx hsx hsx0 hx1_def hρx1 htx htx0 hx2_def
  have hstepy :
      polarSumValue μ u v p y ≤ polarSumValue μ u v p (northMeridianCoord θ) + 4 * η := by
    exact polarSumValue_le_two_step_targetFrame_add_four_eta
      (hdim := hdim) (μ := μ) (z := northMeridianCoord θ) hu hv hp huv hup hvp hη
      hy hρy hsy hsy0 hy1_def hρy1 hty hty0 hy2_def
  have hlowx : β ≤ polarSumValue μ u v p x := hβ hx hxpos hρx
  have hhighx : polarSumValue μ u v p x ≤ β + 5 * η := by
    linarith
  have hlowy : β ≤ polarSumValue μ u v p y := hβ hy hypos hρy
  have hhighy : polarSumValue μ u v p y ≤ β + 5 * η := by
    linarith
  have hxy :
      polarSumValue μ u v p x - polarSumValue μ u v p y ≤ 5 * η := by
    linarith
  have hyx :
      polarSumValue μ u v p y - polarSumValue μ u v p x ≤ 5 * η := by
    linarith
  exact ⟨hxpos, hypos, abs_le.mpr ⟨by linarith, hxy⟩⟩

lemma exists_targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum_on_north
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      0 < x0.2.2 ∧
      horizontalRadius x0 ≠ 0 ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint (coordPoint u v p x0)
            (coordPoint u v p (targetBridgeCoord x0))
            (coordPoint u v p (targetPoleCoord x0)) x)
          (coordPoint u v p x0) < δ →
        dist (coordPoint (coordPoint u v p x0)
            (coordPoint u v p (targetBridgeCoord x0))
            (coordPoint u v p (targetPoleCoord x0)) y)
          (coordPoint u v p x0) < δ →
        |frame_quadratic (H := H)
            (quarterTurnAverageFrameFunction μ u v hu hv huv)
            (coordPoint (coordPoint u v p x0)
              (coordPoint u v p (targetBridgeCoord x0))
              (coordPoint u v p (targetPoleCoord x0)) x) -
          frame_quadratic (H := H)
            (quarterTurnAverageFrameFunction μ u v hu hv huv)
            (coordPoint (coordPoint u v p x0)
              (coordPoint u v p (targetBridgeCoord x0))
              (coordPoint u v p (targetPoleCoord x0)) y)| ≤
          5 * η / 2 := by
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  rcases exists_nonpolar_local_oscillation_neighborhood_of_meridian_near_infimum_on_north
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hθ0 hθpi hβ hη hzβ with
    ⟨x0, δ, hδ, hx0, hx0pos, hρx0, hlocal⟩
  refine ⟨x0, δ, hδ, hx0, hx0pos, hρx0, ?_⟩
  intro x y hx hy hdx hdy
  let xH : H := coordPoint u v p x0
  let bH : H := coordPoint u v p (targetBridgeCoord x0)
  let qH : H := coordPoint u v p (targetPoleCoord x0)
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have hx' :
      (targetFrameReparam x0 x).1 ^ 2 +
          (targetFrameReparam x0 x).2.1 ^ 2 +
          (targetFrameReparam x0 x).2.2 ^ 2 = 1 := by
    exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hx0 hx hρx0
  have hy' :
      (targetFrameReparam x0 y).1 ^ 2 +
          (targetFrameReparam x0 y).2.1 ^ 2 +
          (targetFrameReparam x0 y).2.2 ^ 2 = 1 := by
    exact targetFrameReparam_sq_sum hu hv hp huv hup hvp hx0 hy hρx0
  have hdx' : dist (targetFrameReparam x0 x) x0 < δ := by
    have hle :=
      dist_coords_le_dist_coordPoint hu hv hp huv hup hvp
        (targetFrameReparam x0 x) x0
    have hdistH :
        dist (coordPoint u v p (targetFrameReparam x0 x))
            (coordPoint u v p x0) < δ := by
      simpa [xH, bH, qH, coordPoint_targetFrameReparam] using hdx
    exact lt_of_le_of_lt hle hdistH
  have hdy' : dist (targetFrameReparam x0 y) x0 < δ := by
    have hle :=
      dist_coords_le_dist_coordPoint hu hv hp huv hup hvp
        (targetFrameReparam x0 y) x0
    have hdistH :
        dist (coordPoint u v p (targetFrameReparam x0 y))
            (coordPoint u v p x0) < δ := by
      simpa [xH, bH, qH, coordPoint_targetFrameReparam] using hdy
    exact lt_of_le_of_lt hle hdistH
  have hmain :
      |polarSumValue μ u v p (targetFrameReparam x0 x) -
          polarSumValue μ u v p (targetFrameReparam x0 y)| ≤ 5 * η := by
    rcases hlocal hx' hy' hdx' hdy' with ⟨_, _, hmain⟩
    exact hmain
  have hxAvg :
      2 * frame_quadratic (H := H) μavg
          (coordPoint xH bH qH x) =
        polarSumValue μ u v p (targetFrameReparam x0 x) := by
    simpa [μavg, xH, bH, qH, coordPoint_targetFrameReparam] using
      (two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp
        (targetFrameReparam x0 x))
  have hyAvg :
      2 * frame_quadratic (H := H) μavg
          (coordPoint xH bH qH y) =
        polarSumValue μ u v p (targetFrameReparam x0 y) := by
    simpa [μavg, xH, bH, qH, coordPoint_targetFrameReparam] using
      (two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp
        (targetFrameReparam x0 y))
  let A : ℝ := frame_quadratic (H := H) μavg (coordPoint xH bH qH x)
  let B : ℝ := frame_quadratic (H := H) μavg (coordPoint xH bH qH y)
  have hmain' : |2 * A - 2 * B| ≤ 5 * η := by
    simpa [A, B, hxAvg, hyAvg] using hmain
  have hfactor : |2 * A - 2 * B| = 2 * |A - B| := by
    rw [show 2 * A - 2 * B = 2 * (A - B) by ring]
    rw [abs_mul, abs_of_nonneg (by norm_num)]
  have hscaled : 2 * |A - B| ≤ 5 * η := by
    simpa [hfactor] using hmain'
  have hab : |A - B| ≤ 5 * η / 2 := by
    nlinarith
  simpa [A, B, sub_eq_add_neg] using hab

lemma exists_local_oscillation_neighborhood_of_quarterTurnAverage_at_p_near_infimum_on_north
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic (H := H)
            (quarterTurnAverageFrameFunction μ u v hu hv huv)
            (coordPoint u v p x) -
          frame_quadratic (H := H)
            (quarterTurnAverageFrameFunction μ u v hu hv huv)
            (coordPoint u v p y)| ≤
          10 * η := by
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  rcases exists_targetFrame_cap_oscillation_of_quarterTurnAverage_near_infimum_on_north
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hθ0 hθpi hβ hη hzβ with
    ⟨x0, ε, hε, hx0, hx0pos, hρx0, hcap⟩
  let xH : H := coordPoint u v p x0
  let bH : H := coordPoint u v p (targetBridgeCoord x0)
  let qH : H := coordPoint u v p (targetPoleCoord x0)
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have hxH : ‖xH‖ = 1 := by
    exact coordPoint_norm hu hv hp huv hup hvp hx0
  have hbH : ‖bH‖ = 1 := by
    exact coordPoint_targetBridgeCoord_norm hu hv hp huv hup hvp hx0 hρx0
  have hqH : ‖qH‖ = 1 := by
    exact coordPoint_targetPoleCoord_norm hu hv hp huv hup hvp hρx0
  have hxb : inner (𝕜 := ℂ) xH bH = 0 := by
    exact inner_coordPoint_targetBridgeCoord_zero hu hv hp huv hup hvp hρx0
  have hxq : inner (𝕜 := ℂ) xH qH = 0 := by
    exact inner_coordPoint_targetPoleCoord_zero hu hv hp huv hup hvp hρx0
  have hbq : inner (𝕜 := ℂ) bH qH = 0 := by
    have htmp := inner_targetPoleCoord_targetBridgeCoord_zero hu hv hp huv hup hvp hρx0
    simpa [xH, bH, qH, inner_eq_zero_symm] using htmp
  have hbx : inner (𝕜 := ℂ) bH xH = 0 := by
    simpa [inner_eq_zero_symm] using hxb
  have hqx : inner (𝕜 := ℂ) qH xH = 0 := by
    simpa [inner_eq_zero_symm] using hxq
  have hosc' :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint bH qH xH x) xH < ε →
        dist (coordPoint bH qH xH y) xH < ε →
        |frame_quadratic (H := H) μavg (coordPoint bH qH xH x) -
            frame_quadratic (H := H) μavg (coordPoint bH qH xH y)| ≤
          5 * η / 2 := by
    intro x y hx hy hdx hdy
    have hx' := cycleCoord_sq_sum hx
    have hy' := cycleCoord_sq_sum hy
    have hxc :
        coordPoint bH qH xH x = coordPoint xH bH qH (cycleCoord x) := by
      exact coordPoint_cycle xH bH qH x
    have hyc :
        coordPoint bH qH xH y = coordPoint xH bH qH (cycleCoord y) := by
      exact coordPoint_cycle xH bH qH y
    have hdx' :
        dist (coordPoint xH bH qH (cycleCoord x)) xH < ε := by
      simpa [hxc] using hdx
    have hdy' :
        dist (coordPoint xH bH qH (cycleCoord y)) xH < ε := by
      simpa [hyc] using hdy
    have hmain := hcap hx' hy' hdx' hdy'
    simpa [hxc, hyc] using hmain
  let z : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 poleCoord)
  have hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 := by
    apply cycleCoordInv_sq_sum
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 (by simp [poleCoord]) hρx0
  have ha : 0 ≤ 5 * η / 2 := by
    nlinarith
  rcases sphere_oscillation_bound_of_cap
      (hdim := hdim) (μ := μavg)
      (u := bH) (v := qH) (p := xH)
      hbH hqH hxH hbq hbx hqx
      (a := 5 * η / 2) (ε := ε) ha hε
      (hosc := hosc') (z := z) hz with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hdx hdy
  let tx : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 x)
  let ty : ℝ × ℝ × ℝ := cycleCoordInv (targetFrameCoords x0 y)
  have htx : tx.1 ^ 2 + tx.2.1 ^ 2 + tx.2.2 ^ 2 = 1 := by
    apply cycleCoordInv_sq_sum
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 hx hρx0
  have hty : ty.1 ^ 2 + ty.2.1 ^ 2 + ty.2.2 ^ 2 = 1 := by
    apply cycleCoordInv_sq_sum
    exact targetFrameCoords_sq_sum hu hv hp huv hup hvp hx0 hy hρx0
  have htxPoint :
      coordPoint bH qH xH tx = coordPoint u v p x := by
    rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH) (x := targetFrameCoords x0 x)]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
      (y := targetFrameCoords x0 x)]
    rw [targetFrameReparam_targetFrameCoords (z := x0) (x := x) hx0 hρx0]
  have htyPoint :
      coordPoint bH qH xH ty = coordPoint u v p y := by
    rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH) (x := targetFrameCoords x0 y)]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
      (y := targetFrameCoords x0 y)]
    rw [targetFrameReparam_targetFrameCoords (z := x0) (x := y) hx0 hρx0]
  have hzPoint :
      coordPoint bH qH xH z = p := by
    rw [coordPoint_cycleInv (a := xH) (b := bH) (c := qH) (x := targetFrameCoords x0 poleCoord)]
    rw [coordPoint_targetFrameReparam (u := u) (v := v) (p := p) (z := x0)
      (y := targetFrameCoords x0 poleCoord)]
    rw [targetFrameReparam_targetFrameCoords (z := x0) (x := poleCoord) hx0 hρx0]
    exact coordPoint_poleCoord u v p
  have htxDist :
      dist (coordPoint bH qH xH tx) (coordPoint bH qH xH z) < δ := by
    simpa [htxPoint, hzPoint] using hdx
  have htyDist :
      dist (coordPoint bH qH xH ty) (coordPoint bH qH xH z) < δ := by
    simpa [htyPoint, hzPoint] using hdy
  have hmain :
      |frame_quadratic (H := H) μavg (coordPoint bH qH xH tx) -
          frame_quadratic (H := H) μavg (coordPoint bH qH xH ty)| ≤
        4 * (5 * η / 2) := by
    exact hlocal htx hty htxDist htyDist
  have hmain' :
      |frame_quadratic (H := H) μavg (coordPoint u v p x) -
          frame_quadratic (H := H) μavg (coordPoint u v p y)| ≤
        4 * (5 * η / 2) := by
    simpa [μavg, htxPoint, htyPoint] using hmain
  have hfinal :
      |frame_quadratic (H := H) μavg (coordPoint u v p x) -
          frame_quadratic (H := H) μavg (coordPoint u v p y)| ≤
        10 * η := by
    nlinarith
  simpa [μavg] using hfinal

lemma exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum_on_north
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    (hzβ : polarSumValue μ u v p (northMeridianCoord θ) ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          22 * η := by
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  rcases exists_local_oscillation_neighborhood_of_quarterTurnAverage_at_p_near_infimum_on_north
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hθ0 hθpi hβ hη hzβ with
    ⟨δ, hδ, hlocal⟩
  let μavg : FrameFunction H := quarterTurnAverageFrameFunction μ u v hu hv huv
  have havgp_eq :
      frame_quadratic (H := H) μavg p = frame_quadratic μ p := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp poleCoord
    have hpole :
        polarSumValue μ u v p poleCoord = 2 * frame_quadratic μ p := by
      have hturn : polarQuarterTurnCoord poleCoord = poleCoord := by
        simp [polarQuarterTurnCoord, poleCoord]
      rw [polarSumValue, hturn, coordPoint_poleCoord]
      ring
    have htwo' :
        2 * frame_quadratic (H := H) μavg p = 2 * frame_quadratic μ p := by
      simpa [μavg, coordPoint_poleCoord] using htwo.trans hpole
    nlinarith
  have havgp_le : frame_quadratic (H := H) μavg p ≤ η := by
    rw [havgp_eq]
    exact hη
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hdx hdy
  have hpdist : dist (coordPoint u v p poleCoord) p < δ := by
    simpa [coordPoint_poleCoord] using hδ
  have hlocx :
      |frame_quadratic (H := H) μavg (coordPoint u v p x) -
          frame_quadratic (H := H) μavg p| ≤ 10 * η := by
    simpa [μavg, coordPoint_poleCoord] using
      (hlocal hx (by simp [poleCoord]) hdx hpdist)
  have hlocy :
      |frame_quadratic (H := H) μavg (coordPoint u v p y) -
          frame_quadratic (H := H) μavg p| ≤ 10 * η := by
    simpa [μavg, coordPoint_poleCoord] using
      (hlocal hy (by simp [poleCoord]) hdy hpdist)
  have havgx_le :
      frame_quadratic (H := H) μavg (coordPoint u v p x) ≤ 11 * η := by
    have hupperx :
        frame_quadratic (H := H) μavg (coordPoint u v p x) -
            frame_quadratic (H := H) μavg p ≤ 10 * η := by
      exact (abs_le.mp hlocx).2
    nlinarith
  have havgy_le :
      frame_quadratic (H := H) μavg (coordPoint u v p y) ≤ 11 * η := by
    have huppery :
        frame_quadratic (H := H) μavg (coordPoint u v p y) -
            frame_quadratic (H := H) μavg p ≤ 10 * η := by
      exact (abs_le.mp hlocy).2
    nlinarith
  have hGx_le :
      polarSumValue μ u v p x ≤ 22 * η := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp x
    have htwo' :
        2 * frame_quadratic (H := H) μavg (coordPoint u v p x) ≤ 22 * η := by
      nlinarith
    linarith
  have hGy_le :
      polarSumValue μ u v p y ≤ 22 * η := by
    have htwo :=
      two_mul_frame_quadratic_quarterTurnAverage_eq_polarSumValue
        (μ := μ) (u := u) (v := v) (p := p) hu hv hp huv hup hvp y
    have htwo' :
        2 * frame_quadratic (H := H) μavg (coordPoint u v p y) ≤ 22 * η := by
      nlinarith
    linarith
  have hx_le :
      frame_quadratic μ (coordPoint u v p x) ≤ 22 * η := by
    have hnonneg_rot := frame_quadratic_nonneg μ (coordPoint u v p (polarQuarterTurnCoord x))
    unfold polarSumValue at hGx_le
    linarith
  have hy_le :
      frame_quadratic μ (coordPoint u v p y) ≤ 22 * η := by
    have hnonneg_rot := frame_quadratic_nonneg μ (coordPoint u v p (polarQuarterTurnCoord y))
    unfold polarSumValue at hGy_le
    linarith
  have hx_nonneg : 0 ≤ frame_quadratic μ (coordPoint u v p x) :=
    frame_quadratic_nonneg μ (coordPoint u v p x)
  have hy_nonneg : 0 ≤ frame_quadratic μ (coordPoint u v p y) :=
    frame_quadratic_nonneg μ (coordPoint u v p y)
  have hxy :
      frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y) ≤ 22 * η := by
    linarith
  have hyx :
      frame_quadratic μ (coordPoint u v p y) -
          frame_quadratic μ (coordPoint u v p x) ≤ 22 * η := by
    linarith
  exact abs_le.mpr ⟨by linarith, hxy⟩

lemma thirdCoord_lt_one_of_sq_sum_of_pos_of_horizontalRadius_ne_zero
    {y : ℝ × ℝ × ℝ}
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hypos : 0 < y.2.2)
    (hρy : horizontalRadius y ≠ 0) :
    y.2.2 < 1 := by
  by_contra hy_not_lt
  have hge : 1 ≤ y.2.2 := le_of_not_gt hy_not_lt
  have hsq : 1 ≤ y.2.2 ^ 2 := by
    nlinarith
  have hsum : y.1 ^ 2 + y.2.1 ^ 2 = 0 := by
    nlinarith [hy, hsq]
  have : horizontalRadius y = 0 := by
    have hsq0 : horizontalRadius y ^ 2 = 0 := by
      rw [horizontalRadius_sq y]
      nlinarith [hsum]
    nlinarith [sq_nonneg (horizontalRadius y), hsq0]
  exact hρy this

lemma horizontalRadius_ne_zero_of_sq_sum_of_pos_of_thirdCoord_lt_one
    {y : ℝ × ℝ × ℝ}
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hypos : 0 < y.2.2)
    (hylt : y.2.2 < 1) :
    horizontalRadius y ≠ 0 := by
  intro hρy
  have hsq0 : horizontalRadius y ^ 2 = 0 := by
    nlinarith
  rw [horizontalRadius_sq y] at hsq0
  have hyone : y.2.2 ^ 2 = 1 := by
    nlinarith [hy, hsq0]
  nlinarith

lemma exists_high_positive_point_near_nonpole_infimum_add_three_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    ∃ y : ℝ × ℝ × ℝ,
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      0 < y.2.2 ∧
      horizontalRadius y ≠ 0 ∧
      polarSumValue μ u v p y ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
  rcases exists_rotated_high_positive_meridian_near_nonpole_infimum_add_three_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos hzβ with
    ⟨φ, a, _hθφ, _hφpi, ha, hapos, hρa, hpolar⟩
  let y : ℝ × ℝ × ℝ := meridianFrameReparam z a
  have hy :
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 := by
    dsimp [y]
    exact meridianFrameReparam_sq_sum ha hρ
  have hypos : 0 < y.2.2 := by
    dsimp [y]
    simpa [meridianFrameReparam_explicit hρ] using hapos
  have halt : a.2.2 < 1 :=
    thirdCoord_lt_one_of_sq_sum_of_pos_of_horizontalRadius_ne_zero ha hapos hρa
  have hylt : y.2.2 < 1 := by
    dsimp [y]
    simpa [meridianFrameReparam_explicit hρ] using halt
  have hρy : horizontalRadius y ≠ 0 :=
    horizontalRadius_ne_zero_of_sq_sum_of_pos_of_thirdCoord_lt_one hy hypos hylt
  have hpolar' :
      polarSumValue μ u v p y ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
    dsimp [y]
    rw [polarSumValue_meridianFrameReparam
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (y := a) hρ] at hpolar
    exact hpolar
  exact ⟨y, hy, hypos, hρy, hpolar'⟩

lemma exists_high_positive_point_near_nonpole_infimum_add_three_eta_with_third
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    ∃ y : ℝ × ℝ × ℝ,
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      z.2.2 / 2 < y.2.2 ∧
      0 < y.2.2 ∧
      horizontalRadius y ≠ 0 ∧
      polarSumValue μ u v p y ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
  rcases exists_rotated_high_positive_meridian_near_nonpole_infimum_add_three_eta_with_third
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos hzβ with
    ⟨φ, a, _hθφ, _hφpi, ha, hagthalf, hapos, hρa, hpolar⟩
  let y : ℝ × ℝ × ℝ := meridianFrameReparam z a
  have hy :
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 := by
    dsimp [y]
    exact meridianFrameReparam_sq_sum ha hρ
  have hygthalf : z.2.2 / 2 < y.2.2 := by
    dsimp [y]
    simpa [meridianFrameReparam_explicit hρ] using hagthalf
  have hypos : 0 < y.2.2 := by
    nlinarith
  have halt : a.2.2 < 1 :=
    thirdCoord_lt_one_of_sq_sum_of_pos_of_horizontalRadius_ne_zero ha hapos hρa
  have hylt : y.2.2 < 1 := by
    dsimp [y]
    simpa [meridianFrameReparam_explicit hρ] using halt
  have hρy : horizontalRadius y ≠ 0 :=
    horizontalRadius_ne_zero_of_sq_sum_of_pos_of_thirdCoord_lt_one hy hypos hylt
  have hpolar' :
      polarSumValue μ u v p y ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
    dsimp [y]
    rw [polarSumValue_meridianFrameReparam
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (y := a) hρ] at hpolar
    exact hpolar
  exact ⟨y, hy, hygthalf, hypos, hρy, hpolar'⟩

lemma exists_positive_point_near_pole_nonpole_infimum_add_three_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℝ × ℝ × ℝ,
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      0 < y.2.2 ∧
      horizontalRadius y ≠ 0 ∧
      dist (coordPoint u v p y) p < ε ∧
      polarSumValue μ u v p y ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
  let ε0 : ℝ := min (ε / 3) ((1 : ℝ) / 4)
  have hε0 : 0 < ε0 := by
    dsimp [ε0]
    exact lt_min (by positivity) (by norm_num)
  rcases exists_rotated_high_near_pole_nonpole_infimum_add_three_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos hzβ hε0 with
    ⟨φ, a, _hθφ, _hφpi, ha, hρa, hdist, hpolar⟩
  let y : ℝ × ℝ × ℝ := meridianFrameReparam z a
  have hy :
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 := by
    dsimp [y]
    exact meridianFrameReparam_sq_sum ha hρ
  have hdist_quarter : dist a poleCoord < (1 : ℝ) / 4 := by
    exact lt_of_lt_of_le hdist (min_le_right _ _)
  have ha_third_close : |a.2.2 - poleCoord.2.2| < (1 : ℝ) / 4 :=
    coord_snd_snd_abs_sub_lt_of_dist_lt (x := a) (y := poleCoord) hdist_quarter
  have hapos : 0 < a.2.2 := by
    have hlow := (abs_lt.mp ha_third_close).1
    dsimp [poleCoord] at hlow
    linarith
  have hypos : 0 < y.2.2 := by
    dsimp [y]
    simpa [meridianFrameReparam_explicit hρ] using hapos
  have halt : a.2.2 < 1 :=
    thirdCoord_lt_one_of_sq_sum_of_pos_of_horizontalRadius_ne_zero ha hapos hρa
  have hylt : y.2.2 < 1 := by
    dsimp [y]
    simpa [meridianFrameReparam_explicit hρ] using halt
  have hρy : horizontalRadius y ≠ 0 :=
    horizontalRadius_ne_zero_of_sq_sum_of_pos_of_thirdCoord_lt_one hy hypos hylt
  have hdist_eps : dist a poleCoord < ε / 3 := by
    exact lt_of_lt_of_le hdist (min_le_left _ _)
  have hy_dist : dist (coordPoint u v p y) p < ε := by
    have hmain :
        dist (coordPoint u v p y) p < 3 * (ε / 3) := by
      dsimp [y]
      exact dist_coordPoint_meridianFrameReparam_pole_lt
        hu hv hp huv hup hvp hρ hdist_eps
    have hthree : 3 * (ε / 3) = ε := by ring
    simpa [hthree] using hmain
  have hpolar' :
      polarSumValue μ u v p y ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := by
    dsimp [y]
    rw [← polarSumValue_meridianFrameReparam
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (y := a) hρ]
    exact hpolar
  exact ⟨y, hy, hypos, hρy, hy_dist, hpolar'⟩

lemma exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum_of_low_positive_point_on_north
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzlow : Real.arcsin z.2.2 ≤ Real.pi / 3)
    (hzβ : polarSumValue μ u v p z ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p x)
            p < δ →
        dist
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p y)
            p < δ →
        |frame_quadratic μ
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p x) -
            frame_quadratic μ
              (coordPoint
                (coordPoint u v p (-targetPoleCoord z))
                (coordPoint u v p (horizontalUnitCoord z))
                p y)| ≤
          22 * η := by
  have hzlt1 : z.2.2 < 1 :=
    thirdCoord_lt_one_of_sq_sum_of_pos_of_horizontalRadius_ne_zero hz hzpos hρ
  rcases arcsin_mem_open_quarter hzpos hzlt1 with ⟨hθ0, _hθpi⟩
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'v' : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc]
        using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  have hβ' :
      ∀ {y : ℝ × ℝ × ℝ},
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        0 < y.2.2 →
        horizontalRadius y ≠ 0 →
        β ≤ polarSumValue μ u' w p y := by
    intro y hy hypos hρy
    have hy' :
        (meridianFrameReparam z y).1 ^ 2 +
        (meridianFrameReparam z y).2.1 ^ 2 +
            (meridianFrameReparam z y).2.2 ^ 2 = 1 := by
      exact meridianFrameReparam_sq_sum hy hρ
    have hypos' : 0 < (meridianFrameReparam z y).2.2 := by
      simpa [meridianFrameReparam_explicit hρ] using hypos
    have hylt : y.2.2 < 1 :=
      thirdCoord_lt_one_of_sq_sum_of_pos_of_horizontalRadius_ne_zero hy hypos hρy
    have hylt' : (meridianFrameReparam z y).2.2 < 1 := by
      simpa [meridianFrameReparam_explicit hρ] using hylt
    have hρy' : horizontalRadius (meridianFrameReparam z y) ≠ 0 :=
      horizontalRadius_ne_zero_of_sq_sum_of_pos_of_thirdCoord_lt_one hy' hypos' hylt'
    dsimp [u', w]
    rw [polarSumValue_meridianFrameReparam
      (μ := μ) (u := u) (v := v) (p := p) hρ]
    exact hβ hy' hypos' hρy'
  have hzβ' :
      polarSumValue μ u' w p (northMeridianCoord (Real.arcsin z.2.2)) ≤ β + η := by
    rw [← meridianFrameCoords_self_eq_northMeridian (z := z) hz hρ (le_of_lt hzpos)]
    dsimp [u', w]
    rw [polarSumValue_meridianFrameCoords
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (x := z) hρ]
    exact hzβ
  simpa [u', w] using
    exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum_on_north_low_uniform
      (hdim := hdim) (μ := μ)
      (u := u') (v := w) (p := p)
      hu' hwNorm hp hu'v' hu'p hwp
      hθ0 hzlow hβ' hη hzβ'

lemma exists_uniform_pole_cap_oscillation_of_low_positive_point_near_infimum_on_north
    (hdim : 3 ≤ Module.finrank ℂ H)
    {η : ℝ} (hηpos : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (μ : FrameFunction H) {u v p : H} {β : ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {w : ℝ × ℝ × ℝ},
          w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
          0 < w.2.2 →
          horizontalRadius w ≠ 0 →
          β ≤ polarSumValue μ u v p w) →
        frame_quadratic μ p ≤ η →
        ∀ {z : ℝ × ℝ × ℝ},
          z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
          horizontalRadius z ≠ 0 →
          0 < z.2.2 →
          Real.arcsin z.2.2 ≤ Real.pi / 3 →
          polarSumValue μ u v p z ≤ β + η →
          ∀ {x y : ℝ × ℝ × ℝ},
            x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
            y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
            dist (coordPoint u v p x) p < δ →
            dist (coordPoint u v p y) p < δ →
            |frame_quadratic μ (coordPoint u v p x) -
                frame_quadratic μ (coordPoint u v p y)| ≤
              22 * η := by
  rcases exists_uniform_pole_cap_oscillation_of_low_north_near_infimum
      (H := H) hdim hηpos with
    ⟨δ, hδ, huniform⟩
  refine ⟨δ, hδ, ?_⟩
  intro μ u v p β hu hv hp huv hup hvp hβ hpη z hz hρ hzpos hzlow hzβ x y hx hy hdx hdy
  have hzlt1 : z.2.2 < 1 :=
    thirdCoord_lt_one_of_sq_sum_of_pos_of_horizontalRadius_ne_zero hz hzpos hρ
  rcases arcsin_mem_open_quarter hzpos hzlt1 with ⟨hθ0, _hθpi⟩
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'v' : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc]
        using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  have hβ' :
      ∀ {a : ℝ × ℝ × ℝ},
        a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 = 1 →
        0 < a.2.2 →
        horizontalRadius a ≠ 0 →
        β ≤ polarSumValue μ u' w p a := by
    intro a ha hapos hρa
    have ha' :
        (meridianFrameReparam z a).1 ^ 2 +
        (meridianFrameReparam z a).2.1 ^ 2 +
            (meridianFrameReparam z a).2.2 ^ 2 = 1 := by
      exact meridianFrameReparam_sq_sum ha hρ
    have hapos' : 0 < (meridianFrameReparam z a).2.2 := by
      simpa [meridianFrameReparam_explicit hρ] using hapos
    have halt : a.2.2 < 1 :=
      thirdCoord_lt_one_of_sq_sum_of_pos_of_horizontalRadius_ne_zero ha hapos hρa
    have halt' : (meridianFrameReparam z a).2.2 < 1 := by
      simpa [meridianFrameReparam_explicit hρ] using halt
    have hρa' : horizontalRadius (meridianFrameReparam z a) ≠ 0 :=
      horizontalRadius_ne_zero_of_sq_sum_of_pos_of_thirdCoord_lt_one ha' hapos' halt'
    dsimp [u', w]
    rw [polarSumValue_meridianFrameReparam
      (μ := μ) (u := u) (v := v) (p := p) hρ]
    exact hβ ha' hapos' hρa'
  have hzβ' :
      polarSumValue μ u' w p (northMeridianCoord (Real.arcsin z.2.2)) ≤ β + η := by
    rw [← meridianFrameCoords_self_eq_northMeridian (z := z) hz hρ (le_of_lt hzpos)]
    dsimp [u', w]
    rw [polarSumValue_meridianFrameCoords
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (x := z) hρ]
    exact hzβ
  have hcap :
      ∀ {a b : ℝ × ℝ × ℝ},
        a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 = 1 →
        b.1 ^ 2 + b.2.1 ^ 2 + b.2.2 ^ 2 = 1 →
        dist (coordPoint u' w p a) p < δ →
        dist (coordPoint u' w p b) p < δ →
        |frame_quadratic μ (coordPoint u' w p a) -
            frame_quadratic μ (coordPoint u' w p b)| ≤
          22 * η := by
    exact huniform hθ0 hzlow μ hu' hwNorm hp hu'v' hu'p hwp hβ' hpη hzβ'
  let tx : ℝ × ℝ × ℝ := meridianFrameCoords z x
  let ty : ℝ × ℝ × ℝ := meridianFrameCoords z y
  have htx :
      tx.1 ^ 2 + tx.2.1 ^ 2 + tx.2.2 ^ 2 = 1 := by
    dsimp [tx]
    rw [meridianFrameCoords_eq_meridianFlip z x]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := x) hx hρ)
  have hty :
      ty.1 ^ 2 + ty.2.1 ^ 2 + ty.2.2 ^ 2 = 1 := by
    dsimp [ty]
    rw [meridianFrameCoords_eq_meridianFlip z y]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := y) hy hρ)
  have htxPoint :
      coordPoint u' w p tx = coordPoint u v p x := by
    dsimp [tx, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z x)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z x) = x := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z x)]
      rw [meridianFrameCoords_eq_meridianFlip z x]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have htyPoint :
      coordPoint u' w p ty = coordPoint u v p y := by
    dsimp [ty, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z y)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z y) = y := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z y)]
      rw [meridianFrameCoords_eq_meridianFlip z y]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have htxDist : dist (coordPoint u' w p tx) p < δ := by
    simpa [htxPoint] using hdx
  have htyDist : dist (coordPoint u' w p ty) p < δ := by
    simpa [htyPoint] using hdy
  have hmain := hcap htx hty htxDist htyDist
  simpa [htxPoint, htyPoint] using hmain

lemma exists_uniform_pole_cap_oscillation_of_low_meridian_near_infimum_on_north
    (hdim : 3 ≤ Module.finrank ℂ H)
    {η : ℝ} (hηpos : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (μ : FrameFunction H) {u v p : H} {β : ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {w : ℝ × ℝ × ℝ},
          w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
          0 < w.2.2 →
          horizontalRadius w ≠ 0 →
          β ≤ polarSumValue μ u v p w) →
        frame_quadratic μ p ≤ η →
        ∀ {z : ℝ × ℝ × ℝ},
          z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
          horizontalRadius z ≠ 0 →
          polarSumValue μ u v p (lowHorizontalMeridianCoord z) ≤ β + η →
          ∀ {x y : ℝ × ℝ × ℝ},
            x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
            y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
            dist (coordPoint u v p x) p < δ →
            dist (coordPoint u v p y) p < δ →
            |frame_quadratic μ (coordPoint u v p x) -
                frame_quadratic μ (coordPoint u v p y)| ≤
              22 * η := by
  rcases exists_uniform_pole_cap_oscillation_of_low_positive_point_near_infimum_on_north
      (H := H) hdim hηpos with
    ⟨δ, hδ, huniform⟩
  refine ⟨δ, hδ, ?_⟩
  intro μ u v p β hu hv hp huv hup hvp hβ hpη z _hz hρ hzβ x y hx hy hdx hdy
  exact huniform μ hu hv hp huv hup hvp hβ hpη
    (lowHorizontalMeridianCoord_sq_sum hρ)
    (lowHorizontalMeridianCoord_horizontalRadius_ne_zero hρ)
    (lowHorizontalMeridianCoord_pos hρ)
    (lowHorizontalMeridianCoord_low hρ)
    hzβ hx hy hdx hdy

lemma exists_uniform_pole_cap_oscillation_of_low_meridian_near_nonpole_north_infimum
    (hdim : 3 ≤ Module.finrank ℂ H)
    {η : ℝ} (hηpos : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (μ : FrameFunction H) {u v p : H},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic μ p ≤ η →
        ∀ {z : ℝ × ℝ × ℝ},
          z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
          horizontalRadius z ≠ 0 →
          polarSumValue μ u v p (lowHorizontalMeridianCoord z) ≤
            sInf (northOpenNonpolePolarSumSet μ u v p) + η →
          ∀ {x y : ℝ × ℝ × ℝ},
            x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
            y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
            dist (coordPoint u v p x) p < δ →
            dist (coordPoint u v p y) p < δ →
            |frame_quadratic μ (coordPoint u v p x) -
                frame_quadratic μ (coordPoint u v p y)| ≤
              22 * η := by
  rcases exists_uniform_pole_cap_oscillation_of_low_meridian_near_infimum_on_north
      (H := H) hdim hηpos with
    ⟨δ, hδ, huniform⟩
  refine ⟨δ, hδ, ?_⟩
  intro μ u v p hu hv hp huv hup hvp hpη z hz hρ hzβ x y hx hy hdx hdy
  let β : ℝ := sInf (northOpenNonpolePolarSumSet μ u v p)
  have hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w := by
    intro w hw hwpos hρw
    dsimp [β]
    exact csInf_le
      (northOpenNonpolePolarSumSet_bddBelow μ u v p)
      ⟨w, hw, hwpos, hρw, rfl⟩
  exact huniform μ hu hv hp huv hup hvp hβ hpη hz hρ (by simpa [β] using hzβ)
    hx hy hdx hdy

lemma exists_uniform_pole_cap_oscillation_of_away_positive_point_near_infimum_on_north
    (hdim : 3 ≤ Module.finrank ℂ H)
    {η τ : ℝ} (hηpos : 0 < η) (hτ0 : 0 < τ) (hτpi : τ < Real.pi) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (μ : FrameFunction H) {u v p : H} {β : ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        (∀ {w : ℝ × ℝ × ℝ},
          w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
          0 < w.2.2 →
          horizontalRadius w ≠ 0 →
          β ≤ polarSumValue μ u v p w) →
        frame_quadratic μ p ≤ η →
        ∀ {z : ℝ × ℝ × ℝ},
          z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
          horizontalRadius z ≠ 0 →
          0 < z.2.2 →
          Real.arcsin z.2.2 ≤ Real.pi / 2 - τ →
          polarSumValue μ u v p z ≤ β + η →
          ∀ {x y : ℝ × ℝ × ℝ},
            x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
            y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
            dist (coordPoint u v p x) p < δ →
            dist (coordPoint u v p y) p < δ →
            |frame_quadratic μ (coordPoint u v p x) -
                frame_quadratic μ (coordPoint u v p y)| ≤
              22 * η := by
  rcases exists_uniform_pole_cap_oscillation_of_away_north_near_infimum
      (H := H) hdim hηpos hτ0 hτpi with
    ⟨δ, hδ, huniform⟩
  refine ⟨δ, hδ, ?_⟩
  intro μ u v p β hu hv hp huv hup hvp hβ hpη z hz hρ hzpos hzaway hzβ x y hx hy hdx hdy
  have hzlt1 : z.2.2 < 1 :=
    thirdCoord_lt_one_of_sq_sum_of_pos_of_horizontalRadius_ne_zero hz hzpos hρ
  rcases arcsin_mem_open_quarter hzpos hzlt1 with ⟨hθ0, _hθpi⟩
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'v' : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc]
        using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  have hβ' :
      ∀ {a : ℝ × ℝ × ℝ},
        a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 = 1 →
        0 < a.2.2 →
        horizontalRadius a ≠ 0 →
        β ≤ polarSumValue μ u' w p a := by
    intro a ha hapos hρa
    have ha' :
        (meridianFrameReparam z a).1 ^ 2 +
        (meridianFrameReparam z a).2.1 ^ 2 +
            (meridianFrameReparam z a).2.2 ^ 2 = 1 := by
      exact meridianFrameReparam_sq_sum ha hρ
    have hapos' : 0 < (meridianFrameReparam z a).2.2 := by
      simpa [meridianFrameReparam_explicit hρ] using hapos
    have halt : a.2.2 < 1 :=
      thirdCoord_lt_one_of_sq_sum_of_pos_of_horizontalRadius_ne_zero ha hapos hρa
    have halt' : (meridianFrameReparam z a).2.2 < 1 := by
      simpa [meridianFrameReparam_explicit hρ] using halt
    have hρa' : horizontalRadius (meridianFrameReparam z a) ≠ 0 :=
      horizontalRadius_ne_zero_of_sq_sum_of_pos_of_thirdCoord_lt_one ha' hapos' halt'
    dsimp [u', w]
    rw [polarSumValue_meridianFrameReparam
      (μ := μ) (u := u) (v := v) (p := p) hρ]
    exact hβ ha' hapos' hρa'
  have hzβ' :
      polarSumValue μ u' w p (northMeridianCoord (Real.arcsin z.2.2)) ≤ β + η := by
    rw [← meridianFrameCoords_self_eq_northMeridian (z := z) hz hρ (le_of_lt hzpos)]
    dsimp [u', w]
    rw [polarSumValue_meridianFrameCoords
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (x := z) hρ]
    exact hzβ
  have hcap :
      ∀ {a b : ℝ × ℝ × ℝ},
        a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 = 1 →
        b.1 ^ 2 + b.2.1 ^ 2 + b.2.2 ^ 2 = 1 →
        dist (coordPoint u' w p a) p < δ →
        dist (coordPoint u' w p b) p < δ →
        |frame_quadratic μ (coordPoint u' w p a) -
            frame_quadratic μ (coordPoint u' w p b)| ≤
          22 * η := by
    exact huniform hθ0 hzaway μ hu' hwNorm hp hu'v' hu'p hwp hβ' hpη hzβ'
  let tx : ℝ × ℝ × ℝ := meridianFrameCoords z x
  let ty : ℝ × ℝ × ℝ := meridianFrameCoords z y
  have htx :
      tx.1 ^ 2 + tx.2.1 ^ 2 + tx.2.2 ^ 2 = 1 := by
    dsimp [tx]
    rw [meridianFrameCoords_eq_meridianFlip z x]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := x) hx hρ)
  have hty :
      ty.1 ^ 2 + ty.2.1 ^ 2 + ty.2.2 ^ 2 = 1 := by
    dsimp [ty]
    rw [meridianFrameCoords_eq_meridianFlip z y]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := y) hy hρ)
  have htxPoint :
      coordPoint u' w p tx = coordPoint u v p x := by
    dsimp [tx, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z x)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z x) = x := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z x)]
      rw [meridianFrameCoords_eq_meridianFlip z x]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have htyPoint :
      coordPoint u' w p ty = coordPoint u v p y := by
    dsimp [ty, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z y)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z y) = y := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z y)]
      rw [meridianFrameCoords_eq_meridianFlip z y]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have htxDist : dist (coordPoint u' w p tx) p < δ := by
    simpa [htxPoint] using hdx
  have htyDist : dist (coordPoint u' w p ty) p < δ := by
    simpa [htyPoint] using hdy
  have hmain := hcap htx hty htxDist htyDist
  simpa [htxPoint, htyPoint] using hmain

def UniformPositiveNearInfimumLocalOscillationWith
    (C : ℝ) (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H} {z : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic μ p ≤ η →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        0 < z.2.2 →
        horizontalRadius z ≠ 0 →
        polarSumValue μ u v p z ≤
          sInf (northOpenNonpolePolarSumSet μ u v p) + η →
        ∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) (coordPoint u v p z) < δ →
          dist (coordPoint u v p y) (coordPoint u v p z) < δ →
          |frame_quadratic μ (coordPoint u v p x) -
              frame_quadratic μ (coordPoint u v p y)| ≤
            C * η

lemma exists_uniform_positive_near_infimum_local_oscillation_of_away
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {η τ : ℝ} (hηpos : 0 < η) (hτ0 : 0 < τ) (hτpi : τ < Real.pi) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H} {z : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic μ p ≤ η →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        0 < z.2.2 →
        horizontalRadius z ≠ 0 →
        Real.arcsin z.2.2 ≤ Real.pi / 2 - τ →
        polarSumValue μ u v p z ≤
          sInf (northOpenNonpolePolarSumSet μ u v p) + η →
        ∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) (coordPoint u v p z) < δ →
          dist (coordPoint u v p y) (coordPoint u v p z) < δ →
          |frame_quadratic μ (coordPoint u v p x) -
              frame_quadratic μ (coordPoint u v p y)| ≤
            88 * η := by
  rcases exists_uniform_pole_cap_oscillation_of_away_positive_point_near_infimum_on_north
      (H := H) hdim hηpos hτ0 hτpi with
    ⟨ε, hε, hpoleUniform⟩
  have h22nonneg : 0 ≤ 22 * η := by nlinarith
  rcases sphere_oscillation_bound_of_cap_uniform
      (hdim := hdim) (μ := μ) (a := 22 * η) (ε := ε) h22nonneg hε with
    ⟨δ, hδ, hsphere⟩
  refine ⟨δ, hδ, ?_⟩
  intro u v p z hu hv hp huv hup hvp hpη hz hzpos hρ hzaway hzβ x y hx hy hdx hdy
  let β : ℝ := sInf (northOpenNonpolePolarSumSet μ u v p)
  have hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w := by
    intro w hw hwpos hρw
    dsimp [β]
    exact csInf_le
      (northOpenNonpolePolarSumSet_bddBelow μ u v p)
      ⟨w, hw, hwpos, hρw, rfl⟩
  have hpoleCap :
      ∀ {a b : ℝ × ℝ × ℝ},
        a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 = 1 →
        b.1 ^ 2 + b.2.1 ^ 2 + b.2.2 ^ 2 = 1 →
        dist (coordPoint u v p a) p < ε →
        dist (coordPoint u v p b) p < ε →
        |frame_quadratic μ (coordPoint u v p a) -
            frame_quadratic μ (coordPoint u v p b)| ≤
          22 * η := by
    intro a b ha hb hda hdb
    exact hpoleUniform μ hu hv hp huv hup hvp hβ hpη
      hz hρ hzpos hzaway (by simpa [β] using hzβ) ha hb hda hdb
  have hmain :=
    hsphere hu hv hp huv hup hvp hpoleCap hz hx hy hdx hdy
  have hconst : 4 * (22 * η) = 88 * η := by ring
  simpa [hconst] using hmain

def EndpointPositiveNearInfimumLocalOscillationWith
    (C : ℝ) (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ τ : ℝ, ∃ δ : ℝ,
      0 < τ ∧ τ < Real.pi ∧ 0 < δ ∧
      ∀ {u v p : H} {z : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic μ p ≤ η →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        0 < z.2.2 →
        horizontalRadius z ≠ 0 →
        Real.pi / 2 - τ < Real.arcsin z.2.2 →
        polarSumValue μ u v p z ≤
          sInf (northOpenNonpolePolarSumSet μ u v p) + η →
        ∀ {x y : ℝ × ℝ × ℝ},
          x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
          y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
          dist (coordPoint u v p x) (coordPoint u v p z) < δ →
          dist (coordPoint u v p y) (coordPoint u v p z) < δ →
          |frame_quadratic μ (coordPoint u v p x) -
              frame_quadratic μ (coordPoint u v p y)| ≤
            C * η

lemma uniform_positive_near_infimum_local_of_endpoint_with
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ} (hC : 0 ≤ C)
    (hEndpoint :
      EndpointPositiveNearInfimumLocalOscillationWith C μ) :
    UniformPositiveNearInfimumLocalOscillationWith (C + 88) μ := by
  intro η hη
  rcases hEndpoint hη with
    ⟨τ, δE, hτ0, hτpi, hδE, hendpoint⟩
  rcases exists_uniform_positive_near_infimum_local_oscillation_of_away
      (hdim := hdim) (μ := μ) hη hτ0 hτpi with
    ⟨δA, hδA, haway⟩
  refine ⟨min δE δA, lt_min hδE hδA, ?_⟩
  intro u v p z hu hv hp huv hup hvp hpη hz hzpos hρ hzβ x y hx hy hdx hdy
  have hdxE :
      dist (coordPoint u v p x) (coordPoint u v p z) < δE :=
    lt_of_lt_of_le hdx (min_le_left δE δA)
  have hdyE :
      dist (coordPoint u v p y) (coordPoint u v p z) < δE :=
    lt_of_lt_of_le hdy (min_le_left δE δA)
  have hdxA :
      dist (coordPoint u v p x) (coordPoint u v p z) < δA :=
    lt_of_lt_of_le hdx (min_le_right δE δA)
  have hdyA :
      dist (coordPoint u v p y) (coordPoint u v p z) < δA :=
    lt_of_lt_of_le hdy (min_le_right δE δA)
  by_cases hawaycase : Real.arcsin z.2.2 ≤ Real.pi / 2 - τ
  · have hmain :=
      haway hu hv hp huv hup hvp hpη hz hzpos hρ hawaycase hzβ
        hx hy hdxA hdyA
    have hconst : 88 * η ≤ (C + 88) * η := by
      have hc : 88 ≤ C + 88 := by linarith
      exact mul_le_mul_of_nonneg_right hc (le_of_lt hη)
    exact le_trans hmain hconst
  · have hend : Real.pi / 2 - τ < Real.arcsin z.2.2 :=
      lt_of_not_ge hawaycase
    have hmain :=
      hendpoint hu hv hp huv hup hvp hpη hz hzpos hρ hend hzβ
        hx hy hdxE hdyE
    have hconst : C * η ≤ (C + 88) * η := by
      have hc : C ≤ C + 88 := by linarith
      exact mul_le_mul_of_nonneg_right hc (le_of_lt hη)
    exact le_trans hmain hconst

lemma exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum_of_positive_point_on_north
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ : polarSumValue μ u v p z ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p x)
            p < δ →
        dist
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p y)
            p < δ →
        |frame_quadratic μ
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p x) -
            frame_quadratic μ
              (coordPoint
                (coordPoint u v p (-targetPoleCoord z))
                (coordPoint u v p (horizontalUnitCoord z))
                p y)| ≤
          22 * η := by
  have hzlt1 : z.2.2 < 1 := by
    by_contra hznot
    have hge : 1 ≤ z.2.2 := le_of_not_gt hznot
    have hsq : 1 ≤ z.2.2 ^ 2 := by
      nlinarith
    have hsum : z.1 ^ 2 + z.2.1 ^ 2 = 0 := by
      nlinarith [hz, hsq]
    have hz1 : z.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have hz2 : z.2.1 = 0 := by
      nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, hsum]
    have : horizontalRadius z = 0 := by
      have hsq0 : horizontalRadius z ^ 2 = 0 := by
        rw [horizontalRadius_sq z]
        nlinarith [hz1, hz2]
      nlinarith [sq_nonneg (horizontalRadius z), hsq0]
    exact hρ this
  rcases arcsin_mem_open_quarter hzpos hzlt1 with ⟨hθ0, hθpi⟩
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'v' : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc] using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  have hβ' :
      ∀ {y : ℝ × ℝ × ℝ},
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        0 < y.2.2 →
        horizontalRadius y ≠ 0 →
        β ≤ polarSumValue μ u' w p y := by
    intro y hy hypos hρy
    have hy' :
        (meridianFrameReparam z y).1 ^ 2 +
        (meridianFrameReparam z y).2.1 ^ 2 +
            (meridianFrameReparam z y).2.2 ^ 2 = 1 := by
      exact meridianFrameReparam_sq_sum hy hρ
    have hypos' : 0 < (meridianFrameReparam z y).2.2 := by
      simpa [meridianFrameReparam_explicit hρ] using hypos
    have hylt : y.2.2 < 1 := by
      exact thirdCoord_lt_one_of_sq_sum_of_pos_of_horizontalRadius_ne_zero hy hypos hρy
    have hylt' : (meridianFrameReparam z y).2.2 < 1 := by
      simpa [meridianFrameReparam_explicit hρ] using hylt
    have hρy' : horizontalRadius (meridianFrameReparam z y) ≠ 0 := by
      exact horizontalRadius_ne_zero_of_sq_sum_of_pos_of_thirdCoord_lt_one hy' hypos' hylt'
    dsimp [u', w]
    rw [polarSumValue_meridianFrameReparam
      (μ := μ) (u := u) (v := v) (p := p) hρ]
    exact hβ hy' hypos' hρy'
  have hzβ' :
      polarSumValue μ u' w p (northMeridianCoord (Real.arcsin z.2.2)) ≤ β + η := by
    rw [← meridianFrameCoords_self_eq_northMeridian (z := z) hz hρ (le_of_lt hzpos)]
    dsimp [u', w]
    rw [polarSumValue_meridianFrameCoords
      (μ := μ) (u := u) (v := v) (p := p) (z := z) (x := z) hρ]
    exact hzβ
  simpa [u', w] using
    exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum_on_north
      (hdim := hdim) (μ := μ)
      (u := u') (v := w) (p := p)
      hu' hwNorm hp hu'v' hu'p hwp
      hθ0 hθpi hβ' hη hzβ'

lemma exists_local_oscillation_neighborhood_of_low_positive_point_near_infimum_on_north
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzlow : Real.arcsin z.2.2 ≤ Real.pi / 3)
    (hzβ : polarSumValue μ u v p z ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) (coordPoint u v p z) < δ →
        dist (coordPoint u v p y) (coordPoint u v p z) < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          88 * η := by
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'v' : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc] using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  rcases exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum_of_low_positive_point_on_north
      (hdim := hdim) (μ := μ)
      (u := u) (v := v) (p := p)
      hu hv hp huv hup hvp hβ hη hz hρ hzpos hzlow hzβ with
    ⟨ε, hε, hosc⟩
  have hseed :
      (northMeridianCoord (Real.arcsin z.2.2)).1 ^ 2 +
          (northMeridianCoord (Real.arcsin z.2.2)).2.1 ^ 2 +
          (northMeridianCoord (Real.arcsin z.2.2)).2.2 ^ 2 = 1 := by
    simp [northMeridianCoord]
  have ha : 0 ≤ 22 * η := by
    nlinarith
  rcases sphere_oscillation_bound_of_cap
      (hdim := hdim) (μ := μ)
      (u := u') (v := w) (p := p)
      hu' hwNorm hp hu'v' hu'p hwp
      ha hε hosc hseed with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hdx hdy
  let tx : ℝ × ℝ × ℝ := meridianFrameCoords z x
  let ty : ℝ × ℝ × ℝ := meridianFrameCoords z y
  have htx :
      tx.1 ^ 2 + tx.2.1 ^ 2 + tx.2.2 ^ 2 = 1 := by
    dsimp [tx]
    rw [meridianFrameCoords_eq_meridianFlip z x]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := x) hx hρ)
  have hty :
      ty.1 ^ 2 + ty.2.1 ^ 2 + ty.2.2 ^ 2 = 1 := by
    dsimp [ty]
    rw [meridianFrameCoords_eq_meridianFlip z y]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := y) hy hρ)
  have htxPoint :
      coordPoint u' w p tx = coordPoint u v p x := by
    dsimp [tx, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z x)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z x) = x := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z x)]
      rw [meridianFrameCoords_eq_meridianFlip z x]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have htyPoint :
      coordPoint u' w p ty = coordPoint u v p y := by
    dsimp [ty, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z y)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z y) = y := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z y)]
      rw [meridianFrameCoords_eq_meridianFlip z y]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have hzPoint :
      coordPoint u' w p (northMeridianCoord (Real.arcsin z.2.2)) =
        coordPoint u v p z := by
    dsimp [u', w]
    exact coordPoint_meridianFrameCoords_self_eq_northMeridian
      (u := u) (v := v) (p := p) hz hρ (le_of_lt hzpos)
  have htxDist :
      dist (coordPoint u' w p tx)
          (coordPoint u' w p (northMeridianCoord (Real.arcsin z.2.2))) < δ := by
    simpa [htxPoint, hzPoint] using hdx
  have htyDist :
      dist (coordPoint u' w p ty)
          (coordPoint u' w p (northMeridianCoord (Real.arcsin z.2.2))) < δ := by
    simpa [htyPoint, hzPoint] using hdy
  have hmain :
      |frame_quadratic μ (coordPoint u' w p tx) -
          frame_quadratic μ (coordPoint u' w p ty)| ≤
        4 * (22 * η) := by
    exact hlocal htx hty htxDist htyDist
  have hmain' :
      |frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y)| ≤
        4 * (22 * η) := by
    simpa [htxPoint, htyPoint] using hmain
  have hfinal :
      |frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y)| ≤
        88 * η := by
    nlinarith
  exact hfinal

lemma exists_local_oscillation_neighborhood_of_positive_point_near_infimum_on_north
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w)
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ : polarSumValue μ u v p z ≤ β + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) (coordPoint u v p z) < δ →
        dist (coordPoint u v p y) (coordPoint u v p z) < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          88 * η := by
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hηnonneg : 0 ≤ η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    linarith
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'v' : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc] using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  rcases exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum_of_positive_point_on_north
      (hdim := hdim) (μ := μ)
      (u := u) (v := v) (p := p)
      hu hv hp huv hup hvp hβ hη hz hρ hzpos hzβ with
    ⟨ε, hε, hosc⟩
  have hseed :
      (northMeridianCoord (Real.arcsin z.2.2)).1 ^ 2 +
          (northMeridianCoord (Real.arcsin z.2.2)).2.1 ^ 2 +
          (northMeridianCoord (Real.arcsin z.2.2)).2.2 ^ 2 = 1 := by
    simp [northMeridianCoord]
  have ha : 0 ≤ 22 * η := by
    nlinarith
  rcases sphere_oscillation_bound_of_cap
      (hdim := hdim) (μ := μ)
      (u := u') (v := w) (p := p)
      hu' hwNorm hp hu'v' hu'p hwp
      ha hε hosc hseed with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hdx hdy
  let tx : ℝ × ℝ × ℝ := meridianFrameCoords z x
  let ty : ℝ × ℝ × ℝ := meridianFrameCoords z y
  have htx :
      tx.1 ^ 2 + tx.2.1 ^ 2 + tx.2.2 ^ 2 = 1 := by
    dsimp [tx]
    rw [meridianFrameCoords_eq_meridianFlip z x]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := x) hx hρ)
  have hty :
      ty.1 ^ 2 + ty.2.1 ^ 2 + ty.2.2 ^ 2 = 1 := by
    dsimp [ty]
    rw [meridianFrameCoords_eq_meridianFlip z y]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := y) hy hρ)
  have htxPoint :
      coordPoint u' w p tx = coordPoint u v p x := by
    dsimp [tx, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z x)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z x) = x := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z x)]
      rw [meridianFrameCoords_eq_meridianFlip z x]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have htyPoint :
      coordPoint u' w p ty = coordPoint u v p y := by
    dsimp [ty, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z y)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z y) = y := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z y)]
      rw [meridianFrameCoords_eq_meridianFlip z y]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have hzPoint :
      coordPoint u' w p (northMeridianCoord (Real.arcsin z.2.2)) =
        coordPoint u v p z := by
    dsimp [u', w]
    exact coordPoint_meridianFrameCoords_self_eq_northMeridian
      (u := u) (v := v) (p := p) hz hρ (le_of_lt hzpos)
  have htxDist :
      dist (coordPoint u' w p tx)
          (coordPoint u' w p (northMeridianCoord (Real.arcsin z.2.2))) < δ := by
    simpa [htxPoint, hzPoint] using hdx
  have htyDist :
      dist (coordPoint u' w p ty)
          (coordPoint u' w p (northMeridianCoord (Real.arcsin z.2.2))) < δ := by
    simpa [htyPoint, hzPoint] using hdy
  have hmain :
      |frame_quadratic μ (coordPoint u' w p tx) -
          frame_quadratic μ (coordPoint u' w p ty)| ≤
        4 * (22 * η) := by
    exact hlocal htx hty htxDist htyDist
  have hmain' :
      |frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y)| ≤
        4 * (22 * η) := by
    simpa [htxPoint, htyPoint] using hmain
  have hfinal :
      |frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y)| ≤
        88 * η := by
    nlinarith
  exact hfinal

lemma exists_local_oscillation_neighborhood_of_positive_point_near_nonpole_north_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) (coordPoint u v p z) < δ →
        dist (coordPoint u v p y) (coordPoint u v p z) < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          88 * η := by
  let β : ℝ := sInf (northOpenNonpolePolarSumSet μ u v p)
  have hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w := by
    intro w hw hwpos hρw
    dsimp [β]
    exact csInf_le
      (northOpenNonpolePolarSumSet_bddBelow μ u v p)
      ⟨w, hw, hwpos, hρw, rfl⟩
  have hzβ' : polarSumValue μ u v p z ≤ β + η := by
    simpa [β] using hzβ
  exact exists_local_oscillation_neighborhood_of_positive_point_near_infimum_on_north
    (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hβ hη hz hρ hzpos hzβ'

lemma exists_near_pole_point_local_oscillation_of_nonpole_north_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hηpos : 0 < η)
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : ℝ × ℝ × ℝ, ∃ δ : ℝ,
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 ∧
      0 < y.2.2 ∧
      horizontalRadius y ≠ 0 ∧
      dist (coordPoint u v p y) p < ε ∧
      0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1 →
        x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x₁) (coordPoint u v p y) < δ →
        dist (coordPoint u v p x₂) (coordPoint u v p y) < δ →
        |frame_quadratic μ (coordPoint u v p x₁) -
            frame_quadratic μ (coordPoint u v p x₂)| ≤
          264 * η := by
  rcases exists_positive_point_near_pole_nonpole_infimum_add_three_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos hzβ hε with
    ⟨y, hy, hypos, hρy, hydist, hyβ⟩
  have hη3 : frame_quadratic μ p ≤ 3 * η := by
    nlinarith
  have hyβ3 :
      polarSumValue μ u v p y ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := hyβ
  rcases exists_local_oscillation_neighborhood_of_positive_point_near_nonpole_north_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη3 hy hρy hypos hyβ3 with
    ⟨δ, hδ, hlocal⟩
  refine ⟨y, δ, hy, hypos, hρy, hydist, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdx₁ hdx₂
  have hmain := hlocal hx₁ hx₂ hdx₁ hdx₂
  have hconst : 88 * (3 * η) = 264 * η := by ring
  simpa [hconst] using hmain

def UniformPoleCapOscillationBound
    (C : ℝ) (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H} {x y : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic μ p ≤ η →
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          C * η

lemma uniform_pole_cap_of_uniform_positive_near_infimum_local_with
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ}
    (hLocal :
      UniformPositiveNearInfimumLocalOscillationWith (H := H) C μ) :
    UniformPoleCapOscillationBound (H := H) (3 * C) μ := by
  intro η hη
  have hη3pos : 0 < 3 * η := by nlinarith
  rcases hLocal hη3pos with ⟨δ, hδ, hlocal⟩
  refine ⟨δ / 4, by positivity, ?_⟩
  intro u v p x y hu hv hp huv hup hvp hpη hx hy hdx hdy
  rcases exists_northOpenNonpolePolarSum_near_infimum
      (μ := μ) u v p hη with
    ⟨z, hz, hzpos, hρz, hzβlt⟩
  have hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η :=
    le_of_lt hzβlt
  have hδ4 : 0 < δ / 4 := by positivity
  rcases exists_positive_point_near_pole_nonpole_infimum_add_three_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
      hpη hz hρz hzpos hzβ hδ4 with
    ⟨a, ha, hapos, hρa, hadist, haβ⟩
  have hpη3 : frame_quadratic μ p ≤ 3 * η := by nlinarith
  have haβ3 :
      polarSumValue μ u v p a ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η := haβ
  have hxa :
      dist (coordPoint u v p x) (coordPoint u v p a) < δ := by
    have htri :=
      dist_triangle (coordPoint u v p x) p (coordPoint u v p a)
    have hpa : dist p (coordPoint u v p a) < δ / 4 := by
      simpa [dist_comm] using hadist
    nlinarith
  have hya :
      dist (coordPoint u v p y) (coordPoint u v p a) < δ := by
    have htri :=
      dist_triangle (coordPoint u v p y) p (coordPoint u v p a)
    have hpa : dist p (coordPoint u v p a) < δ / 4 := by
      simpa [dist_comm] using hadist
    nlinarith
  have hmain :=
    hlocal hu hv hp huv hup hvp hpη3 ha hapos hρa haβ3 hx hy hxa hya
  have hconst : C * (3 * η) = (3 * C) * η := by ring
  simpa [hconst] using hmain

lemma exists_endpoint_arcsin_pole_cap_radius
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ τ < Real.pi ∧
      ∀ {u v p : H} {z : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        0 < z.2.2 →
        Real.pi / 2 - τ < Real.arcsin z.2.2 →
        dist (coordPoint u v p z) p < ε := by
  let τ : ℝ := min (Real.pi / 4) (ε ^ 2 / 4)
  have hτpos : 0 < τ := by
    dsimp [τ]
    exact lt_min (by positivity) (by positivity)
  have hτpi : τ < Real.pi := by
    have hτle : τ ≤ Real.pi / 4 := min_le_left _ _
    nlinarith [Real.pi_pos]
  refine ⟨τ, hτpos, hτpi, ?_⟩
  intro u v p z hu hv hp huv hup hvp hz hzpos hend
  have hz_le_one : z.2.2 ≤ 1 := by
    nlinarith [sq_nonneg z.1, sq_nonneg z.2.1, sq_nonneg (z.2.2 - 1), hz]
  have hsin : Real.sin (Real.arcsin z.2.2) = z.2.2 := by
    exact Real.sin_arcsin (by linarith) hz_le_one
  have harc_le : Real.arcsin z.2.2 ≤ Real.pi / 2 :=
    Real.arcsin_le_pi_div_two _
  have hangle_nonneg : 0 ≤ Real.pi / 2 - Real.arcsin z.2.2 := by
    linarith
  have hangle_lt : Real.pi / 2 - Real.arcsin z.2.2 < τ := by
    linarith
  have hsin_lip :=
    Real.abs_sin_sub_sin_le (Real.pi / 2) (Real.arcsin z.2.2)
  have hone_sub_le :
      1 - z.2.2 ≤ Real.pi / 2 - Real.arcsin z.2.2 := by
    have hleft : |Real.sin (Real.pi / 2) - Real.sin (Real.arcsin z.2.2)| =
        1 - z.2.2 := by
      rw [Real.sin_pi_div_two, hsin]
      exact abs_of_nonneg (sub_nonneg.mpr hz_le_one)
    have hright : |Real.pi / 2 - Real.arcsin z.2.2| =
        Real.pi / 2 - Real.arcsin z.2.2 :=
      abs_of_nonneg hangle_nonneg
    calc
      1 - z.2.2 =
          |Real.sin (Real.pi / 2) - Real.sin (Real.arcsin z.2.2)| := hleft.symm
      _ ≤ |Real.pi / 2 - Real.arcsin z.2.2| := hsin_lip
      _ = Real.pi / 2 - Real.arcsin z.2.2 := hright
  have hone_sub_lt : 1 - z.2.2 < τ :=
    lt_of_le_of_lt hone_sub_le hangle_lt
  have hτle_eps : τ ≤ ε ^ 2 / 4 := min_le_right _ _
  have hdist_sq :
      dist (coordPoint u v p z) p ^ 2 < ε ^ 2 := by
    rw [dist_coordPoint_pole_sq_eq_two_mul_one_sub_third
      hu hv hp huv hup hvp hz]
    nlinarith
  exact (sq_lt_sq₀ dist_nonneg (le_of_lt hε)).1 hdist_sq

lemma exists_endpoint_arcsin_local_pole_cap_radius
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, ∃ δ : ℝ,
      0 < τ ∧ τ < Real.pi ∧ 0 < δ ∧
      ∀ {u v p : H} {z x : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        0 < z.2.2 →
        Real.pi / 2 - τ < Real.arcsin z.2.2 →
        dist (coordPoint u v p x) (coordPoint u v p z) < δ →
        dist (coordPoint u v p x) p < ε := by
  have hε2 : 0 < ε / 2 := by positivity
  rcases exists_endpoint_arcsin_pole_cap_radius (H := H) hε2 with
    ⟨τ, hτ0, hτpi, hpole⟩
  refine ⟨τ, ε / 2, hτ0, hτpi, hε2, ?_⟩
  intro u v p z x hu hv hp huv hup hvp hz _hx hzpos hend hdx
  have hzdist : dist (coordPoint u v p z) p < ε / 2 :=
    hpole hu hv hp huv hup hvp hz hzpos hend
  have htri := dist_triangle (coordPoint u v p x) (coordPoint u v p z) p
  nlinarith

lemma endpoint_positive_near_infimum_local_of_uniform_pole_cap_with
    (μ : FrameFunction H) {C : ℝ}
    (hPole : UniformPoleCapOscillationBound (H := H) C μ) :
    EndpointPositiveNearInfimumLocalOscillationWith (H := H) C μ := by
  intro η hη
  rcases hPole hη with ⟨ε, hε, hcap⟩
  have hε4 : 0 < ε / 4 := by positivity
  rcases exists_endpoint_arcsin_pole_cap_radius (H := H) hε4 with
    ⟨τ, hτ0, hτpi, hpole_near⟩
  refine ⟨τ, ε / 4, hτ0, hτpi, hε4, ?_⟩
  intro u v p z hu hv hp huv hup hvp hpη hz hzpos hρ hend _hzβ x y hx hy hdx hdy
  have hzdist :
      dist (coordPoint u v p z) p < ε / 4 :=
    hpole_near hu hv hp huv hup hvp hz hzpos hend
  have hxdist : dist (coordPoint u v p x) p < ε := by
    have htri := dist_triangle (coordPoint u v p x) (coordPoint u v p z) p
    nlinarith
  have hydist : dist (coordPoint u v p y) p < ε := by
    have htri := dist_triangle (coordPoint u v p y) (coordPoint u v p z) p
    nlinarith
  exact hcap hu hv hp huv hup hvp hpη hx hy hxdist hydist

lemma uniform_pole_cap_of_endpoint_with
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ} (hC : 0 ≤ C)
    (hEndpoint :
      EndpointPositiveNearInfimumLocalOscillationWith (H := H) C μ) :
    UniformPoleCapOscillationBound (H := H) (3 * (C + 88)) μ := by
  exact
    uniform_pole_cap_of_uniform_positive_near_infimum_local_with
      (H := H) hdim μ
      (uniform_positive_near_infimum_local_of_endpoint_with
        (H := H) hdim μ hC hEndpoint)

lemma targetBridgeCoord_third_neg
    (z : ℝ × ℝ × ℝ) :
    (targetBridgeCoord z).2.2 = -horizontalRadius z := by
  rfl

lemma horizontalRadius_pos_of_ne_zero
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    0 < horizontalRadius z := by
  have hnonneg : 0 ≤ horizontalRadius z := by
    dsimp [horizontalRadius]
    exact Real.sqrt_nonneg _
  exact lt_of_le_of_ne' hnonneg hρ

lemma horizontalRadius_sq_add_third_sq
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1) :
    horizontalRadius z ^ 2 + z.2.2 ^ 2 = 1 := by
  rw [horizontalRadius_sq z]
  linarith

lemma cos_arcsin_horizontalRadius_eq_third
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hzpos : 0 < z.2.2) :
    Real.cos (Real.arcsin (horizontalRadius z)) = z.2.2 := by
  rw [Real.cos_arcsin]
  have hsum := horizontalRadius_sq_add_third_sq (z := z) hz
  have hradicand_nonneg : 0 ≤ 1 - horizontalRadius z ^ 2 := by
    nlinarith [sq_nonneg z.2.2]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (le_of_lt hzpos)).1
  rw [Real.sq_sqrt hradicand_nonneg]
  nlinarith

lemma sin_arcsin_horizontalRadius_eq
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    Real.sin (Real.arcsin (horizontalRadius z)) = horizontalRadius z := by
  have hρ_nonneg : 0 ≤ horizontalRadius z := le_of_lt (horizontalRadius_pos_of_ne_zero hρ)
  have hsum := horizontalRadius_sq_add_third_sq (z := z) hz
  have hρ_sq_le : horizontalRadius z ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg z.2.2]
  have hρ_le_one : horizontalRadius z ≤ 1 :=
    (sq_le_one_iff₀ hρ_nonneg).mp hρ_sq_le
  exact Real.sin_arcsin (by linarith) hρ_le_one

lemma gleasonPsiSwap_signed_low_bridge_zero
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2) :
    Thm25.gleasonPsiSwap (Real.arcsin (horizontalRadius z))
      0 z.2.2 (horizontalRadius z) = 0 := by
  have hsin := sin_arcsin_horizontalRadius_eq (z := z) hz hρ
  have hcos := cos_arcsin_horizontalRadius_eq_third (z := z) hz hzpos
  unfold Thm25.gleasonPsiSwap Thm25.gleasonPsi
  rw [hsin, hcos]
  ring

lemma polarSumValue_signed_low_bridge_le_northMeridian_add_two_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2) :
    polarSumValue μ u v p (0, (-z.2.2, horizontalRadius z)) ≤
      polarSumValue μ (-u) (-v) p
        (northMeridianCoord (Real.arcsin (horizontalRadius z))) + 2 * η := by
  have hu' : ‖-u‖ = 1 := by simpa using hu
  have hv' : ‖-v‖ = 1 := by simpa using hv
  have huv' : inner (𝕜 := ℂ) (-u) (-v) = 0 := by simpa using huv
  have hup' : inner (𝕜 := ℂ) (-u) p = 0 := by simpa using hup
  have hvp' : inner (𝕜 := ℂ) (-v) p = 0 := by simpa using hvp
  have hy :
      (0 : ℝ) ^ 2 + z.2.2 ^ 2 + horizontalRadius z ^ 2 = 1 := by
    have hsum := horizontalRadius_sq_add_third_sq (z := z) hz
    nlinarith
  have hρy : horizontalRadius (0, (z.2.2, horizontalRadius z)) ≠ 0 := by
    dsimp [horizontalRadius]
    rw [zero_pow (by norm_num : (2 : Nat) ≠ 0), zero_add, Real.sqrt_sq_eq_abs]
    exact abs_ne_zero.mpr (ne_of_gt hzpos)
  have hψ :
      Thm25.gleasonPsiSwap (Real.arcsin (horizontalRadius z))
        (0 : ℝ) z.2.2 (horizontalRadius z) = 0 :=
    gleasonPsiSwap_signed_low_bridge_zero (z := z) hz hρ hzpos
  have hmain :=
    polarSumValue_le_northMeridian_of_gleasonPsiSwap_zero_add_two_eta
      (hdim := hdim) (μ := μ) hu' hv' hp huv' hup' hvp' hη hy hρy hψ
  simpa [polarSumValue_neg_neg_frame] using hmain

lemma neg_targetBridgeCoord_third_pos
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    0 < (-(targetBridgeCoord z)).2.2 := by
  simp [targetBridgeCoord, horizontalRadius_pos_of_ne_zero hρ]

lemma horizontalRadius_neg_targetBridgeCoord_ne_zero
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2) :
    horizontalRadius (-(targetBridgeCoord z)) ≠ 0 := by
  have hsq :
      (-(targetBridgeCoord z)).1 ^ 2 +
        (-(targetBridgeCoord z)).2.1 ^ 2 +
          (-(targetBridgeCoord z)).2.2 ^ 2 = 1 := by
    simpa using targetBridgeCoord_sq_sum hz hρ
  exact horizontalRadius_ne_zero_of_sq_sum_of_pos_of_thirdCoord_lt_one hsq
    (neg_targetBridgeCoord_third_pos hρ)
    (by
      have hρsq := horizontalRadius_sq z
      have hthird :
          (-(targetBridgeCoord z)).2.2 = horizontalRadius z := by
        simp [targetBridgeCoord]
      have hz3sq_pos : 0 < z.2.2 ^ 2 := by positivity
      have hρsq_lt_one : horizontalRadius z ^ 2 < 1 := by
        nlinarith
      have hρpos := horizontalRadius_pos_of_ne_zero hρ
      rw [hthird]
      nlinarith)

lemma polarSumValue_targetBridgeCoord_ge_nonpole_infimum
    (μ : FrameFunction H) {u v p : H}
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2) :
    sInf (northOpenNonpolePolarSumSet μ u v p) ≤
      polarSumValue μ u v p (targetBridgeCoord z) := by
  have hneg_sq :
      (-(targetBridgeCoord z)).1 ^ 2 +
        (-(targetBridgeCoord z)).2.1 ^ 2 +
          (-(targetBridgeCoord z)).2.2 ^ 2 = 1 := by
    simpa using targetBridgeCoord_sq_sum hz hρ
  have hneg_pos : 0 < (-(targetBridgeCoord z)).2.2 :=
    neg_targetBridgeCoord_third_pos hρ
  have hneg_rho : horizontalRadius (-(targetBridgeCoord z)) ≠ 0 :=
    horizontalRadius_neg_targetBridgeCoord_ne_zero hz hρ hzpos
  have hβ :
      sInf (northOpenNonpolePolarSumSet μ u v p) ≤
        polarSumValue μ u v p (-(targetBridgeCoord z)) := by
    exact csInf_le
      (northOpenNonpolePolarSumSet_bddBelow μ u v p)
      ⟨-(targetBridgeCoord z), hneg_sq, hneg_pos, hneg_rho, rfl⟩
  simpa [polarSumValue_neg_coord] using hβ

lemma targetBridgeCoord_eq_meridianFrameReparam_bridge
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    targetBridgeCoord z =
      meridianFrameReparam z (0, (z.2.2, -horizontalRadius z)) := by
  rw [meridianFrameReparam_explicit hρ]
  ext <;> simp [targetBridgeCoord]

lemma polarSumValue_targetBridgeCoord_eq_rotated_bridge
    (μ : FrameFunction H) (u v p : H)
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    polarSumValue μ u v p (targetBridgeCoord z) =
      polarSumValue μ
        (coordPoint u v p (-targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z))
        p (0, (z.2.2, -horizontalRadius z)) := by
  rw [polarSumValue_meridianFrameReparam
    (μ := μ) (u := u) (v := v) (p := p) (z := z)
    (y := (0, (z.2.2, -horizontalRadius z))) hρ]
  rw [← targetBridgeCoord_eq_meridianFrameReparam_bridge (z := z) hρ]

lemma polarSumValue_targetBridgeCoord_eq_rotated_positive_low
    (μ : FrameFunction H) (u v p : H)
    {z : ℝ × ℝ × ℝ} (hρ : horizontalRadius z ≠ 0) :
    polarSumValue μ u v p (targetBridgeCoord z) =
      polarSumValue μ
        (coordPoint u v p (-targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z))
        p (0, (-z.2.2, horizontalRadius z)) := by
  rw [polarSumValue_targetBridgeCoord_eq_rotated_bridge
    (μ := μ) (u := u) (v := v) (p := p) hρ]
  simpa using
    (polarSumValue_neg_coord μ
      (coordPoint u v p (-targetPoleCoord z))
      (coordPoint u v p (horizontalUnitCoord z))
      p (0, (z.2.2, -horizontalRadius z))).symm

lemma polarSumValue_lowHorizontalMeridianCoord_le_high_add_targetBridge_slack
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    polarSumValue μ u v p (lowHorizontalMeridianCoord z) ≤
      polarSumValue μ u v p z +
        (polarSumValue μ u v p (targetBridgeCoord z) -
          sInf (northOpenNonpolePolarSumSet μ u v p)) := by
  have hlow_sq :
      (lowHorizontalMeridianCoord z).1 ^ 2 +
        (lowHorizontalMeridianCoord z).2.1 ^ 2 +
          (lowHorizontalMeridianCoord z).2.2 ^ 2 = 1 :=
    lowHorizontalMeridianCoord_sq_sum hρ
  have hlow_rho : horizontalRadius (lowHorizontalMeridianCoord z) ≠ 0 :=
    lowHorizontalMeridianCoord_horizontalRadius_ne_zero hρ
  have hlow_pos : 0 < (lowHorizontalMeridianCoord z).2.2 :=
    lowHorizontalMeridianCoord_pos hρ
  have htarget_low_lower :
      sInf (northOpenNonpolePolarSumSet μ u v p) ≤
        polarSumValue μ u v p
          (targetBridgeCoord (lowHorizontalMeridianCoord z)) :=
    polarSumValue_targetBridgeCoord_ge_nonpole_infimum
      (μ := μ) hlow_sq hlow_rho hlow_pos
  have hid :=
    polarSumValue_lowHorizontalMeridianCoord_sub_eq_targetBridge_sub
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hz hρ
  linarith

lemma polarSumValue_lowHorizontalMeridianCoord_near_infimum_of_targetBridge_near
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η C : ℝ}
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hz_near :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η)
    (hbridge_near :
      polarSumValue μ u v p (targetBridgeCoord z) ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + C * η) :
    polarSumValue μ u v p (lowHorizontalMeridianCoord z) ≤
      sInf (northOpenNonpolePolarSumSet μ u v p) + (C + 1) * η := by
  have hmain :=
    polarSumValue_lowHorizontalMeridianCoord_le_high_add_targetBridge_slack
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hz hρ
  nlinarith

def EndpointTargetBridgeNearInfimumWith
    (C : ℝ) (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ τ : ℝ, 0 < τ ∧ τ < Real.pi ∧
      ∀ {u v p : H} {z : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic μ p ≤ η →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        0 < z.2.2 →
        horizontalRadius z ≠ 0 →
        Real.pi / 2 - τ < Real.arcsin z.2.2 →
        polarSumValue μ u v p z ≤
          sInf (northOpenNonpolePolarSumSet μ u v p) + η →
        polarSumValue μ u v p (targetBridgeCoord z) ≤
          sInf (northOpenNonpolePolarSumSet μ u v p) + C * η

def EndpointTraceNearInfimumWith
    (C : ℝ) (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ τ : ℝ, 0 < τ ∧ τ < Real.pi ∧
      ∀ {u v p : H} {z : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic μ p ≤ η →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        0 < z.2.2 →
        horizontalRadius z ≠ 0 →
        Real.pi / 2 - τ < Real.arcsin z.2.2 →
        polarSumValue μ u v p z ≤
          sInf (northOpenNonpolePolarSumSet μ u v p) + η →
        coordTraceValue μ u v p ≤
          2 * sInf (northOpenNonpolePolarSumSet μ u v p) + C * η

lemma endpoint_targetBridge_near_of_trace_near
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ}
    (hTrace : EndpointTraceNearInfimumWith (H := H) C μ) :
    EndpointTargetBridgeNearInfimumWith (H := H) (C + 1) μ := by
  intro η hη
  rcases hTrace hη with ⟨τ, hτ0, hτpi, htrace⟩
  refine ⟨τ, hτ0, hτpi, ?_⟩
  intro u v p z hu hv hp huv hup hvp hpη hz hzpos hρ hend hzβ
  have htrace_bound :
      coordTraceValue μ u v p ≤
        2 * sInf (northOpenNonpolePolarSumSet μ u v p) + C * η :=
    htrace hu hv hp huv hup hvp hpη hz hzpos hρ hend hzβ
  have hz_lower :
      sInf (northOpenNonpolePolarSumSet μ u v p) ≤
        polarSumValue μ u v p z := by
    exact csInf_le
      (northOpenNonpolePolarSumSet_bddBelow μ u v p)
      ⟨z, hz, hzpos, hρ, rfl⟩
  have hid :=
    polarSumValue_add_targetBridgeCoord_eq_trace_add_p
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hz hρ
  nlinarith

lemma endpoint_positive_near_infimum_local_of_targetBridge_near
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ} (hC : 0 ≤ C)
    (hTB : EndpointTargetBridgeNearInfimumWith (H := H) C μ) :
    EndpointPositiveNearInfimumLocalOscillationWith (H := H) (22 * (C + 1)) μ := by
  intro η hη
  have hηlow : 0 < (C + 1) * η := by nlinarith
  rcases exists_uniform_pole_cap_oscillation_of_low_meridian_near_nonpole_north_infimum
      (H := H) hdim hηlow with
    ⟨ε, hε, hlowcap⟩
  rcases hTB hη with ⟨τTB, hτTB0, hτTBpi, htarget⟩
  rcases exists_endpoint_arcsin_local_pole_cap_radius (H := H) hε with
    ⟨τG, δ, hτG0, hτGpi, hδ, hgeom⟩
  refine ⟨min τTB τG, δ, lt_min hτTB0 hτG0, ?_, hδ, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) hτTBpi
  intro u v p z hu hv hp huv hup hvp hpη hz hzpos hρ hend hzβ x y hx hy hdx hdy
  have hendTB : Real.pi / 2 - τTB < Real.arcsin z.2.2 := by
    have hle : min τTB τG ≤ τTB := min_le_left _ _
    linarith
  have hendG : Real.pi / 2 - τG < Real.arcsin z.2.2 := by
    have hle : min τTB τG ≤ τG := min_le_right _ _
    linarith
  have hbridge_near :
      polarSumValue μ u v p (targetBridgeCoord z) ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + C * η :=
    htarget hu hv hp huv hup hvp hpη hz hzpos hρ hendTB hzβ
  have hlow_near :
      polarSumValue μ u v p (lowHorizontalMeridianCoord z) ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + (C + 1) * η := by
    exact
      polarSumValue_lowHorizontalMeridianCoord_near_infimum_of_targetBridge_near
        (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hz hρ hzβ hbridge_near
  have hdx_pole : dist (coordPoint u v p x) p < ε :=
    hgeom hu hv hp huv hup hvp hz hx hzpos hendG hdx
  have hdy_pole : dist (coordPoint u v p y) p < ε :=
    hgeom hu hv hp huv hup hvp hz hy hzpos hendG hdy
  have hpηlow : frame_quadratic μ p ≤ (C + 1) * η := by
    have hp_nonneg := frame_quadratic_nonneg μ p
    nlinarith
  have hmain :=
    hlowcap μ hu hv hp huv hup hvp hpηlow hz hρ hlow_near hx hy hdx_pole hdy_pole
  have hconst : 22 * ((C + 1) * η) = (22 * (C + 1)) * η := by ring
  simpa [hconst] using hmain

lemma endpoint_positive_near_infimum_local_of_trace_near
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ} (hC : 0 ≤ C)
    (hTrace : EndpointTraceNearInfimumWith (H := H) C μ) :
    EndpointPositiveNearInfimumLocalOscillationWith (H := H) (22 * (C + 2)) μ := by
  have hTB :
      EndpointTargetBridgeNearInfimumWith (H := H) (C + 1) μ :=
    endpoint_targetBridge_near_of_trace_near (H := H) hdim μ hTrace
  have hC1 : 0 ≤ C + 1 := by nlinarith
  have hlocal :
      EndpointPositiveNearInfimumLocalOscillationWith
        (H := H) (22 * ((C + 1) + 1)) μ :=
    endpoint_positive_near_infimum_local_of_targetBridge_near
      (H := H) hdim μ (C := C + 1) hC1 hTB
  have hconst : 22 * ((C + 1) + 1) = 22 * (C + 2) := by ring
  intro η hη
  simpa [hconst] using hlocal (η := η) hη

lemma uniform_pole_cap_of_trace_near_with
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ} (hC : 0 ≤ C)
    (hTrace : EndpointTraceNearInfimumWith (H := H) C μ) :
    UniformPoleCapOscillationBound (H := H)
      (3 * (22 * (C + 2) + 88)) μ := by
  have hEndpoint :
      EndpointPositiveNearInfimumLocalOscillationWith
        (H := H) (22 * (C + 2)) μ :=
    endpoint_positive_near_infimum_local_of_trace_near
      (H := H) hdim μ hC hTrace
  have hCend : 0 ≤ 22 * (C + 2) := by nlinarith
  intro η hη
  exact
    uniform_pole_cap_of_endpoint_with
      (H := H) hdim μ hCend hEndpoint (η := η) hη

def EndpointRotatedTargetBridgeNearInfimumWith
    (C : ℝ) (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ τ : ℝ, 0 < τ ∧ τ < Real.pi ∧
      ∀ {u v p : H} {z : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic μ p ≤ η →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        0 < z.2.2 →
        horizontalRadius z ≠ 0 →
        Real.pi / 2 - τ < Real.arcsin z.2.2 →
        polarSumValue μ u v p z ≤
          sInf (northOpenNonpolePolarSumSet μ u v p) + η →
        polarSumValue μ
            (coordPoint u v p (-targetPoleCoord z))
            (coordPoint u v p (horizontalUnitCoord z))
            p (0, (-z.2.2, horizontalRadius z)) ≤
          sInf (northOpenNonpolePolarSumSet μ
            (coordPoint u v p (-targetPoleCoord z))
            (coordPoint u v p (horizontalUnitCoord z))
            p) + C * η

lemma endpoint_rotated_targetBridge_near_of_trace_near
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ}
    (hTrace : EndpointTraceNearInfimumWith (H := H) C μ) :
    EndpointRotatedTargetBridgeNearInfimumWith (H := H) (C + 1) μ := by
  have hTB :
      EndpointTargetBridgeNearInfimumWith (H := H) (C + 1) μ :=
    endpoint_targetBridge_near_of_trace_near (H := H) hdim μ hTrace
  intro η hη
  rcases hTB hη with ⟨τ, hτ0, hτpi, htarget⟩
  refine ⟨τ, hτ0, hτpi, ?_⟩
  intro u v p z hu hv hp huv hup hvp hpη hz hzpos hρ hend hzβ
  have htarget_bound :
      polarSumValue μ u v p (targetBridgeCoord z) ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + (C + 1) * η :=
    htarget hu hv hp huv hup hvp hpη hz hzpos hρ hend hzβ
  have hband :
      sInf (northOpenNonpolePolarSumSet μ u v p) ≤
          sInf (northOpenNonpolePolarSumSet μ
            (coordPoint u v p (-targetPoleCoord z))
            (coordPoint u v p (horizontalUnitCoord z))
            p) ∧
        sInf (northOpenNonpolePolarSumSet μ
            (coordPoint u v p (-targetPoleCoord z))
            (coordPoint u v p (horizontalUnitCoord z))
            p) ≤
          sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η :=
    rotated_nonpole_infimum_band
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hpη hz hρ hzpos hzβ
  have htarget_eq :
      polarSumValue μ u v p (targetBridgeCoord z) =
        polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p (0, (-z.2.2, horizontalRadius z)) :=
    polarSumValue_targetBridgeCoord_eq_rotated_positive_low
      (μ := μ) u v p hρ
  rw [← htarget_eq]
  nlinarith

lemma endpoint_targetBridge_near_of_rotated_targetBridge_near
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ}
    (hRot :
      EndpointRotatedTargetBridgeNearInfimumWith (H := H) C μ) :
    EndpointTargetBridgeNearInfimumWith (H := H) (C + 3) μ := by
  intro η hη
  rcases hRot hη with ⟨τ, hτ0, hτpi, hrot⟩
  refine ⟨τ, hτ0, hτpi, ?_⟩
  intro u v p z hu hv hp huv hup hvp hpη hz hzpos hρ hend hzβ
  have hrot_bound :
      polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p (0, (-z.2.2, horizontalRadius z)) ≤
        sInf (northOpenNonpolePolarSumSet μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p) + C * η :=
    hrot hu hv hp huv hup hvp hpη hz hzpos hρ hend hzβ
  have hband :
      sInf (northOpenNonpolePolarSumSet μ u v p) ≤
          sInf (northOpenNonpolePolarSumSet μ
            (coordPoint u v p (-targetPoleCoord z))
            (coordPoint u v p (horizontalUnitCoord z))
            p) ∧
        sInf (northOpenNonpolePolarSumSet μ
            (coordPoint u v p (-targetPoleCoord z))
            (coordPoint u v p (horizontalUnitCoord z))
            p) ≤
          sInf (northOpenNonpolePolarSumSet μ u v p) + 3 * η :=
    rotated_nonpole_infimum_band
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hpη hz hρ hzpos hzβ
  have htarget_eq :
      polarSumValue μ u v p (targetBridgeCoord z) =
        polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p (0, (-z.2.2, horizontalRadius z)) :=
    polarSumValue_targetBridgeCoord_eq_rotated_positive_low
      (μ := μ) u v p hρ
  rw [htarget_eq]
  nlinarith

lemma endpoint_trace_near_of_rotated_targetBridge_near
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ}
    (hRot :
      EndpointRotatedTargetBridgeNearInfimumWith (H := H) C μ) :
    EndpointTraceNearInfimumWith (H := H) (C + 4) μ := by
  have hTB :
      EndpointTargetBridgeNearInfimumWith (H := H) (C + 3) μ :=
    endpoint_targetBridge_near_of_rotated_targetBridge_near
      (H := H) hdim μ hRot
  intro η hη
  rcases hTB hη with ⟨τ, hτ0, hτpi, htarget⟩
  refine ⟨τ, hτ0, hτpi, ?_⟩
  intro u v p z hu hv hp huv hup hvp hpη hz hzpos hρ hend hzβ
  have htarget_bound :
      polarSumValue μ u v p (targetBridgeCoord z) ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + (C + 3) * η :=
    htarget hu hv hp huv hup hvp hpη hz hzpos hρ hend hzβ
  have hquad_nonneg : 0 ≤ frame_quadratic μ p :=
    frame_quadratic_nonneg μ p
  have hid :=
    polarSumValue_add_targetBridgeCoord_eq_trace_add_p
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hz hρ
  nlinarith

lemma endpoint_positive_near_infimum_local_of_rotated_targetBridge_near
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ} (hC : 0 ≤ C)
    (hRot :
      EndpointRotatedTargetBridgeNearInfimumWith (H := H) C μ) :
    EndpointPositiveNearInfimumLocalOscillationWith
      (H := H) (22 * (C + 4)) μ := by
  have hTB :
      EndpointTargetBridgeNearInfimumWith (H := H) (C + 3) μ :=
    endpoint_targetBridge_near_of_rotated_targetBridge_near
      (H := H) hdim μ hRot
  have hC3 : 0 ≤ C + 3 := by nlinarith
  have hlocal :
      EndpointPositiveNearInfimumLocalOscillationWith
        (H := H) (22 * ((C + 3) + 1)) μ :=
    endpoint_positive_near_infimum_local_of_targetBridge_near
      (H := H) hdim μ (C := C + 3) hC3 hTB
  have hconst : 22 * ((C + 3) + 1) = 22 * (C + 4) := by ring
  intro η hη
  simpa [hconst] using hlocal (η := η) hη

lemma uniform_pole_cap_of_rotated_targetBridge_near_with
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ} (hC : 0 ≤ C)
    (hRot :
      EndpointRotatedTargetBridgeNearInfimumWith (H := H) C μ) :
    UniformPoleCapOscillationBound (H := H)
      (3 * (22 * (C + 4) + 88)) μ := by
  have hEndpoint :
      EndpointPositiveNearInfimumLocalOscillationWith
        (H := H) (22 * (C + 4)) μ :=
    endpoint_positive_near_infimum_local_of_rotated_targetBridge_near
      (H := H) hdim μ hC hRot
  have hCend : 0 ≤ 22 * (C + 4) := by nlinarith
  intro η hη
  exact
    uniform_pole_cap_of_endpoint_with
      (H := H) hdim μ hCend hEndpoint (η := η) hη

lemma exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_nonpole_north_infimum_of_positive_point
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p x)
            p < δ →
        dist
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p y)
            p < δ →
        |frame_quadratic μ
            (coordPoint
              (coordPoint u v p (-targetPoleCoord z))
              (coordPoint u v p (horizontalUnitCoord z))
              p x) -
            frame_quadratic μ
              (coordPoint
                (coordPoint u v p (-targetPoleCoord z))
                (coordPoint u v p (horizontalUnitCoord z))
                p y)| ≤
          22 * η := by
  let β : ℝ := sInf (northOpenNonpolePolarSumSet μ u v p)
  have hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1 →
        0 < w.2.2 →
        horizontalRadius w ≠ 0 →
        β ≤ polarSumValue μ u v p w := by
    intro w hw hwpos hρw
    dsimp [β]
    exact csInf_le
      (northOpenNonpolePolarSumSet_bddBelow μ u v p)
      ⟨w, hw, hwpos, hρw, rfl⟩
  have hzβ' : polarSumValue μ u v p z ≤ β + η := by
    simpa [β] using hzβ
  exact exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_infimum_of_positive_point_on_north
    (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hβ hη hz hρ hzpos hzβ'

lemma exists_local_oscillation_neighborhood_of_point_near_nonpole_north_infimum_of_positive_point
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    {z a : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η)
    (ha : a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 = 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) (coordPoint u v p a) < δ →
        dist (coordPoint u v p y) (coordPoint u v p a) < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          88 * η := by
  let w : H := coordPoint u v p (horizontalUnitCoord z)
  let u' : H := coordPoint u v p (-targetPoleCoord z)
  have hwNorm : ‖w‖ = 1 := by
    dsimp [w]
    exact coordPoint_norm hu hv hp huv hup hvp (horizontalUnitCoord_sq_sum hρ)
  have hu' : ‖u'‖ = 1 := by
    dsimp [u']
    exact coordPoint_norm hu hv hp huv hup hvp (by
      simpa [targetPoleCoord] using targetPoleCoord_sq_sum hρ)
  have hu'v' : inner (𝕜 := ℂ) u' w = 0 := by
    dsimp [u', w]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    have h0 : coordDot (-targetPoleCoord z) (horizontalUnitCoord z) = 0 := by
      have hbase : coordDot (targetPoleCoord z) (horizontalUnitCoord z) = 0 :=
        coordDot_targetPole_horizontalUnitCoord hρ
      have hbase' := congrArg Neg.neg hbase
      simpa [coordDot, mul_neg, neg_mul, mul_comm, add_comm, add_left_comm, add_assoc] using hbase'
    exact_mod_cast h0
  have hu'p : inner (𝕜 := ℂ) u' p = 0 := by
    dsimp [u']
    have hu'p' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot, poleCoord, targetPoleCoord]
    simpa [coordPoint_poleCoord u v p] using hu'p'
  have hwp : inner (𝕜 := ℂ) w p = 0 := by
    have hwp' :
        inner (𝕜 := ℂ)
          (coordPoint u v p (horizontalUnitCoord z))
          (coordPoint u v p poleCoord) = 0 := by
      rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
      simp [coordDot_pole_horizontalUnitCoord, coordDot_comm]
    simpa [w, coordPoint_poleCoord u v p] using hwp'
  rcases exists_local_oscillation_neighborhood_of_frame_quadratic_at_p_near_nonpole_north_infimum_of_positive_point
      (hdim := hdim) (μ := μ)
      (u := u) (v := v) (p := p)
      hu hv hp huv hup hvp hη hz hρ hzpos hzβ with
    ⟨ε, hε, hosc⟩
  let s : ℝ × ℝ × ℝ := meridianFrameCoords z a
  have hs :
      s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 = 1 := by
    dsimp [s]
    rw [meridianFrameCoords_eq_meridianFlip z a]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := a) ha hρ)
  have ha0 : 0 ≤ 22 * η := by
    have hpnonneg := frame_quadratic_nonneg μ p
    nlinarith
  rcases sphere_oscillation_bound_of_cap
      (hdim := hdim) (μ := μ)
      (u := u') (v := w) (p := p)
      hu' hwNorm hp hu'v' hu'p hwp
      ha0 hε hosc hs with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hdx hdy
  let tx : ℝ × ℝ × ℝ := meridianFrameCoords z x
  let ty : ℝ × ℝ × ℝ := meridianFrameCoords z y
  have htx :
      tx.1 ^ 2 + tx.2.1 ^ 2 + tx.2.2 ^ 2 = 1 := by
    dsimp [tx]
    rw [meridianFrameCoords_eq_meridianFlip z x]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := x) hx hρ)
  have hty :
      ty.1 ^ 2 + ty.2.1 ^ 2 + ty.2.2 ^ 2 = 1 := by
    dsimp [ty]
    rw [meridianFrameCoords_eq_meridianFlip z y]
    exact meridianFlip_sq_sum (equatorFrameCoords_sq_sum (z := z) (x := y) hy hρ)
  have htxPoint :
      coordPoint u' w p tx = coordPoint u v p x := by
    dsimp [tx, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z x)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z x) = x := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z x)]
      rw [meridianFrameCoords_eq_meridianFlip z x]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have htyPoint :
      coordPoint u' w p ty = coordPoint u v p y := by
    dsimp [ty, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z y)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z y) = y := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z y)]
      rw [meridianFrameCoords_eq_meridianFlip z y]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have hsPoint :
      coordPoint u' w p s = coordPoint u v p a := by
    dsimp [s, u', w]
    rw [coordPoint_meridianFrameReparam (u := u) (v := v) (p := p) (z := z)
      (y := meridianFrameCoords z a)]
    have hcoord :
        meridianFrameReparam z (meridianFrameCoords z a) = a := by
      rw [meridianFrameReparam_eq_equatorFrameReparam z (meridianFrameCoords z a)]
      rw [meridianFrameCoords_eq_meridianFlip z a]
      simp [meridianFlip, equatorFrameReparam_equatorFrameCoords, hρ]
    simpa [hcoord]
  have htxDist :
      dist (coordPoint u' w p tx) (coordPoint u' w p s) < δ := by
    simpa [htxPoint, hsPoint] using hdx
  have htyDist :
      dist (coordPoint u' w p ty) (coordPoint u' w p s) < δ := by
    simpa [htyPoint, hsPoint] using hdy
  have hmain :
      |frame_quadratic μ (coordPoint u' w p tx) -
          frame_quadratic μ (coordPoint u' w p ty)| ≤
        4 * (22 * η) := by
    exact hlocal htx hty htxDist htyDist
  have hmain' :
      |frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y)| ≤
        4 * (22 * η) := by
    simpa [htxPoint, htyPoint] using hmain
  have hfinal :
      |frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y)| ≤
        88 * η := by
    nlinarith
  exact hfinal

lemma exists_local_oscillation_neighborhood_of_point_of_nonpole_north_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hηpos : 0 < η)
    (hη : frame_quadratic μ p ≤ η)
    {a : ℝ × ℝ × ℝ}
    (ha : a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 = 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) (coordPoint u v p a) < δ →
        dist (coordPoint u v p y) (coordPoint u v p a) < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          88 * η := by
  rcases exists_northOpenNonpolePolarSum_near_infimum
      (μ := μ) (u := u) (v := v) (p := p) hηpos with
    ⟨z, hz, hzpos, hρ, hzβ⟩
  exact exists_local_oscillation_neighborhood_of_point_near_nonpole_north_infimum_of_positive_point
    (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos (le_of_lt hzβ) ha

lemma polarSumValue_rotated_northMeridian_le_nonpole_infimum_add_five_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η θ : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    (hθpi : θ < Real.pi / 2)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hφθ : Real.arcsin z.2.2 < θ)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    polarSumValue μ
        (coordPoint u v p (-targetPoleCoord z))
        (coordPoint u v p (horizontalUnitCoord z))
        p (northMeridianCoord θ) ≤
      sInf (northOpenNonpolePolarSumSet μ u v p) + 5 * η := by
  have hstep :=
    polarSumValue_rotated_northMeridian_le_positive_point_add_four_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hθpi hz hρ hzpos hφθ
  linarith

lemma polarSumValue_rotated_northMeridian_band_above_nonpole_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η θ : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hφθ : Real.arcsin z.2.2 < θ)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    sInf (northOpenNonpolePolarSumSet μ u v p) ≤
        polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p (northMeridianCoord θ) ∧
      polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p (northMeridianCoord θ) ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + 5 * η := by
  have hupper :=
    polarSumValue_rotated_northMeridian_le_nonpole_infimum_add_five_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hθpi hz hρ hzpos hφθ hzβ
  have htheta_sq :
      (northMeridianCoord θ).1 ^ 2 +
          (northMeridianCoord θ).2.1 ^ 2 +
          (northMeridianCoord θ).2.2 ^ 2 = 1 := by
    simp [northMeridianCoord]
  have htheta_pos : 0 < (northMeridianCoord θ).2.2 := by
    have hθltπ : θ < Real.pi := by nlinarith [Real.pi_pos]
    simpa [northMeridianCoord] using Real.sin_pos_of_pos_of_lt_pi hθ0 hθltπ
  have htheta_lt_one : (northMeridianCoord θ).2.2 < 1 := by
    have hθneg : -(Real.pi / 2) < θ := by nlinarith [hθ0, Real.pi_pos]
    have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨hθneg, hθpi⟩
    have hcos_sq_pos : 0 < Real.cos θ ^ 2 := by positivity
    have hsum := Real.sin_sq_add_cos_sq θ
    simpa [northMeridianCoord] using (by nlinarith : Real.sin θ < 1)
  have htheta_rho :
      horizontalRadius (northMeridianCoord θ) ≠ 0 :=
    horizontalRadius_ne_zero_of_sq_sum_of_pos_of_thirdCoord_lt_one
      htheta_sq htheta_pos htheta_lt_one
  have hlow :
      sInf (northOpenNonpolePolarSumSet μ u v p) ≤
        polarSumValue μ
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p (northMeridianCoord θ) := by
    let a : ℝ × ℝ × ℝ := northMeridianCoord θ
    have ha' :
        (meridianFrameReparam z a).1 ^ 2 +
          (meridianFrameReparam z a).2.1 ^ 2 +
            (meridianFrameReparam z a).2.2 ^ 2 = 1 := by
      exact meridianFrameReparam_sq_sum (by simpa [a] using htheta_sq) hρ
    have hapos' : 0 < (meridianFrameReparam z a).2.2 := by
      simpa [a, meridianFrameReparam_explicit hρ] using htheta_pos
    have halt' : (meridianFrameReparam z a).2.2 < 1 := by
      simpa [a, meridianFrameReparam_explicit hρ] using htheta_lt_one
    have hρa' : horizontalRadius (meridianFrameReparam z a) ≠ 0 :=
      horizontalRadius_ne_zero_of_sq_sum_of_pos_of_thirdCoord_lt_one ha' hapos' halt'
    have hβle :
        sInf (northOpenNonpolePolarSumSet μ u v p) ≤
          polarSumValue μ u v p (meridianFrameReparam z a) := by
      exact csInf_le
        (northOpenNonpolePolarSumSet_bddBelow μ u v p)
        ⟨meridianFrameReparam z a, ha', hapos', hρa', rfl⟩
    simpa [a, polarSumValue_meridianFrameReparam (μ := μ) (u := u) (v := v) (p := p)
      (z := z) (y := northMeridianCoord θ) hρ] using hβle
  exact ⟨hlow, hupper⟩

lemma frame_quadratic_rotated_northMeridian_le_nonpole_infimum_add_five_eta
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η θ : ℝ}
    (hη : frame_quadratic μ p ≤ η)
    (hθpi : θ < Real.pi / 2)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzpos : 0 < z.2.2)
    (hφθ : Real.arcsin z.2.2 < θ)
    (hzβ :
      polarSumValue μ u v p z ≤
        sInf (northOpenNonpolePolarSumSet μ u v p) + η) :
    frame_quadratic μ
        (coordPoint
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p (northMeridianCoord θ)) ≤
      sInf (northOpenNonpolePolarSumSet μ u v p) + 5 * η := by
  have hpolar :=
    polarSumValue_rotated_northMeridian_le_nonpole_infimum_add_five_eta
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hθpi
      hz hρ hzpos hφθ hzβ
  have hnonneg :
      0 ≤ frame_quadratic μ
        (coordPoint
          (coordPoint u v p (-targetPoleCoord z))
          (coordPoint u v p (horizontalUnitCoord z))
          p (polarQuarterTurnCoord (northMeridianCoord θ))) :=
    frame_quadratic_nonneg μ _
  unfold polarSumValue at hpolar
  linarith

lemma exists_pole_oscillation_neighborhood_of_nonpole_north_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hηpos : 0 < η)
    (hη : frame_quadratic μ p ≤ η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          88 * η := by
  rcases exists_local_oscillation_neighborhood_of_point_of_nonpole_north_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hηpos hη
      (a := poleCoord) (by norm_num [poleCoord]) with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hy hdx hdy
  exact hlocal hx hy
    (by simpa [coordPoint_poleCoord] using hdx)
    (by simpa [coordPoint_poleCoord] using hdy)

lemma exists_coordSphere_uniform_oscillation_neighborhood_of_nonpole_north_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hηpos : 0 < η)
    (hη : frame_quadratic μ p ≤ η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {a x y : ℝ × ℝ × ℝ},
        a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2 = 1 →
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) (coordPoint u v p a) < δ →
        dist (coordPoint u v p y) (coordPoint u v p a) < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          352 * η := by
  rcases exists_pole_oscillation_neighborhood_of_nonpole_north_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hηpos hη with
    ⟨ε, hε, hpole⟩
  have h88_nonneg : 0 ≤ 88 * η := by
    have hp_nonneg := frame_quadratic_nonneg μ p
    nlinarith
  rcases sphere_oscillation_bound_of_cap_uniform
      (hdim := hdim) (μ := μ) (a := 88 * η) (ε := ε) h88_nonneg hε with
    ⟨δ, hδ, hglobal⟩
  refine ⟨δ, hδ, ?_⟩
  intro a x y ha hx hy hdx hdy
  have hbound :
      |frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p y)| ≤
        4 * (88 * η) := by
    exact hglobal hu hv hp huv hup hvp hpole ha hx hy hdx hdy
  have hconst : 4 * (88 * η) = 352 * η := by ring
  simpa [hconst] using hbound

lemma horizontal_bridge_oscillation_of_pole_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η δ : ℝ}
    (hcap :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤ 88 * η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzdist : dist (coordPoint u v p z) p < δ) :
    |frame_quadratic μ (coordPoint u v p (horizontalUnitCoord z)) -
        frame_quadratic μ (coordPoint u v p (targetBridgeCoord z))| ≤ 88 * η := by
  have hdiff :
      frame_quadratic μ (coordPoint u v p (horizontalUnitCoord z)) -
          frame_quadratic μ (coordPoint u v p (targetBridgeCoord z)) =
        frame_quadratic μ (coordPoint u v p z) - frame_quadratic μ p := by
    exact frame_quadratic_horizontalUnit_sub_targetBridge
      (H := H) hdim μ hu hv hp huv hup hvp hz hρ
  have hpole : poleCoord.1 ^ 2 + poleCoord.2.1 ^ 2 + poleCoord.2.2 ^ 2 = 1 := by
    norm_num [poleCoord]
  have hpdist : dist (coordPoint u v p poleCoord) p < δ := by
    have hδpos : 0 < δ := lt_of_le_of_lt dist_nonneg hzdist
    simpa [coordPoint_poleCoord] using hδpos
  have hmain :
      |frame_quadratic μ (coordPoint u v p z) -
          frame_quadratic μ (coordPoint u v p poleCoord)| ≤ 88 * η := by
    exact hcap hz hpole hzdist hpdist
  simpa [hdiff, coordPoint_poleCoord] using hmain

lemma horizontal_bridge_upper_of_pole_cap_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η δ C : ℝ}
    (hcap :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤ C * η)
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0)
    (hzdist : dist (coordPoint u v p z) p < δ) :
    frame_quadratic μ (coordPoint u v p (horizontalUnitCoord z)) -
        frame_quadratic μ (coordPoint u v p (targetBridgeCoord z)) ≤ C * η := by
  have hdiff :
      frame_quadratic μ (coordPoint u v p (horizontalUnitCoord z)) -
          frame_quadratic μ (coordPoint u v p (targetBridgeCoord z)) =
        frame_quadratic μ (coordPoint u v p z) - frame_quadratic μ p := by
    exact frame_quadratic_horizontalUnit_sub_targetBridge
      (H := H) hdim μ hu hv hp huv hup hvp hz hρ
  have hpole : poleCoord.1 ^ 2 + poleCoord.2.1 ^ 2 + poleCoord.2.2 ^ 2 = 1 := by
    norm_num [poleCoord]
  have hpdist : dist (coordPoint u v p poleCoord) p < δ := by
    have hδpos : 0 < δ := lt_of_le_of_lt dist_nonneg hzdist
    simpa [coordPoint_poleCoord] using hδpos
  have hmain :
      |frame_quadratic μ (coordPoint u v p z) -
          frame_quadratic μ (coordPoint u v p poleCoord)| ≤ C * η := by
    exact hcap hz hpole hzdist hpdist
  have hupper :
      frame_quadratic μ (coordPoint u v p z) -
          frame_quadratic μ (coordPoint u v p poleCoord) ≤ C * η :=
    (abs_le.mp hmain).2
  simpa [hdiff, coordPoint_poleCoord] using hupper

lemma exists_horizontal_bridge_oscillation_neighborhood_of_nonpole_north_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hηpos : 0 < η)
    (hη : frame_quadratic μ p ≤ η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {z : ℝ × ℝ × ℝ},
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        horizontalRadius z ≠ 0 →
        dist (coordPoint u v p z) p < δ →
        |frame_quadratic μ (coordPoint u v p (horizontalUnitCoord z)) -
            frame_quadratic μ (coordPoint u v p (targetBridgeCoord z))| ≤ 88 * η := by
  rcases exists_pole_oscillation_neighborhood_of_nonpole_north_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hηpos hη with
    ⟨δ, hδ, hcap⟩
  refine ⟨δ, hδ, ?_⟩
  intro z hz hρ hzdist
  exact horizontal_bridge_oscillation_of_pole_cap
    (hdim := hdim) (μ := μ) hu hv hp huv hup hvp
    (η := η) (δ := δ) hcap hz hρ hzdist

lemma exists_positive_point_local_oscillation_of_nonpole_north_infimum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {η : ℝ}
    (hηpos : 0 < η)
    (hη : frame_quadratic μ p ≤ η) :
    ∃ z : ℝ × ℝ × ℝ, ∃ δ : ℝ,
      z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 ∧
      0 < z.2.2 ∧
      horizontalRadius z ≠ 0 ∧
      polarSumValue μ u v p z <
        sInf (northOpenNonpolePolarSumSet μ u v p) + η ∧
      0 < δ ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) (coordPoint u v p z) < δ →
        dist (coordPoint u v p y) (coordPoint u v p z) < δ →
        |frame_quadratic μ (coordPoint u v p x) -
            frame_quadratic μ (coordPoint u v p y)| ≤
          88 * η := by
  rcases exists_northOpenNonpolePolarSum_near_infimum
      (μ := μ) (u := u) (v := v) (p := p) hηpos with
    ⟨z, hz, hzpos, hρ, hzβ⟩
  rcases exists_local_oscillation_neighborhood_of_positive_point_near_nonpole_north_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hη hz hρ hzpos (le_of_lt hzβ) with
    ⟨δ, hδ, hlocal⟩
  exact ⟨z, δ, hz, hzpos, hρ, hzβ, hδ, hlocal⟩

lemma frame_quadratic_continuousOn_coordSphere_of_zero_at_p
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic μ p = 0) :
    ContinuousOn
      (fun x : ℝ × ℝ × ℝ => frame_quadratic μ (coordPoint u v p x))
      {x : ℝ × ℝ × ℝ | x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1} := by
  intro a ha
  refine (Metric.continuousWithinAt_iff).2 ?_
  intro ε hε
  let η : ℝ := ε / 176
  have hηpos : 0 < η := by
    dsimp [η]
    exact div_pos hε (by norm_num)
  have hη : frame_quadratic μ p ≤ η := by
    simpa [hp0] using (le_of_lt hηpos : 0 ≤ η)
  rcases exists_local_oscillation_neighborhood_of_point_of_nonpole_north_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hηpos hη ha with
    ⟨δH, hδH, hlocal⟩
  refine ⟨δH / 4, by positivity, ?_⟩
  intro x hx hxa
  have hxaH :
      dist (coordPoint u v p x) (coordPoint u v p a) < δH := by
    have hle := dist_coordPoint_le_three_mul_dist_coords hu hv hp x a
    have hlt : 3 * dist x a < δH := by
      nlinarith [hδH, hxa]
    exact lt_of_le_of_lt hle hlt
  have haa : dist (coordPoint u v p a) (coordPoint u v p a) < δH := by
    simpa using hδH
  have hbound :
      |frame_quadratic μ (coordPoint u v p x) -
          frame_quadratic μ (coordPoint u v p a)| ≤
        88 * η := by
    exact hlocal hx ha hxaH haa
  have hlt : 88 * η < ε := by
    dsimp [η]
    nlinarith
  have hdist :
      dist (frame_quadratic μ (coordPoint u v p x))
        (frame_quadratic μ (coordPoint u v p a)) ≤
        88 * η := by
    simpa [Real.dist_eq] using hbound
  exact lt_of_le_of_lt hdist hlt

lemma frame_quadratic_continuousOn_coordSphereImage_of_zero_at_p
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic μ p = 0) :
    ContinuousOn (fun x : H => frame_quadratic μ x) (coordSphereImage u v p) := by
  intro b hb
  rcases hb with ⟨a, ha, rfl⟩
  refine (Metric.continuousWithinAt_iff).2 ?_
  intro ε hε
  let η : ℝ := ε / 176
  have hηpos : 0 < η := by
    dsimp [η]
    exact div_pos hε (by norm_num)
  have hη : frame_quadratic μ p ≤ η := by
    simpa [hp0] using (le_of_lt hηpos : 0 ≤ η)
  rcases exists_local_oscillation_neighborhood_of_point_of_nonpole_north_infimum
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hηpos hη ha with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxb
  rcases hx with ⟨xcoord, hxcoord, rfl⟩
  have haa : dist (coordPoint u v p a) (coordPoint u v p a) < δ := by
    simpa using hδ
  have hbound :
      |frame_quadratic μ (coordPoint u v p xcoord) -
          frame_quadratic μ (coordPoint u v p a)| ≤
        88 * η := by
    exact hlocal hxcoord ha hxb haa
  have hlt : 88 * η < ε := by
    dsimp [η]
    nlinarith
  have hdist :
      dist (frame_quadratic μ (coordPoint u v p xcoord))
        (frame_quadratic μ (coordPoint u v p a)) ≤
        88 * η := by
    simpa [Real.dist_eq] using hbound
  exact lt_of_le_of_lt hdist hlt

end Thm28
