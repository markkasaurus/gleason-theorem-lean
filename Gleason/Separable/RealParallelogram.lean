import Gleason.Separable.RealLocalQuadratic

/-!
# The Global Parallelogram Identity over the Real Field

The local quadratic representation on real three-dimensional subspaces first
gives the parallelogram identity for orthogonal vectors. A common orthogonal
direction then removes the orthogonality restriction.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def realPairVec (x y : H) : Fin 2 → H
  | 0 => x
  | 1 => y

omit [CompleteSpace H] in
/-- In rank at least three, any two vectors have a nonzero common orthogonal
vector. -/
theorem exists_nonzero_common_orthogonal_real
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H) (x y : H) :
    ∃ w : H, w ≠ 0 ∧ inner ℝ w x = 0 ∧ inner ℝ w y = 0 := by
  let K : Submodule ℝ H := Submodule.span ℝ (Set.range (realPairVec x y))
  letI : FiniteDimensional ℝ K :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range (realPairVec x y))
  letI : CompleteSpace K := FiniteDimensional.complete ℝ K
  have hKrank : Module.rank ℝ K ≤ (2 : Cardinal) := by
    calc
      Module.rank ℝ K ≤ Cardinal.mk (Set.range (realPairVec x y)) := by
        exact rank_span_le _
      _ ≤ 2 := by
        simpa using (Cardinal.mk_range_le_lift (f := realPairVec x y))
  have hKlt : Module.rank ℝ K < Module.rank ℝ H := by
    have h23 : (2 : Cardinal) < 3 := by norm_num
    exact lt_of_le_of_lt hKrank (h23.trans_le hdim)
  obtain ⟨z, hz⟩ := K.exists_smul_notMem_of_rank_lt hKlt
  have hzK : z ∉ K := by
    simpa using hz (1 : ℝ) one_ne_zero
  let w : H := z - K.starProjection z
  have hwK : w ∈ Submodule.orthogonal K := by
    exact K.sub_starProjection_mem_orthogonal z
  have hxK : x ∈ K := by
    exact Submodule.subset_span ⟨0, rfl⟩
  have hyK : y ∈ K := by
    exact Submodule.subset_span ⟨1, rfl⟩
  have hwx : inner ℝ w x = 0 :=
    (K.mem_orthogonal' w).mp hwK x hxK
  have hwy : inner ℝ w y = 0 :=
    (K.mem_orthogonal' w).mp hwK y hyK
  have hw0 : w ≠ 0 := by
    intro hw
    apply hzK
    apply K.starProjection_eq_self_iff.mp
    exact (sub_eq_zero.mp hw).symm
  exact ⟨w, hw0, hwx, hwy⟩

theorem quadraticMap_real_parallelogram
    (Q : QuadraticMap ℝ RealSphereAmbient ℝ) (x y : RealSphereAmbient) :
    Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y := by
  rw [QuadraticMap.map_add Q x y]
  rw [show x - y = x + -y by rfl, QuadraticMap.map_add Q x (-y)]
  rw [Q.map_neg, Q.polar_neg_right]
  change Q x + Q y + QuadraticMap.polar Q x y +
      (Q x + Q y + -QuadraticMap.polar Q x y) =
    2 * Q x + 2 * Q y
  ring

namespace ProjectionMeasure

/-- Local quadraticity yields the parallelogram identity for orthogonal real
vectors. -/
theorem quadraticValue_orthogonal_parallelogram
    (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H)
    (x y : H) (hxy : inner ℝ x y = 0) :
    m.quadraticValue (x + y) + m.quadraticValue (x - y) =
      2 * m.quadraticValue x + 2 * m.quadraticValue y := by
  by_cases hx : x = 0
  · subst x
    have hneg := m.quadraticValue_smul (-1 : ℝ) y
    simp at hneg
    rw [zero_add, zero_sub, m.quadraticValue_zero, hneg]
    ring
  by_cases hy : y = 0
  · subst y
    simp
    ring
  let u : H := ‖x‖⁻¹ • x
  let v : H := ‖y‖⁻¹ • y
  have hu : ‖u‖ = 1 := by
    simpa [u] using norm_smul_inv_norm (𝕜 := ℝ) hx
  have hv : ‖v‖ = 1 := by
    simpa [v] using norm_smul_inv_norm (𝕜 := ℝ) hy
  have huv : inner ℝ u v = 0 := by
    simp [u, v, inner_smul_left, inner_smul_right, hxy]
  obtain ⟨w0, hw0, hw0u, hw0v⟩ :=
    exists_nonzero_common_orthogonal_real hdim u v
  let w : H := ‖w0‖⁻¹ • w0
  have hw : ‖w‖ = 1 := by
    simpa [w] using norm_smul_inv_norm (𝕜 := ℝ) hw0
  have huw : inner ℝ u w = 0 := by
    rw [real_inner_comm]
    simp [w, inner_smul_left, hw0u]
  have hvw : inner ℝ v w = 0 := by
    rw [real_inner_comm]
    simp [w, inner_smul_left, hw0v]
  let e : RealSphereAmbient →ₗᵢ[ℝ] H :=
    realTripleLinearIsometry u v w hu hv hw huv huw hvw
  obtain ⟨Q, hQ⟩ := m.exists_quadraticMap_on_realTripleIsometry e
  let a : RealSphereAmbient := ‖x‖ • sphereE1.1
  let b : RealSphereAmbient := ‖y‖ • sphereE2.1
  have heu : e sphereE1.1 = u := by
    exact realTripleLinearIsometry_apply_sphereE1 u v w hu hv hw huv huw hvw
  have hev : e sphereE2.1 = v := by
    exact realTripleLinearIsometry_apply_sphereE2 u v w hu hv hw huv huw hvw
  have hxu : ‖x‖ • u = x := by
    simp [u, smul_smul, hx]
  have hyv : ‖y‖ • v = y := by
    simp [v, smul_smul, hy]
  have hea : e a = x := by
    simp [a, e.map_smul, heu, hxu]
  have heb : e b = y := by
    simp [b, e.map_smul, hev, hyv]
  have hpar := quadraticMap_real_parallelogram Q a b
  simpa [← hQ, map_add, map_sub, hea, heb] using hpar

set_option maxHeartbeats 800000 in
/-- The homogeneous function associated with a real projection measure
satisfies the global parallelogram identity. -/
theorem quadraticValue_parallelogram_real
    (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H)
    (x y : H) :
    m.quadraticValue (x + y) + m.quadraticValue (x - y) =
      2 * m.quadraticValue x + 2 * m.quadraticValue y := by
  by_cases hy0 : y = 0
  · subst y
    simp
    ring
  obtain ⟨w, hw0, hwx, hwy⟩ :=
    exists_nonzero_common_orthogonal_real hdim x y
  have hxw : inner ℝ x w = 0 := by
    rw [real_inner_comm]
    exact hwx
  have hyw : inner ℝ y w = 0 := by
    rw [real_inner_comm]
    exact hwy
  let d : ℝ := inner ℝ w w
  have hd : d ≠ 0 := by
    intro h
    exact hw0 (inner_self_eq_zero.mp h)
  let s : ℝ := -inner ℝ x y / d
  have hs : s * d = -inner ℝ x y := by
    calc
      s * d = (-inner ℝ x y / d) * d := by rfl
      _ = (-inner ℝ x y) * (d⁻¹ * d) := by
        simp [div_eq_mul_inv, mul_assoc]
      _ = -inner ℝ x y := by rw [inv_mul_cancel₀ hd, mul_one]
  have hs0 : inner ℝ x y + s * d = 0 := by
    rw [hs]
    ring
  have horth1 : inner ℝ (x + w) (y + s • w) = 0 := by
    calc
      inner ℝ (x + w) (y + s • w) =
          inner ℝ x y + s * inner ℝ w w := by
        simp [inner_add_left, inner_add_right, inner_smul_right,
          hxw, hwy]
      _ = inner ℝ x y + s * d := by rfl
      _ = 0 := hs0
  have horth2 : inner ℝ (x - w) (y - s • w) = 0 := by
    calc
      inner ℝ (x - w) (y - s • w) =
          inner ℝ x y + s * inner ℝ w w := by
        simp [sub_eq_add_neg, inner_add_left, inner_add_right, inner_smul_right,
          hxw, hwy]
      _ = inner ℝ x y + s * d := by rfl
      _ = 0 := hs0
  let q : H → ℝ := m.quadraticValue
  let zw : H := w + s • w
  let tw : H := w - s • w
  have E1 := m.quadraticValue_orthogonal_parallelogram hdim
    (x + w) (y + s • w) horth1
  have E2 := m.quadraticValue_orthogonal_parallelogram hdim
    (x - w) (y - s • w) horth2
  have E1rw :
      q ((x + y) + zw) + q ((x - y) + tw) =
        2 * q (x + w) + 2 * q (y + s • w) := by
    simpa [q, zw, tw, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using E1
  have E2rw :
      q ((x + y) - zw) + q ((x - y) - tw) =
        2 * q (x - w) + 2 * q (y - s • w) := by
    simpa [q, zw, tw, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using E2
  have sumE :
      (q ((x + y) + zw) + q ((x + y) - zw)) +
          (q ((x - y) + tw) + q ((x - y) - tw)) =
        2 * (q (x + w) + q (x - w)) +
          2 * (q (y + s • w) + q (y - s • w)) := by
    linarith [E1rw, E2rw]
  have hxy_zw : inner ℝ (x + y) zw = 0 := by
    simp [zw, inner_add_left, inner_add_right, inner_smul_right, hxw, hyw]
  have hxm_tw : inner ℝ (x - y) tw = 0 := by
    simp [tw, sub_eq_add_neg, inner_add_left, inner_add_right,
      inner_smul_right, hxw, hyw]
  have Pxy :
      q ((x + y) + zw) + q ((x + y) - zw) =
        2 * q (x + y) + 2 * q zw := by
    simpa [q] using
      m.quadraticValue_orthogonal_parallelogram hdim (x + y) zw hxy_zw
  have Pxm :
      q ((x - y) + tw) + q ((x - y) - tw) =
        2 * q (x - y) + 2 * q tw := by
    simpa [q] using
      m.quadraticValue_orthogonal_parallelogram hdim (x - y) tw hxm_tw
  have HS0 :
      2 * (q (x + y) + q (x - y)) + 2 * (q zw + q tw) =
        2 * (q (x + w) + q (x - w)) +
          2 * (q (y + s • w) + q (y - s • w)) := by
    linarith [sumE, Pxy, Pxm]
  have Pxw : q (x + w) + q (x - w) = 2 * q x + 2 * q w := by
    simpa [q] using m.quadraticValue_orthogonal_parallelogram hdim x w hxw
  have Pyw :
      q (y + s • w) + q (y - s • w) =
        2 * q y + 2 * q (s • w) := by
    have hysw : inner ℝ y (s • w) = 0 := by
      simp [inner_smul_right, hyw]
    simpa [q] using
      m.quadraticValue_orthogonal_parallelogram hdim y (s • w) hysw
  have HS1 :
      2 * (q (x + y) + q (x - y)) + 2 * (q zw + q tw) =
        4 * q x + 4 * q y + 4 * q w + 4 * q (s • w) := by
    linarith [HS0, Pxw, Pyw]
  have qs : q (s • w) = s ^ 2 * q w := by
    simpa [q, sq_abs] using m.quadraticValue_smul s w
  have qzw : q zw = (1 + s) ^ 2 * q w := by
    have hzw : zw = (1 + s) • w := by
      simp [zw, add_smul]
    simpa [q, hzw, sq_abs] using m.quadraticValue_smul (1 + s) w
  have qtw : q tw = (1 - s) ^ 2 * q w := by
    have htw : tw = (1 - s) • w := by
      simpa [tw] using (sub_smul (1 : ℝ) s w).symm
    simpa [q, htw, sq_abs] using m.quadraticValue_smul (1 - s) w
  have hnorm : (1 + s) ^ 2 + (1 - s) ^ 2 = 2 + 2 * s ^ 2 := by ring
  have wcancel : 2 * (q zw + q tw) = 4 * q w + 4 * q (s • w) := by
    calc
      2 * (q zw + q tw) =
          2 * (((1 + s) ^ 2 + (1 - s) ^ 2) * q w) := by
        rw [qzw, qtw]
        ring
      _ = 2 * ((2 + 2 * s ^ 2) * q w) := by rw [hnorm]
      _ = 4 * q w + 4 * (s ^ 2 * q w) := by ring
      _ = 4 * q w + 4 * q (s • w) := by rw [qs]
  have HS2 :
      2 * (q (x + y) + q (x - y)) = 4 * q x + 4 * q y := by
    linarith [HS1, wcancel]
  have hfinal : q (x + y) + q (x - y) = 2 * q x + 2 * q y := by
    linarith [HS2]
  exact hfinal

end ProjectionMeasure

end ClassicalGleason.Separable
