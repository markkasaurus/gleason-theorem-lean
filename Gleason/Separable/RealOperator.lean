import Gleason.Separable.RealParallelogram

/-!
# The Representing Operator over the Real Field

Real polarization and the Riesz representation theorem turn the bounded
quadratic function into a bounded positive self-adjoint operator.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

structure IsBoundedRealQuadraticForm (q : H → ℝ) : Prop where
  sq_hom : ∀ (c : ℝ) (x : H), q (c • x) = c ^ 2 * q x
  parallelogram : ∀ x y : H,
    q (x + y) + q (x - y) = 2 * q x + 2 * q y
  bounded : ∃ C : ℝ, ∀ x : H, |q x| ≤ C * ‖x‖ ^ 2

namespace ProjectionMeasure

theorem quadraticValue_isBoundedRealQuadraticForm
    (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H) :
    IsBoundedRealQuadraticForm m.quadraticValue := by
  refine ⟨?_, m.quadraticValue_parallelogram_real hdim, ?_⟩
  · intro c x
    simpa [sq_abs] using m.quadraticValue_smul c x
  · exact ⟨m.μ 1, m.abs_quadraticValue_le⟩

end ProjectionMeasure

def realPolarization (q : H → ℝ) (x y : H) : ℝ :=
  (q (x + y) - q (x - y)) / 4

namespace IsBoundedRealQuadraticForm

variable {q : H → ℝ} (hq : IsBoundedRealQuadraticForm q)

include hq

omit [CompleteSpace H] in
theorem map_zero : q 0 = 0 := by
  have h := hq.1 0 (0 : H)
  simpa using h

omit [CompleteSpace H] in
theorem map_neg (x : H) : q (-x) = q x := by
  simpa [neg_one_smul] using hq.1 (-1) x

omit [CompleteSpace H] in
theorem map_sub_comm (a b : H) : q (a - b) = q (b - a) := by
  rw [show a - b = -(b - a) by abel, map_neg hq]

omit [CompleteSpace H] in
private theorem diff_add (x y z : H) :
    q (x + (y + z)) - q (x - (y + z)) =
      (q (x + y) - q (x - y)) + (q (x + z) - q (x - z)) := by
  let A : ℝ := q (x + (y + z))
  let E : ℝ := q (x - (y + z))
  let B : ℝ := q (x + y - z)
  let C : ℝ := q (x - y + z)
  let D : ℝ := q (x - y - z)
  have hDE : D = E := by
    have h : x - y - z = x - (y + z) := by abel
    simp [D, E, h]
  have p1 : q (x + (y + z)) + q (x + y - z) =
      2 * q (x + y) + 2 * q z := by
    simpa [add_assoc, sub_eq_add_neg, add_comm, add_left_comm] using
      hq.parallelogram (x + y) z
  have p2 : q (x - y + z) + q (x - y - z) =
      2 * q (x - y) + 2 * q z := by
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      hq.parallelogram (x - y) z
  have p3 : q (x + (y + z)) + q (x - y + z) =
      2 * q (x + z) + 2 * q y := by
    simpa [add_assoc, sub_eq_add_neg, add_comm, add_left_comm] using
      hq.parallelogram (x + z) y
  have p4 : q (x + y - z) + q (x - (y + z)) =
      2 * q (x - z) + 2 * q y := by
    simpa [add_assoc, sub_eq_add_neg, add_comm, add_left_comm] using
      hq.parallelogram (x - z) y
  have p2' : C + E = 2 * q (x - y) + 2 * q z := by
    simpa [C, D, E, hDE] using p2
  have p1' : A + B = 2 * q (x + y) + 2 * q z := by
    simpa [A, B] using p1
  have p3' : A + C = 2 * q (x + z) + 2 * q y := by
    simpa [A, C] using p3
  have p4' : B + E = 2 * q (x - z) + 2 * q y := by
    simpa [B, E] using p4
  have h1 : A + B - C - E = 2 * (q (x + y) - q (x - y)) := by
    linarith [p1', p2']
  have h2 : A + C - B - E = 2 * (q (x + z) - q (x - z)) := by
    linarith [p3', p4']
  have h : A - E =
      (q (x + y) - q (x - y)) + (q (x + z) - q (x - z)) := by
    linarith [h1, h2]
  simpa [A, E] using h

omit [CompleteSpace H] in
theorem realPolarization_add_right (x y z : H) :
    realPolarization q x (y + z) =
      realPolarization q x y + realPolarization q x z := by
  have h := diff_add hq x y z
  dsimp [realPolarization]
  linarith

omit [CompleteSpace H] in
theorem realPolarization_symm (x y : H) :
    realPolarization q x y = realPolarization q y x := by
  unfold realPolarization
  rw [add_comm]
  rw [map_sub_comm hq x y]

omit [CompleteSpace H] in
theorem realPolarization_add_left (x y z : H) :
    realPolarization q (x + y) z =
      realPolarization q x z + realPolarization q y z := by
  rw [realPolarization_symm hq (x + y) z,
    realPolarization_add_right hq z x y,
    realPolarization_symm hq z x, realPolarization_symm hq z y]

omit [CompleteSpace H] in
theorem realPolarization_zero_left (y : H) :
    realPolarization q 0 y = 0 := by
  simp [realPolarization, map_neg hq]

omit [InnerProductSpace ℝ H] [CompleteSpace H] hq in
theorem realPolarization_zero_right (x : H) :
    realPolarization q x 0 = 0 := by
  simp [realPolarization]

omit [CompleteSpace H] in
theorem realPolarization_smul_left (r : ℝ) (x y : H) :
    realPolarization q (r • x) y = r * realPolarization q x y := by
  let f : ℝ →+ ℝ :=
    { toFun := fun t => realPolarization q (t • x) y
      map_zero' := by
        simpa using hq.realPolarization_zero_left y
      map_add' := by
        intro a b
        simpa [add_smul] using
          hq.realPolarization_add_left (a • x) (b • x) y }
  rcases hq.bounded with ⟨C, hC⟩
  let C₀ : ℝ := max C 0
  let K : ℝ := ‖x‖ + ‖y‖
  let R : ℝ := C₀ * K ^ 2
  have hC₀ : 0 ≤ C₀ := le_max_right C 0
  have hC_le : C ≤ C₀ := le_max_left C 0
  have hK : 0 ≤ K := add_nonneg (norm_nonneg x) (norm_nonneg y)
  have hq_bound (z : H) (hz : ‖z‖ ≤ K) : |q z| ≤ R := by
    have hz_sq : ‖z‖ ^ 2 ≤ K ^ 2 := by
      nlinarith [norm_nonneg z]
    calc
      |q z| ≤ C * ‖z‖ ^ 2 := hC z
      _ ≤ C₀ * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hC_le (sq_nonneg ‖z‖)
      _ ≤ C₀ * K ^ 2 := mul_le_mul_of_nonneg_left hz_sq hC₀
      _ = R := rfl
  have hsubset :
      Set.image (fun t : ℝ => f t) (Metric.ball (0 : ℝ) 1) ⊆
        Metric.closedBall (0 : ℝ) R := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    have ht_one : ‖t‖ ≤ (1 : ℝ) := by
      have ht' : dist t 0 < (1 : ℝ) := by
        simpa [Metric.mem_ball] using ht
      simpa [dist_eq_norm] using ht'.le
    have htx : ‖t • x‖ ≤ ‖x‖ := by
      calc
        ‖t • x‖ = ‖t‖ * ‖x‖ := norm_smul t x
        _ ≤ 1 * ‖x‖ :=
          mul_le_mul_of_nonneg_right ht_one (norm_nonneg x)
        _ = ‖x‖ := one_mul _
    have hplus : ‖t • x + y‖ ≤ K := by
      calc
        ‖t • x + y‖ ≤ ‖t • x‖ + ‖y‖ := norm_add_le _ _
        _ ≤ ‖x‖ + ‖y‖ := add_le_add htx le_rfl
        _ = K := rfl
    have hminus : ‖t • x - y‖ ≤ K := by
      calc
        ‖t • x - y‖ ≤ ‖t • x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + ‖y‖ := add_le_add htx le_rfl
        _ = K := rfl
    have hq_plus := hq_bound (t • x + y) hplus
    have hq_minus := hq_bound (t • x - y) hminus
    have hdiff :
        |q (t • x + y) - q (t • x - y)| ≤ 2 * R := by
      calc
        |q (t • x + y) - q (t • x - y)| ≤
            |q (t • x + y)| + |q (t • x - y)| := abs_sub _ _
        _ ≤ R + R := add_le_add hq_plus hq_minus
        _ = 2 * R := by ring
    have hpol : |realPolarization q (t • x) y| ≤ R := by
      rw [realPolarization, abs_div]
      have hR : 0 ≤ R := mul_nonneg hC₀ (sq_nonneg K)
      nlinarith
    simpa [f, Metric.mem_closedBall, Real.dist_eq] using hpol
  have hf_bounded :
      Bornology.IsBounded
        (Set.image (fun t : ℝ => f t) (Metric.ball (0 : ℝ) 1)) := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).2 ?_
    exact ⟨R, hsubset⟩
  have hf_cont : Continuous f := by
    refine AddMonoidHom.continuous_of_isBounded_nhds_zero f
      (Metric.ball_mem_nhds (0 : ℝ) (ε := (1 : ℝ)) (by norm_num)) ?_
    simpa using hf_bounded
  have hlin := map_real_smul f hf_cont r (1 : ℝ)
  simpa [f] using hlin

omit [CompleteSpace H] in
theorem realPolarization_smul_right (r : ℝ) (x y : H) :
    realPolarization q x (r • y) = r * realPolarization q x y := by
  rw [hq.realPolarization_symm x (r • y),
    hq.realPolarization_smul_left r y x,
    hq.realPolarization_symm y x]

omit [InnerProductSpace ℝ H] [CompleteSpace H] hq in
private theorem realPolarization_bound_unit
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hbound : ∀ z : H, |q z| ≤ C₀ * ‖z‖ ^ 2)
    (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    |realPolarization q x y| ≤ 2 * C₀ := by
  have hplus : ‖x + y‖ ≤ (2 : ℝ) := by
    calc
      ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
      _ = 2 := by rw [hx, hy]; norm_num
  have hminus : ‖x - y‖ ≤ (2 : ℝ) := by
    calc
      ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ = 2 := by rw [hx, hy]; norm_num
  have hplus_sq : ‖x + y‖ ^ 2 ≤ (4 : ℝ) := by
    nlinarith [norm_nonneg (x + y)]
  have hminus_sq : ‖x - y‖ ^ 2 ≤ (4 : ℝ) := by
    nlinarith [norm_nonneg (x - y)]
  have hq_plus : |q (x + y)| ≤ 4 * C₀ := by
    calc
      |q (x + y)| ≤ C₀ * ‖x + y‖ ^ 2 := hbound _
      _ ≤ C₀ * 4 := mul_le_mul_of_nonneg_left hplus_sq hC₀
      _ = 4 * C₀ := by ring
  have hq_minus : |q (x - y)| ≤ 4 * C₀ := by
    calc
      |q (x - y)| ≤ C₀ * ‖x - y‖ ^ 2 := hbound _
      _ ≤ C₀ * 4 := mul_le_mul_of_nonneg_left hminus_sq hC₀
      _ = 4 * C₀ := by ring
  rw [realPolarization, abs_div]
  have hdiff : |q (x + y) - q (x - y)| ≤ 8 * C₀ := by
    calc
      |q (x + y) - q (x - y)| ≤ |q (x + y)| + |q (x - y)| :=
        abs_sub _ _
      _ ≤ 4 * C₀ + 4 * C₀ := add_le_add hq_plus hq_minus
      _ = 8 * C₀ := by ring
  nlinarith

omit [CompleteSpace H] in
theorem realPolarization_le_norm_mul_norm :
    ∃ C : ℝ, ∀ x y : H,
      |realPolarization q x y| ≤ C * ‖x‖ * ‖y‖ := by
  rcases hq.bounded with ⟨C, hC⟩
  let C₀ : ℝ := max C 0
  have hC₀ : 0 ≤ C₀ := le_max_right C 0
  have hC_le : C ≤ C₀ := le_max_left C 0
  have hbound : ∀ z : H, |q z| ≤ C₀ * ‖z‖ ^ 2 := by
    intro z
    exact (hC z).trans
      (mul_le_mul_of_nonneg_right hC_le (sq_nonneg ‖z‖))
  refine ⟨2 * C₀, ?_⟩
  intro x y
  by_cases hx : x = 0
  · subst x
    simp [hq.realPolarization_zero_left]
  by_cases hy : y = 0
  · subst y
    simp [realPolarization_zero_right]
  let x₀ : H := ‖x‖⁻¹ • x
  let y₀ : H := ‖y‖⁻¹ • y
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hx₀ : ‖x₀‖ = 1 := by
    simp [x₀, norm_smul, hnx]
  have hy₀ : ‖y₀‖ = 1 := by
    simp [y₀, norm_smul, hny]
  have hx_repr : x = ‖x‖ • x₀ := by
    simp [x₀, smul_smul, hnx]
  have hy_repr : y = ‖y‖ • y₀ := by
    simp [y₀, smul_smul, hny]
  have hunit : |realPolarization q x₀ y₀| ≤ 2 * C₀ :=
    realPolarization_bound_unit C₀ hC₀ hbound x₀ y₀ hx₀ hy₀
  have hpol : realPolarization q x y =
      ‖x‖ * (‖y‖ * realPolarization q x₀ y₀) := by
    calc
      realPolarization q x y =
          realPolarization q (‖x‖ • x₀) y := by rw [← hx_repr]
      _ = ‖x‖ * realPolarization q x₀ y :=
        hq.realPolarization_smul_left _ _ _
      _ = ‖x‖ * realPolarization q x₀ (‖y‖ • y₀) := by rw [← hy_repr]
      _ = ‖x‖ * (‖y‖ * realPolarization q x₀ y₀) := by
        rw [hq.realPolarization_smul_right]
  have hscale := mul_le_mul_of_nonneg_left hunit
    (mul_nonneg (norm_nonneg x) (norm_nonneg y))
  rw [hpol, abs_mul, abs_mul,
    abs_of_nonneg (norm_nonneg x), abs_of_nonneg (norm_nonneg y)]
  simpa [mul_assoc, mul_comm, mul_left_comm] using hscale

theorem realPolarization_eq_inner_product :
    ∃ T : H →L[ℝ] H,
      (∀ x y : H, realPolarization q x y = inner ℝ (T x) y) ∧
      (∀ x : H, q x = inner ℝ (T x) x) := by
  rcases hq.realPolarization_le_norm_mul_norm with ⟨C, hpol⟩
  let C₀ : ℝ := max C 0
  have hC₀ : 0 ≤ C₀ := le_max_right C 0
  have hC_le : C ≤ C₀ := le_max_left C 0
  have hpol₀ : ∀ x y : H,
      ‖realPolarization q x y‖ ≤ C₀ * ‖x‖ * ‖y‖ := by
    intro x y
    calc
      ‖realPolarization q x y‖ = |realPolarization q x y| :=
        Real.norm_eq_abs _
      _ ≤ C * ‖x‖ * ‖y‖ := hpol x y
      _ ≤ C₀ * ‖x‖ * ‖y‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC_le (norm_nonneg x))
          (norm_nonneg y)
  let ψ (x : H) : H →ₗ[ℝ] ℝ :=
    { toFun := fun y => realPolarization q x y
      map_add' := hq.realPolarization_add_right x
      map_smul' := by
        intro r y
        simpa using hq.realPolarization_smul_right r x y }
  have hψ : ∀ x y : H, ‖ψ x y‖ ≤ (C₀ * ‖x‖) * ‖y‖ := by
    intro x y
    simpa [ψ, mul_assoc] using hpol₀ x y
  let φ : H → (H →L[ℝ] ℝ) := fun x =>
    LinearMap.mkContinuous (ψ x) (C₀ * ‖x‖) (hψ x)
  have hφ : ∀ x : H, ‖φ x‖ ≤ C₀ * ‖x‖ := by
    intro x
    exact LinearMap.mkContinuous_norm_le (ψ x)
      (mul_nonneg hC₀ (norm_nonneg x)) (hψ x)
  let BLinear : H →ₗ⋆[ℝ] (H →L[ℝ] ℝ) :=
    { toFun := φ
      map_add' := by
        intro x₁ x₂
        ext y
        exact hq.realPolarization_add_left x₁ x₂ y
      map_smul' := by
        intro r x
        ext y
        simpa using hq.realPolarization_smul_left r x y }
  let B : H →L⋆[ℝ] (H →L[ℝ] ℝ) :=
    BLinear.mkContinuous C₀ (by
      intro x
      simpa [BLinear] using hφ x)
  let T : H →L[ℝ] H :=
    InnerProductSpace.continuousLinearMapOfBilin (E := H) B
  have hrepr : ∀ x y : H,
      realPolarization q x y = inner ℝ (T x) y := by
    intro x y
    have h := InnerProductSpace.continuousLinearMapOfBilin_apply
      (B := B) x y
    change inner ℝ (T x) y = realPolarization q x y at h
    exact h.symm
  refine ⟨T, hrepr, ?_⟩
  intro x
  have htwo : q ((2 : ℝ) • x) = 4 * q x := by
    simpa [show (2 : ℝ) ^ 2 = 4 by norm_num] using hq.sq_hom 2 x
  have htwo' : q (x + x) = 4 * q x := by
    simpa [two_smul] using htwo
  have hdiag : realPolarization q x x = q x := by
    rw [realPolarization]
    have hxsub : x - x = (0 : H) := sub_self x
    rw [hxsub, hq.map_zero, htwo']
    ring
  rw [← hdiag]
  exact hrepr x x

end IsBoundedRealQuadraticForm

namespace ProjectionMeasure

/-- The operator determined by the real polarization of the rank-one measure. -/
def realRepresentingOperator (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H) : H →L[ℝ] H :=
  (IsBoundedRealQuadraticForm.realPolarization_eq_inner_product
    (m.quadraticValue_isBoundedRealQuadraticForm hdim)).choose

theorem realPolarization_eq_inner_realRepresentingOperator
    (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H) (x y : H) :
    realPolarization m.quadraticValue x y =
      inner ℝ (m.realRepresentingOperator hdim x) y :=
  (IsBoundedRealQuadraticForm.realPolarization_eq_inner_product
    (m.quadraticValue_isBoundedRealQuadraticForm hdim)).choose_spec.1 x y

theorem quadraticValue_eq_inner_realRepresentingOperator
    (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H) (x : H) :
    m.quadraticValue x =
      inner ℝ (m.realRepresentingOperator hdim x) x :=
  (IsBoundedRealQuadraticForm.realPolarization_eq_inner_product
    (m.quadraticValue_isBoundedRealQuadraticForm hdim)).choose_spec.2 x

theorem realRepresentingOperator_isSelfAdjoint
    (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H) :
    IsSelfAdjoint (m.realRepresentingOperator hdim) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  calc
    inner ℝ (m.realRepresentingOperator hdim x) y =
        realPolarization m.quadraticValue x y :=
      (m.realPolarization_eq_inner_realRepresentingOperator hdim x y).symm
    _ = realPolarization m.quadraticValue y x :=
      (m.quadraticValue_isBoundedRealQuadraticForm hdim).realPolarization_symm x y
    _ = inner ℝ (m.realRepresentingOperator hdim y) x :=
      m.realPolarization_eq_inner_realRepresentingOperator hdim y x
    _ = inner ℝ x (m.realRepresentingOperator hdim y) :=
      real_inner_comm x _

theorem realRepresentingOperator_isPositive
    (m : ProjectionMeasure ℝ H)
    (hdim : (3 : Cardinal) ≤ Module.rank ℝ H) :
    (m.realRepresentingOperator hdim).IsPositive := by
  refine (ContinuousLinearMap.isPositive_def'
    (T := m.realRepresentingOperator hdim)).2
      ⟨m.realRepresentingOperator_isSelfAdjoint hdim, ?_⟩
  intro x
  simpa [m.quadraticValue_eq_inner_realRepresentingOperator hdim x] using
    m.quadraticValue_nonneg x

end ProjectionMeasure

end ClassicalGleason.Separable
