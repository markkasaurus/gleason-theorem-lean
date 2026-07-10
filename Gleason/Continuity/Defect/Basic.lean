import Gleason.Continuity.AlgebraicFoundation

noncomputable section

open GleasonBridge RankOne

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

/-! ## Great-circle upper bound at a low point

If Q(p) is small and v ⊥ p on the unit sphere, then for any rotation
  x = a·p + b·v  (a²+b²=1)
we have  Q(x) ≤ Q(v).

This is because great_circle_constancy gives Q(x) + Q(x̃) = Q(p) + Q(v),
and Q(x̃) ≥ 0, so Q(x) ≤ Q(p) + Q(v). -/

lemma great_circle_upper_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p v : H) (hp : ‖p‖ = 1) (hv : ‖v‖ = 1) (hpv : inner (𝕜 := ℂ) p v = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    frame_quadratic μ ((a : ℂ) • p + (b : ℂ) • v) ≤
      frame_quadratic μ p + frame_quadratic μ v := by
  have hgc := GleasonBridge.great_circle_constancy hdim μ p v hp hv hpv a b hab
  have hnn := frame_quadratic_nonneg μ ((b : ℂ) • p - (a : ℂ) • v)
  linarith

/-! ## Trace bound on the equator

For an ONB {p, v, w}, the trace condition gives Q(p)+Q(v)+Q(w) = const.
So Q(v) = trace - Q(p) - Q(w) ≤ trace.
Combined with the preceding estimate: Q(x) ≤ Q(p) + Q(v) ≤ Q(p) + trace. -/

/-! ## Restricted-parallelogram one-sided bound

From rp_split_sum: Q((x+w)/√2) + Q((x-w)/√2) = Q(x) + Q(w) for unit x ⊥ w.
Since Q ≥ 0, we get Q((x+w)/√2) ≤ Q(x) + Q(w) and Q((x-w)/√2) ≤ Q(x) + Q(w).
This is the "no factor of 2" bound — one term, not two. -/

lemma rp_split_one_sided_plus
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (x w : H) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hxw : inner (𝕜 := ℂ) x w = 0) :
    frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) ≤
      frame_quadratic μ x + frame_quadratic μ w := by
  have hsplit := GleasonBridge.rp_split_sum hdim μ x w hx hw hxw
  have hnn := frame_quadratic_nonneg μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w))
  linarith

lemma rp_split_one_sided_minus
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (x w : H) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hxw : inner (𝕜 := ℂ) x w = 0) :
    frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)) ≤
      frame_quadratic μ x + frame_quadratic μ w := by
  have hsplit := GleasonBridge.rp_split_sum hdim μ x w hx hw hxw
  have hnn := frame_quadratic_nonneg μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w))
  linarith

/-! ## Oscillation one-sided bound

From oscillation_splitting_sphere:
  Q(x) - Q(p) = [Q(x') - Q(p')] + [Q(x'') - Q(p'')]
Since Q ≥ 0, Q(p') ≥ 0, so Q(x') - Q(p') ≤ Q(x'). Similarly Q(x'') ≤ Q(x'').
Therefore: Q(x) - Q(p) ≤ Q(x') + Q(x'') = Q(x) + Q(w) (by rp_split_sum).
This is just the tautology Q(x)-Q(p) ≤ Q(x)+Q(w), which is always true.

The USEFUL direction is: Q(x) - Q(p) ≥ -Q(p') - Q(p'') = -(Q(p)+Q(w)).
So Q(x) ≥ Q(p) - Q(p) - Q(w) = -Q(w). But Q(x) ≥ 0 is tighter.

The real payoff: bounding Q(x) using the SPLIT of Q(p):
  Q(x') + Q(x'') = Q(x) + Q(w)
  Q(p') + Q(p'') = Q(p) + Q(w)
So: Q(x') - Q(p') = Q(x) - Q(p) - (Q(x'') - Q(p''))
And since Q(x'') ≥ 0, Q(p'') ≥ 0, we get:
  Q(x') - Q(p') ≤ Q(x) - Q(p) + Q(p'')  [dropping -Q(x'') ≤ 0]
  Q(x') - Q(p') ≥ Q(x) - Q(p) - Q(x'')   [dropping Q(p'') ≥ 0]
-/

lemma oscillation_split_upper
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p x w : H) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hpw : inner (𝕜 := ℂ) p w = 0) (hxw : inner (𝕜 := ℂ) x w = 0) :
    frame_quadratic μ x - frame_quadratic μ p ≤
      frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) +
      frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)) -
      frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w)) := by
  have hsplit := GleasonBridge.oscillation_splitting_sphere hdim μ p x w hp hx hw hpw hxw
  have hnn := frame_quadratic_nonneg μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p - w))
  linarith

/-! ## Global sphere bound from the trace

For ANY unit vector x, Q(x) ≤ W where W is the 3D trace.
This uses `frame_quadratic_sphere_bound` directly. -/

lemma sphere_uniform_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (x : H) (hx : ‖x‖ = 1) :
    ∃ W : ℝ, 0 ≤ W ∧ 0 ≤ frame_quadratic μ x ∧ frame_quadratic μ x ≤ W := by
  rcases GleasonBridge.frame_quadratic_sphere_bound hdim μ x hx with ⟨W, hnn, hle⟩
  exact ⟨W, le_trans hnn hle, hnn, hle⟩

/-! ## Great-circle value bound from nonnegativity

If Q(p) = m (near infimum) on the sphere, and x = cosθ·p + sinθ·v
where v ⊥ p, then:
  m ≤ Q(x) ≤ Q(p) + Q(v)

The lower bound is just Q(x) ≥ 0 ≥ m when m is the infimum.
The upper bound is great_circle_upper_bound.
The KEY point: Q(x) - Q(p) ≤ Q(v) for ANY x on this great circle. -/

lemma great_circle_oscillation_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p v : H) (hp : ‖p‖ = 1) (hv : ‖v‖ = 1) (hpv : inner (𝕜 := ℂ) p v = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    frame_quadratic μ ((a : ℂ) • p + (b : ℂ) • v) - frame_quadratic μ p ≤
      frame_quadratic μ v := by
  have hub := great_circle_upper_bound hdim μ p v hp hv hpv a b hab
  linarith

/-! ## Uniform upper bound on the sphere

There exists a single constant W such that Q(x) ≤ W for all unit x. -/

lemma sphere_uniform_upper
    (μ : FrameFunction H) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ x : H, ‖x‖ = 1 → frame_quadratic μ x ≤ W := by
  rcases frame_quadratic_bounded (H := H) μ with ⟨C, hC⟩
  refine ⟨|C|, abs_nonneg C, ?_⟩
  intro x hx
  have h := hC x
  have : ‖x‖ ^ 2 = 1 := by rw [hx]; norm_num
  calc frame_quadratic μ x ≤ |frame_quadratic μ x| := le_abs_self _
    _ ≤ C * ‖x‖ ^ 2 := h
    _ = C * 1 := by rw [this]
    _ = C := mul_one C
    _ ≤ |C| := le_abs_self C

/-! ## Complementary point on a great circle

Q(cosθ·p + sinθ·v) = Q(p) + Q(v) - Q(sinθ·p - cosθ·v).
So Q at any angle θ is determined by the 2D trace minus Q at the
complementary angle (θ + π/2). -/

lemma great_circle_complementary
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p v : H) (hp : ‖p‖ = 1) (hv : ‖v‖ = 1) (hpv : inner (𝕜 := ℂ) p v = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    frame_quadratic μ ((a : ℂ) • p + (b : ℂ) • v) =
      frame_quadratic μ p + frame_quadratic μ v -
        frame_quadratic μ ((b : ℂ) • p - (a : ℂ) • v) := by
  have hgc := GleasonBridge.great_circle_constancy hdim μ p v hp hv hpv a b hab
  linarith

/-! ## Near-infimum existence

For any ε > 0, the set {Q(x) : ‖x‖ = 1} has points below inf + ε.
We state this concretely: for any bound B on Q values on the sphere,
there exists a sphere point p with Q(p) ≤ B. -/

lemma exists_sphere_point_le_avg
    (_hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (_hu : ‖u‖ = 1) (_hv : ‖v‖ = 1) (_hw : ‖w‖ = 1)
    (_huv : inner (𝕜 := ℂ) u v = 0) (_huw : inner (𝕜 := ℂ) u w = 0)
    (_hvw : inner (𝕜 := ℂ) v w = 0) :
    min (min (frame_quadratic μ u) (frame_quadratic μ v)) (frame_quadratic μ w) ≤
      (frame_quadratic μ u + frame_quadratic μ v + frame_quadratic μ w) / 3 := by
  have hu_nn := frame_quadratic_nonneg μ u
  have hv_nn := frame_quadratic_nonneg μ v
  have hw_nn := frame_quadratic_nonneg μ w
  have h1 := min_le_left (frame_quadratic μ u) (frame_quadratic μ v)
  have h2 := min_le_right (frame_quadratic μ u) (frame_quadratic μ v)
  have h3 := min_le_right (min (frame_quadratic μ u) (frame_quadratic μ v))
                           (frame_quadratic μ w)
  have h4 := min_le_left (min (frame_quadratic μ u) (frame_quadratic μ v))
                          (frame_quadratic μ w)
  nlinarith

/-! ## Restricted parallelogram for equal-norm orthogonal vectors

The existing `frame_quadratic_parallelogram_of_orthogonal_eq_norm` gives
Q(x+y)+Q(x-y) = 2Q(x)+2Q(y) when x ⊥ y, ‖x‖ = ‖y‖.
This works for ANY equal norms, not just unit vectors. -/

/-! ## Orthogonal parallelogram from defect vanishing

If we can prove D_{uv}(a,b) = 0 for orthonormal (u,v) and all real (a,b),
then Q(x+y)+Q(x-y) = 2Q(x)+2Q(y) for all x ⊥ y.

This is because for x = au, y = bv (orthonormal frame):
  Q(au+bv)+Q(au-bv) = 2a²Q(u)+2b²Q(v) + D(a,b)
and if D(a,b)=0, then = 2Q(au)+2Q(bv) = 2Q(x)+2Q(y) by homogeneity.

For general x ⊥ y (not in a common ONB), pick u = x/‖x‖, v = y/‖y‖:
  Q(x+y)+Q(x-y) with a=‖x‖, b=‖y‖ gives the same.

Key: the restricted RP gives D(a,a)=0. We need D(a,b)=0 for all a,b.
-/

/-! ## Parallelogram identity for zero vectors

Base cases where one vector is zero. -/

lemma parallelogram_zero_left (μ : FrameFunction H) (y : H) :
    frame_quadratic μ (0 + y) + frame_quadratic μ (0 - y) =
      2 * frame_quadratic μ 0 + 2 * frame_quadratic μ y := by
  simp [zero_add, zero_sub, frame_quadratic_zero μ, frame_quadratic_neg μ, two_mul]

lemma parallelogram_zero_right (μ : FrameFunction H) (x : H) :
    frame_quadratic μ (x + 0) + frame_quadratic μ (x - 0) =
      2 * frame_quadratic μ x + 2 * frame_quadratic μ 0 := by
  simp [add_zero, sub_zero, frame_quadratic_zero μ, two_mul]

/-! ## Parallelogram identity for collinear vectors

When y = c•x for some real c, the parallelogram identity holds by
direct computation using homogeneity Q(a•x) = |a|²·Q(x). -/

lemma parallelogram_collinear_real (μ : FrameFunction H) (x : H) (c : ℝ) :
    frame_quadratic μ (x + (c : ℂ) • x) + frame_quadratic μ (x - (c : ℂ) • x) =
      2 * frame_quadratic μ x + 2 * frame_quadratic μ ((c : ℂ) • x) := by
  have h1 : x + (c : ℂ) • x = ((1 + c : ℝ) : ℂ) • x := by
    simp [add_smul, one_smul, Complex.ofReal_add]
  have h2 : x - (c : ℂ) • x = ((1 - c : ℝ) : ℂ) • x := by
    simp [sub_smul, one_smul, Complex.ofReal_sub]
  rw [h1, h2]
  have hQ1 := frame_quadratic_sq_hom μ ((1 + c : ℝ) : ℂ) x
  have hQ2 := frame_quadratic_sq_hom μ ((1 - c : ℝ) : ℂ) x
  have hQc := frame_quadratic_sq_hom μ (c : ℂ) x
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hQ1 hQ2 hQc
  rw [hQ1, hQ2, hQc]
  ring_nf

/-! ## Parallelogram identity for equal-norm orthogonal vectors

Wrap the existing restricted RP to match our target signature. -/

lemma parallelogram_orthogonal_eq_norm
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (x y : H) (hxy : inner (𝕜 := ℂ) x y = 0) (hn : ‖x‖ = ‖y‖) :
    frame_quadratic μ (x + y) + frame_quadratic μ (x - y) =
      2 * frame_quadratic μ x + 2 * frame_quadratic μ y :=
  GleasonBridge.frame_quadratic_parallelogram_of_orthogonal_eq_norm hdim μ x y hxy hn

/-! ## Continuity estimates on the sphere

### Infimum of Q on the sphere

The infimum M = inf{Q(x) : ‖x‖ = 1} exists, and M ≥ 0. -/

def Q_sphere_set (μ : FrameFunction H) : Set ℝ :=
  Set.image (fun x => frame_quadratic μ x) (Metric.sphere (0 : H) 1)

lemma Q_sphere_set_bddBelow (μ : FrameFunction H) :
    BddBelow (Q_sphere_set μ) := by
  use 0
  intro y hy
  rcases hy with ⟨x, hx_mem, rfl⟩
  exact frame_quadratic_nonneg μ x

lemma Q_sphere_set_nonempty (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H) :
    (Q_sphere_set μ).Nonempty := by
  have : 0 < Module.finrank ℂ H := by omega
  haveI : Nontrivial H := Module.nontrivial_of_finrank_pos this
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  set u : H := (↑(‖v‖⁻¹) : ℂ) • v with hu_def
  have hu_norm : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ hvn]
  exact ⟨frame_quadratic μ u, u, by simp [Metric.mem_sphere, hu_norm], rfl⟩

lemma Q_sphere_inf_nonneg (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H) :
    0 ≤ sInf (Q_sphere_set μ) := by
  exact le_csInf (Q_sphere_set_nonempty hdim μ) (fun y hy => by
    rcases hy with ⟨x, _, rfl⟩; exact frame_quadratic_nonneg μ x)

lemma Q_sphere_inf_le (μ : FrameFunction H)
    (x : H) (hx : ‖x‖ = 1) :
    sInf (Q_sphere_set μ) ≤ frame_quadratic μ x := by
  exact csInf_le (Q_sphere_set_bddBelow μ) ⟨x, by simp [Metric.mem_sphere, hx], rfl⟩

lemma frame_quadratic_ge_inf_mul_norm_sq
    (μ : FrameFunction H) (x : H) :
    sInf (Q_sphere_set μ) * ‖x‖ ^ 2 ≤ frame_quadratic μ x := by
  by_cases hx : x = 0
  · subst hx
    simp [frame_quadratic_zero]
  · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    let u : H := (((‖x‖⁻¹ : ℝ) : ℂ) • x)
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hxn]
    have h_le : sInf (Q_sphere_set μ) ≤ frame_quadratic μ u := Q_sphere_inf_le μ u hu
    have hx_eq : x = ((‖x‖ : ℝ) : ℂ) • u := by
      dsimp [u]
      rw [smul_smul]
      simp [hxn]
    have h_hom' : frame_quadratic μ x = ‖x‖ ^ 2 * frame_quadratic μ u := by
      nth_rewrite 1 [hx_eq]
      calc
        frame_quadratic μ (((‖x‖ : ℝ) : ℂ) • u) = ‖(((‖x‖ : ℝ) : ℂ))‖ ^ 2 * frame_quadratic μ u := by
          exact frame_quadratic_sq_hom (H := H) μ (((‖x‖ : ℝ) : ℂ)) u
        _ = ‖x‖ ^ 2 * frame_quadratic μ u := by
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    calc
      sInf (Q_sphere_set μ) * ‖x‖ ^ 2 = ‖x‖ ^ 2 * sInf (Q_sphere_set μ) := by ring
      _ ≤ ‖x‖ ^ 2 * frame_quadratic μ u := mul_le_mul_of_nonneg_left h_le (sq_nonneg ‖x‖)
      _ = frame_quadratic μ x := h_hom'.symm

/-! ### Near-infimum points

For any ε > 0, there exists a unit vector p with Q(p) < inf + ε. -/

lemma exists_near_infimum (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : H, ‖p‖ = 1 ∧ frame_quadratic μ p < sInf (Q_sphere_set μ) + ε := by
  have hne := Q_sphere_set_nonempty hdim μ
  have hbb := Q_sphere_set_bddBelow μ
  obtain ⟨y, hy_mem, hy_lt⟩ := exists_lt_of_csInf_lt hne (by linarith : sInf (Q_sphere_set μ) < sInf (Q_sphere_set μ) + ε)
  rcases hy_mem with ⟨p, hp_mem, rfl⟩
  exact ⟨p, by simpa [Metric.mem_sphere] using hp_mem, hy_lt⟩

/-! ### Nonnegativity of the shifted function

Define f(x) = Q(x) - M for x on the sphere. Then f ≥ 0 and inf f = 0.
f inherits ALL functional equations (great-circle, rp-split, etc.)
because subtracting a constant preserves additive identities. -/

lemma shifted_nonneg (μ : FrameFunction H)
    (x : H) (hx : ‖x‖ = 1) :
    0 ≤ frame_quadratic μ x - sInf (Q_sphere_set μ) := by
  linarith [Q_sphere_inf_le μ x hx]

/-! ### Great-circle constancy of the shifted function

f(a·p + b·v) + f(b·p - a·v) = f(p) + f(v) where f = Q - M.
This is identical to great_circle_constancy because M cancels. -/

lemma shifted_great_circle
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p v : H) (hp : ‖p‖ = 1) (hv : ‖v‖ = 1) (hpv : inner (𝕜 := ℂ) p v = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (M : ℝ) :
    (frame_quadratic μ ((a : ℂ) • p + (b : ℂ) • v) - M) +
        (frame_quadratic μ ((b : ℂ) • p - (a : ℂ) • v) - M) =
      (frame_quadratic μ p - M) + (frame_quadratic μ v - M) := by
  have hgc := GleasonBridge.great_circle_constancy hdim μ p v hp hv hpv a b hab
  linarith

/-! ### Great-circle bound at a near-infimum point

If f(p) < ε (p is near the infimum), then for x on a great circle through p:
  f(x) ≤ f(p) + f(v) < ε + f(v)
where v ⊥ p is the equatorial direction. -/

lemma shifted_upper_bound_on_circle
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p v : H) (hp : ‖p‖ = 1) (hv : ‖v‖ = 1) (hpv : inner (𝕜 := ℂ) p v = 0)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    (M : ℝ) (hM : ∀ x : H, ‖x‖ = 1 → M ≤ frame_quadratic μ x) :
    frame_quadratic μ ((a : ℂ) • p + (b : ℂ) • v) - M ≤
      (frame_quadratic μ p - M) + (frame_quadratic μ v - M) := by
  have hgc := shifted_great_circle hdim μ p v hp hv hpv a b hab M
  -- Need: the complementary point bp-av is unit, so hM gives Q(bp-av) ≥ M.
  have hcomp_unit : ‖((b : ℂ) • p - (a : ℂ) • v)‖ = 1 := by
    -- bp - av = bp + (-a)v, and bp ⊥ (-a)v since p ⊥ v
    have hsub : (b : ℂ) • p - (a : ℂ) • v = (b : ℂ) • p + ((-a : ℝ) : ℂ) • v := by
      push_cast; simp [sub_eq_add_neg, neg_smul]
    rw [hsub]
    have hpv' : inner (𝕜 := ℂ) ((b : ℂ) • p) (((-a : ℝ) : ℂ) • v) = 0 := by
      simp only [inner_smul_left, inner_smul_right, hpv, mul_zero]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      ((b : ℂ) • p) (((-a : ℝ) : ℂ) • v) hpv'
    have : ‖(b : ℂ) • p + ((-a : ℝ) : ℂ) • v‖ ^ 2 = 1 := by
      rw [sq, h]; simp [norm_smul, Complex.norm_real, Real.norm_eq_abs, hp, hv, sq_abs]; linarith
    nlinarith [norm_nonneg ((b : ℂ) • p + ((-a : ℝ) : ℂ) • v)]
  linarith [hM _ hcomp_unit]

/-! ### Restricted parallelogram for the shifted function

f(x')+f(x'') = f(x)+f(w) where f = Q - M (constant cancels in the sum). -/

lemma shifted_rp_split
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (x w : H) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1)
    (hxw : inner (𝕜 := ℂ) x w = 0) (M : ℝ) :
    (frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) - M) +
    (frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)) - M) =
      (frame_quadratic μ x - M) + (frame_quadratic μ w - M) := by
  have hsplit := GleasonBridge.rp_split_sum hdim μ x w hx hw hxw
  linarith

/-! ## Phase invariance

Q(c•x) = Q(x) when ‖c‖ = 1. Immediate from Q(c•x) = ‖c‖²·Q(x). -/

lemma frame_quadratic_phase_inv (μ : FrameFunction H) (c : ℂ) (hc : ‖c‖ = 1) (x : H) :
    frame_quadratic μ (c • x) = frame_quadratic μ x := by
  have h := frame_quadratic_sq_hom μ c x
  rw [hc, one_pow, one_mul] at h
  exact h

/-! ## Collinear parallelogram identity for complex scalars

For any c : ℂ, Q((1+c)•x) + Q((1-c)•x) = 2Q(x) + 2Q(c•x).
Proof: |1+c|² + |1-c|² = 2 + 2|c|² (expand and simplify). -/

lemma parallelogram_collinear_complex (μ : FrameFunction H) (x : H) (c : ℂ) :
    frame_quadratic μ ((1 + c) • x) + frame_quadratic μ ((1 - c) • x) =
      2 * frame_quadratic μ x + 2 * frame_quadratic μ (c • x) := by
  have h1 := frame_quadratic_sq_hom μ (1 + c) x
  have h2 := frame_quadratic_sq_hom μ (1 - c) x
  have hc := frame_quadratic_sq_hom μ c x
  rw [h1, h2, hc]
  have key : ‖1 + c‖ ^ 2 + ‖1 - c‖ ^ 2 = 2 + 2 * ‖c‖ ^ 2 := by
    have norm_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      have := Complex.normSq_apply z; rw [sq, sq]; linarith
    rw [norm_sq, norm_sq, norm_sq]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  have : ‖1 + c‖ ^ 2 * frame_quadratic μ x + ‖1 - c‖ ^ 2 * frame_quadratic μ x =
      (‖1 + c‖ ^ 2 + ‖1 - c‖ ^ 2) * frame_quadratic μ x := by ring
  rw [this, key]
  ring

/-! ## Orthogonal projection decomposition

For x ≠ 0, define c = ⟪x,y⟫/‖x‖² and y_perp = y - c•x.
Then ⟪x, y_perp⟫ = 0 (using Mathlib convention: inner is conj-linear
in first arg, linear in second).
This is the standard orthogonal decomposition y = c•x + y_perp. -/

lemma inner_projection_remainder_eq_zero (x y : H) (hx : x ≠ 0) :
    inner (𝕜 := ℂ) x (y - ((inner (𝕜 := ℂ) x y / (↑(‖x‖ ^ 2) : ℂ)) • x)) = 0 := by
  rw [inner_sub_right, inner_smul_right]
  have hxx : inner (𝕜 := ℂ) x x = (1 : ℂ) * ↑(‖x‖ ^ 2 : ℝ) := by
    simp [inner_self_eq_norm_sq_to_K]
  rw [hxx]
  have hxsq : (↑(‖x‖ ^ 2) : ℂ) ≠ 0 := by
    push_cast; simp [norm_ne_zero_iff.mpr hx]
  field_simp; ring

/-! ## Preservation of orthogonality under scalar multiplication

If ⟪x, z⟫ = 0 then ⟪c•x, z⟫ = 0 for any scalar c.
This means (1+c)•x ⊥ y_perp and (1-c)•x ⊥ y_perp. -/

lemma inner_smul_left_eq_zero {x z : H} (c : ℂ) (h : inner (𝕜 := ℂ) x z = 0) :
    inner (𝕜 := ℂ) (c • x) z = 0 := by
  rw [inner_smul_left, h, mul_zero]

/-! ## Decomposition equations for the parallelogram identity

For x ≠ 0, define c = ⟪x,y⟫/‖x‖² and y_perp = y - c•x. Then:
  x + y = (1+c)•x + y_perp  (with (1+c)•x ⊥ y_perp)
  x - y = (1-c)•x + (-y_perp)  (with (1-c)•x ⊥ -y_perp) -/

lemma decompose_sum (x y : H) (c : ℂ) :
    x + y = (1 + c) • x + (y - c • x) := by
  simp only [add_smul, one_smul]; abel

lemma decompose_diff (x y : H) (c : ℂ) :
    x - y = (1 - c) • x + (-(y - c • x)) := by
  simp only [sub_smul, one_smul]; abel

/-! ## Orthogonality of transferred points

For unit x ⊥ w, the transferred points (x±w)/√2 are orthogonal to
the cross direction x∓w. This is needed for iterating the oscillation splitting. -/

lemma transferred_orthogonal_plus
    (x w : H) (hx : ‖x‖ = 1) (hw : ‖w‖ = 1) (hxw : inner (𝕜 := ℂ) x w = 0) :
    inner (𝕜 := ℂ) ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w))
      ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)) = 0 := by
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right,
    inner_self_eq_norm_sq_to_K]
  have hwx : inner (𝕜 := ℂ) w x = 0 := by rwa [inner_eq_zero_symm]
  simp [hxw, hwx, hx, hw]

/-! ## Orthogonal witnesses for oscillation transfer

In dim ≥ 3, for any two unit vectors x, p, there exists a unit w orthogonal to both.
This is the dimension hypothesis in action. -/

lemma exists_unit_orth_to_pair
    (hdim : 3 ≤ Module.finrank ℂ H) (x p : H) :
    ∃ w : H, ‖w‖ = 1 ∧ inner (𝕜 := ℂ) x w = 0 ∧ inner (𝕜 := ℂ) p w = 0 := by
  exact exists_unit_orthogonal_to_pair (H := H) hdim x p

/-! ## Oscillation bound with a witness

For ANY two unit vectors x, p on S² (dim ≥ 3), there EXISTS a unit w ⊥ both
such that the oscillation bound holds. This packages the oscillation splitting
with the existence of the third direction into a single usable lemma. -/

lemma oscillation_bound_with_witness
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p x : H) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) :
    ∃ w : H, ‖w‖ = 1 ∧ inner (𝕜 := ℂ) p w = 0 ∧ inner (𝕜 := ℂ) x w = 0 ∧
      |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p| ≤
        |frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) -
         frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w))| +
        |frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)) -
         frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p - w))| := by
  obtain ⟨w, hw, hpw, hxw⟩ := exists_unit_orth_to_pair hdim p x
  exact ⟨w, hw, hpw, hxw,
    GleasonBridge.oscillation_abs_bound hdim μ p x w hp hx hw hpw hxw⟩

lemma oscillation_transferred_dist_sub
    (p x w : H) :
    ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w) -
        (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p - w)‖ =
      (Real.sqrt 2)⁻¹ * ‖x - p‖ := by
  simpa [sub_eq_add_neg] using
    (GleasonBridge.oscillation_transferred_dist (p := p) (x := x) (w := -w))

lemma oscillation_bound_with_witness_contractive
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p x : H) (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) :
    ∃ w : H, ‖w‖ = 1 ∧ inner (𝕜 := ℂ) p w = 0 ∧ inner (𝕜 := ℂ) x w = 0 ∧
      |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p| ≤
        |frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) -
         frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w))| +
        |frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w)) -
         frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p - w))|
      ∧
      ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w) -
          (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w)‖ =
        (Real.sqrt 2)⁻¹ * ‖x - p‖
      ∧
      ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x - w) -
          (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p - w)‖ =
        (Real.sqrt 2)⁻¹ * ‖x - p‖ := by
  rcases oscillation_bound_with_witness hdim μ p x hp hx with
    ⟨w, hw, hpw, hxw, hosc⟩
  refine ⟨w, hw, hpw, hxw, hosc, ?_, ?_⟩
  · simpa using
      (GleasonBridge.oscillation_transferred_dist (p := p) (x := x) (w := w))
  · simpa using oscillation_transferred_dist_sub (p := p) (x := x) (w := w)

def sphere_oscillation_set (μ : FrameFunction H) (δ : ℝ) : Set ℝ :=
  {t : ℝ |
    ∃ p x : H,
      ‖p‖ = 1 ∧ ‖x‖ = 1 ∧ dist x p ≤ δ ∧
      t = |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p|}

def sphere_oscillation_sup (μ : FrameFunction H) (δ : ℝ) : ℝ :=
  sSup (sphere_oscillation_set (H := H) μ δ)

lemma sphere_oscillation_set_nonempty
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (sphere_oscillation_set (H := H) μ δ).Nonempty := by
  rcases Q_sphere_set_nonempty (H := H) hdim μ with ⟨q, x, hxS, hq⟩
  have hx : ‖x‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hxS
  refine ⟨0, x, x, hx, hx, ?_, ?_⟩
  · simpa using hδ
  · simp

lemma sphere_oscillation_set_bddAbove
    (μ : FrameFunction H) (δ : ℝ) :
    BddAbove (sphere_oscillation_set (H := H) μ δ) := by
  rcases frame_quadratic_bounded (H := H) μ with ⟨C, hC⟩
  refine ⟨2 * |C|, ?_⟩
  intro t ht
  rcases ht with ⟨p, x, hp, hx, hdist, rfl⟩
  have hCx : |frame_quadratic (H := H) μ x| ≤ |C| := by
    have h0 : |frame_quadratic (H := H) μ x| ≤ C * ‖x‖ ^ 2 := hC x
    have h1 : C * ‖x‖ ^ 2 ≤ |C| * ‖x‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg ‖x‖)
    have h2 : |frame_quadratic (H := H) μ x| ≤ |C| * ‖x‖ ^ 2 := le_trans h0 h1
    simpa [hx] using h2
  have hCp : |frame_quadratic (H := H) μ p| ≤ |C| := by
    have h0 : |frame_quadratic (H := H) μ p| ≤ C * ‖p‖ ^ 2 := hC p
    have h1 : C * ‖p‖ ^ 2 ≤ |C| * ‖p‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg ‖p‖)
    have h2 : |frame_quadratic (H := H) μ p| ≤ |C| * ‖p‖ ^ 2 := le_trans h0 h1
    simpa [hp] using h2
  calc
    |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p|
        ≤ |frame_quadratic (H := H) μ x| + |frame_quadratic (H := H) μ p| := by
            simpa using
              (abs_sub_le (frame_quadratic (H := H) μ x) 0
                (frame_quadratic (H := H) μ p))
    _ ≤ |C| + |C| := by gcongr
    _ = 2 * |C| := by ring

lemma abs_frame_diff_le_sphere_oscillation_sup
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    {p x : H} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) (hd : dist x p ≤ δ) :
      |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p|
      ≤ sSup (sphere_oscillation_set (H := H) μ δ) := by
  have hmem :
      |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p|
        ∈ sphere_oscillation_set (H := H) μ δ := by
    refine ⟨p, x, hp, hx, hd, rfl⟩
  exact le_csSup (sphere_oscillation_set_bddAbove (H := H) μ δ) hmem

lemma abs_frame_diff_le_sphere_oscillation
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    {p x : H} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) (hd : dist x p ≤ δ) :
    |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p|
      ≤ sphere_oscillation_sup (H := H) μ δ := by
  simpa [sphere_oscillation_sup] using
    abs_frame_diff_le_sphere_oscillation_sup (H := H) hdim μ hδ hp hx hd

lemma sphere_oscillation_split_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {δ : ℝ} (hδ : 0 ≤ δ)
    {p x : H} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) (hd : dist x p ≤ δ) :
    |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p|
      ≤
    2 * sSup (sphere_oscillation_set (H := H) μ ((Real.sqrt 2)⁻¹ * δ)) := by
  rcases oscillation_bound_with_witness_contractive hdim μ p x hp hx with
    ⟨w, hw, hpw, hxw, hosc, hdist_plus, hdist_minus⟩
  let c : ℝ := (Real.sqrt 2)⁻¹
  let xplus : H := (((c : ℝ) : ℂ) • (x + w))
  let pplus : H := (((c : ℝ) : ℂ) • (p + w))
  let xminus : H := (((c : ℝ) : ℂ) • (x - w))
  let pminus : H := (((c : ℝ) : ℂ) • (p - w))
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact inv_nonneg.mpr (Real.sqrt_nonneg 2)
  have hδ' : 0 ≤ c * δ := by nlinarith
  have hxp : ‖x - p‖ ≤ δ := by
    simpa [dist_eq_norm] using hd
  have hxplus : ‖xplus‖ = 1 := by
    simpa [xplus, c] using
      GleasonBridge.oscillation_transferred_norm x w hx hw hxw
  have hpplus : ‖pplus‖ = 1 := by
    simpa [pplus, c] using
      GleasonBridge.oscillation_transferred_norm p w hp hw hpw
  have hxminus : ‖xminus‖ = 1 := by
    simpa [xminus, c, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      GleasonBridge.oscillation_transferred_norm_sub x w hx hw hxw
  have hpminus : ‖pminus‖ = 1 := by
    simpa [pminus, c, RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      GleasonBridge.oscillation_transferred_norm_sub p w hp hw hpw
  have hdist_plus_le : dist xplus pplus ≤ c * δ := by
    have hnorm :
        ‖xplus - pplus‖ = c * ‖x - p‖ := by
      simpa [xplus, pplus, c] using hdist_plus
    calc
      dist xplus pplus = ‖xplus - pplus‖ := by simp [dist_eq_norm]
      _ = c * ‖x - p‖ := hnorm
      _ ≤ c * δ := by
            exact mul_le_mul_of_nonneg_left hxp hc_nonneg
  have hdist_minus_le : dist xminus pminus ≤ c * δ := by
    have hnorm :
        ‖xminus - pminus‖ = c * ‖x - p‖ := by
      simpa [xminus, pminus, c, RCLike.real_smul_eq_coe_smul (K := ℂ)] using hdist_minus
    calc
      dist xminus pminus = ‖xminus - pminus‖ := by simp [dist_eq_norm]
      _ = c * ‖x - p‖ := hnorm
      _ ≤ c * δ := by
            exact mul_le_mul_of_nonneg_left hxp hc_nonneg
  have hplus_bound :
      |frame_quadratic (H := H) μ xplus - frame_quadratic (H := H) μ pplus|
        ≤ sphere_oscillation_sup (H := H) μ (c * δ) := by
    exact abs_frame_diff_le_sphere_oscillation hdim μ hδ' hpplus hxplus hdist_plus_le
  have hminus_bound :
      |frame_quadratic (H := H) μ xminus - frame_quadratic (H := H) μ pminus|
        ≤ sphere_oscillation_sup (H := H) μ (c * δ) := by
    exact abs_frame_diff_le_sphere_oscillation hdim μ hδ' hpminus hxminus hdist_minus_le
  have hosc' :
      |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p|
        ≤
      |frame_quadratic (H := H) μ xplus - frame_quadratic (H := H) μ pplus| +
      |frame_quadratic (H := H) μ xminus - frame_quadratic (H := H) μ pminus| := by
    simpa [xplus, pplus, xminus, pminus, c, RCLike.real_smul_eq_coe_smul (K := ℂ)] using hosc
  have hplus_bound' :
      |frame_quadratic (H := H) μ xplus - frame_quadratic (H := H) μ pplus|
        ≤ sphere_oscillation_sup (H := H) μ ((Real.sqrt 2)⁻¹ * δ) := by
    simpa [c] using hplus_bound
  have hminus_bound' :
      |frame_quadratic (H := H) μ xminus - frame_quadratic (H := H) μ pminus|
        ≤ sphere_oscillation_sup (H := H) μ ((Real.sqrt 2)⁻¹ * δ) := by
    simpa [c] using hminus_bound
  have hsum :
      |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p|
        ≤
      sphere_oscillation_sup (H := H) μ ((Real.sqrt 2)⁻¹ * δ) +
        sphere_oscillation_sup (H := H) μ ((Real.sqrt 2)⁻¹ * δ) := by
    exact le_trans hosc' (add_le_add hplus_bound' hminus_bound')
  calc
    |frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p|
        ≤
      sphere_oscillation_sup (H := H) μ ((Real.sqrt 2)⁻¹ * δ) +
        sphere_oscillation_sup (H := H) μ ((Real.sqrt 2)⁻¹ * δ) := hsum
    _ = 2 * sphere_oscillation_sup (H := H) μ ((Real.sqrt 2)⁻¹ * δ) := by ring

lemma sphere_oscillation_sup_split_recurrence
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    sphere_oscillation_sup (H := H) μ δ
      ≤ 2 * sphere_oscillation_sup (H := H) μ ((Real.sqrt 2)⁻¹ * δ) := by
  refine csSup_le ?_ ?_
  · exact sphere_oscillation_set_nonempty (H := H) hdim μ hδ
  · intro t ht
    rcases ht with ⟨p, x, hp, hx, hdist, rfl⟩
    simpa [sphere_oscillation_sup] using
      sphere_oscillation_split_bound (H := H) hdim μ hδ hp hx hdist

lemma sphere_oscillation_set_mono
    (μ : FrameFunction H) {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    sphere_oscillation_set (H := H) μ δ₁ ⊆
      sphere_oscillation_set (H := H) μ δ₂ := by
  intro t ht
  rcases ht with ⟨p, x, hp, hx, hd, rfl⟩
  exact ⟨p, x, hp, hx, le_trans hd hδ, rfl⟩

lemma sphere_oscillation_sup_mono
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {δ₁ δ₂ : ℝ} (hδ1 : 0 ≤ δ₁) (hδ12 : δ₁ ≤ δ₂) :
    sphere_oscillation_sup (H := H) μ δ₁ ≤
      sphere_oscillation_sup (H := H) μ δ₂ := by
  refine csSup_le ?_ ?_
  · exact sphere_oscillation_set_nonempty (H := H) hdim μ hδ1
  · intro t ht
    exact le_csSup
      (sphere_oscillation_set_bddAbove (H := H) μ δ₂)
      ((sphere_oscillation_set_mono (H := H) μ hδ12) ht)

lemma sphere_oscillation_sup_split_iterate
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ n : ℕ,
      sphere_oscillation_sup (H := H) μ δ
        ≤
      (2 : ℝ) ^ n *
        sphere_oscillation_sup (H := H) μ (((Real.sqrt 2)⁻¹ : ℝ) ^ n * δ) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hc_nonneg : 0 ≤ ((Real.sqrt 2)⁻¹ : ℝ) := by
        exact inv_nonneg.mpr (Real.sqrt_nonneg 2)
      have hδn : 0 ≤ (((Real.sqrt 2)⁻¹ : ℝ) ^ n * δ) := by
        exact mul_nonneg (pow_nonneg hc_nonneg n) hδ
      have hstep :
          sphere_oscillation_sup (H := H) μ (((Real.sqrt 2)⁻¹ : ℝ) ^ n * δ)
            ≤
          2 * sphere_oscillation_sup (H := H) μ (((Real.sqrt 2)⁻¹ : ℝ) * ((((Real.sqrt 2)⁻¹ : ℝ) ^ n * δ))) := by
        exact sphere_oscillation_sup_split_recurrence (H := H) hdim μ hδn
      calc
        sphere_oscillation_sup (H := H) μ δ
            ≤ (2 : ℝ) ^ n *
                sphere_oscillation_sup (H := H) μ (((Real.sqrt 2)⁻¹ : ℝ) ^ n * δ) := ih
        _ ≤ (2 : ℝ) ^ n *
              (2 * sphere_oscillation_sup (H := H) μ
                  (((Real.sqrt 2)⁻¹ : ℝ) * ((((Real.sqrt 2)⁻¹ : ℝ) ^ n * δ)))) := by
              gcongr
        _ = (2 : ℝ) ^ (n + 1) *
              sphere_oscillation_sup (H := H) μ (((Real.sqrt 2)⁻¹ : ℝ) ^ (n + 1) * δ) := by
              ring_nf

/-! ## Sphere bound for transferred points

Transferred points stay on S², and Q values at all sphere points
are bounded by W. So each oscillation term is bounded by 2W. -/

lemma oscillation_term_bound
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (x p w : H) (hx : ‖x‖ = 1) (hp : ‖p‖ = 1) (hw : ‖w‖ = 1)
    (hxw : inner (𝕜 := ℂ) x w = 0) (hpw : inner (𝕜 := ℂ) p w = 0) :
    |frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) -
     frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w))| ≤
      2 * (frame_quadratic (H := H) μ x + frame_quadratic (H := H) μ p +
           2 * frame_quadratic (H := H) μ w) := by
  have hx' := oscillation_transferred_norm x w hx hw hxw
  have hp' := oscillation_transferred_norm p w hp hw hpw
  rcases sphere_uniform_bound hdim μ _ hx' with ⟨Wx, _, hQx'_nn, _⟩
  rcases sphere_uniform_bound hdim μ _ hp' with ⟨Wp, _, hQp'_nn, _⟩
  have hQx_nn := frame_quadratic_nonneg (H := H) μ x
  have hQp_nn := frame_quadratic_nonneg (H := H) μ p
  have hQw_nn := frame_quadratic_nonneg (H := H) μ w
  -- Use rp_split one-sided bounds
  have hx_ub := rp_split_one_sided_plus hdim μ x w hx hw hxw
  have hp_ub := rp_split_one_sided_plus hdim μ p w hp hw hpw
  -- For nonneg a, b: |a - b| ≤ a + b
  have hab : |frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) -
     frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w))| ≤
       frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)) +
       frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w)) := by
    rcases le_or_gt (frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (x + w)))
      (frame_quadratic (H := H) μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p + w))) with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  linarith

/-! ## Mixed-defect norm factorization

The mixed defect `D(u+cw, v, 1, s)` from the cross-plane transfer has base
vector `u+cw` with `‖u+cw‖² = 1+c²`. We express this as `local_defect_g`
which is simply `D(x, v, 1, s)` for arbitrary x.

Key fact: `local_defect_g μ (u+cw) v s` = `Q(u+cw+sv) + Q(u+cw-sv) - 2Q(u+cw) - 2s²Q(v)`.
No normalization needed — the definition works for any base vector. -/

lemma mixed_defect_eq_local_defect_g
    (μ : FrameFunction H) (u v w : H) (c s : ℝ) :
    local_quad2DDefect μ (u + (c : ℂ) • w) v 1 s =
      local_defect_g μ (u + (c : ℂ) • w) v s := by
  rfl

/-! ## Cross-plane transfer for the local defect

Rewrite the cross-plane transfer purely in terms of local_defect_g. -/

lemma cross_plane_transfer_g
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s : ℝ) (c : ℝ) (hc : c ^ 2 = 1 + s ^ 2) :
    2 * local_defect_g μ u v s =
      2 * local_defect_g μ u w c +
        local_defect_g μ (u + (c : ℂ) • w) v s +
        local_defect_g μ (u - (c : ℂ) • w) v s := by
  have hcpt := GleasonBridge.cross_plane_transfer hdim μ u v w hu hv hw huv huw hvw s c hc
  -- cross_plane_transfer uses local_quad2DDefect with real-smul notation
  -- Convert: u + (c : ℝ) • w = u + (c : ℂ) • w (since ℝ-smul = ℂ-cast-smul)
  simp only [local_defect_g] at hcpt ⊢
  convert hcpt using 2 <;> congr 1 <;> simp [sub_eq_add_neg, neg_smul]

/-! ## Growth bound on mixed defects

The mixed defect `g_{x, v}(s)` for any vector x is bounded by C·(1+s²).
This generalizes `local_defect_g_growth_bound` (which requires orthonormal base).
The bound follows from |Q(z)| ≤ C‖z‖² and triangle inequality on norms. -/

lemma mixed_defect_growth_bound
    (μ : FrameFunction H) (x v : H) (hv : ‖v‖ = 1) :
    ∃ C : ℝ, ∀ s : ℝ,
      |local_defect_g μ x v s| ≤ C * (1 + s ^ 2) := by
  rcases frame_quadratic_bounded (H := H) μ with ⟨C0, hC0⟩
  -- C0 ≥ 0 from |Q(v)| ≤ C0·‖v‖² = C0 and Q(v) ≥ 0
  have hC0_nn : 0 ≤ C0 := by
    have h1 := (abs_le.mp (hC0 v)).2
    have h2 := frame_quadratic_nonneg (H := H) μ v
    have h3 : ‖v‖ ^ 2 = 1 := by rw [hv]; norm_num
    nlinarith
  refine ⟨6 * C0 * (1 + ‖x‖ ^ 2), ?_⟩
  intro s
  simp only [local_defect_g, local_quad2DDefect, local_quad2DExpr, Complex.ofReal_one, one_smul,
    one_pow, mul_one]
  set Qp := frame_quadratic (H := H) μ (x + (s : ℂ) • v)
  set Qm := frame_quadratic (H := H) μ (x - (s : ℂ) • v)
  set Qx := frame_quadratic (H := H) μ x
  set Qv := frame_quadratic (H := H) μ v
  -- Non-negativity
  have hQp_nn := frame_quadratic_nonneg (H := H) μ (x + (s : ℂ) • v)
  have hQm_nn := frame_quadratic_nonneg (H := H) μ (x - (s : ℂ) • v)
  have hQx_nn := frame_quadratic_nonneg (H := H) μ x
  have hQv_nn := frame_quadratic_nonneg (H := H) μ v
  -- Upper bounds from |Q(z)| ≤ C0 * ‖z‖²
  have hQp_ub := (abs_le.mp (hC0 (x + (s : ℂ) • v))).2
  have hQm_ub := (abs_le.mp (hC0 (x - (s : ℂ) • v))).2
  have hQx_ub := (abs_le.mp (hC0 x)).2
  have hQv_ub := (abs_le.mp (hC0 v)).2
  have hsv : ‖(s : ℂ) • v‖ = |s| := by
    simp [norm_smul, Complex.norm_real, Real.norm_eq_abs, hv]
  have hv1 : ‖v‖ ^ 2 = 1 := by rw [hv]; norm_num
  -- Norm bounds: ‖x±sv‖ ≤ ‖x‖+|s|
  have hn1 : ‖x + (s : ℂ) • v‖ ≤ ‖x‖ + |s| := by
    calc ‖x + (s : ℂ) • v‖ ≤ ‖x‖ + ‖(s : ℂ) • v‖ := norm_add_le _ _
      _ = ‖x‖ + |s| := by rw [hsv]
  have hn2 : ‖x - (s : ℂ) • v‖ ≤ ‖x‖ + |s| := by
    calc ‖x - (s : ℂ) • v‖ ≤ ‖x‖ + ‖(s : ℂ) • v‖ := norm_sub_le _ _
      _ = ‖x‖ + |s| := by rw [hsv]
  -- Qp ≤ C0*(‖x‖+|s|)² and Qm ≤ C0*(‖x‖+|s|)²
  have hQp_le : Qp ≤ C0 * (‖x‖ + |s|) ^ 2 :=
    calc Qp ≤ C0 * ‖x + (s : ℂ) • v‖ ^ 2 := hQp_ub
      _ ≤ C0 * (‖x‖ + |s|) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hC0_nn
          exact sq_le_sq' (by nlinarith [norm_nonneg (x + (s : ℂ) • v)]) hn1
  have hQm_le : Qm ≤ C0 * (‖x‖ + |s|) ^ 2 :=
    calc Qm ≤ C0 * ‖x - (s : ℂ) • v‖ ^ 2 := hQm_ub
      _ ≤ C0 * (‖x‖ + |s|) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hC0_nn
          exact sq_le_sq' (by nlinarith [norm_nonneg (x - (s : ℂ) • v)]) hn2
  have hQx_le : Qx ≤ C0 * ‖x‖ ^ 2 := hQx_ub
  have hQv_le : Qv ≤ C0 := by nlinarith [hQv_ub, hv1]
  -- (‖x‖+|s|)² ≤ 2(‖x‖²+s²) by AM-GM
  have ham : (‖x‖ + |s|) ^ 2 ≤ 2 * (‖x‖ ^ 2 + s ^ 2) := by
    nlinarith [sq_nonneg (‖x‖ - |s|), sq_abs s]
  -- ‖x‖²+s² ≤ (1+‖x‖²)(1+s²)
  have hprod : ‖x‖ ^ 2 + s ^ 2 ≤ (1 + ‖x‖ ^ 2) * (1 + s ^ 2) := by
    nlinarith [sq_nonneg ‖x‖, sq_nonneg s]
  -- Combine for upper bound
  have hQpm_upper : Qp + Qm ≤ 4 * C0 * (‖x‖ ^ 2 + s ^ 2) := by
    nlinarith
  -- Combine for lower bound on negative terms
  have hQxv_lower : 2 * Qx + 2 * s ^ 2 * Qv ≤ 2 * C0 * (‖x‖ ^ 2 + s ^ 2) := by
    have h1 : 2 * Qx ≤ 2 * C0 * ‖x‖ ^ 2 := by linarith
    have h2 : 2 * s ^ 2 * Qv ≤ 2 * s ^ 2 * C0 := by
      apply mul_le_mul_of_nonneg_left hQv_le; nlinarith [sq_nonneg s]
    linarith
  -- Final: use ‖x‖²+s² ≤ (1+‖x‖²)(1+s²) and the C0 monotonicity
  have hfinal : 4 * C0 * (‖x‖ ^ 2 + s ^ 2) ≤ 6 * C0 * (1 + ‖x‖ ^ 2) * (1 + s ^ 2) := by
    have h := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 4 * C0 by linarith)
    nlinarith [mul_nonneg (show 0 ≤ 2 * C0 by linarith)
      (show 0 ≤ (1 + ‖x‖ ^ 2) * (1 + s ^ 2) by nlinarith [sq_nonneg ‖x‖, sq_nonneg s])]
  have hfinal2 : 2 * C0 * (‖x‖ ^ 2 + s ^ 2) ≤ 6 * C0 * (1 + ‖x‖ ^ 2) * (1 + s ^ 2) := by
    linarith
  -- s²*Qv ≤ s²*C0 (needed for lower bound)
  have hs2Qv : s ^ 2 * Qv ≤ s ^ 2 * C0 :=
    mul_le_mul_of_nonneg_left hQv_le (sq_nonneg s)
  -- s²*Qv ≥ 0 (needed for upper bound)
  have hs2Qv_nn : 0 ≤ s ^ 2 * Qv :=
    mul_nonneg (sq_nonneg s) hQv_nn
  rw [abs_le]; constructor
  · -- Lower: defect ≥ -(2Qx+2s²Qv) ≥ -2C0(‖x‖²+s²) ≥ -6C0(1+‖x‖²)(1+s²)
    linarith
  · -- Upper: defect ≤ Qp+Qm ≤ 4C0(‖x‖²+s²) ≤ 6C0(1+‖x‖²)(1+s²)
    linarith


/-! ## Vanishing of the two-variable defect

If `local_defect_g μ u v t = 0` for ALL t, then `local_quad2DDefect μ u v a b = 0`
for ALL real (a,b). This uses ratio reduction: D(a,b) = a²·g(b/a). -/

lemma defect_zero_of_g_zero
    (μ : FrameFunction H) (u v : H)
    (hg0 : ∀ t : ℝ, local_defect_g μ u v t = 0)
    (a b : ℝ) : local_quad2DDefect μ u v a b = 0 :=
  GleasonBridge.local_quad2DDefect_eq_zero_of_local_defect_g_zero μ u v hg0 a b

/-! ## Defect vanishing from the Cauchy–Jensen equation

If g satisfies the CJ equation g(s+t)+g(s-t) = 2g(s)+2g(t), then g ≡ 0.
This combines:
- cauchy_jensen_solution: CJ + growth bound → g(t) = t²·g(1)
- local_defect_g_one_eq_zero: g(1) = 0
- local_defect_g_growth_bound: |g(t)| ≤ C(1+t²)
-/

lemma local_defect_g_zero_of_cj
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hCJ : ∀ s t : ℝ, local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) =
      2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t)
    (t : ℝ) : local_defect_g μ u v t = 0 := by
  have hbound := GleasonBridge.local_defect_g_growth_bound μ u v hu hv huv
  have hcj_sol := GleasonBridge.cauchy_jensen_solution (local_defect_g μ u v) hCJ hbound t
  have hg1 := GleasonBridge.local_defect_g_one_eq_zero hdim μ u v hu hv huv
  rw [hcj_sol, hg1, mul_zero]

/-! ## Full parallelogram identity from the orthogonal case

The full parallelogram identity Q(x+y)+Q(x-y) = 2Q(x)+2Q(y) for ALL x, y
follows from three ingredients:
1. The orthogonal PI: D(x,y) = 0 when x ⊥ y (any norms).
2. The collinear identity: Q((1+c)x)+Q((1-c)x) = 2Q(x)+2Q(cx).
3. Decomposition: y = cx + z with z ⊥ x, then
   Q(x+y) = Q((1+c)x+z) = Q((1+c)x)+Q(z) (orthogonal PI)
   Q(x-y) = Q((1-c)x-z) = Q((1-c)x)+Q(z) (orthogonal PI + Q(-z)=Q(z))
   Adding: Q(x+y)+Q(x-y) = Q((1+c)x)+Q((1-c)x)+2Q(z)
                           = 2Q(x)+2Q(cx)+2Q(z)  (collinear PI)
                           = 2Q(x)+2(Q(cx)+Q(z))
                           = 2Q(x)+2Q(y)         (orthogonal PI on cx ⊥ z)
-/

lemma full_pi_of_orthogonal_pi
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (horth : ∀ (x y : H), inner (𝕜 := ℂ) x y = 0 →
      frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
        2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y)
    (x y : H) :
    frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
      2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by
  have hquad : μ.HasQuad2D := by
    intro u v hu hv huv
    refine ⟨2 * frame_quadratic (H := H) μ u, 0, 2 * frame_quadratic (H := H) μ v, ?_⟩
    intro a b
    have huv' : inner (𝕜 := ℂ) ((a : ℂ) • u) ((b : ℂ) • v) = 0 := by
      simp [huv]
    have hpar :=
      horth ((a : ℂ) • u) ((b : ℂ) • v) huv'
    have hQa : frame_quadratic (H := H) μ ((a : ℂ) • u) = a ^ 2 * frame_quadratic (H := H) μ u := by
      have h := frame_quadratic_sq_hom (H := H) μ (a : ℂ) u
      simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
    have hQb : frame_quadratic (H := H) μ ((b : ℂ) • v) = b ^ 2 * frame_quadratic (H := H) μ v := by
      have h := frame_quadratic_sq_hom (H := H) μ (b : ℂ) v
      simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
    have hpar' : local_quad2DExpr μ u v a b =
        2 * frame_quadratic (H := H) μ ((a : ℂ) • u) +
        2 * frame_quadratic (H := H) μ ((b : ℂ) • v) := by
      simpa [local_quad2DExpr] using hpar
    have hpoly : local_quad2DExpr μ u v a b =
        (2 * frame_quadratic (H := H) μ u) * a ^ 2 +
        0 * a * b +
        (2 * frame_quadratic (H := H) μ v) * b ^ 2 := by
      linarith [hpar', hQa, hQb]
    simpa [local_quad2DExpr] using hpoly
  simpa using _root_.frame_quadratic_parallelogram (H := H) hdim μ hquad x y

/-! ## Orthogonal parallelogram identity for arbitrary norms

For orthogonal x ⊥ y: write x = au, y = bv with u, v orthonormal.
Then D(x,y) = local_quad2DDefect μ u v a b = 0 (from g ≡ 0 via defect_zero_of_g_zero).
This gives Q(x+y)+Q(x-y) = 2Q(x)+2Q(y) for ALL x ⊥ y. -/

lemma orthogonal_pi_of_g_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hg0 : ∀ (u v : H), ‖u‖ = 1 → ‖v‖ = 1 → inner (𝕜 := ℂ) u v = 0 →
      ∀ t : ℝ, local_defect_g μ u v t = 0)
    (x y : H) (hxy : inner (𝕜 := ℂ) x y = 0) :
    frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
      2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by
  -- Handle zero cases
  by_cases hx : x = 0
  · subst hx; simp
    have h0 : frame_quadratic (H := H) μ 0 = 0 := by
      have h := frame_quadratic_sq_hom (H := H) μ (0 : ℂ) y; simp at h; exact h
    have hny : frame_quadratic (H := H) μ (-y) = frame_quadratic (H := H) μ y := by
      have h := frame_quadratic_sq_hom (H := H) μ (-1 : ℂ) y
      simp [norm_neg] at h
      exact h
    rw [h0, hny]; ring
  by_cases hy : y = 0
  · subst hy; simp
    have h0 : frame_quadratic (H := H) μ 0 = 0 := by
      have h := frame_quadratic_sq_hom (H := H) μ (0 : ℂ) x; simp at h; exact h
    rw [h0]; ring
  -- Both nonzero: normalize
  set u := (↑(‖x‖⁻¹) : ℂ) • x with hu_def
  set v := (↑(‖y‖⁻¹) : ℂ) • y with hv_def
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hyn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hu_norm : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hxn]
  have hv_norm : ‖v‖ = 1 := by
    rw [hv_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)), inv_mul_cancel₀ hyn]
  have huv : inner (𝕜 := ℂ) u v = 0 := by
    rw [hu_def, hv_def, inner_smul_left, inner_smul_right, hxy, mul_zero, mul_zero]
  -- x = ‖x‖ • u, y = ‖y‖ • v
  have hx_eq : x = (↑‖x‖ : ℂ) • u := by
    rw [hu_def, smul_smul]; simp [hxn]
  have hy_eq : y = (↑‖y‖ : ℂ) • v := by
    rw [hv_def, smul_smul]; simp [hyn]
  -- local_quad2DDefect μ u v ‖x‖ ‖y‖ = 0
  have hg_all := hg0 u v hu_norm hv_norm huv
  have hD0 := defect_zero_of_g_zero μ u v hg_all ‖x‖ ‖y‖
  -- Unfold the defect to get the PI
  simp only [local_quad2DDefect, local_quad2DExpr] at hD0
  have hhom_x : frame_quadratic (H := H) μ x = ‖x‖ ^ 2 * frame_quadratic (H := H) μ u := by
    have h := frame_quadratic_sq_hom (H := H) μ (↑‖x‖ : ℂ) u
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)] at h
    conv_lhs => rw [hx_eq]
    exact h
  have hhom_y : frame_quadratic (H := H) μ y = ‖y‖ ^ 2 * frame_quadratic (H := H) μ v := by
    have h := frame_quadratic_sq_hom (H := H) μ (↑‖y‖ : ℂ) v
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)] at h
    conv_lhs => rw [hy_eq]
    exact h
  have hxy_sum : x + y = (↑‖x‖ : ℂ) • u + (↑‖y‖ : ℂ) • v := by
    conv_lhs => rw [hx_eq, hy_eq]
  have hxy_diff : x - y = (↑‖x‖ : ℂ) • u - (↑‖y‖ : ℂ) • v := by
    conv_lhs => rw [hx_eq, hy_eq]
  rw [hxy_sum, hxy_diff, hhom_x, hhom_y]
  linarith

/-! ## Parallelogram identity from the Cauchy–Jensen equation

Given the CJ equation for g (for all orthonormal pairs), derive the full PI. -/

lemma full_pi_from_cj
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hCJ : ∀ (u v : H), ‖u‖ = 1 → ‖v‖ = 1 → inner (𝕜 := ℂ) u v = 0 →
      ∀ s t : ℝ, local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) =
        2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t)
    (x y : H) :
    frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
      2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by
  -- Step 1: CJ → g ≡ 0 for all orthonormal pairs
  have hg0 : ∀ (u v : H), ‖u‖ = 1 → ‖v‖ = 1 → inner (𝕜 := ℂ) u v = 0 →
      ∀ t : ℝ, local_defect_g μ u v t = 0 := by
    intro u v hu hv huv t
    exact local_defect_g_zero_of_cj hdim μ u v hu hv huv (hCJ u v hu hv huv) t
  -- Step 2: g ≡ 0 → orthogonal PI for all norms
  have horth : ∀ (a b : H), inner (𝕜 := ℂ) a b = 0 →
      frame_quadratic (H := H) μ (a + b) + frame_quadratic (H := H) μ (a - b) =
        2 * frame_quadratic (H := H) μ a + 2 * frame_quadratic (H := H) μ b := by
    intro a b hab
    exact orthogonal_pi_of_g_zero hdim μ hg0 a b hab
  -- Step 3: Orthogonal PI + collinear PI → full PI
  exact full_pi_of_orthogonal_pi hdim μ horth x y

/-! ## Vanishing of bounded midpoint-additive functions

**Theorem**: If h : ℝ → ℝ satisfies
1. h(s+t) + h(s-t) = 2·h(s) for all s,t  (midpoint equation)
2. h(0) = h(1) = 0
3. |h(s)| ≤ C·(1+s²)  (polynomial growth)
then h ≡ 0.

**Proof sketch**:
- h(-t) = -h(t) and h(nt) = n·h(t) for integer n (from midpoint equation).
- h(n) = 0 for all n ∈ ℤ (from h(1)=0 and integer homogeneity).
- |h| bounded on ℝ: for any t, choose k ∈ ℤ with |2k-t| ≤ 1, then
  h(t) = -h(2k-t) and |h(2k-t)| ≤ C·(1+1) = 2C.
- n·|h(s)| = |h(n·s)| ≤ 2C for all positive integers n, so h(s) = 0.
-/

private lemma midpoint_neg' (h : ℝ → ℝ)
    (hmid : ∀ s t : ℝ, h (s + t) + h (s - t) = 2 * h s)
    (h0 : h 0 = 0) (t : ℝ) : h (-t) = -h t := by
  have := hmid 0 t; simp [h0] at this; linarith

private lemma midpoint_int_zero' (h : ℝ → ℝ)
    (hmid : ∀ s t : ℝ, h (s + t) + h (s - t) = 2 * h s)
    (h0 : h 0 = 0) (h1 : h 1 = 0) (n : ℕ) : h (↑n : ℝ) = 0 := by
  have hpair : ∀ m : ℕ, h (↑m : ℝ) = 0 ∧ h (↑(m + 1) : ℝ) = 0 := by
    intro m
    induction m with
    | zero =>
        constructor
        · simpa using h0
        · simpa using h1
    | succ m ih =>
        rcases ih with ⟨hm, hm1⟩
        constructor
        · simpa [Nat.succ_eq_add_one] using hm1
        · have hstep := hmid (↑(m + 1) : ℝ) 1
          have hc1 : (↑(m + 1) : ℝ) + 1 = (↑(m + 2) : ℝ) := by
            push_cast
            ring
          have hc2 : (↑(m + 1) : ℝ) - 1 = (↑m : ℝ) := by
            push_cast
            ring
          rw [hc1, hc2, hm, hm1] at hstep
          linarith
  exact (hpair n).1

private lemma midpoint_nat_hom' (h : ℝ → ℝ)
    (hmid : ∀ s t : ℝ, h (s + t) + h (s - t) = 2 * h s)
    (h0 : h 0 = 0) (n : ℕ) (t : ℝ) : h (↑n * t) = ↑n * h t := by
  have hpair : ∀ m : ℕ,
      h (↑m * t) = ↑m * h t ∧ h (↑(m + 1) * t) = ↑(m + 1) * h t := by
    intro m
    induction m with
    | zero =>
        constructor
        · simp [h0]
        · simp
    | succ m ih =>
        rcases ih with ⟨hm, hm1⟩
        constructor
        · simpa [Nat.succ_eq_add_one] using hm1
        · have hstep := hmid (↑(m + 1) * t) t
          have hc1 : ↑(m + 1) * t + t = ↑(m + 2) * t := by
            push_cast
            ring
          have hc2 : ↑(m + 1) * t - t = ↑m * t := by
            push_cast
            ring
          rw [hc1, hc2, hm, hm1] at hstep
          have hstep' :
              h (↑(m + 2) * t) = 2 * ((↑(m + 1) : ℝ) * h t) - (↑m : ℝ) * h t := by
            linarith
          have hcoeff :
              2 * ((↑(m + 1) : ℝ) * h t) - (↑m : ℝ) * h t = (↑(m + 2) : ℝ) * h t := by
            calc
              2 * ((↑(m + 1) : ℝ) * h t) - (↑m : ℝ) * h t
                  = (2 * (↑(m + 1) : ℝ) - (↑m : ℝ)) * h t := by ring
              _ = (↑(m + 2) : ℝ) * h t := by
                  have hmcast : 2 * (↑(m + 1) : ℝ) - (↑m : ℝ) = (↑(m + 2) : ℝ) := by
                    have hm1_cast : (↑(m + 1) : ℝ) = (↑m : ℝ) + 1 := by
                      norm_num [Nat.cast_add]
                    have hm2_cast : (↑(m + 2) : ℝ) = (↑m : ℝ) + 2 := by
                      norm_num [Nat.cast_add]
                    nlinarith [hm1_cast, hm2_cast]
                  rw [hmcast]
          rw [hstep', hcoeff]
  exact (hpair n).1

lemma midpoint_additive_bounded_zero
    (h : ℝ → ℝ)
    (hmid : ∀ s t : ℝ, h (s + t) + h (s - t) = 2 * h s)
    (h0 : h 0 = 0) (h1 : h 1 = 0)
    (C : ℝ) (hC_nn : 0 ≤ C) (hC : ∀ s : ℝ, |h s| ≤ C * (1 + s ^ 2))
    (s : ℝ) : h s = 0 := by
  have hneg := midpoint_neg' h hmid h0
  have hint_nn := midpoint_int_zero' h hmid h0 h1
  have hnat_mul := midpoint_nat_hom' h hmid h0
  -- h at negative integers = 0
  have hint_neg : ∀ n : ℕ, h (-(↑n : ℝ)) = 0 := by
    intro n; rw [hneg, hint_nn n, neg_zero]
  -- |h| bounded on all of ℝ by 2C
  -- For any t, choose k : ℤ with |2k-t| ≤ 1, then h(t) = -h(2k-t).
  have hbdd : ∀ t : ℝ, |h t| ≤ 2 * C := by
    intro t
    set k : ℤ := ⌊(t + 1) / 2⌋
    have hk_ub : (↑k : ℝ) ≤ (t + 1) / 2 := Int.floor_le _
    have hk_lb : (t + 1) / 2 < ↑k + 1 := Int.lt_floor_add_one _
    -- |2k - t| ≤ 1
    have hclose : (2 * ↑k - t) ^ 2 ≤ 1 := by nlinarith
    -- h(k) = 0 for integer k
    have hk_zero : h (↑k : ℝ) = 0 := by
      rcases k with (n | n)
      · exact hint_nn n
      · change h (↑(Int.negSucc n) : ℝ) = 0
        simp only [Int.cast_negSucc]
        exact hint_neg (n + 1)
    -- From midpoint eq at s=k, u=t-k: h(t) + h(2k-t) = 2h(k) = 0
    have hmid_k := hmid (↑k : ℝ) (t - ↑k)
    have hc1 : (↑k : ℝ) + (t - ↑k) = t := by ring
    have hc2 : (↑k : ℝ) - (t - ↑k) = 2 * ↑k - t := by ring
    rw [hc1, hc2, hk_zero] at hmid_k
    -- h(t) = -h(2k - t)
    have hsym : h t = -h (2 * ↑k - t) := by linarith
    rw [hsym, abs_neg]
    calc |h (2 * ↑k - t)| ≤ C * (1 + (2 * ↑k - t) ^ 2) := hC _
      _ ≤ C * (1 + 1) := by nlinarith
      _ = 2 * C := by ring
  -- Conclusion: n·|h(s)| = |h(n·s)| ≤ 2C for all n, so h(s) = 0
  by_contra hs
  have hs_pos : 0 < |h s| := abs_pos.mpr hs
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * C / |h s|)
  have hn_pos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp at hn; linarith [div_nonneg (by linarith : (0 : ℝ) ≤ 2 * C) (le_of_lt hs_pos)]
    · exact hp
  have h_large : 2 * C < ↑n * |h s| := by
    rwa [div_lt_iff₀ hs_pos] at hn
  have h_small : ↑n * |h s| ≤ 2 * C := by
    have := hbdd (↑n * s)
    rw [hnat_mul n s, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at this
    exact this
  linarith

/-! ## Line restriction of the parallelogram identity

From the full PI, the restriction of Q to any line through p is a
quadratic polynomial: Q(p + sv) = Q(v)·s² + α·s + Q(p)
where α = Q(p+v) - Q(v) - Q(p).

The quadratic structure follows from the midpoint equation for the
"centered" function, proved via `midpoint_additive_bounded_zero`. -/

lemma line_restriction_quadratic
    (μ : FrameFunction H)
    (hfull : ∀ (a b : H),
      frame_quadratic (H := H) μ (a + b) + frame_quadratic (H := H) μ (a - b) =
        2 * frame_quadratic (H := H) μ a + 2 * frame_quadratic (H := H) μ b)
    (p v : H) (s : ℝ) :
    frame_quadratic (H := H) μ (p + (↑s : ℂ) • v) =
      frame_quadratic (H := H) μ v * s ^ 2 +
        (frame_quadratic (H := H) μ (p + v) - frame_quadratic (H := H) μ v -
          frame_quadratic (H := H) μ p) * s +
        frame_quadratic (H := H) μ p := by
  -- Define f(s) = Q(p + sv), g(s) = f(s) - Q(v)s², h(s) = g(s) - g(0) - s(g(1)-g(0))
  set Qv := frame_quadratic (H := H) μ v
  set Qp := frame_quadratic (H := H) μ p
  set Qpv := frame_quadratic (H := H) μ (p + v)
  set f : ℝ → ℝ := fun s => frame_quadratic (H := H) μ (p + (↑s : ℂ) • v)
  -- f satisfies the CJ-type equation: f(s+t)+f(s-t) = 2f(s)+2t²Qv
  have hf_cj : ∀ s t : ℝ,
      f (s + t) + f (s - t) = 2 * f s + 2 * t ^ 2 * Qv := by
    intro s t
    have hQtv : frame_quadratic (H := H) μ ((↑t : ℂ) • v) = t ^ 2 * Qv := by
      have h := frame_quadratic_sq_hom (H := H) μ (↑t : ℂ) v
      simpa [Qv, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
    have hmain : f (s + t) + f (s - t) =
        2 * f s + 2 * frame_quadratic (H := H) μ ((↑t : ℂ) • v) := by
      simpa [f, add_smul, sub_smul, sub_eq_add_neg, add_assoc, Complex.ofReal_add,
        Complex.ofReal_sub] using hfull (p + (↑s : ℂ) • v) ((↑t : ℂ) • v)
    calc
      f (s + t) + f (s - t)
          = 2 * f s + 2 * frame_quadratic (H := H) μ ((↑t : ℂ) • v) := hmain
      _ = 2 * f s + 2 * t ^ 2 * Qv := by
          rw [hQtv]
          ring
  -- Define h(s) = f(s) - Qv·s² - (Qpv - Qv - Qp)·s - Qp
  set α := Qpv - Qv - Qp
  set h : ℝ → ℝ := fun s => f s - Qv * s ^ 2 - α * s - Qp
  -- h satisfies midpoint equation, h(0) = h(1) = 0
  have h_mid : ∀ s t : ℝ, h (s + t) + h (s - t) = 2 * h s := by
    intro s t; simp only [h]
    have := hf_cj s t; linarith [sq_nonneg t]
  have h_0 : h 0 = 0 := by
    simp [h, f, Qp]
  have h_1 : h 1 = 0 := by
    simp [h, f, α, Qv, Qp, Qpv]
  -- h has polynomial growth
  rcases frame_quadratic_bounded (H := H) μ with ⟨B, hB⟩
  have h_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, |h s| ≤ C * (1 + s ^ 2) := by
    refine ⟨|B| * (‖p‖ ^ 2 + ‖v‖ ^ 2) + |Qv| + |α| + |Qp|, by positivity, ?_⟩
    intro s
    have hs_abs : |s| ≤ 1 + s ^ 2 := by
      nlinarith [sq_nonneg (|s| - 1), sq_abs s]
    have hs_sq : s ^ 2 ≤ 1 + s ^ 2 := by
      nlinarith
    have h1s : 1 ≤ 1 + s ^ 2 := by
      nlinarith [sq_nonneg s]
    have hf_bound : |f s| ≤ |B| * (‖p‖ ^ 2 + ‖v‖ ^ 2) * (1 + s ^ 2) := by
      have hB0 : |f s| ≤ B * ‖p + (↑s : ℂ) • v‖ ^ 2 := hB _
      have hB1 : B * ‖p + (↑s : ℂ) • v‖ ^ 2 ≤ |B| * ‖p + (↑s : ℂ) • v‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right (le_abs_self B) (sq_nonneg ‖p + (↑s : ℂ) • v‖)
      have hB2 : |f s| ≤ |B| * ‖p + (↑s : ℂ) • v‖ ^ 2 := le_trans hB0 hB1
      have hnorm : ‖p + (↑s : ℂ) • v‖ ≤ ‖p‖ + |s| * ‖v‖ := by
        calc ‖p + (↑s : ℂ) • v‖ ≤ ‖p‖ + ‖(↑s : ℂ) • v‖ := norm_add_le _ _
          _ = ‖p‖ + |s| * ‖v‖ := by
              rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
      have hsq :
          ‖p + (↑s : ℂ) • v‖ ^ 2 ≤ (‖p‖ + |s| * ‖v‖) ^ 2 := by
        nlinarith [hnorm, norm_nonneg (p + (↑s : ℂ) • v)]
      have hmix :
          (‖p‖ + |s| * ‖v‖) ^ 2 ≤ (‖p‖ ^ 2 + ‖v‖ ^ 2) * (1 + s ^ 2) := by
        have hsqabs : |s| ^ 2 = s ^ 2 := by
          simpa [sq] using (sq_abs s)
        nlinarith [sq_nonneg (‖p‖ * |s| - ‖v‖), hsqabs]
      calc
        |f s| ≤ |B| * ‖p + (↑s : ℂ) • v‖ ^ 2 := hB2
        _ ≤ |B| * (‖p‖ + |s| * ‖v‖) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hsq (abs_nonneg B)
        _ ≤ |B| * ((‖p‖ ^ 2 + ‖v‖ ^ 2) * (1 + s ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hmix (abs_nonneg B)
        _ = |B| * (‖p‖ ^ 2 + ‖v‖ ^ 2) * (1 + s ^ 2) := by ring
    have htri :
        |h s| ≤ |f s| + |Qv| * s ^ 2 + |α| * |s| + |Qp| := by
      have hform : h s = f s - (Qv * s ^ 2 + α * s + Qp) := by
        simp [h]
        ring
      rw [hform]
      have hsub : f s - (Qv * s ^ 2 + α * s + Qp) = f s + (-(Qv * s ^ 2 + α * s + Qp)) := by ring
      rw [hsub]
      calc
        |f s + (-(Qv * s ^ 2 + α * s + Qp))| ≤ |f s| + |-(Qv * s ^ 2 + α * s + Qp)| := abs_add_le _ _
        _ = |f s| + |Qv * s ^ 2 + α * s + Qp| := by rw [abs_neg]
        _ ≤ |f s| + (|Qv * s ^ 2 + α * s| + |Qp|) := by
            have htmp := abs_add_le (Qv * s ^ 2 + α * s) Qp
            linarith
        _ ≤ |f s| + ((|Qv * s ^ 2| + |α * s|) + |Qp|) := by
            have htmp := abs_add_le (Qv * s ^ 2) (α * s)
            linarith
        _ = |f s| + |Qv| * s ^ 2 + |α| * |s| + |Qp| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg s)]
            ring
    have hQv_term : |Qv| * s ^ 2 ≤ |Qv| * (1 + s ^ 2) := by
      exact mul_le_mul_of_nonneg_left hs_sq (abs_nonneg Qv)
    have hα_term : |α| * |s| ≤ |α| * (1 + s ^ 2) := by
      exact mul_le_mul_of_nonneg_left hs_abs (abs_nonneg α)
    have hQp_term : |Qp| ≤ |Qp| * (1 + s ^ 2) := by
      nlinarith [abs_nonneg Qp, h1s]
    calc
      |h s| ≤ |f s| + |Qv| * s ^ 2 + |α| * |s| + |Qp| := htri
      _ ≤ |B| * (‖p‖ ^ 2 + ‖v‖ ^ 2) * (1 + s ^ 2) + |Qv| * s ^ 2 + |α| * |s| + |Qp| := by
          linarith [hf_bound]
      _ ≤ |B| * (‖p‖ ^ 2 + ‖v‖ ^ 2) * (1 + s ^ 2) +
            |Qv| * (1 + s ^ 2) + |α| * (1 + s ^ 2) + |Qp| * (1 + s ^ 2) := by
          nlinarith [hQv_term, hα_term, hQp_term]
      _ = (|B| * (‖p‖ ^ 2 + ‖v‖ ^ 2) + |Qv| + |α| + |Qp|) * (1 + s ^ 2) := by
          ring
  obtain ⟨C, hC_nn, hC⟩ := h_bound
  -- Apply midpoint theorem: h ≡ 0
  have h_zero := midpoint_additive_bounded_zero h h_mid h_0 h_1 C hC_nn hC s
  -- h(s) = 0 means f(s) = Qv·s² + α·s + Qp
  simp only [h] at h_zero; linarith

/-! ## Discriminant bound from nonnegativity

If Q(v)·s² + α·s + Q(p) ≥ 0 for all s ∈ ℝ, with Q(v), Q(p) ≥ 0,
then α² ≤ 4·Q(p)·Q(v). -/

lemma discriminant_bound_of_nonneg (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hnn : ∀ s : ℝ, 0 ≤ a * s ^ 2 + b * s + c) : b ^ 2 ≤ 4 * c * a := by
  by_cases ha0 : a = 0
  · subst ha0; simp at hnn ⊢
    by_contra hb
    have hb_ne : b ≠ 0 := fun h => hb (by rw [h])
    have heval := hnn (-(c + 1) / b)
    have hsimp : b * (-(c + 1) / b) + c = -1 := by field_simp; linarith
    linarith
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h4a_pos : (0 : ℝ) < 4 * a := by positivity
    have hmin := hnn (-b / (2 * a))
    have key : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c =
        c - b ^ 2 / (4 * a) := by field_simp; ring
    rw [key] at hmin
    have := (div_le_iff₀ h4a_pos).mp (sub_nonneg.mp hmin)
    linarith

/-! ## Continuity on the sphere from the parallelogram identity

The full parallelogram identity implies Q is Lipschitz on the unit sphere.

From `line_restriction_quadratic`: Q(p+sv) = Q(v)s² + αs + Q(p).
Since Q ≥ 0, the discriminant bound gives α² ≤ 4Q(p)Q(v).
With v = x-p: |Q(x)-Q(p)| = |α+Q(v)| ≤ |α|+Q(v) ≤ 2√(Q(p)Q(v))+Q(v) ≤ 3C‖x-p‖. -/

lemma sphere_continuous_of_full_pi
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hfull : ∀ (a b : H),
      frame_quadratic (H := H) μ (a + b) + frame_quadratic (H := H) μ (a - b) =
        2 * frame_quadratic (H := H) μ a + 2 * frame_quadratic (H := H) μ b) :
    ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1) := by
  rcases frame_quadratic_bounded (H := H) μ with ⟨C, hC⟩
  have hC_nn : 0 ≤ C := by
    haveI : Nontrivial H := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℂ H)
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have h1 := (abs_le.mp (hC x)).2
    have h2 := frame_quadratic_nonneg (H := H) μ x
    have h3 : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
    nlinarith
  apply Metric.continuousOn_iff.mpr
  intro p hp ε hε
  rw [Metric.mem_sphere] at hp
  have hp1 : ‖p‖ = 1 := by simpa [dist_zero_right] using hp
  -- Use line_restriction_quadratic: Q(p+sv) = Qv·s² + α·s + Qp
  -- With v = x-p: Q(x) = Q(x-p) + α + Q(p) where α² ≤ 4Q(p)Q(x-p)
  -- So |Q(x)-Q(p)| = |α + Q(x-p)| ≤ |α| + Q(x-p)
  -- ≤ 2√(Q(p)Q(x-p)) + Q(x-p) ≤ 2C‖x-p‖ + C‖x-p‖²
  use min 1 (ε / (3 * C + 1))
  refine ⟨by positivity, ?_⟩
  intro x hx hdist
  rw [Metric.mem_sphere] at hx
  have hx1 : ‖x‖ = 1 := by simpa [dist_zero_right] using hx
  rw [Real.dist_eq]
  set v := x - p
  have hdist' : ‖v‖ < min 1 (ε / (3 * C + 1)) := by
    rwa [dist_eq_norm] at hdist
  -- Q(p + 1·v) = Q(v)·1² + α·1 + Q(p) from line_restriction_quadratic
  have hline := line_restriction_quadratic μ hfull p v 1
  simp only [Complex.ofReal_one, one_smul, one_pow, mul_one] at hline
  -- So α = Q(p+v) - Q(v) - Q(p) = Q(x) - Q(v) - Q(p)
  set α := frame_quadratic (H := H) μ (p + v) - frame_quadratic (H := H) μ v -
    frame_quadratic (H := H) μ p
  -- Q(x) - Q(p) = α + Q(v)
  have hQdiff : frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p = α +
      frame_quadratic (H := H) μ v := by
    show frame_quadratic (H := H) μ x - frame_quadratic (H := H) μ p =
      (frame_quadratic (H := H) μ (p + v) - frame_quadratic (H := H) μ v -
        frame_quadratic (H := H) μ p) + frame_quadratic (H := H) μ v
    have : p + v = x := by simp [v]
    rw [this]; ring
  -- Discriminant bound: α² ≤ 4·Q(p)·Q(v) (from nonnegativity of Q along the line)
  have hnn : ∀ s : ℝ, 0 ≤ frame_quadratic (H := H) μ v * s ^ 2 + α * s +
      frame_quadratic (H := H) μ p := by
    intro s
    have := line_restriction_quadratic μ hfull p v s
    have := frame_quadratic_nonneg (H := H) μ (p + (↑s : ℂ) • v)
    linarith
  have hQv_nn := frame_quadratic_nonneg (H := H) μ v
  have hQp_nn := frame_quadratic_nonneg (H := H) μ p
  have hdisc := discriminant_bound_of_nonneg _ α _ hQv_nn hQp_nn hnn
  -- Bounds: Q(v) ≤ C‖v‖², Q(p) ≤ C
  have hQv_ub : frame_quadratic (H := H) μ v ≤ C * ‖v‖ ^ 2 := (abs_le.mp (hC v)).2
  have hQp_ub : frame_quadratic (H := H) μ p ≤ C := by
    have := (abs_le.mp (hC p)).2; rw [hp1] at this; linarith
  -- |α| ≤ 2√(Q(p)·Q(v)) ≤ 2C‖v‖
  have hα_sq : α ^ 2 ≤ 4 * C * (C * ‖v‖ ^ 2) := by nlinarith
  have hα_bound : |α| ≤ 2 * C * ‖v‖ := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    calc α ^ 2 ≤ 4 * C * (C * ‖v‖ ^ 2) := hα_sq
      _ = (2 * C * ‖v‖) ^ 2 := by ring
  -- |Q(x) - Q(p)| = |α + Q(v)| ≤ |α| + Q(v) ≤ 2C‖v‖ + C‖v‖²
  rw [hQdiff]
  calc |α + frame_quadratic (H := H) μ v|
      ≤ |α| + |frame_quadratic (H := H) μ v| := abs_add_le _ _
    _ = |α| + frame_quadratic (H := H) μ v := by rw [abs_of_nonneg hQv_nn]
    _ ≤ 2 * C * ‖v‖ + C * ‖v‖ ^ 2 := by linarith
    _ ≤ 2 * C * ‖v‖ + C * ‖v‖ := by
        have hv_le_1 : ‖v‖ ≤ 1 := by linarith [min_le_left 1 (ε / (3 * C + 1))]
        have : ‖v‖ ^ 2 ≤ ‖v‖ := by nlinarith [norm_nonneg v]
        nlinarith
    _ = 3 * C * ‖v‖ := by ring
    _ < ε := by
        have hv_lt : ‖v‖ < ε / (3 * C + 1) := lt_of_lt_of_le hdist' (min_le_right _ _)
        have h3C1_pos : (0 : ℝ) < 3 * C + 1 := by linarith
        have key : ‖v‖ * (3 * C + 1) < ε := by rwa [lt_div_iff₀ h3C1_pos] at hv_lt
        nlinarith [norm_nonneg v]

/-! ## Cauchy–Jensen residual

We package the CJ residual and prove basic identities that hold without
assuming CJ itself. -/

def local_defect_residual
    (μ : FrameFunction H) (u v : H) (s t : ℝ) : ℝ :=
  local_quad2DDefect μ u v 1 (s + t) +
    local_quad2DDefect μ u v 1 (s - t) -
    2 * local_quad2DDefect μ u v 1 s -
    2 * local_quad2DDefect μ u v 1 t

lemma local_defect_g_cj_of_residual_zero
    (μ : FrameFunction H) (u v : H) (s t : ℝ)
    (hres : local_defect_residual μ u v s t = 0) :
    local_defect_g μ u v (s + t) + local_defect_g μ u v (s - t) =
      2 * local_defect_g μ u v s + 2 * local_defect_g μ u v t := by
  exact GleasonBridge.local_defect_g_cj_of_inhom_jensen_of_residual_zero μ u v s t (by
    simpa [local_defect_residual, local_defect_g] using hres)

lemma local_defect_residual_zero_right
    (μ : FrameFunction H) (u v : H) (s : ℝ) :
    local_defect_residual μ u v s 0 = 0 := by
  unfold local_defect_residual
  have h0 : local_quad2DDefect μ u v 1 0 = 0 :=
    GleasonBridge.local_quad2DDefect_zero_right μ u v 1
  rw [h0]
  ring_nf

lemma local_defect_residual_zero_left
    (μ : FrameFunction H) (u v : H) (t : ℝ) :
    local_defect_residual μ u v 0 t = 0 := by
  unfold local_defect_residual
  have h0 : local_quad2DDefect μ u v 1 0 = 0 :=
    GleasonBridge.local_quad2DDefect_zero_right μ u v 1
  have heven : local_quad2DDefect μ u v 1 (-t) = local_quad2DDefect μ u v 1 t :=
    GleasonBridge.local_quad2DDefect_even_b μ u v 1 t
  simp [sub_eq_add_neg, h0, heven]
  linarith

lemma local_defect_residual_symm
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    local_defect_residual μ u v s t = local_defect_residual μ u v t s := by
  unfold local_defect_residual
  have hst : local_quad2DDefect μ u v 1 (s - t) = local_quad2DDefect μ u v 1 (t - s) := by
    have h := GleasonBridge.local_quad2DDefect_even_b μ u v 1 (t - s)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  rw [add_comm s t, hst, add_comm t s]
  ring

/-! ## Shifted-base decomposition

Translate pair defects with shifted base vectors back to the `g`/residual
language on the original orthonormal pair. -/

lemma shifted_base_pair_sum_eq_second_difference
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t +
      local_quad2DDefect μ (u - (s : ℂ) • v) v 1 t =
    local_defect_g μ u v (s + t) +
      local_defect_g μ u v (s - t) -
      2 * local_defect_g μ u v s := by
  have hpp : (u + (s : ℂ) • v) + (t : ℂ) • v = u + ((s + t : ℝ) : ℂ) • v := by
    simp [add_smul, add_assoc, add_left_comm, add_comm, Complex.ofReal_add]
  have hpm : (u + (s : ℂ) • v) - (t : ℂ) • v = u + ((s - t : ℝ) : ℂ) • v := by
    simp [sub_eq_add_neg, add_smul, add_assoc, add_left_comm, add_comm, Complex.ofReal_sub]
  have hmp : (u - (s : ℂ) • v) + (t : ℂ) • v = u - ((s - t : ℝ) : ℂ) • v := by
    simp [sub_eq_add_neg, add_smul, sub_smul, add_assoc, add_left_comm, add_comm, Complex.ofReal_sub]
  have hmm : (u - (s : ℂ) • v) - (t : ℂ) • v = u - ((s + t : ℝ) : ℂ) • v := by
    simp [sub_eq_add_neg, add_smul, sub_smul, add_assoc, add_left_comm, add_comm, Complex.ofReal_add]
  unfold local_defect_g
  simp only [local_quad2DDefect, local_quad2DExpr, Complex.ofReal_one, one_smul, one_pow, mul_one]
  rw [hpp, hpm, hmp, hmm]
  ring

lemma shifted_base_pair_sum_eq_residual
    (μ : FrameFunction H) (u v : H) (s t : ℝ) :
    local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t +
      local_quad2DDefect μ (u - (s : ℂ) • v) v 1 t =
    local_defect_residual μ u v s t + 2 * local_defect_g μ u v t := by
  calc
    local_quad2DDefect μ (u + (s : ℂ) • v) v 1 t +
        local_quad2DDefect μ (u - (s : ℂ) • v) v 1 t
        =
      local_defect_g μ u v (s + t) +
        local_defect_g μ u v (s - t) -
        2 * local_defect_g μ u v s := shifted_base_pair_sum_eq_second_difference μ u v s t
    _ = local_defect_residual μ u v s t + 2 * local_defect_g μ u v t := by
        unfold local_defect_residual local_defect_g
        ring

/-! ## Base scaling for `local_defect_g`

Scaling the base vector rescales both the value and the argument. -/

lemma local_defect_g_smul_base
    (μ : FrameFunction H) (u v : H) (r s : ℝ) (hr : r ≠ 0) :
    local_defect_g μ ((r : ℂ) • u) v s =
      r ^ 2 * local_defect_g μ u v (s / r) := by
  have hrewrite :
      local_defect_g μ ((r : ℂ) • u) v s = local_quad2DDefect μ u v r s := by
    have hru : frame_quadratic (H := H) μ ((r : ℂ) • u) =
        r ^ 2 * frame_quadratic (H := H) μ u := by
      have h := frame_quadratic_sq_hom (H := H) μ (r : ℂ) u
      simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
    have hru' : frame_quadratic (H := H) μ (r • u) =
        r ^ 2 * frame_quadratic (H := H) μ u := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r u]
      exact hru
    unfold local_defect_g local_quad2DDefect local_quad2DExpr
    simp [smul_add, smul_sub, smul_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    linarith [hru']
  rw [hrewrite]
  have hhom := GleasonBridge.local_quad2DDefect_hom μ u v r 1 (s / r)
  have hs : r * (s / r) = s := by field_simp [hr]
  calc
    local_quad2DDefect μ u v r s
        = local_quad2DDefect μ u v (r * 1) (r * (s / r)) := by simp [hs]
    _ = r ^ 2 * local_quad2DDefect μ u v 1 (s / r) := hhom
    _ = r ^ 2 * local_defect_g μ u v (s / r) := by rfl

lemma local_defect_g_normalize_base
    (μ : FrameFunction H) (x v : H) (s : ℝ) (hx : x ≠ 0) :
    let xhat : H := (↑(‖x‖⁻¹) : ℂ) • x
    local_defect_g μ x v s =
      ‖x‖ ^ 2 * local_defect_g μ xhat v (s / ‖x‖) := by
  intro xhat
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hx_eq : x = (↑‖x‖ : ℂ) • xhat := by
    dsimp [xhat]
    rw [smul_smul]
    simp [hxn]
  have hsmul :
      local_defect_g μ ((↑‖x‖ : ℂ) • xhat) v s =
        ‖x‖ ^ 2 * local_defect_g μ xhat v (s / ‖x‖) :=
    local_defect_g_smul_base μ xhat v ‖x‖ s hxn
  rw [← hx_eq] at hsmul
  exact hsmul

/-! ## Shifted-base norm formulas

For an orthonormal pair `(u,w)`, the shifted vectors `u ± c w` have
norm-squared `1 + c²`. -/

lemma norm_sq_add_smul_of_orthonormal
    (u w : H) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (huw : inner (𝕜 := ℂ) u w = 0) (c : ℝ) :
    ‖u + (c : ℂ) • w‖ ^ 2 = 1 + c ^ 2 := by
  have horth : inner (𝕜 := ℂ) u ((c : ℂ) • w) = 0 := by simp [huw]
  have hsq :
      ‖u + (c : ℂ) • w‖ ^ 2 = ‖u‖ ^ 2 + ‖(c : ℂ) • w‖ ^ 2 := by
    simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u ((c : ℂ) • w) horth
  calc
    ‖u + (c : ℂ) • w‖ ^ 2 = ‖u‖ ^ 2 + ‖(c : ℂ) • w‖ ^ 2 := hsq
    _ = 1 + c ^ 2 := by
      simp [hu, hw, norm_smul, Real.norm_eq_abs, sq_abs]

lemma norm_sq_sub_smul_of_orthonormal
    (u w : H) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (huw : inner (𝕜 := ℂ) u w = 0) (c : ℝ) :
    ‖u - (c : ℂ) • w‖ ^ 2 = 1 + c ^ 2 := by
  simpa [sub_eq_add_neg, neg_smul, neg_sq] using
    norm_sq_add_smul_of_orthonormal u w hu hw huw (-c)

lemma local_defect_g_neg_one_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0) :
    local_defect_g μ u v (-1) = 0 := by
  have heven : local_defect_g μ u v (-1) = local_defect_g μ u v 1 := by
    simpa using GleasonBridge.local_defect_g_even μ u v 1
  simpa [GleasonBridge.local_defect_g_one_eq_zero hdim μ u v hu hv huv] using heven

lemma local_defect_g_sq_one_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) (ht : t ^ 2 = 1) :
    local_defect_g μ u v t = 0 := by
  have hsq : t ^ 2 = (1 : ℝ) ^ 2 := by simpa using ht
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with ht1 | ht1
  · simpa [ht1] using GleasonBridge.local_defect_g_one_eq_zero hdim μ u v hu hv huv
  · simpa [ht1] using local_defect_g_neg_one_eq_zero hdim μ u v hu hv huv

lemma local_defect_g_zero_of_orthogonal_norm_sq
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (x v : H) (s : ℝ) (hx : x ≠ 0) (hv : ‖v‖ = 1)
    (hxv : inner (𝕜 := ℂ) x v = 0) (hsq : ‖x‖ ^ 2 = s ^ 2) :
    local_defect_g μ x v s = 0 := by
  set xhat : H := ((↑‖x‖ : ℂ)⁻¹) • x
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hxhat_norm : ‖xhat‖ = 1 := by
    simp [xhat, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ hxn]
  have hxhatv : inner (𝕜 := ℂ) xhat v = 0 := by
    simp [xhat, hxv]
  have hratio_sq : (s / ‖x‖) ^ 2 = 1 := by
    calc
      (s / ‖x‖) ^ 2 = s ^ 2 / ‖x‖ ^ 2 := by ring
      _ = 1 := by rw [← hsq, div_self (pow_ne_zero 2 hxn)]
  have hunit_zero : local_defect_g μ xhat v (s / ‖x‖) = 0 :=
    local_defect_g_sq_one_eq_zero hdim μ xhat v hxhat_norm hv hxhatv (s / ‖x‖) hratio_sq
  have hscale : local_defect_g μ x v s = ‖x‖ ^ 2 * local_defect_g μ xhat v (s / ‖x‖) := by
    simpa [xhat] using local_defect_g_normalize_base μ x v s hx
  rw [hscale, hunit_zero, mul_zero]


end
