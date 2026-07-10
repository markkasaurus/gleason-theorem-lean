import SphericalHarmonics.Density
import SphericalHarmonics.Orthogonality
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.L2Space

open scoped BigOperators

namespace SphericalHarmonics

set_option maxHeartbeats 400000 in
/-- The counterclockwise `(0,1)`-plane rotation applied to a point of `ℝ^3`.
This is the pointwise action of `rotation01 t`.symm used to differentiate polynomial pullbacks. -/
noncomputable def rot01Point (t : ℝ) (x : E3) : E3 :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm <|
    fun
    | 0 => Real.cos t * x 0 - Real.sin t * x 1
    | 1 => Real.sin t * x 0 + Real.cos t * x 1
    | 2 => x 2

@[simp] theorem rot01Point_apply_zero (t : ℝ) (x : E3) :
    rot01Point t x 0 = Real.cos t * x 0 - Real.sin t * x 1 := by
  simp [rot01Point]

@[simp] theorem rot01Point_apply_one (t : ℝ) (x : E3) :
    rot01Point t x 1 = Real.sin t * x 0 + Real.cos t * x 1 := by
  simp [rot01Point]

@[simp] theorem rot01Point_apply_two (t : ℝ) (x : E3) :
    rot01Point t x 2 = x 2 := by
  simp [rot01Point]

theorem hasDerivAt_rot01Point_zero (x : E3) (t : ℝ) :
    HasDerivAt (fun s => rot01Point s x 0) (-rot01Point t x 1) t := by
  simp [rot01Point_apply_zero, rot01Point_apply_one]
  convert ((Real.hasDerivAt_cos t).mul_const (x 0)).sub
      ((Real.hasDerivAt_sin t).mul_const (x 1)) using 1
  ring

theorem hasDerivAt_rot01Point_one (x : E3) (t : ℝ) :
    HasDerivAt (fun s => rot01Point s x 1) (rot01Point t x 0) t := by
  simp [rot01Point_apply_zero, rot01Point_apply_one]
  convert ((Real.hasDerivAt_sin t).mul_const (x 0)).add
      ((Real.hasDerivAt_cos t).mul_const (x 1)) using 1
  ring

theorem hasDerivAt_rot01Point_two (x : E3) (t : ℝ) :
    HasDerivAt (fun s => rot01Point s x 2) 0 t := by
  simpa [rot01Point_apply_two] using hasDerivAt_const t (x 2)

theorem eval_angularDeriv_mul_X_zero (p : Poly3) (x : E3) :
    MvPolynomial.eval x.ofLp (angularDeriv 0 1 (p * MvPolynomial.X 0)) =
      MvPolynomial.eval x.ofLp (angularDeriv 0 1 p) * x 0 - x 1 * MvPolynomial.eval x.ofLp p := by
  simp [angularDeriv, MvPolynomial.pderiv_mul, sub_eq_add_neg]
  ring

theorem eval_angularDeriv_mul_X_one (p : Poly3) (x : E3) :
    MvPolynomial.eval x.ofLp (angularDeriv 0 1 (p * MvPolynomial.X 1)) =
      MvPolynomial.eval x.ofLp (angularDeriv 0 1 p) * x 1 + x 0 * MvPolynomial.eval x.ofLp p := by
  simp [angularDeriv, MvPolynomial.pderiv_mul, sub_eq_add_neg]
  ring

theorem eval_angularDeriv_mul_X_two (p : Poly3) (x : E3) :
    MvPolynomial.eval x.ofLp (angularDeriv 0 1 (p * MvPolynomial.X 2)) =
      MvPolynomial.eval x.ofLp (angularDeriv 0 1 p) * x 2 := by
  simp [angularDeriv, MvPolynomial.pderiv_mul, sub_eq_add_neg]
  ring

theorem hasDerivAt_eval_rot01Point (p : Poly3) (x : E3) (t : ℝ) :
    HasDerivAt (fun s => MvPolynomial.eval (rot01Point s x).ofLp p)
      (MvPolynomial.eval (rot01Point t x).ofLp (angularDeriv 0 1 p)) t := by
  refine MvPolynomial.induction_on (motive := fun p : Poly3 =>
    HasDerivAt (fun s => MvPolynomial.eval (rot01Point s x).ofLp p)
      (MvPolynomial.eval (rot01Point t x).ofLp (angularDeriv 0 1 p)) t) p ?_ ?_ ?_
  · intro a
    simpa [angularDeriv] using hasDerivAt_const t a
  · intro p q hp hq
    convert hp.add hq using 1
    · ext s
      simp [MvPolynomial.eval_add]
    · simp [angularDeriv, sub_eq_add_neg, left_distrib]
      ring
  · intro p i hp
    fin_cases i
    · convert hp.mul (hasDerivAt_rot01Point_zero x t) using 1
      · ext s
        simp [MvPolynomial.eval_mul]
      · convert eval_angularDeriv_mul_X_zero p (rot01Point t x) using 1
        ring
    · convert hp.mul (hasDerivAt_rot01Point_one x t) using 1
      · ext s
        simp [MvPolynomial.eval_mul]
      · simpa [rot01Point_apply_zero, rot01Point_apply_one, mul_comm, mul_left_comm, mul_assoc] using
          eval_angularDeriv_mul_X_one p (rot01Point t x)
    · convert hp.mul (hasDerivAt_rot01Point_two x t) using 1
      · ext s
        simp [MvPolynomial.eval_mul]
      · simpa [rot01Point_apply_two] using
          eval_angularDeriv_mul_X_two p (rot01Point t x)

theorem rot01Point_add (s t : ℝ) (x : E3) :
    rot01Point s (rot01Point t x) = rot01Point (s + t) x := by
  ext i
  fin_cases i
  · simp [rot01Point, Real.cos_add, Real.sin_add]
    ring
  · simp [rot01Point, Real.cos_add, Real.sin_add]
    ring
  · simp [rot01Point]

@[simp] theorem rot01Point_zero (x : E3) : rot01Point 0 x = x := by
  ext i
  fin_cases i <;> simp [rot01Point]

@[simp] theorem rot01Point_neg_add_self (t : ℝ) (x : E3) :
    rot01Point (-t) (rot01Point t x) = x := by
  simpa using rot01Point_add (-t) t x

@[simp] theorem rot01Point_add_neg_self (t : ℝ) (x : E3) :
    rot01Point t (rot01Point (-t) x) = x := by
  simpa [add_comm] using rot01Point_add t (-t) x

theorem rot01Point_norm_sq (t : ℝ) (x : E3) :
    ‖rot01Point t x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three]
  simp [rot01Point_apply_zero, rot01Point_apply_one, rot01Point_apply_two, pow_two]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq t]

noncomputable def rot01Linear (t : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun x := rot01Point t x
  map_add' x y := by
    ext i
    fin_cases i <;> simp [rot01Point] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [rot01Point] <;> ring

noncomputable def rot01LinearIsometry (t : ℝ) : E3 →ₗᵢ[ℝ] E3 :=
  (rot01Linear t).toLinearIsometry <| by
    intro x y
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← (rot01Linear t).map_sub]
    have hsq := rot01Point_norm_sq t (x - y)
    exact congrArg ENNReal.ofReal <|
      sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp <| by simpa [rot01Linear] using hsq

/-- The clockwise ambient rotation in the `(0,1)`-plane. Its inverse acts by `rot01Point t`. -/
noncomputable def rotation01 (t : ℝ) : Rotation :=
  LinearIsometryEquiv.ofLinearIsometry
    (rot01LinearIsometry (-t))
    (rot01Linear t)
    (by
      ext x i
      change rot01Point (-t) (rot01Point t x) i = x i
      simpa using congrArg (fun z : E3 => z i) (rot01Point_neg_add_self t x))
    (by
      ext x i
      change rot01Point t (rot01Point (-t) x) i = x i
      simpa using congrArg (fun z : E3 => z i) (rot01Point_add_neg_self t x))

@[simp] theorem rotation01_apply (t : ℝ) (x : E3) :
    rotation01 t x = rot01Point (-t) x := rfl

@[simp] theorem rotation01_symm_apply (t : ℝ) (x : E3) :
    (rotation01 t).symm x = rot01Point t x := rfl

noncomputable def rot01Eval (p : Poly3) (t : ℝ) (x : S2) : ℝ :=
  MvPolynomial.eval (rot01Point t (x : E3)).ofLp p

noncomputable def rot01Integrand (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot01Eval p t x * rot01Eval q t x

noncomputable def rot01IntegrandDeriv (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot01Eval (angularDeriv 0 1 p) t x * rot01Eval q t x +
    rot01Eval p t x * rot01Eval (angularDeriv 0 1 q) t x

theorem rotation01_measurePreserving (t : ℝ) :
    MeasureTheory.MeasurePreserving
      ((Rotation.toSphereEquiv ((rotation01 t).symm)).toHomeomorph.toMeasurableEquiv)
      rotationMeasure rotationMeasure := by
  refine ⟨((Rotation.toSphereEquiv ((rotation01 t).symm)).toHomeomorph.toMeasurableEquiv).measurable, ?_⟩
  simpa using Rotation.map_rotationMeasure ((rotation01 t).symm)

theorem integral_rot01Integrand_eq_zero_time (p q : Poly3) (t : ℝ) :
    ∫ x, rot01Integrand p q t x ∂rotationMeasure =
      ∫ x, rot01Integrand p q 0 x ∂rotationMeasure := by
  let e : S2 ≃ᵐ S2 :=
    (Rotation.toSphereEquiv ((rotation01 t).symm)).toHomeomorph.toMeasurableEquiv
  let g : S2 → ℝ := rot01Integrand p q 0
  have hpres : MeasureTheory.MeasurePreserving e rotationMeasure rotationMeasure :=
    rotation01_measurePreserving t
  calc
    ∫ x, rot01Integrand p q t x ∂rotationMeasure
        = ∫ x, g (e x) ∂rotationMeasure := by
            simp [rot01Integrand, rot01Eval, g, e, rot01Point_zero, rotation01_symm_apply]
    _ = ∫ y, g y ∂rotationMeasure := hpres.integral_comp' g

theorem continuous_rot01Point_uncurry : Continuous (fun z : ℝ × E3 => rot01Point z.1 z.2) := by
  let e := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm
  have hcoords : Continuous (fun z : ℝ × E3 =>
      fun i : Fin 3 =>
        match i with
        | 0 => Real.cos z.1 * z.2 0 - Real.sin z.1 * z.2 1
        | 1 => Real.sin z.1 * z.2 0 + Real.cos z.1 * z.2 1
        | 2 => z.2 2) := by
    have h0 : Continuous (fun z : ℝ × E3 => z.2 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp continuous_snd
    have h1 : Continuous (fun z : ℝ × E3 => z.2 1) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).comp continuous_snd
    have h2 : Continuous (fun z : ℝ × E3 => z.2 2) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).comp continuous_snd
    apply continuous_pi
    intro i
    fin_cases i
    · exact ((Real.continuous_cos.comp continuous_fst).mul h0).sub
        ((Real.continuous_sin.comp continuous_fst).mul h1)
    · exact ((Real.continuous_sin.comp continuous_fst).mul h0).add
        ((Real.continuous_cos.comp continuous_fst).mul h1)
    · simpa using h2
  simpa [rot01Point] using e.continuous.comp hcoords

theorem continuous_rot01Eval_uncurry (p : Poly3) :
    Continuous (fun z : ℝ × S2 => rot01Eval p z.1 z.2) := by
  have hpoint : Continuous (fun z : ℝ × S2 => rot01Point z.1 (z.2 : E3)) := by
    have hmap : Continuous (fun z : ℝ × S2 => (z.1, (z.2 : E3))) := by
      continuity
    simpa using continuous_rot01Point_uncurry.comp hmap
  simpa [rot01Eval] using
    ((MvPolynomial.continuous_eval p).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))).comp hpoint

theorem continuous_rot01Integrand_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot01Integrand p q z.1 z.2) := by
  simp [rot01Integrand]
  exact (continuous_rot01Eval_uncurry p).mul (continuous_rot01Eval_uncurry q)

theorem continuous_rot01IntegrandDeriv_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot01IntegrandDeriv p q z.1 z.2) := by
  simp [rot01IntegrandDeriv]
  exact
    ((continuous_rot01Eval_uncurry (angularDeriv 0 1 p)).mul
      (continuous_rot01Eval_uncurry q)).add
      ((continuous_rot01Eval_uncurry p).mul
        (continuous_rot01Eval_uncurry (angularDeriv 0 1 q)))

theorem continuous_rot01Integrand (p q : Poly3) (t : ℝ) :
    Continuous (rot01Integrand p q t) := by
  have hmap : Continuous (fun x : S2 => (t, x)) := by
    continuity
  simpa using (continuous_rot01Integrand_uncurry p q).comp hmap

theorem continuous_rot01IntegrandDeriv (p q : Poly3) (t : ℝ) :
    Continuous (rot01IntegrandDeriv p q t) := by
  have hmap : Continuous (fun x : S2 => (t, x)) := by
    continuity
  simpa using (continuous_rot01IntegrandDeriv_uncurry p q).comp hmap

theorem hasDerivAt_rot01Integrand (p q : Poly3) (t : ℝ) (x : S2) :
    HasDerivAt (fun s => rot01Integrand p q s x) (rot01IntegrandDeriv p q t x) t := by
  simp [rot01Integrand, rot01IntegrandDeriv]
  exact (hasDerivAt_eval_rot01Point p (x : E3) t).mul (hasDerivAt_eval_rot01Point q (x : E3) t)

theorem integrable_of_continuous_sphere {f : S2 → ℝ} (hf : Continuous f) :
    MeasureTheory.Integrable f rotationMeasure := by
  simpa [MeasureTheory.integrableOn_univ, MeasureTheory.Measure.restrict_univ] using
    hf.continuousOn.integrableOn_compact (μ := rotationMeasure) isCompact_univ

theorem exists_bound_rot01IntegrandDeriv (p q : Poly3) :
    ∃ C : ℝ, ∀ t ∈ Metric.ball (0 : ℝ) 1, ∀ x : S2, ‖rot01IntegrandDeriv p q t x‖ ≤ C := by
  let f : ℝ × S2 → ℝ := fun z => rot01IntegrandDeriv p q z.1 z.2
  have hcompact : IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ (Set.univ : Set S2)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn (continuous_rot01IntegrandDeriv_uncurry p q).continuousOn
  refine ⟨C, ?_⟩
  intro t ht x
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact ⟨by linarith [abs_lt.mp ht |>.1], by linarith [abs_lt.mp ht |>.2]⟩
  exact hC (t, x) ⟨ht', trivial⟩

theorem integral_rot01IntegrandDeriv_zero (p q : Poly3) :
    ∫ x, rot01IntegrandDeriv p q 0 x ∂rotationMeasure = 0 := by
  obtain ⟨C, hC⟩ := exists_bound_rot01IntegrandDeriv p q
  obtain ⟨-, hderiv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := rotationMeasure) (x₀ := (0 : ℝ)) (ε := 1)
      (by norm_num)
      (Filter.Eventually.of_forall fun t =>
        (continuous_rot01Integrand p q t).aestronglyMeasurable)
      (integrable_of_continuous_sphere (continuous_rot01Integrand p q 0))
      ((continuous_rot01IntegrandDeriv p q 0).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x t ht => hC t ht x)
      (show MeasureTheory.Integrable (fun _ : S2 => C) rotationMeasure by
        simpa using (MeasureTheory.integrable_const C))
      (Filter.Eventually.of_forall fun x t ht =>
        hasDerivAt_rot01Integrand p q t x)
  have hconst :
      HasDerivAt (fun u => ∫ x, rot01Integrand p q u x ∂rotationMeasure) 0 0 := by
    convert hasDerivAt_const (0 : ℝ) (∫ x, rot01Integrand p q 0 x ∂rotationMeasure) using 1
    ext u
    exact integral_rot01Integrand_eq_zero_time p q u
  exact (hconst.unique hderiv).symm

theorem inner_rot01_skew_add (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 0 1 p)))
        (continuousToLp (restrictToSphere q)) +
      inner ℝ
        (continuousToLp (restrictToSphere p))
        (continuousToLp (restrictToSphere (angularDeriv 0 1 q))) = 0 := by
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (restrictToSphere (angularDeriv 0 1 p))
      (restrictToSphere q)]
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (restrictToSphere p)
      (restrictToSphere (angularDeriv 0 1 q))]
  simp [starRingEnd_apply, mul_comm, mul_left_comm, mul_assoc]
  have h1 : MeasureTheory.Integrable
      (fun x : S2 =>
        MvPolynomial.eval x.1.ofLp p * MvPolynomial.eval x.1.ofLp (angularDeriv 0 1 q))
      rotationMeasure := by
    exact integrable_of_continuous_sphere
      ((restrictToSphere p).continuous.mul (restrictToSphere (angularDeriv 0 1 q)).continuous)
  have h2 : MeasureTheory.Integrable
      (fun x : S2 =>
        MvPolynomial.eval x.1.ofLp q * MvPolynomial.eval x.1.ofLp (angularDeriv 0 1 p))
      rotationMeasure := by
    exact integrable_of_continuous_sphere
      ((restrictToSphere q).continuous.mul (restrictToSphere (angularDeriv 0 1 p)).continuous)
  rw [← MeasureTheory.integral_add h2 h1]
  simpa [rot01IntegrandDeriv, rot01Integrand, rot01Eval, restrictToSphere_apply,
    rot01Point_zero, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    using integral_rot01IntegrandDeriv_zero p q

theorem inner_rot01_skew (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 0 1 p)))
        (continuousToLp (restrictToSphere q)) =
      -inner ℝ
        (continuousToLp (restrictToSphere p))
        (continuousToLp (restrictToSphere (angularDeriv 0 1 q))) := by
  exact eq_neg_iff_add_eq_zero.2 (inner_rot01_skew_add p q)

/-- The counterclockwise `(1,2)`-plane rotation applied to a point of `ℝ^3`. -/
noncomputable def rot12Point (t : ℝ) (x : E3) : E3 :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm <|
    fun
    | 0 => x 0
    | 1 => Real.cos t * x 1 - Real.sin t * x 2
    | 2 => Real.sin t * x 1 + Real.cos t * x 2

@[simp] theorem rot12Point_apply_zero (t : ℝ) (x : E3) :
    rot12Point t x 0 = x 0 := by simp [rot12Point]

@[simp] theorem rot12Point_apply_one (t : ℝ) (x : E3) :
    rot12Point t x 1 = Real.cos t * x 1 - Real.sin t * x 2 := by simp [rot12Point]

@[simp] theorem rot12Point_apply_two (t : ℝ) (x : E3) :
    rot12Point t x 2 = Real.sin t * x 1 + Real.cos t * x 2 := by simp [rot12Point]

theorem hasDerivAt_rot12Point_zero (x : E3) (t : ℝ) :
    HasDerivAt (fun s => rot12Point s x 0) 0 t := by
  simpa [rot12Point_apply_zero] using hasDerivAt_const t (x 0)

theorem hasDerivAt_rot12Point_one (x : E3) (t : ℝ) :
    HasDerivAt (fun s => rot12Point s x 1) (-rot12Point t x 2) t := by
  simp [rot12Point_apply_one, rot12Point_apply_two]
  convert ((Real.hasDerivAt_cos t).mul_const (x 1)).sub
      ((Real.hasDerivAt_sin t).mul_const (x 2)) using 1
  ring

theorem hasDerivAt_rot12Point_two (x : E3) (t : ℝ) :
    HasDerivAt (fun s => rot12Point s x 2) (rot12Point t x 1) t := by
  simp [rot12Point_apply_one, rot12Point_apply_two]
  convert ((Real.hasDerivAt_sin t).mul_const (x 1)).add
      ((Real.hasDerivAt_cos t).mul_const (x 2)) using 1
  ring

theorem eval_angularDeriv12_mul_X_zero (p : Poly3) (x : E3) :
    MvPolynomial.eval x.ofLp (angularDeriv 1 2 (p * MvPolynomial.X 0)) =
      MvPolynomial.eval x.ofLp (angularDeriv 1 2 p) * x 0 := by
  simp [angularDeriv, sub_eq_add_neg]
  ring

theorem eval_angularDeriv12_mul_X_one (p : Poly3) (x : E3) :
    MvPolynomial.eval x.ofLp (angularDeriv 1 2 (p * MvPolynomial.X 1)) =
      MvPolynomial.eval x.ofLp (angularDeriv 1 2 p) * x 1 - x 2 * MvPolynomial.eval x.ofLp p := by
  simp [angularDeriv, sub_eq_add_neg]
  ring

theorem eval_angularDeriv12_mul_X_two (p : Poly3) (x : E3) :
    MvPolynomial.eval x.ofLp (angularDeriv 1 2 (p * MvPolynomial.X 2)) =
      MvPolynomial.eval x.ofLp (angularDeriv 1 2 p) * x 2 + x 1 * MvPolynomial.eval x.ofLp p := by
  simp [angularDeriv, sub_eq_add_neg]
  ring

theorem hasDerivAt_eval_rot12Point (p : Poly3) (x : E3) (t : ℝ) :
    HasDerivAt (fun s => MvPolynomial.eval (rot12Point s x).ofLp p)
      (MvPolynomial.eval (rot12Point t x).ofLp (angularDeriv 1 2 p)) t := by
  refine MvPolynomial.induction_on (motive := fun p : Poly3 =>
    HasDerivAt (fun s => MvPolynomial.eval (rot12Point s x).ofLp p)
      (MvPolynomial.eval (rot12Point t x).ofLp (angularDeriv 1 2 p)) t) p ?_ ?_ ?_
  · intro a
    simpa [angularDeriv] using hasDerivAt_const t a
  · intro p q hp hq
    convert hp.add hq using 1
    · ext s
      simp [MvPolynomial.eval_add]
    · simp [angularDeriv, sub_eq_add_neg, left_distrib]
      ring
  · intro p i hp
    fin_cases i
    · convert hp.mul (hasDerivAt_rot12Point_zero x t) using 1
      · ext s
        simp [MvPolynomial.eval_mul]
      · simpa [rot12Point_apply_zero] using eval_angularDeriv12_mul_X_zero p (rot12Point t x)
    · convert hp.mul (hasDerivAt_rot12Point_one x t) using 1
      · ext s
        simp [MvPolynomial.eval_mul]
      · convert eval_angularDeriv12_mul_X_one p (rot12Point t x) using 1
        ring
    · convert hp.mul (hasDerivAt_rot12Point_two x t) using 1
      · ext s
        simp [MvPolynomial.eval_mul]
      · simpa [rot12Point_apply_one, rot12Point_apply_two, mul_comm, mul_left_comm, mul_assoc] using
          eval_angularDeriv12_mul_X_two p (rot12Point t x)

theorem rot12Point_add (s t : ℝ) (x : E3) :
    rot12Point s (rot12Point t x) = rot12Point (s + t) x := by
  ext i
  fin_cases i
  · simp [rot12Point]
  · simp [rot12Point, Real.cos_add, Real.sin_add]
    ring
  · simp [rot12Point, Real.cos_add, Real.sin_add]
    ring

@[simp] theorem rot12Point_zero (x : E3) : rot12Point 0 x = x := by
  ext i
  fin_cases i <;> simp [rot12Point]

@[simp] theorem rot12Point_neg_add_self (t : ℝ) (x : E3) :
    rot12Point (-t) (rot12Point t x) = x := by simpa using rot12Point_add (-t) t x

@[simp] theorem rot12Point_add_neg_self (t : ℝ) (x : E3) :
    rot12Point t (rot12Point (-t) x) = x := by simpa [add_comm] using rot12Point_add t (-t) x

theorem rot12Point_norm_sq (t : ℝ) (x : E3) :
    ‖rot12Point t x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three]
  simp [rot12Point_apply_zero, rot12Point_apply_one, rot12Point_apply_two, pow_two]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq t]

noncomputable def rot12Linear (t : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun x := rot12Point t x
  map_add' x y := by
    ext i
    fin_cases i <;> simp [rot12Point] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [rot12Point] <;> ring

noncomputable def rot12LinearIsometry (t : ℝ) : E3 →ₗᵢ[ℝ] E3 :=
  (rot12Linear t).toLinearIsometry <| by
    intro x y
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← (rot12Linear t).map_sub]
    have hsq := rot12Point_norm_sq t (x - y)
    exact congrArg ENNReal.ofReal <|
      sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp <| by simpa [rot12Linear] using hsq

noncomputable def rotation12 (t : ℝ) : Rotation :=
  LinearIsometryEquiv.ofLinearIsometry
    (rot12LinearIsometry (-t))
    (rot12Linear t)
    (by
      ext x i
      change rot12Point (-t) (rot12Point t x) i = x i
      simpa using congrArg (fun z : E3 => z i) (rot12Point_neg_add_self t x))
    (by
      ext x i
      change rot12Point t (rot12Point (-t) x) i = x i
      simpa using congrArg (fun z : E3 => z i) (rot12Point_add_neg_self t x))

@[simp] theorem rotation12_apply (t : ℝ) (x : E3) :
    rotation12 t x = rot12Point (-t) x := rfl

@[simp] theorem rotation12_symm_apply (t : ℝ) (x : E3) :
    (rotation12 t).symm x = rot12Point t x := rfl

noncomputable def rot12Eval (p : Poly3) (t : ℝ) (x : S2) : ℝ :=
  MvPolynomial.eval (rot12Point t (x : E3)).ofLp p

noncomputable def rot12Integrand (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot12Eval p t x * rot12Eval q t x

noncomputable def rot12IntegrandDeriv (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot12Eval (angularDeriv 1 2 p) t x * rot12Eval q t x +
    rot12Eval p t x * rot12Eval (angularDeriv 1 2 q) t x

theorem rotation12_measurePreserving (t : ℝ) :
    MeasureTheory.MeasurePreserving
      ((Rotation.toSphereEquiv ((rotation12 t).symm)).toHomeomorph.toMeasurableEquiv)
      rotationMeasure rotationMeasure := by
  refine ⟨((Rotation.toSphereEquiv ((rotation12 t).symm)).toHomeomorph.toMeasurableEquiv).measurable, ?_⟩
  simpa using Rotation.map_rotationMeasure ((rotation12 t).symm)

theorem integral_rot12Integrand_eq_zero_time (p q : Poly3) (t : ℝ) :
    ∫ x, rot12Integrand p q t x ∂rotationMeasure =
      ∫ x, rot12Integrand p q 0 x ∂rotationMeasure := by
  let e : S2 ≃ᵐ S2 :=
    (Rotation.toSphereEquiv ((rotation12 t).symm)).toHomeomorph.toMeasurableEquiv
  let g : S2 → ℝ := rot12Integrand p q 0
  have hpres : MeasureTheory.MeasurePreserving e rotationMeasure rotationMeasure :=
    rotation12_measurePreserving t
  calc
    ∫ x, rot12Integrand p q t x ∂rotationMeasure
        = ∫ x, g (e x) ∂rotationMeasure := by
            simp [rot12Integrand, rot12Eval, g, e, rot12Point_zero, rotation12_symm_apply]
    _ = ∫ y, g y ∂rotationMeasure := hpres.integral_comp' g

theorem continuous_rot12Point_uncurry : Continuous (fun z : ℝ × E3 => rot12Point z.1 z.2) := by
  let e := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm
  have hcoords : Continuous (fun z : ℝ × E3 =>
      fun i : Fin 3 =>
        match i with
        | 0 => z.2 0
        | 1 => Real.cos z.1 * z.2 1 - Real.sin z.1 * z.2 2
        | 2 => Real.sin z.1 * z.2 1 + Real.cos z.1 * z.2 2) := by
    have h0 : Continuous (fun z : ℝ × E3 => z.2 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp continuous_snd
    have h1 : Continuous (fun z : ℝ × E3 => z.2 1) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).comp continuous_snd
    have h2 : Continuous (fun z : ℝ × E3 => z.2 2) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).comp continuous_snd
    apply continuous_pi
    intro i
    fin_cases i
    · simpa using h0
    · exact ((Real.continuous_cos.comp continuous_fst).mul h1).sub
        ((Real.continuous_sin.comp continuous_fst).mul h2)
    · exact ((Real.continuous_sin.comp continuous_fst).mul h1).add
        ((Real.continuous_cos.comp continuous_fst).mul h2)
  simpa [rot12Point] using e.continuous.comp hcoords

theorem continuous_rot12Eval_uncurry (p : Poly3) :
    Continuous (fun z : ℝ × S2 => rot12Eval p z.1 z.2) := by
  have hpoint : Continuous (fun z : ℝ × S2 => rot12Point z.1 (z.2 : E3)) := by
    have hmap : Continuous (fun z : ℝ × S2 => (z.1, (z.2 : E3))) := by continuity
    simpa using continuous_rot12Point_uncurry.comp hmap
  simpa [rot12Eval] using
    ((MvPolynomial.continuous_eval p).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))).comp hpoint

theorem continuous_rot12Integrand_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot12Integrand p q z.1 z.2) := by
  simp [rot12Integrand]
  exact (continuous_rot12Eval_uncurry p).mul (continuous_rot12Eval_uncurry q)

theorem continuous_rot12IntegrandDeriv_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot12IntegrandDeriv p q z.1 z.2) := by
  simp [rot12IntegrandDeriv]
  exact
    ((continuous_rot12Eval_uncurry (angularDeriv 1 2 p)).mul
      (continuous_rot12Eval_uncurry q)).add
      ((continuous_rot12Eval_uncurry p).mul
        (continuous_rot12Eval_uncurry (angularDeriv 1 2 q)))

theorem continuous_rot12Integrand (p q : Poly3) (t : ℝ) :
    Continuous (rot12Integrand p q t) := by
  have hmap : Continuous (fun x : S2 => (t, x)) := by continuity
  simpa using (continuous_rot12Integrand_uncurry p q).comp hmap

theorem continuous_rot12IntegrandDeriv (p q : Poly3) (t : ℝ) :
    Continuous (rot12IntegrandDeriv p q t) := by
  have hmap : Continuous (fun x : S2 => (t, x)) := by continuity
  simpa using (continuous_rot12IntegrandDeriv_uncurry p q).comp hmap

theorem hasDerivAt_rot12Integrand (p q : Poly3) (t : ℝ) (x : S2) :
    HasDerivAt (fun s => rot12Integrand p q s x) (rot12IntegrandDeriv p q t x) t := by
  simp [rot12Integrand, rot12IntegrandDeriv]
  exact (hasDerivAt_eval_rot12Point p (x : E3) t).mul (hasDerivAt_eval_rot12Point q (x : E3) t)

theorem exists_bound_rot12IntegrandDeriv (p q : Poly3) :
    ∃ C : ℝ, ∀ t ∈ Metric.ball (0 : ℝ) 1, ∀ x : S2, ‖rot12IntegrandDeriv p q t x‖ ≤ C := by
  let f : ℝ × S2 → ℝ := fun z => rot12IntegrandDeriv p q z.1 z.2
  have hcompact : IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ (Set.univ : Set S2)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn (continuous_rot12IntegrandDeriv_uncurry p q).continuousOn
  refine ⟨C, ?_⟩
  intro t ht x
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact ⟨by linarith [abs_lt.mp ht |>.1], by linarith [abs_lt.mp ht |>.2]⟩
  exact hC (t, x) ⟨ht', trivial⟩

theorem integral_rot12IntegrandDeriv_zero (p q : Poly3) :
    ∫ x, rot12IntegrandDeriv p q 0 x ∂rotationMeasure = 0 := by
  obtain ⟨C, hC⟩ := exists_bound_rot12IntegrandDeriv p q
  obtain ⟨-, hderiv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := rotationMeasure) (x₀ := (0 : ℝ)) (ε := 1)
      (by norm_num)
      (Filter.Eventually.of_forall fun t =>
        (continuous_rot12Integrand p q t).aestronglyMeasurable)
      (integrable_of_continuous_sphere (continuous_rot12Integrand p q 0))
      ((continuous_rot12IntegrandDeriv p q 0).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x t ht => hC t ht x)
      (show MeasureTheory.Integrable (fun _ : S2 => C) rotationMeasure by
        simpa using (MeasureTheory.integrable_const C))
      (Filter.Eventually.of_forall fun x t ht =>
        hasDerivAt_rot12Integrand p q t x)
  have hconst :
      HasDerivAt (fun u => ∫ x, rot12Integrand p q u x ∂rotationMeasure) 0 0 := by
    convert hasDerivAt_const (0 : ℝ) (∫ x, rot12Integrand p q 0 x ∂rotationMeasure) using 1
    ext u
    exact integral_rot12Integrand_eq_zero_time p q u
  exact (hconst.unique hderiv).symm

theorem inner_rot12_skew_add (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 1 2 p)))
        (continuousToLp (restrictToSphere q)) +
      inner ℝ
        (continuousToLp (restrictToSphere p))
        (continuousToLp (restrictToSphere (angularDeriv 1 2 q))) = 0 := by
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (restrictToSphere (angularDeriv 1 2 p))
      (restrictToSphere q)]
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (restrictToSphere p)
      (restrictToSphere (angularDeriv 1 2 q))]
  simp [mul_comm]
  have h1 : MeasureTheory.Integrable
      (fun x : S2 =>
        MvPolynomial.eval x.1.ofLp p * MvPolynomial.eval x.1.ofLp (angularDeriv 1 2 q))
      rotationMeasure := by
    exact integrable_of_continuous_sphere
      ((restrictToSphere p).continuous.mul (restrictToSphere (angularDeriv 1 2 q)).continuous)
  have h2 : MeasureTheory.Integrable
      (fun x : S2 =>
        MvPolynomial.eval x.1.ofLp q * MvPolynomial.eval x.1.ofLp (angularDeriv 1 2 p))
      rotationMeasure := by
    exact integrable_of_continuous_sphere
      ((restrictToSphere q).continuous.mul (restrictToSphere (angularDeriv 1 2 p)).continuous)
  rw [← MeasureTheory.integral_add h2 h1]
  simpa [rot12IntegrandDeriv, rot12Integrand, rot12Eval, restrictToSphere_apply,
    rot12Point_zero, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    using integral_rot12IntegrandDeriv_zero p q

theorem inner_rot12_skew (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 1 2 p)))
        (continuousToLp (restrictToSphere q)) =
      -inner ℝ
        (continuousToLp (restrictToSphere p))
        (continuousToLp (restrictToSphere (angularDeriv 1 2 q))) := by
  exact eq_neg_iff_add_eq_zero.2 (inner_rot12_skew_add p q)

/-- The counterclockwise `(2,0)`-plane rotation applied to a point of `ℝ^3`. -/
noncomputable def rot20Point (t : ℝ) (x : E3) : E3 :=
  (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm <|
    fun
    | 0 => Real.sin t * x 2 + Real.cos t * x 0
    | 1 => x 1
    | 2 => Real.cos t * x 2 - Real.sin t * x 0

@[simp] theorem rot20Point_apply_zero (t : ℝ) (x : E3) :
    rot20Point t x 0 = Real.sin t * x 2 + Real.cos t * x 0 := by simp [rot20Point]

@[simp] theorem rot20Point_apply_one (t : ℝ) (x : E3) :
    rot20Point t x 1 = x 1 := by simp [rot20Point]

@[simp] theorem rot20Point_apply_two (t : ℝ) (x : E3) :
    rot20Point t x 2 = Real.cos t * x 2 - Real.sin t * x 0 := by simp [rot20Point]

theorem hasDerivAt_rot20Point_zero (x : E3) (t : ℝ) :
    HasDerivAt (fun s => rot20Point s x 0) (rot20Point t x 2) t := by
  simp [rot20Point_apply_zero, rot20Point_apply_two]
  convert ((Real.hasDerivAt_sin t).mul_const (x 2)).add
      ((Real.hasDerivAt_cos t).mul_const (x 0)) using 1
  ring

theorem hasDerivAt_rot20Point_one (x : E3) (t : ℝ) :
    HasDerivAt (fun s => rot20Point s x 1) 0 t := by
  simpa [rot20Point_apply_one] using hasDerivAt_const t (x 1)

theorem hasDerivAt_rot20Point_two (x : E3) (t : ℝ) :
    HasDerivAt (fun s => rot20Point s x 2) (-rot20Point t x 0) t := by
  simp [rot20Point_apply_zero, rot20Point_apply_two]
  convert ((Real.hasDerivAt_cos t).mul_const (x 2)).sub
      ((Real.hasDerivAt_sin t).mul_const (x 0)) using 1
  ring

theorem eval_angularDeriv20_mul_X_zero (p : Poly3) (x : E3) :
    MvPolynomial.eval x.ofLp (angularDeriv 2 0 (p * MvPolynomial.X 0)) =
      MvPolynomial.eval x.ofLp (angularDeriv 2 0 p) * x 0 + x 2 * MvPolynomial.eval x.ofLp p := by
  simp [angularDeriv, sub_eq_add_neg]
  ring

theorem eval_angularDeriv20_mul_X_one (p : Poly3) (x : E3) :
    MvPolynomial.eval x.ofLp (angularDeriv 2 0 (p * MvPolynomial.X 1)) =
      MvPolynomial.eval x.ofLp (angularDeriv 2 0 p) * x 1 := by
  simp [angularDeriv, sub_eq_add_neg]
  ring

theorem eval_angularDeriv20_mul_X_two (p : Poly3) (x : E3) :
    MvPolynomial.eval x.ofLp (angularDeriv 2 0 (p * MvPolynomial.X 2)) =
      MvPolynomial.eval x.ofLp (angularDeriv 2 0 p) * x 2 - x 0 * MvPolynomial.eval x.ofLp p := by
  simp [angularDeriv, sub_eq_add_neg]
  ring

theorem hasDerivAt_eval_rot20Point (p : Poly3) (x : E3) (t : ℝ) :
    HasDerivAt (fun s => MvPolynomial.eval (rot20Point s x).ofLp p)
      (MvPolynomial.eval (rot20Point t x).ofLp (angularDeriv 2 0 p)) t := by
  refine MvPolynomial.induction_on (motive := fun p : Poly3 =>
    HasDerivAt (fun s => MvPolynomial.eval (rot20Point s x).ofLp p)
      (MvPolynomial.eval (rot20Point t x).ofLp (angularDeriv 2 0 p)) t) p ?_ ?_ ?_
  · intro a
    simpa [angularDeriv] using hasDerivAt_const t a
  · intro p q hp hq
    convert hp.add hq using 1
    · ext s
      simp [MvPolynomial.eval_add]
    · simp [angularDeriv, sub_eq_add_neg, left_distrib]
      ring
  · intro p i hp
    fin_cases i
    · convert hp.mul (hasDerivAt_rot20Point_zero x t) using 1
      · ext s
        simp [MvPolynomial.eval_mul]
      · simpa [rot20Point_apply_zero, rot20Point_apply_two, mul_comm, mul_left_comm, mul_assoc] using
          eval_angularDeriv20_mul_X_zero p (rot20Point t x)
    · convert hp.mul (hasDerivAt_rot20Point_one x t) using 1
      · ext s
        simp [MvPolynomial.eval_mul]
      · simpa [rot20Point_apply_one] using eval_angularDeriv20_mul_X_one p (rot20Point t x)
    · convert hp.mul (hasDerivAt_rot20Point_two x t) using 1
      · ext s
        simp [MvPolynomial.eval_mul]
      · convert eval_angularDeriv20_mul_X_two p (rot20Point t x) using 1
        ring

theorem rot20Point_add (s t : ℝ) (x : E3) :
    rot20Point s (rot20Point t x) = rot20Point (s + t) x := by
  ext i
  fin_cases i
  · simp [rot20Point, Real.cos_add, Real.sin_add]
    ring
  · simp [rot20Point]
  · simp [rot20Point, Real.cos_add, Real.sin_add]
    ring

@[simp] theorem rot20Point_zero (x : E3) : rot20Point 0 x = x := by
  ext i
  fin_cases i <;> simp [rot20Point]

@[simp] theorem rot20Point_neg_add_self (t : ℝ) (x : E3) :
    rot20Point (-t) (rot20Point t x) = x := by simpa using rot20Point_add (-t) t x

@[simp] theorem rot20Point_add_neg_self (t : ℝ) (x : E3) :
    rot20Point t (rot20Point (-t) x) = x := by simpa [add_comm] using rot20Point_add t (-t) x

theorem rot20Point_norm_sq (t : ℝ) (x : E3) :
    ‖rot20Point t x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Fin.sum_univ_three]
  simp [rot20Point_apply_zero, rot20Point_apply_one, rot20Point_apply_two, pow_two]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq t]

noncomputable def rot20Linear (t : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun x := rot20Point t x
  map_add' x y := by
    ext i
    fin_cases i <;> simp [rot20Point] <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [rot20Point] <;> ring

noncomputable def rot20LinearIsometry (t : ℝ) : E3 →ₗᵢ[ℝ] E3 :=
  (rot20Linear t).toLinearIsometry <| by
    intro x y
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm, ← (rot20Linear t).map_sub]
    have hsq := rot20Point_norm_sq t (x - y)
    exact congrArg ENNReal.ofReal <|
      sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp <| by simpa [rot20Linear] using hsq

noncomputable def rotation20 (t : ℝ) : Rotation :=
  LinearIsometryEquiv.ofLinearIsometry
    (rot20LinearIsometry (-t))
    (rot20Linear t)
    (by
      ext x i
      change rot20Point (-t) (rot20Point t x) i = x i
      simpa using congrArg (fun z : E3 => z i) (rot20Point_neg_add_self t x))
    (by
      ext x i
      change rot20Point t (rot20Point (-t) x) i = x i
      simpa using congrArg (fun z : E3 => z i) (rot20Point_add_neg_self t x))

@[simp] theorem rotation20_apply (t : ℝ) (x : E3) :
    rotation20 t x = rot20Point (-t) x := rfl

@[simp] theorem rotation20_symm_apply (t : ℝ) (x : E3) :
    (rotation20 t).symm x = rot20Point t x := rfl

noncomputable def rot20Eval (p : Poly3) (t : ℝ) (x : S2) : ℝ :=
  MvPolynomial.eval (rot20Point t (x : E3)).ofLp p

noncomputable def rot20Integrand (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot20Eval p t x * rot20Eval q t x

noncomputable def rot20IntegrandDeriv (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot20Eval (angularDeriv 2 0 p) t x * rot20Eval q t x +
    rot20Eval p t x * rot20Eval (angularDeriv 2 0 q) t x

theorem rotation20_measurePreserving (t : ℝ) :
    MeasureTheory.MeasurePreserving
      ((Rotation.toSphereEquiv ((rotation20 t).symm)).toHomeomorph.toMeasurableEquiv)
      rotationMeasure rotationMeasure := by
  refine ⟨((Rotation.toSphereEquiv ((rotation20 t).symm)).toHomeomorph.toMeasurableEquiv).measurable, ?_⟩
  simpa using Rotation.map_rotationMeasure ((rotation20 t).symm)

theorem integral_rot20Integrand_eq_zero_time (p q : Poly3) (t : ℝ) :
    ∫ x, rot20Integrand p q t x ∂rotationMeasure =
      ∫ x, rot20Integrand p q 0 x ∂rotationMeasure := by
  let e : S2 ≃ᵐ S2 :=
    (Rotation.toSphereEquiv ((rotation20 t).symm)).toHomeomorph.toMeasurableEquiv
  let g : S2 → ℝ := rot20Integrand p q 0
  have hpres : MeasureTheory.MeasurePreserving e rotationMeasure rotationMeasure :=
    rotation20_measurePreserving t
  calc
    ∫ x, rot20Integrand p q t x ∂rotationMeasure
        = ∫ x, g (e x) ∂rotationMeasure := by
            simp [rot20Integrand, rot20Eval, g, e, rot20Point_zero, rotation20_symm_apply]
    _ = ∫ y, g y ∂rotationMeasure := hpres.integral_comp' g

theorem continuous_rot20Point_uncurry : Continuous (fun z : ℝ × E3 => rot20Point z.1 z.2) := by
  let e := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm
  have hcoords : Continuous (fun z : ℝ × E3 =>
      fun i : Fin 3 =>
        match i with
        | 0 => Real.sin z.1 * z.2 2 + Real.cos z.1 * z.2 0
        | 1 => z.2 1
        | 2 => Real.cos z.1 * z.2 2 - Real.sin z.1 * z.2 0) := by
    have h0 : Continuous (fun z : ℝ × E3 => z.2 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).comp continuous_snd
    have h1 : Continuous (fun z : ℝ × E3 => z.2 1) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).comp continuous_snd
    have h2 : Continuous (fun z : ℝ × E3 => z.2 2) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).comp continuous_snd
    apply continuous_pi
    intro i
    fin_cases i
    · exact ((Real.continuous_sin.comp continuous_fst).mul h2).add
        ((Real.continuous_cos.comp continuous_fst).mul h0)
    · simpa using h1
    · exact ((Real.continuous_cos.comp continuous_fst).mul h2).sub
        ((Real.continuous_sin.comp continuous_fst).mul h0)
  simpa [rot20Point] using e.continuous.comp hcoords

theorem continuous_rot20Eval_uncurry (p : Poly3) :
    Continuous (fun z : ℝ × S2 => rot20Eval p z.1 z.2) := by
  have hpoint : Continuous (fun z : ℝ × S2 => rot20Point z.1 (z.2 : E3)) := by
    have hmap : Continuous (fun z : ℝ × S2 => (z.1, (z.2 : E3))) := by continuity
    simpa using continuous_rot20Point_uncurry.comp hmap
  simpa [rot20Eval] using
    ((MvPolynomial.continuous_eval p).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))).comp hpoint

theorem continuous_rot20Integrand_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot20Integrand p q z.1 z.2) := by
  simp [rot20Integrand]
  exact (continuous_rot20Eval_uncurry p).mul (continuous_rot20Eval_uncurry q)

theorem continuous_rot20IntegrandDeriv_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot20IntegrandDeriv p q z.1 z.2) := by
  simp [rot20IntegrandDeriv]
  exact
    ((continuous_rot20Eval_uncurry (angularDeriv 2 0 p)).mul
      (continuous_rot20Eval_uncurry q)).add
      ((continuous_rot20Eval_uncurry p).mul
        (continuous_rot20Eval_uncurry (angularDeriv 2 0 q)))

theorem continuous_rot20Integrand (p q : Poly3) (t : ℝ) :
    Continuous (rot20Integrand p q t) := by
  have hmap : Continuous (fun x : S2 => (t, x)) := by continuity
  simpa using (continuous_rot20Integrand_uncurry p q).comp hmap

theorem continuous_rot20IntegrandDeriv (p q : Poly3) (t : ℝ) :
    Continuous (rot20IntegrandDeriv p q t) := by
  have hmap : Continuous (fun x : S2 => (t, x)) := by continuity
  simpa using (continuous_rot20IntegrandDeriv_uncurry p q).comp hmap

theorem hasDerivAt_rot20Integrand (p q : Poly3) (t : ℝ) (x : S2) :
    HasDerivAt (fun s => rot20Integrand p q s x) (rot20IntegrandDeriv p q t x) t := by
  simp [rot20Integrand, rot20IntegrandDeriv]
  exact (hasDerivAt_eval_rot20Point p (x : E3) t).mul (hasDerivAt_eval_rot20Point q (x : E3) t)

theorem exists_bound_rot20IntegrandDeriv (p q : Poly3) :
    ∃ C : ℝ, ∀ t ∈ Metric.ball (0 : ℝ) 1, ∀ x : S2, ‖rot20IntegrandDeriv p q t x‖ ≤ C := by
  let f : ℝ × S2 → ℝ := fun z => rot20IntegrandDeriv p q z.1 z.2
  have hcompact : IsCompact (Set.Icc (-1 : ℝ) 1 ×ˢ (Set.univ : Set S2)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn (continuous_rot20IntegrandDeriv_uncurry p q).continuousOn
  refine ⟨C, ?_⟩
  intro t ht x
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact ⟨by linarith [abs_lt.mp ht |>.1], by linarith [abs_lt.mp ht |>.2]⟩
  exact hC (t, x) ⟨ht', trivial⟩

theorem integral_rot20IntegrandDeriv_zero (p q : Poly3) :
    ∫ x, rot20IntegrandDeriv p q 0 x ∂rotationMeasure = 0 := by
  obtain ⟨C, hC⟩ := exists_bound_rot20IntegrandDeriv p q
  obtain ⟨-, hderiv⟩ :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := rotationMeasure) (x₀ := (0 : ℝ)) (ε := 1)
      (by norm_num)
      (Filter.Eventually.of_forall fun t =>
        (continuous_rot20Integrand p q t).aestronglyMeasurable)
      (integrable_of_continuous_sphere (continuous_rot20Integrand p q 0))
      ((continuous_rot20IntegrandDeriv p q 0).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x t ht => hC t ht x)
      (show MeasureTheory.Integrable (fun _ : S2 => C) rotationMeasure by
        simpa using (MeasureTheory.integrable_const C))
      (Filter.Eventually.of_forall fun x t ht =>
        hasDerivAt_rot20Integrand p q t x)
  have hconst :
      HasDerivAt (fun u => ∫ x, rot20Integrand p q u x ∂rotationMeasure) 0 0 := by
    convert hasDerivAt_const (0 : ℝ) (∫ x, rot20Integrand p q 0 x ∂rotationMeasure) using 1
    ext u
    exact integral_rot20Integrand_eq_zero_time p q u
  exact (hconst.unique hderiv).symm

theorem inner_rot20_skew_add (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 2 0 p)))
        (continuousToLp (restrictToSphere q)) +
      inner ℝ
        (continuousToLp (restrictToSphere p))
        (continuousToLp (restrictToSphere (angularDeriv 2 0 q))) = 0 := by
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (restrictToSphere (angularDeriv 2 0 p))
      (restrictToSphere q)]
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (restrictToSphere p)
      (restrictToSphere (angularDeriv 2 0 q))]
  simp [mul_comm]
  have h1 : MeasureTheory.Integrable
      (fun x : S2 =>
        MvPolynomial.eval x.1.ofLp p * MvPolynomial.eval x.1.ofLp (angularDeriv 2 0 q))
      rotationMeasure := by
    exact integrable_of_continuous_sphere
      ((restrictToSphere p).continuous.mul (restrictToSphere (angularDeriv 2 0 q)).continuous)
  have h2 : MeasureTheory.Integrable
      (fun x : S2 =>
        MvPolynomial.eval x.1.ofLp q * MvPolynomial.eval x.1.ofLp (angularDeriv 2 0 p))
      rotationMeasure := by
    exact integrable_of_continuous_sphere
      ((restrictToSphere q).continuous.mul (restrictToSphere (angularDeriv 2 0 p)).continuous)
  rw [← MeasureTheory.integral_add h2 h1]
  simpa [rot20IntegrandDeriv, rot20Integrand, rot20Eval, restrictToSphere_apply,
    rot20Point_zero, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    using integral_rot20IntegrandDeriv_zero p q

theorem inner_rot20_skew (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 2 0 p)))
        (continuousToLp (restrictToSphere q)) =
      -inner ℝ
        (continuousToLp (restrictToSphere p))
        (continuousToLp (restrictToSphere (angularDeriv 2 0 q))) := by
  exact eq_neg_iff_add_eq_zero.2 (inner_rot20_skew_add p q)

theorem sum_angularDeriv_sq_eq_neg_degree_weight {n : ℕ} {p : Poly3}
    (hp : p ∈ harmonicHomogeneousSubmodule n) :
    angularDeriv 0 1 (angularDeriv 0 1 p) +
        angularDeriv 1 2 (angularDeriv 1 2 p) +
      angularDeriv 2 0 (angularDeriv 2 0 p) =
      -((((n * (n + 1) : ℕ) : ℝ)) • p) := by
  rcases Submodule.mem_inf.1 hp with ⟨hhom, hharm⟩
  have hpHom : p.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule n p).mp hhom
  have heuler : eulerOperator p = n • p := eulerOperator_apply_eq_smul_of_isHomogeneous hpHom
  have heuler2 : eulerOperator (eulerOperator p) = n • (n • p) := by
    rw [heuler, map_nsmul, heuler]
  calc
    angularDeriv 0 1 (angularDeriv 0 1 p) +
        angularDeriv 1 2 (angularDeriv 1 2 p) +
      angularDeriv 2 0 (angularDeriv 2 0 p)
        = radiusSq * laplacian p - eulerOperator (eulerOperator p) - eulerOperator p :=
            sum_angularDeriv_sq p
    _ = -(n • (n • p)) - n • p := by
      rw [show laplacian p = 0 from hharm, heuler2, heuler]
      simp
    _ = -((n * n) • p) - n • p := by
      congr 1
      simpa [mul_comm] using (smul_smul n n p)
    _ = -(((n * n) • p) + n • p) := by
      simpa [sub_eq_add_neg] using (neg_add ((n * n) • p) (n • p)).symm
    _ = -(((n * n) + n) • p) := by rw [← add_nsmul]
    _ = -((n * (n + 1)) • p) := by
      simpa [Nat.mul_add, Nat.mul_one, add_comm, add_left_comm, add_assoc]
    _ = -((((n * (n + 1) : ℕ) : ℝ)) • p) := by
      simp [Algebra.smul_def]

theorem strictMono_degreeWeight : StrictMono (fun n : ℕ => n * (n + 1)) := by
  intro a b hab
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have h : (a : ℝ) * (a + 1) < (b : ℝ) * (b + 1) := by
    nlinarith
  exact_mod_cast h

theorem degreeWeight_ne_of_ne {n m : ℕ} (hnm : n ≠ m) :
    (((n * (n + 1) : ℕ) : ℝ)) ≠ (((m * (m + 1) : ℕ) : ℝ)) := by
  intro h
  apply hnm
  apply strictMono_degreeWeight.injective
  exact_mod_cast h

theorem inner_rot01_sq (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 0 1 (angularDeriv 0 1 p))))
        (continuousToLp (restrictToSphere q)) =
      -inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 0 1 p)))
        (continuousToLp (restrictToSphere (angularDeriv 0 1 q))) := by
  simpa using inner_rot01_skew (angularDeriv 0 1 p) q

theorem inner_rot12_sq (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 1 2 (angularDeriv 1 2 p))))
        (continuousToLp (restrictToSphere q)) =
      -inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 1 2 p)))
        (continuousToLp (restrictToSphere (angularDeriv 1 2 q))) := by
  simpa using inner_rot12_skew (angularDeriv 1 2 p) q

theorem inner_rot20_sq (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 2 0 (angularDeriv 2 0 p))))
        (continuousToLp (restrictToSphere q)) =
      -inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 2 0 p)))
        (continuousToLp (restrictToSphere (angularDeriv 2 0 q))) := by
  simpa using inner_rot20_skew (angularDeriv 2 0 p) q

theorem inner_rot01_sq_selfAdjoint (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 0 1 (angularDeriv 0 1 p))))
        (continuousToLp (restrictToSphere q)) =
      inner ℝ
        (continuousToLp (restrictToSphere p))
        (continuousToLp (restrictToSphere (angularDeriv 0 1 (angularDeriv 0 1 q)))) := by
  calc
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 0 1 (angularDeriv 0 1 p))))
        (continuousToLp (restrictToSphere q))
      = -inner ℝ
          (continuousToLp (restrictToSphere (angularDeriv 0 1 p)))
          (continuousToLp (restrictToSphere (angularDeriv 0 1 q))) := inner_rot01_sq p q
    _ = inner ℝ
          (continuousToLp (restrictToSphere p))
          (continuousToLp (restrictToSphere (angularDeriv 0 1 (angularDeriv 0 1 q)))) := by
        rw [inner_rot01_skew p (angularDeriv 0 1 q)]
        simp

theorem inner_rot12_sq_selfAdjoint (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 1 2 (angularDeriv 1 2 p))))
        (continuousToLp (restrictToSphere q)) =
      inner ℝ
        (continuousToLp (restrictToSphere p))
        (continuousToLp (restrictToSphere (angularDeriv 1 2 (angularDeriv 1 2 q)))) := by
  calc
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 1 2 (angularDeriv 1 2 p))))
        (continuousToLp (restrictToSphere q))
      = -inner ℝ
          (continuousToLp (restrictToSphere (angularDeriv 1 2 p)))
          (continuousToLp (restrictToSphere (angularDeriv 1 2 q))) := inner_rot12_sq p q
    _ = inner ℝ
          (continuousToLp (restrictToSphere p))
          (continuousToLp (restrictToSphere (angularDeriv 1 2 (angularDeriv 1 2 q)))) := by
        rw [inner_rot12_skew p (angularDeriv 1 2 q)]
        simp

theorem inner_rot20_sq_selfAdjoint (p q : Poly3) :
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 2 0 (angularDeriv 2 0 p))))
        (continuousToLp (restrictToSphere q)) =
      inner ℝ
        (continuousToLp (restrictToSphere p))
        (continuousToLp (restrictToSphere (angularDeriv 2 0 (angularDeriv 2 0 q)))) := by
  calc
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 2 0 (angularDeriv 2 0 p))))
        (continuousToLp (restrictToSphere q))
      = -inner ℝ
          (continuousToLp (restrictToSphere (angularDeriv 2 0 p)))
          (continuousToLp (restrictToSphere (angularDeriv 2 0 q))) := inner_rot20_sq p q
    _ = inner ℝ
          (continuousToLp (restrictToSphere p))
          (continuousToLp (restrictToSphere (angularDeriv 2 0 (angularDeriv 2 0 q)))) := by
        rw [inner_rot20_skew p (angularDeriv 2 0 q)]
        simp

theorem inner_sum_angularDeriv_sq_selfAdjoint (p q : Poly3) :
    inner ℝ
        (continuousToLp <|
          restrictToSphere
            (angularDeriv 0 1 (angularDeriv 0 1 p) +
              angularDeriv 1 2 (angularDeriv 1 2 p) +
              angularDeriv 2 0 (angularDeriv 2 0 p)))
        (continuousToLp (restrictToSphere q)) =
      inner ℝ
        (continuousToLp (restrictToSphere p))
        (continuousToLp <|
          restrictToSphere
            (angularDeriv 0 1 (angularDeriv 0 1 q) +
              angularDeriv 1 2 (angularDeriv 1 2 q) +
              angularDeriv 2 0 (angularDeriv 2 0 q))) := by
  calc
    inner ℝ
        (continuousToLp <|
          restrictToSphere
            (angularDeriv 0 1 (angularDeriv 0 1 p) +
              angularDeriv 1 2 (angularDeriv 1 2 p) +
              angularDeriv 2 0 (angularDeriv 2 0 p)))
        (continuousToLp (restrictToSphere q))
      =
        inner ℝ
          (continuousToLp (restrictToSphere (angularDeriv 0 1 (angularDeriv 0 1 p))))
          (continuousToLp (restrictToSphere q)) +
        inner ℝ
          (continuousToLp (restrictToSphere (angularDeriv 1 2 (angularDeriv 1 2 p))))
          (continuousToLp (restrictToSphere q)) +
        inner ℝ
          (continuousToLp (restrictToSphere (angularDeriv 2 0 (angularDeriv 2 0 p))))
          (continuousToLp (restrictToSphere q)) := by
            simpa [add_assoc, inner_add_left]
    _ =
        inner ℝ
          (continuousToLp (restrictToSphere p))
          (continuousToLp (restrictToSphere (angularDeriv 0 1 (angularDeriv 0 1 q)))) +
        inner ℝ
          (continuousToLp (restrictToSphere p))
          (continuousToLp (restrictToSphere (angularDeriv 1 2 (angularDeriv 1 2 q)))) +
        inner ℝ
          (continuousToLp (restrictToSphere p))
          (continuousToLp (restrictToSphere (angularDeriv 2 0 (angularDeriv 2 0 q)))) := by
            rw [inner_rot01_sq_selfAdjoint, inner_rot12_sq_selfAdjoint, inner_rot20_sq_selfAdjoint]
    _ =
        inner ℝ
          (continuousToLp (restrictToSphere p))
          (continuousToLp <|
            restrictToSphere
              (angularDeriv 0 1 (angularDeriv 0 1 q) +
                angularDeriv 1 2 (angularDeriv 1 2 q) +
                angularDeriv 2 0 (angularDeriv 2 0 q))) := by
            simpa [add_assoc, inner_add_right]

theorem inner_eq_zero_of_mem_harmonicHomogeneousSubmodule_ne {n m : ℕ} {p q : Poly3}
    (hnm : n ≠ m)
    (hp : p ∈ harmonicHomogeneousSubmodule n)
    (hq : q ∈ harmonicHomogeneousSubmodule m) :
    inner ℝ
        (continuousToLp (restrictToSphere p))
        (continuousToLp (restrictToSphere q)) = 0 := by
  let u : MeasureTheory.Lp ℝ 2 rotationMeasure := continuousToLp (restrictToSphere p)
  let v : MeasureTheory.Lp ℝ 2 rotationMeasure := continuousToLp (restrictToSphere q)
  let a : ℝ := ((n * (n + 1) : ℕ) : ℝ)
  let b : ℝ := ((m * (m + 1) : ℕ) : ℝ)
  have hself :
      inner ℝ
          (continuousToLp <|
            restrictToSphere
              (angularDeriv 0 1 (angularDeriv 0 1 p) +
                angularDeriv 1 2 (angularDeriv 1 2 p) +
                angularDeriv 2 0 (angularDeriv 2 0 p)))
          v =
        inner ℝ
          u
          (continuousToLp <|
            restrictToSphere
              (angularDeriv 0 1 (angularDeriv 0 1 q) +
                angularDeriv 1 2 (angularDeriv 1 2 q) +
                angularDeriv 2 0 (angularDeriv 2 0 q))) := by
    simpa [u, v] using inner_sum_angularDeriv_sq_selfAdjoint p q
  have hleft :
      inner ℝ
          (continuousToLp <|
            restrictToSphere
              (angularDeriv 0 1 (angularDeriv 0 1 p) +
                angularDeriv 1 2 (angularDeriv 1 2 p) +
                angularDeriv 2 0 (angularDeriv 2 0 p)))
          v =
        -a * inner ℝ u v := by
    rw [sum_angularDeriv_sq_eq_neg_degree_weight hp]
    dsimp [a]
    rw [restrictToSphere.map_neg, ContinuousLinearMap.map_neg, inner_neg_left,
      restrictToSphere.map_smul, ContinuousLinearMap.map_smul, inner_smul_left]
    rw [show (starRingEnd ℝ) ↑(n * (n + 1)) = (↑(n * (n + 1)) : ℝ) by simp]
    simpa [u]
  have hright :
      inner ℝ
          u
          (continuousToLp <|
            restrictToSphere
              (angularDeriv 0 1 (angularDeriv 0 1 q) +
                angularDeriv 1 2 (angularDeriv 1 2 q) +
                angularDeriv 2 0 (angularDeriv 2 0 q))) =
        -b * inner ℝ u v := by
    rw [sum_angularDeriv_sq_eq_neg_degree_weight hq]
    dsimp [b]
    rw [restrictToSphere.map_neg, ContinuousLinearMap.map_neg, inner_neg_right,
      restrictToSphere.map_smul, ContinuousLinearMap.map_smul, inner_smul_right]
    simpa [v]
  have hEq : -a * inner ℝ u v = -b * inner ℝ u v := by
    calc
      -a * inner ℝ u v =
          inner ℝ
            (continuousToLp <|
              restrictToSphere
                (angularDeriv 0 1 (angularDeriv 0 1 p) +
                  angularDeriv 1 2 (angularDeriv 1 2 p) +
                  angularDeriv 2 0 (angularDeriv 2 0 p)))
            v := hleft.symm
      _ =
          inner ℝ
            u
            (continuousToLp <|
              restrictToSphere
                (angularDeriv 0 1 (angularDeriv 0 1 q) +
                  angularDeriv 1 2 (angularDeriv 1 2 q) +
                  angularDeriv 2 0 (angularDeriv 2 0 q))) := hself
      _ = -b * inner ℝ u v := hright
  have hmul : (b - a) * inner ℝ u v = 0 := by
    calc
      (b - a) * inner ℝ u v = (-a * inner ℝ u v) - (-b * inner ℝ u v) := by
        ring
      _ = 0 := sub_eq_zero.mpr hEq
  rcases mul_eq_zero.mp hmul with hcoeff | hinner
  · have hab : b = a := sub_eq_zero.mp hcoeff
    exact False.elim <| degreeWeight_ne_of_ne hnm hab.symm
  · simpa [u, v] using hinner

theorem sectorL2_isOrtho_of_ne {n m : ℕ} (hnm : n ≠ m) :
    sectorL2 n ⟂ sectorL2 m := by
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu v hv
  rcases hu with ⟨f, hf, rfl⟩
  rcases hv with ⟨g, hg, rfl⟩
  rcases hf with ⟨p, hp, rfl⟩
  rcases hg with ⟨q, hq, rfl⟩
  exact inner_eq_zero_of_mem_harmonicHomogeneousSubmodule_ne hnm hp hq

theorem sectorL2_orthogonalFamily :
    OrthogonalFamily ℝ (fun n : ℕ => sectorL2 n) fun n => (sectorL2 n).subtypeₗᵢ :=
  OrthogonalFamily.of_pairwise <| by
    intro n m hnm
    exact sectorL2_isOrtho_of_ne hnm

end SphericalHarmonics
