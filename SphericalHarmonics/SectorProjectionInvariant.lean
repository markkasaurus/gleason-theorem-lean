import SphericalHarmonics.GeometricInvariant
import SphericalHarmonics.SectorOrthogonality
import SphericalHarmonics.L2Decomposition
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace SphericalHarmonics

/-- The fixed-time `(0,1)`-rotation pullback of an ambient polynomial restriction. -/
noncomputable def rot01Continuous (p : Poly3) (t : ℝ) : C(S2, ℝ) where
  toFun := rot01Eval p t
  continuous_toFun := by
    have hmap : Continuous (fun x : S2 => (t, x)) := by
      continuity
    simpa using (continuous_rot01Eval_uncurry p).comp hmap

/-- The fixed-time `(1,2)`-rotation pullback of an ambient polynomial restriction. -/
noncomputable def rot12Continuous (p : Poly3) (t : ℝ) : C(S2, ℝ) where
  toFun := rot12Eval p t
  continuous_toFun := by
    have hmap : Continuous (fun x : S2 => (t, x)) := by
      continuity
    simpa using (continuous_rot12Eval_uncurry p).comp hmap

/-- The fixed-time `(2,0)`-rotation pullback of an ambient polynomial restriction. -/
noncomputable def rot20Continuous (p : Poly3) (t : ℝ) : C(S2, ℝ) where
  toFun := rot20Eval p t
  continuous_toFun := by
    have hmap : Continuous (fun x : S2 => (t, x)) := by
      continuity
    simpa using (continuous_rot20Eval_uncurry p).comp hmap

@[simp] theorem rot01Continuous_apply (p : Poly3) (t : ℝ) (x : S2) :
    rot01Continuous p t x = rot01Eval p t x := rfl

@[simp] theorem rot12Continuous_apply (p : Poly3) (t : ℝ) (x : S2) :
    rot12Continuous p t x = rot12Eval p t x := rfl

@[simp] theorem rot20Continuous_apply (p : Poly3) (t : ℝ) (x : S2) :
    rot20Continuous p t x = rot20Eval p t x := rfl

@[simp] theorem rot01Continuous_zero (p : Poly3) :
    rot01Continuous p 0 = restrictToSphere p := by
  ext x
  simp [rot01Continuous, rot01Eval, rot01Point_zero, restrictToSphere_apply]

@[simp] theorem rot12Continuous_zero (p : Poly3) :
    rot12Continuous p 0 = restrictToSphere p := by
  ext x
  simp [rot12Continuous, rot12Eval, rot12Point_zero, restrictToSphere_apply]

@[simp] theorem rot20Continuous_zero (p : Poly3) :
    rot20Continuous p 0 = restrictToSphere p := by
  ext x
  simp [rot20Continuous, rot20Eval, rot20Point_zero, restrictToSphere_apply]

@[simp] theorem rot01Continuous_eq_compContinuous (p : Poly3) (t : ℝ) :
    rot01Continuous p t =
      Rotation.compContinuous (rotation01 t) (restrictToSphere p) := by
  ext x
  simp [rot01Continuous, rot01Eval, Rotation.compContinuous_apply, rotation01_symm_apply]

@[simp] theorem rot12Continuous_eq_compContinuous (p : Poly3) (t : ℝ) :
    rot12Continuous p t =
      Rotation.compContinuous (rotation12 t) (restrictToSphere p) := by
  ext x
  simp [rot12Continuous, rot12Eval, Rotation.compContinuous_apply, rotation12_symm_apply]

@[simp] theorem rot20Continuous_eq_compContinuous (p : Poly3) (t : ℝ) :
    rot20Continuous p t =
      Rotation.compContinuous (rotation20 t) (restrictToSphere p) := by
  ext x
  simp [rot20Continuous, rot20Eval, Rotation.compContinuous_apply, rotation20_symm_apply]

/-- Scalar matrix coefficient for the `(0,1)`-rotation orbit of a polynomial restriction. -/
noncomputable def rot01Inner (p q : Poly3) (t : ℝ) : ℝ :=
  ∫ x, rot01Eval p t x * restrictToSphere q x ∂rotationMeasure

/-- Scalar matrix coefficient for the `(1,2)`-rotation orbit of a polynomial restriction. -/
noncomputable def rot12Inner (p q : Poly3) (t : ℝ) : ℝ :=
  ∫ x, rot12Eval p t x * restrictToSphere q x ∂rotationMeasure

/-- Scalar matrix coefficient for the `(2,0)`-rotation orbit of a polynomial restriction. -/
noncomputable def rot20Inner (p q : Poly3) (t : ℝ) : ℝ :=
  ∫ x, rot20Eval p t x * restrictToSphere q x ∂rotationMeasure

@[simp] theorem rot01Inner_zero (p q : Poly3) :
    rot01Inner p q 0 =
      inner ℝ (continuousToLp (restrictToSphere p)) (continuousToLp (restrictToSphere q)) := by
  rw [rot01Inner]
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (restrictToSphere p) (restrictToSphere q)]
  simp [rot01Eval, rot01Point_zero, restrictToSphere_apply, mul_comm]

@[simp] theorem rot12Inner_zero (p q : Poly3) :
    rot12Inner p q 0 =
      inner ℝ (continuousToLp (restrictToSphere p)) (continuousToLp (restrictToSphere q)) := by
  rw [rot12Inner]
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (restrictToSphere p) (restrictToSphere q)]
  simp [rot12Eval, rot12Point_zero, restrictToSphere_apply, mul_comm]

@[simp] theorem rot20Inner_zero (p q : Poly3) :
    rot20Inner p q 0 =
      inner ℝ (continuousToLp (restrictToSphere p)) (continuousToLp (restrictToSphere q)) := by
  rw [rot20Inner]
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (restrictToSphere p) (restrictToSphere q)]
  simp [rot20Eval, rot20Point_zero, restrictToSphere_apply, mul_comm]

noncomputable def rot01InnerIntegrand (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot01Eval p t x * restrictToSphere q x

noncomputable def rot12InnerIntegrand (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot12Eval p t x * restrictToSphere q x

noncomputable def rot20InnerIntegrand (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot20Eval p t x * restrictToSphere q x

noncomputable def rot01InnerIntegrandDeriv (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot01Eval (angularDeriv 0 1 p) t x * restrictToSphere q x

noncomputable def rot12InnerIntegrandDeriv (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot12Eval (angularDeriv 1 2 p) t x * restrictToSphere q x

noncomputable def rot20InnerIntegrandDeriv (p q : Poly3) (t : ℝ) (x : S2) : ℝ :=
  rot20Eval (angularDeriv 2 0 p) t x * restrictToSphere q x

theorem continuous_rot01InnerIntegrand_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot01InnerIntegrand p q z.1 z.2) := by
  simp [rot01InnerIntegrand]
  exact
    (continuous_rot01Eval_uncurry p).mul
      ((restrictToSphere q).continuous.comp continuous_snd)

theorem continuous_rot12InnerIntegrand_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot12InnerIntegrand p q z.1 z.2) := by
  simp [rot12InnerIntegrand]
  exact
    (continuous_rot12Eval_uncurry p).mul
      ((restrictToSphere q).continuous.comp continuous_snd)

theorem continuous_rot20InnerIntegrand_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot20InnerIntegrand p q z.1 z.2) := by
  simp [rot20InnerIntegrand]
  exact
    (continuous_rot20Eval_uncurry p).mul
      ((restrictToSphere q).continuous.comp continuous_snd)

theorem continuous_rot01InnerIntegrandDeriv_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot01InnerIntegrandDeriv p q z.1 z.2) := by
  simp [rot01InnerIntegrandDeriv]
  exact
    (continuous_rot01Eval_uncurry (angularDeriv 0 1 p)).mul
      ((restrictToSphere q).continuous.comp continuous_snd)

theorem continuous_rot12InnerIntegrandDeriv_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot12InnerIntegrandDeriv p q z.1 z.2) := by
  simp [rot12InnerIntegrandDeriv]
  exact
    (continuous_rot12Eval_uncurry (angularDeriv 1 2 p)).mul
      ((restrictToSphere q).continuous.comp continuous_snd)

theorem continuous_rot20InnerIntegrandDeriv_uncurry (p q : Poly3) :
    Continuous (fun z : ℝ × S2 => rot20InnerIntegrandDeriv p q z.1 z.2) := by
  simp [rot20InnerIntegrandDeriv]
  exact
    (continuous_rot20Eval_uncurry (angularDeriv 2 0 p)).mul
      ((restrictToSphere q).continuous.comp continuous_snd)

theorem hasDerivAt_rot01InnerIntegrand (p q : Poly3) (t : ℝ) (x : S2) :
    HasDerivAt (fun s => rot01InnerIntegrand p q s x) (rot01InnerIntegrandDeriv p q t x) t := by
  simpa [rot01InnerIntegrand, rot01InnerIntegrandDeriv] using
    (hasDerivAt_eval_rot01Point p (x : E3) t).mul
      (hasDerivAt_const t (restrictToSphere q x))

theorem hasDerivAt_rot12InnerIntegrand (p q : Poly3) (t : ℝ) (x : S2) :
    HasDerivAt (fun s => rot12InnerIntegrand p q s x) (rot12InnerIntegrandDeriv p q t x) t := by
  simpa [rot12InnerIntegrand, rot12InnerIntegrandDeriv] using
    (hasDerivAt_eval_rot12Point p (x : E3) t).mul
      (hasDerivAt_const t (restrictToSphere q x))

theorem hasDerivAt_rot20InnerIntegrand (p q : Poly3) (t : ℝ) (x : S2) :
    HasDerivAt (fun s => rot20InnerIntegrand p q s x) (rot20InnerIntegrandDeriv p q t x) t := by
  simpa [rot20InnerIntegrand, rot20InnerIntegrandDeriv] using
    (hasDerivAt_eval_rot20Point p (x : E3) t).mul
      (hasDerivAt_const t (restrictToSphere q x))

theorem exists_bound_rot01InnerIntegrandDeriv (p q : Poly3) (t₀ : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Metric.ball t₀ 1, ∀ x : S2, ‖rot01InnerIntegrandDeriv p q t x‖ ≤ C := by
  let f : ℝ × S2 → ℝ := fun z => rot01InnerIntegrandDeriv p q z.1 z.2
  have hcompact : IsCompact (Set.Icc (t₀ - 1) (t₀ + 1) ×ˢ (Set.univ : Set S2)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (continuous_rot01InnerIntegrandDeriv_uncurry p q).continuousOn
  refine ⟨C, ?_⟩
  intro t ht x
  have ht' : t ∈ Set.Icc (t₀ - 1) (t₀ + 1) := by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact ⟨by linarith [abs_lt.mp ht |>.1], by linarith [abs_lt.mp ht |>.2]⟩
  exact hC (t, x) ⟨ht', trivial⟩

theorem exists_bound_rot12InnerIntegrandDeriv (p q : Poly3) (t₀ : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Metric.ball t₀ 1, ∀ x : S2, ‖rot12InnerIntegrandDeriv p q t x‖ ≤ C := by
  let f : ℝ × S2 → ℝ := fun z => rot12InnerIntegrandDeriv p q z.1 z.2
  have hcompact : IsCompact (Set.Icc (t₀ - 1) (t₀ + 1) ×ˢ (Set.univ : Set S2)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (continuous_rot12InnerIntegrandDeriv_uncurry p q).continuousOn
  refine ⟨C, ?_⟩
  intro t ht x
  have ht' : t ∈ Set.Icc (t₀ - 1) (t₀ + 1) := by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact ⟨by linarith [abs_lt.mp ht |>.1], by linarith [abs_lt.mp ht |>.2]⟩
  exact hC (t, x) ⟨ht', trivial⟩

theorem exists_bound_rot20InnerIntegrandDeriv (p q : Poly3) (t₀ : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Metric.ball t₀ 1, ∀ x : S2, ‖rot20InnerIntegrandDeriv p q t x‖ ≤ C := by
  let f : ℝ × S2 → ℝ := fun z => rot20InnerIntegrandDeriv p q z.1 z.2
  have hcompact : IsCompact (Set.Icc (t₀ - 1) (t₀ + 1) ×ˢ (Set.univ : Set S2)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (continuous_rot20InnerIntegrandDeriv_uncurry p q).continuousOn
  refine ⟨C, ?_⟩
  intro t ht x
  have ht' : t ∈ Set.Icc (t₀ - 1) (t₀ + 1) := by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact ⟨by linarith [abs_lt.mp ht |>.1], by linarith [abs_lt.mp ht |>.2]⟩
  exact hC (t, x) ⟨ht', trivial⟩

theorem hasDerivAt_integral_rot01InnerIntegrand (p q : Poly3) (t₀ : ℝ) :
    HasDerivAt
      (fun t => ∫ x, rot01InnerIntegrand p q t x ∂rotationMeasure)
      (∫ x, rot01InnerIntegrandDeriv p q t₀ x ∂rotationMeasure) t₀ := by
  obtain ⟨C, hC⟩ := exists_bound_rot01InnerIntegrandDeriv p q t₀
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := rotationMeasure) (x₀ := t₀) (ε := 1)
      (by norm_num)
      (Filter.Eventually.of_forall fun t =>
        (by
          have hmap : Continuous (fun x : S2 => (t, x)) := by continuity
          simpa using ((continuous_rot01InnerIntegrand_uncurry p q).comp hmap).aestronglyMeasurable))
      (integrable_of_continuous_sphere <| by
        have hmap : Continuous (fun x : S2 => (t₀, x)) := by continuity
        simpa using (continuous_rot01InnerIntegrand_uncurry p q).comp hmap)
      ((by
        have hmap : Continuous (fun x : S2 => (t₀, x)) := by continuity
        simpa using ((continuous_rot01InnerIntegrandDeriv_uncurry p q).comp hmap).aestronglyMeasurable))
      (Filter.Eventually.of_forall fun x t ht => hC t ht x)
      (show MeasureTheory.Integrable (fun _ : S2 => C) rotationMeasure by
        simpa using (MeasureTheory.integrable_const C))
      (Filter.Eventually.of_forall fun x t ht =>
        hasDerivAt_rot01InnerIntegrand p q t x)).2

theorem hasDerivAt_integral_rot12InnerIntegrand (p q : Poly3) (t₀ : ℝ) :
    HasDerivAt
      (fun t => ∫ x, rot12InnerIntegrand p q t x ∂rotationMeasure)
      (∫ x, rot12InnerIntegrandDeriv p q t₀ x ∂rotationMeasure) t₀ := by
  obtain ⟨C, hC⟩ := exists_bound_rot12InnerIntegrandDeriv p q t₀
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := rotationMeasure) (x₀ := t₀) (ε := 1)
      (by norm_num)
      (Filter.Eventually.of_forall fun t =>
        (by
          have hmap : Continuous (fun x : S2 => (t, x)) := by continuity
          simpa using ((continuous_rot12InnerIntegrand_uncurry p q).comp hmap).aestronglyMeasurable))
      (integrable_of_continuous_sphere <| by
        have hmap : Continuous (fun x : S2 => (t₀, x)) := by continuity
        simpa using (continuous_rot12InnerIntegrand_uncurry p q).comp hmap)
      ((by
        have hmap : Continuous (fun x : S2 => (t₀, x)) := by continuity
        simpa using ((continuous_rot12InnerIntegrandDeriv_uncurry p q).comp hmap).aestronglyMeasurable))
      (Filter.Eventually.of_forall fun x t ht => hC t ht x)
      (show MeasureTheory.Integrable (fun _ : S2 => C) rotationMeasure by
        simpa using (MeasureTheory.integrable_const C))
      (Filter.Eventually.of_forall fun x t ht =>
        hasDerivAt_rot12InnerIntegrand p q t x)).2

theorem hasDerivAt_integral_rot20InnerIntegrand (p q : Poly3) (t₀ : ℝ) :
    HasDerivAt
      (fun t => ∫ x, rot20InnerIntegrand p q t x ∂rotationMeasure)
      (∫ x, rot20InnerIntegrandDeriv p q t₀ x ∂rotationMeasure) t₀ := by
  obtain ⟨C, hC⟩ := exists_bound_rot20InnerIntegrandDeriv p q t₀
  exact
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := rotationMeasure) (x₀ := t₀) (ε := 1)
      (by norm_num)
      (Filter.Eventually.of_forall fun t =>
        (by
          have hmap : Continuous (fun x : S2 => (t, x)) := by continuity
          simpa using ((continuous_rot20InnerIntegrand_uncurry p q).comp hmap).aestronglyMeasurable))
      (integrable_of_continuous_sphere <| by
        have hmap : Continuous (fun x : S2 => (t₀, x)) := by continuity
        simpa using (continuous_rot20InnerIntegrand_uncurry p q).comp hmap)
      ((by
        have hmap : Continuous (fun x : S2 => (t₀, x)) := by continuity
        simpa using ((continuous_rot20InnerIntegrandDeriv_uncurry p q).comp hmap).aestronglyMeasurable))
      (Filter.Eventually.of_forall fun x t ht => hC t ht x)
      (show MeasureTheory.Integrable (fun _ : S2 => C) rotationMeasure by
        simpa using (MeasureTheory.integrable_const C))
      (Filter.Eventually.of_forall fun x t ht =>
        hasDerivAt_rot20InnerIntegrand p q t x)).2

theorem hasDerivAt_rot01Inner (p q : Poly3) (t : ℝ) :
    HasDerivAt (rot01Inner p q) (rot01Inner (angularDeriv 0 1 p) q t) t := by
  simpa [rot01Inner, rot01InnerIntegrand, rot01InnerIntegrandDeriv]
    using hasDerivAt_integral_rot01InnerIntegrand p q t

theorem hasDerivAt_rot12Inner (p q : Poly3) (t : ℝ) :
    HasDerivAt (rot12Inner p q) (rot12Inner (angularDeriv 1 2 p) q t) t := by
  simpa [rot12Inner, rot12InnerIntegrand, rot12InnerIntegrandDeriv]
    using hasDerivAt_integral_rot12InnerIntegrand p q t

theorem hasDerivAt_rot20Inner (p q : Poly3) (t : ℝ) :
    HasDerivAt (rot20Inner p q) (rot20Inner (angularDeriv 2 0 p) q t) t := by
  simpa [rot20Inner, rot20InnerIntegrand, rot20InnerIntegrandDeriv]
    using hasDerivAt_integral_rot20InnerIntegrand p q t

theorem deriv_rot01Inner (p q : Poly3) :
    deriv (rot01Inner p q) = rot01Inner (angularDeriv 0 1 p) q := by
  funext t
  exact (hasDerivAt_rot01Inner p q t).deriv

theorem deriv_rot12Inner (p q : Poly3) :
    deriv (rot12Inner p q) = rot12Inner (angularDeriv 1 2 p) q := by
  funext t
  exact (hasDerivAt_rot12Inner p q t).deriv

theorem deriv_rot20Inner (p q : Poly3) :
    deriv (rot20Inner p q) = rot20Inner (angularDeriv 2 0 p) q := by
  funext t
  exact (hasDerivAt_rot20Inner p q t).deriv

/-- The canonical map from degree-`n` harmonic homogeneous ambient polynomials to the `L²`
degree-`n` spherical harmonic sector. -/
noncomputable def harmonicToSectorL2 (n : ℕ) :
    harmonicHomogeneousSubmodule n →ₗ[ℝ] sectorL2 n :=
  (sectorToSectorL2 n).comp (restrictToSector n)

@[simp] theorem harmonicToSectorL2_coe (n : ℕ) (p : harmonicHomogeneousSubmodule n) :
    ((harmonicToSectorL2 n p : sectorL2 n) : L2S2Geom) =
      continuousToLp (restrictToSphere p.1) := rfl

theorem harmonicToSectorL2_surjective (n : ℕ) :
    Function.Surjective (harmonicToSectorL2 n) := by
  intro u
  rcases sectorToSectorL2_surjective n u with ⟨f, rfl⟩
  rcases restrictToSector_surjective n f with ⟨p, rfl⟩
  exact ⟨p, rfl⟩

/-- The rotation action restricted to the degree-`n` `L²` harmonic sector. -/
noncomputable def sectorCompL2Rotation (ρ : Rotation) (n : ℕ) :
    sectorL2 n →ₗᵢ[ℝ] sectorL2 n where
  toLinearMap :=
    { toFun := fun x => ⟨Rotation.compL2Rotation ρ x.1, compL2Rotation_mem_sectorL2 ρ n x.2⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  norm_map' := by
    intro x
    simpa using (Rotation.compL2Rotation ρ).norm_map x.1

/-- The `(0,1)`-rotation flow on the degree-`n` `L²` harmonic sector. -/
noncomputable def sectorRotation01 (n : ℕ) (t : ℝ) :
    sectorL2 n →ₗᵢ[ℝ] sectorL2 n :=
  sectorCompL2Rotation ((rotation01 t).symm) n

/-- The `(1,2)`-rotation flow on the degree-`n` `L²` harmonic sector. -/
noncomputable def sectorRotation12 (n : ℕ) (t : ℝ) :
    sectorL2 n →ₗᵢ[ℝ] sectorL2 n :=
  sectorCompL2Rotation ((rotation12 t).symm) n

/-- The `(2,0)`-rotation flow on the degree-`n` `L²` harmonic sector. -/
noncomputable def sectorRotation20 (n : ℕ) (t : ℝ) :
    sectorL2 n →ₗᵢ[ℝ] sectorL2 n :=
  sectorCompL2Rotation ((rotation20 t).symm) n

@[simp] theorem sectorOrthogonalProjection_compL2Rotation_apply (ρ : Rotation) (n : ℕ)
    (x : L2S2Geom) :
    (sectorL2 n).orthogonalProjection (Rotation.compL2Rotation ρ x) =
      sectorCompL2Rotation ρ n ((sectorL2 n).orthogonalProjection x) := by
  apply Subtype.ext
  simpa [sectorCompL2Rotation] using sectorL2_starProjection_compL2Rotation_apply ρ n x

@[simp] theorem sectorRotation01_harmonicToSectorL2_coe
    (n : ℕ) (p : harmonicHomogeneousSubmodule n) (t : ℝ) :
    ((sectorRotation01 n t (harmonicToSectorL2 n p) : sectorL2 n) : L2S2Geom) =
      continuousToLp (rot01Continuous p.1 t) := by
  simpa [sectorRotation01, sectorCompL2Rotation, harmonicToSectorL2,
    rot01Continuous_eq_compContinuous] using
    (continuousToLp_compContinuous_symm ((rotation01 t).symm) (restrictToSphere p.1))

@[simp] theorem sectorRotation12_harmonicToSectorL2_coe
    (n : ℕ) (p : harmonicHomogeneousSubmodule n) (t : ℝ) :
    ((sectorRotation12 n t (harmonicToSectorL2 n p) : sectorL2 n) : L2S2Geom) =
      continuousToLp (rot12Continuous p.1 t) := by
  simpa [sectorRotation12, sectorCompL2Rotation, harmonicToSectorL2,
    rot12Continuous_eq_compContinuous] using
    (continuousToLp_compContinuous_symm ((rotation12 t).symm) (restrictToSphere p.1))

@[simp] theorem sectorRotation20_harmonicToSectorL2_coe
    (n : ℕ) (p : harmonicHomogeneousSubmodule n) (t : ℝ) :
    ((sectorRotation20 n t (harmonicToSectorL2 n p) : sectorL2 n) : L2S2Geom) =
      continuousToLp (rot20Continuous p.1 t) := by
  simpa [sectorRotation20, sectorCompL2Rotation, harmonicToSectorL2,
    rot20Continuous_eq_compContinuous] using
    (continuousToLp_compContinuous_symm ((rotation20 t).symm) (restrictToSphere p.1))

theorem inner_sectorRotation01_harmonicToSectorL2
    {n k : ℕ} (p : harmonicHomogeneousSubmodule n) (q : harmonicHomogeneousSubmodule k)
    (t : ℝ) :
    inner ℝ
      (((sectorRotation01 n t (harmonicToSectorL2 n p) : sectorL2 n) : L2S2Geom))
      (((harmonicToSectorL2 k q : sectorL2 k) : L2S2Geom)) =
      rot01Inner p.1 q.1 t := by
  rw [sectorRotation01_harmonicToSectorL2_coe, harmonicToSectorL2_coe]
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (rot01Continuous p.1 t)
    (restrictToSphere q.1)]
  simp [rot01Inner, rot01InnerIntegrand, rot01Continuous, rot01Eval, mul_comm]

theorem inner_sectorRotation12_harmonicToSectorL2
    {n k : ℕ} (p : harmonicHomogeneousSubmodule n) (q : harmonicHomogeneousSubmodule k)
    (t : ℝ) :
    inner ℝ
      (((sectorRotation12 n t (harmonicToSectorL2 n p) : sectorL2 n) : L2S2Geom))
      (((harmonicToSectorL2 k q : sectorL2 k) : L2S2Geom)) =
      rot12Inner p.1 q.1 t := by
  rw [sectorRotation12_harmonicToSectorL2_coe, harmonicToSectorL2_coe]
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (rot12Continuous p.1 t)
    (restrictToSphere q.1)]
  simp [rot12Inner, rot12InnerIntegrand, rot12Continuous, rot12Eval, mul_comm]

theorem inner_sectorRotation20_harmonicToSectorL2
    {n k : ℕ} (p : harmonicHomogeneousSubmodule n) (q : harmonicHomogeneousSubmodule k)
    (t : ℝ) :
    inner ℝ
      (((sectorRotation20 n t (harmonicToSectorL2 n p) : sectorL2 n) : L2S2Geom))
      (((harmonicToSectorL2 k q : sectorL2 k) : L2S2Geom)) =
      rot20Inner p.1 q.1 t := by
  rw [sectorRotation20_harmonicToSectorL2_coe, harmonicToSectorL2_coe]
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (rot20Continuous p.1 t)
    (restrictToSphere q.1)]
  simp [rot20Inner, rot20InnerIntegrand, rot20Continuous, rot20Eval, mul_comm]

theorem sum_secondDerivAt_zero_rotInner_eq_neg_degreeWeight
    {n k : ℕ} (p : harmonicHomogeneousSubmodule n) (q : harmonicHomogeneousSubmodule k) :
    deriv (deriv (rot01Inner p.1 q.1)) 0 +
        deriv (deriv (rot12Inner p.1 q.1)) 0 +
      deriv (deriv (rot20Inner p.1 q.1)) 0 =
      -((((n * (n + 1) : ℕ) : ℝ))) *
        inner ℝ (continuousToLp (restrictToSphere p.1)) (continuousToLp (restrictToSphere q.1)) := by
  rw [deriv_rot01Inner, deriv_rot01Inner, deriv_rot12Inner, deriv_rot12Inner,
    deriv_rot20Inner, deriv_rot20Inner]
  rw [rot01Inner_zero, rot12Inner_zero, rot20Inner_zero]
  have hsum := sum_angularDeriv_sq_eq_neg_degree_weight (n := n) p.2
  calc
    inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 0 1 (angularDeriv 0 1 p.1))))
        (continuousToLp (restrictToSphere q.1)) +
      inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 1 2 (angularDeriv 1 2 p.1))))
        (continuousToLp (restrictToSphere q.1)) +
      inner ℝ
        (continuousToLp (restrictToSphere (angularDeriv 2 0 (angularDeriv 2 0 p.1))))
        (continuousToLp (restrictToSphere q.1))
        =
      inner ℝ
        (continuousToLp <|
          restrictToSphere
            (angularDeriv 0 1 (angularDeriv 0 1 p.1) +
              angularDeriv 1 2 (angularDeriv 1 2 p.1) +
              angularDeriv 2 0 (angularDeriv 2 0 p.1)))
        (continuousToLp (restrictToSphere q.1)) := by
          simp [inner_add_left, add_assoc]
    _ =
      inner ℝ
        (continuousToLp (restrictToSphere (-((((n * (n + 1) : ℕ) : ℝ)) • p.1)))
        )
        (continuousToLp (restrictToSphere q.1)) := by
          rw [hsum]
    _ = -((((n * (n + 1) : ℕ) : ℝ))) *
        inner ℝ (continuousToLp (restrictToSphere p.1)) (continuousToLp (restrictToSphere q.1)) := by
          rw [restrictToSphere.map_neg, ContinuousLinearMap.map_neg, inner_neg_left,
            restrictToSphere.map_smul, ContinuousLinearMap.map_smul, inner_smul_left]
          simp

theorem sum_secondDerivAt_zero_sectorRotation_eq_neg_degreeWeight
    {n k : ℕ} (u : sectorL2 n) (v : sectorL2 k) :
    deriv (deriv
      (fun t => inner ℝ (((sectorRotation01 n t u : sectorL2 n) : L2S2Geom)) (v : L2S2Geom))) 0 +
        deriv (deriv
          (fun t => inner ℝ (((sectorRotation12 n t u : sectorL2 n) : L2S2Geom)) (v : L2S2Geom))) 0 +
      deriv (deriv
        (fun t => inner ℝ (((sectorRotation20 n t u : sectorL2 n) : L2S2Geom)) (v : L2S2Geom))) 0 =
      -((((n * (n + 1) : ℕ) : ℝ))) * inner ℝ (u : L2S2Geom) (v : L2S2Geom) := by
  rcases harmonicToSectorL2_surjective n u with ⟨p, rfl⟩
  rcases harmonicToSectorL2_surjective k v with ⟨q, rfl⟩
  have h01 :
      (fun t =>
        inner ℝ
          (((sectorRotation01 n t (harmonicToSectorL2 n p) : sectorL2 n) : L2S2Geom))
          (((harmonicToSectorL2 k q : sectorL2 k) : L2S2Geom))) =
        rot01Inner p.1 q.1 := by
    funext t
    exact inner_sectorRotation01_harmonicToSectorL2 p q t
  have h12 :
      (fun t =>
        inner ℝ
          (((sectorRotation12 n t (harmonicToSectorL2 n p) : sectorL2 n) : L2S2Geom))
          (((harmonicToSectorL2 k q : sectorL2 k) : L2S2Geom))) =
        rot12Inner p.1 q.1 := by
    funext t
    exact inner_sectorRotation12_harmonicToSectorL2 p q t
  have h20 :
      (fun t =>
        inner ℝ
          (((sectorRotation20 n t (harmonicToSectorL2 n p) : sectorL2 n) : L2S2Geom))
          (((harmonicToSectorL2 k q : sectorL2 k) : L2S2Geom))) =
        rot20Inner p.1 q.1 := by
    funext t
    exact inner_sectorRotation20_harmonicToSectorL2 p q t
  rw [h01, h12, h20]
  simpa [harmonicToSectorL2] using sum_secondDerivAt_zero_rotInner_eq_neg_degreeWeight p q

/-- The `(m,n)` block of orthogonal projection onto a closed subspace, relative to the harmonic
sector decomposition. -/
noncomputable def sectorBlock (K : ClosedSubmodule ℝ L2S2Geom) (m n : ℕ) :
    sectorL2 n →L[ℝ] sectorL2 m :=
  (sectorL2 m).orthogonalProjection ∘L K.toSubmodule.starProjection ∘L (sectorL2 n).subtypeL

@[simp] theorem sectorBlock_coe_apply (K : ClosedSubmodule ℝ L2S2Geom) (m n : ℕ)
    (u : sectorL2 n) :
    ((sectorBlock K m n u : sectorL2 m) : L2S2Geom) =
      (sectorL2 m).starProjection (K.toSubmodule.starProjection u.1) := rfl

theorem sectorBlock_sectorRotation01
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K)
    (m n : ℕ) (t : ℝ) (u : sectorL2 n) :
    sectorRotation01 m t (sectorBlock K m n u) = sectorBlock K m n (sectorRotation01 n t u) := by
  apply Subtype.ext
  change
    Rotation.compL2Rotation ((rotation01 t).symm)
        (((sectorBlock K m n u : sectorL2 m) : L2S2Geom)) =
      ((sectorBlock K m n (sectorRotation01 n t u) : sectorL2 m) : L2S2Geom)
  rw [sectorBlock_coe_apply, sectorBlock_coe_apply]
  calc
    Rotation.compL2Rotation ((rotation01 t).symm)
        ((sectorL2 m).starProjection (K.toSubmodule.starProjection u.1))
        =
      (sectorL2 m).starProjection
        (Rotation.compL2Rotation ((rotation01 t).symm) (K.toSubmodule.starProjection u.1)) := by
          symm
          exact sectorL2_starProjection_compL2Rotation_apply ((rotation01 t).symm) m
            (K.toSubmodule.starProjection u.1)
    _ =
      (sectorL2 m).starProjection
        (K.toSubmodule.starProjection (Rotation.compL2Rotation ((rotation01 t).symm) u.1)) := by
          rw [← ClosedSubmodule.starProjection_compL2Rotation_apply K hK ((rotation01 t).symm) u.1]
    _ =
      (sectorL2 m).starProjection (K.toSubmodule.starProjection ((sectorRotation01 n t u).1)) := by
          rfl

theorem sectorBlock_sectorRotation12
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K)
    (m n : ℕ) (t : ℝ) (u : sectorL2 n) :
    sectorRotation12 m t (sectorBlock K m n u) = sectorBlock K m n (sectorRotation12 n t u) := by
  apply Subtype.ext
  change
    Rotation.compL2Rotation ((rotation12 t).symm)
        (((sectorBlock K m n u : sectorL2 m) : L2S2Geom)) =
      ((sectorBlock K m n (sectorRotation12 n t u) : sectorL2 m) : L2S2Geom)
  rw [sectorBlock_coe_apply, sectorBlock_coe_apply]
  calc
    Rotation.compL2Rotation ((rotation12 t).symm)
        ((sectorL2 m).starProjection (K.toSubmodule.starProjection u.1))
        =
      (sectorL2 m).starProjection
        (Rotation.compL2Rotation ((rotation12 t).symm) (K.toSubmodule.starProjection u.1)) := by
          symm
          exact sectorL2_starProjection_compL2Rotation_apply ((rotation12 t).symm) m
            (K.toSubmodule.starProjection u.1)
    _ =
      (sectorL2 m).starProjection
        (K.toSubmodule.starProjection (Rotation.compL2Rotation ((rotation12 t).symm) u.1)) := by
          rw [← ClosedSubmodule.starProjection_compL2Rotation_apply K hK ((rotation12 t).symm) u.1]
    _ =
      (sectorL2 m).starProjection (K.toSubmodule.starProjection ((sectorRotation12 n t u).1)) := by
          rfl

theorem sectorBlock_sectorRotation20
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K)
    (m n : ℕ) (t : ℝ) (u : sectorL2 n) :
    sectorRotation20 m t (sectorBlock K m n u) = sectorBlock K m n (sectorRotation20 n t u) := by
  apply Subtype.ext
  change
    Rotation.compL2Rotation ((rotation20 t).symm)
        (((sectorBlock K m n u : sectorL2 m) : L2S2Geom)) =
      ((sectorBlock K m n (sectorRotation20 n t u) : sectorL2 m) : L2S2Geom)
  rw [sectorBlock_coe_apply, sectorBlock_coe_apply]
  calc
    Rotation.compL2Rotation ((rotation20 t).symm)
        ((sectorL2 m).starProjection (K.toSubmodule.starProjection u.1))
        =
      (sectorL2 m).starProjection
        (Rotation.compL2Rotation ((rotation20 t).symm) (K.toSubmodule.starProjection u.1)) := by
          symm
          exact sectorL2_starProjection_compL2Rotation_apply ((rotation20 t).symm) m
            (K.toSubmodule.starProjection u.1)
    _ =
      (sectorL2 m).starProjection
        (K.toSubmodule.starProjection (Rotation.compL2Rotation ((rotation20 t).symm) u.1)) := by
          rw [← ClosedSubmodule.starProjection_compL2Rotation_apply K hK ((rotation20 t).symm) u.1]
    _ =
      (sectorL2 m).starProjection (K.toSubmodule.starProjection ((sectorRotation20 n t u).1)) := by
          rfl

theorem inner_sectorBlock_apply_eq_inner_apply_sectorBlock
    (K : ClosedSubmodule ℝ L2S2Geom) (m n : ℕ) (u : sectorL2 n) (v : sectorL2 m) :
    inner ℝ (((sectorBlock K m n u : sectorL2 m) : L2S2Geom)) (v : L2S2Geom) =
      inner ℝ (u : L2S2Geom) (((sectorBlock K n m v : sectorL2 n) : L2S2Geom)) := by
  calc
    inner ℝ (((sectorBlock K m n u : sectorL2 m) : L2S2Geom)) (v : L2S2Geom)
        = inner ℝ (K.toSubmodule.starProjection u.1) (v : L2S2Geom) := by
            rw [sectorBlock_coe_apply]
            simpa using
              (sectorL2 m).inner_starProjection_left_eq_right
                (K.toSubmodule.starProjection u.1) v.1
    _ = inner ℝ u.1 (K.toSubmodule.starProjection v.1) := by
          simpa using (K.toSubmodule.inner_starProjection_left_eq_right u.1 v.1)
    _ = inner ℝ u.1 ((sectorL2 n).starProjection (K.toSubmodule.starProjection v.1)) := by
          rw [← (sectorL2 n).starProjection_eq_self_iff.mpr u.2]
          simpa using (sectorL2 n).inner_starProjection_left_eq_right u.1
            (K.toSubmodule.starProjection v.1)
    _ = inner ℝ (u : L2S2Geom) (((sectorBlock K n m v : sectorL2 n) : L2S2Geom)) := by
          rw [sectorBlock_coe_apply]

theorem inner_sectorBlock_eq_zero_of_ne
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K)
    {m n : ℕ} (hmn : m ≠ n) (u : sectorL2 n) (v : sectorL2 m) :
    inner ℝ (sectorBlock K m n u) v = 0 := by
  let B : sectorL2 n →L[ℝ] sectorL2 m := sectorBlock K m n
  let a : ℝ := (((m * (m + 1) : ℕ) : ℝ))
  let b : ℝ := (((n * (n + 1) : ℕ) : ℝ))
  have h01 :
      (fun t => inner ℝ (sectorRotation01 m t (B u)) v) =
        fun t => inner ℝ (sectorRotation01 n t u) ((sectorBlock K n m) v) := by
    funext t
    calc
      inner ℝ (sectorRotation01 m t (B u)) v
          = inner ℝ (B (sectorRotation01 n t u)) v := by
              simpa [B] using congrArg (fun w : sectorL2 m => inner ℝ w v)
                (sectorBlock_sectorRotation01 K hK m n t u)
      _ = inner ℝ (sectorRotation01 n t u) ((sectorBlock K n m) v) := by
              simpa [B] using
                inner_sectorBlock_apply_eq_inner_apply_sectorBlock K m n (sectorRotation01 n t u) v
  have h12 :
      (fun t => inner ℝ (sectorRotation12 m t (B u)) v) =
        fun t => inner ℝ (sectorRotation12 n t u) ((sectorBlock K n m) v) := by
    funext t
    calc
      inner ℝ (sectorRotation12 m t (B u)) v
          = inner ℝ (B (sectorRotation12 n t u)) v := by
              simpa [B] using congrArg (fun w : sectorL2 m => inner ℝ w v)
                (sectorBlock_sectorRotation12 K hK m n t u)
      _ = inner ℝ (sectorRotation12 n t u) ((sectorBlock K n m) v) := by
              simpa [B] using
                inner_sectorBlock_apply_eq_inner_apply_sectorBlock K m n (sectorRotation12 n t u) v
  have h20 :
      (fun t => inner ℝ (sectorRotation20 m t (B u)) v) =
        fun t => inner ℝ (sectorRotation20 n t u) ((sectorBlock K n m) v) := by
    funext t
    calc
      inner ℝ (sectorRotation20 m t (B u)) v
          = inner ℝ (B (sectorRotation20 n t u)) v := by
              simpa [B] using congrArg (fun w : sectorL2 m => inner ℝ w v)
                (sectorBlock_sectorRotation20 K hK m n t u)
      _ = inner ℝ (sectorRotation20 n t u) ((sectorBlock K n m) v) := by
              simpa [B] using
                inner_sectorBlock_apply_eq_inner_apply_sectorBlock K m n (sectorRotation20 n t u) v
  have hderiv01 : deriv (deriv (fun t => inner ℝ (sectorRotation01 m t (B u)) v)) 0 =
      deriv (deriv (fun t => inner ℝ (sectorRotation01 n t u) ((sectorBlock K n m) v))) 0 := by
    simpa [h01] using congrArg (fun f : ℝ → ℝ => deriv (deriv f) 0) h01
  have hderiv12 : deriv (deriv (fun t => inner ℝ (sectorRotation12 m t (B u)) v)) 0 =
      deriv (deriv (fun t => inner ℝ (sectorRotation12 n t u) ((sectorBlock K n m) v))) 0 := by
    simpa [h12] using congrArg (fun f : ℝ → ℝ => deriv (deriv f) 0) h12
  have hderiv20 : deriv (deriv (fun t => inner ℝ (sectorRotation20 m t (B u)) v)) 0 =
      deriv (deriv (fun t => inner ℝ (sectorRotation20 n t u) ((sectorBlock K n m) v))) 0 := by
    simpa [h20] using congrArg (fun f : ℝ → ℝ => deriv (deriv f) 0) h20
  have hleft :
      deriv (deriv (fun t => inner ℝ (sectorRotation01 m t (B u)) v)) 0 +
          deriv (deriv (fun t => inner ℝ (sectorRotation12 m t (B u)) v)) 0 +
        deriv (deriv (fun t => inner ℝ (sectorRotation20 m t (B u)) v)) 0 =
        -a * inner ℝ (B u) v := by
    simpa [a, B] using sum_secondDerivAt_zero_sectorRotation_eq_neg_degreeWeight (B u) v
  have hright :
      deriv (deriv (fun t => inner ℝ (sectorRotation01 n t u) ((sectorBlock K n m) v))) 0 +
          deriv (deriv (fun t => inner ℝ (sectorRotation12 n t u) ((sectorBlock K n m) v))) 0 +
        deriv (deriv (fun t => inner ℝ (sectorRotation20 n t u) ((sectorBlock K n m) v))) 0 =
        -b * inner ℝ u ((sectorBlock K n m) v) := by
    simpa [b] using
      sum_secondDerivAt_zero_sectorRotation_eq_neg_degreeWeight u ((sectorBlock K n m) v)
  have hadj : inner ℝ u ((sectorBlock K n m) v) = inner ℝ (B u) v := by
    simpa [B] using (inner_sectorBlock_apply_eq_inner_apply_sectorBlock K m n u v).symm
  have hEq : -a * inner ℝ (B u) v = -b * inner ℝ (B u) v := by
    have hsumderiv :
        deriv (deriv (fun t => inner ℝ (sectorRotation01 m t (B u)) v)) 0 +
            deriv (deriv (fun t => inner ℝ (sectorRotation12 m t (B u)) v)) 0 +
          deriv (deriv (fun t => inner ℝ (sectorRotation20 m t (B u)) v)) 0 =
          deriv (deriv (fun t => inner ℝ (sectorRotation01 n t u) ((sectorBlock K n m) v))) 0 +
            deriv (deriv (fun t => inner ℝ (sectorRotation12 n t u) ((sectorBlock K n m) v))) 0 +
          deriv (deriv (fun t => inner ℝ (sectorRotation20 n t u) ((sectorBlock K n m) v))) 0 := by
      exact congrArg₂ (fun x z => x + z)
        (congrArg₂ (· + ·) hderiv01 hderiv12) hderiv20
    calc
      -a * inner ℝ (B u) v
          =
        deriv (deriv (fun t => inner ℝ (sectorRotation01 m t (B u)) v)) 0 +
            deriv (deriv (fun t => inner ℝ (sectorRotation12 m t (B u)) v)) 0 +
          deriv (deriv (fun t => inner ℝ (sectorRotation20 m t (B u)) v)) 0 := hleft.symm
      _ =
        deriv (deriv (fun t => inner ℝ (sectorRotation01 n t u) ((sectorBlock K n m) v))) 0 +
            deriv (deriv (fun t => inner ℝ (sectorRotation12 n t u) ((sectorBlock K n m) v))) 0 +
          deriv (deriv (fun t => inner ℝ (sectorRotation20 n t u) ((sectorBlock K n m) v))) 0 := hsumderiv
      _ = -b * inner ℝ u ((sectorBlock K n m) v) := hright
      _ = -b * inner ℝ (B u) v := by rw [hadj]
  have hmul : (b - a) * inner ℝ (B u) v = 0 := by
    calc
      (b - a) * inner ℝ (B u) v = (-a * inner ℝ (B u) v) - (-b * inner ℝ (B u) v) := by
        ring
      _ = 0 := sub_eq_zero.mpr hEq
  rcases mul_eq_zero.mp hmul with hcoeff | hinner
  · have hab : b = a := sub_eq_zero.mp hcoeff
    exact False.elim <| degreeWeight_ne_of_ne hmn hab.symm
  · simpa [B] using hinner

theorem sectorBlock_eq_zero_of_ne
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K)
    {m n : ℕ} (hmn : m ≠ n) :
    sectorBlock K m n = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  have hzero : ∀ v : sectorL2 m, inner ℝ (sectorBlock K m n u) v = inner ℝ (0 : sectorL2 m) v := by
    intro v
    simpa using inner_sectorBlock_eq_zero_of_ne K hK hmn u v
  exact ext_inner_right ℝ hzero

theorem hasSum_sectorL2_starProjection (x : L2S2Geom) :
    HasSum (fun n : ℕ => (sectorL2 n).starProjection x) x := by
  let w := sectorL2_isHilbertSum.linearIsometryEquiv x
  have hsum := sectorL2_isHilbertSum.hasSum_linearIsometryEquiv_symm w
  have hfun :
      (fun n : ℕ => ((w n : sectorL2 n) : L2S2Geom)) =
        fun n : ℕ => (sectorL2 n).starProjection x := by
    funext n
    symm
    simpa [w] using
      IsHilbertSum.starProjection_eq_linearIsometryEquiv_symm_single
        (V := sectorL2) sectorL2_isHilbertSum n x
  simpa [w, hfun] using hsum

theorem ClosedSubmodule.starProjection_mem_sectorL2_of_isRotationInvariant
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K)
    {n : ℕ} {x : L2S2Geom} (hx : x ∈ sectorL2 n) :
    K.toSubmodule.starProjection x ∈ sectorL2 n := by
  let y : L2S2Geom := K.toSubmodule.starProjection x
  have hsum : HasSum (fun m : ℕ => (sectorL2 m).starProjection y) y :=
    hasSum_sectorL2_starProjection y
  have hterms : ∀ m : ℕ, m ≠ n → (sectorL2 m).starProjection y = 0 := by
    intro m hmn
    let u : sectorL2 n := ⟨x, hx⟩
    have hb : sectorBlock K m n u = 0 := by
      simpa using congrArg (fun f : sectorL2 n →L[ℝ] sectorL2 m => f u)
        (sectorBlock_eq_zero_of_ne K hK hmn)
    simpa [sectorBlock, y, u] using congrArg (fun v : sectorL2 m => (v : L2S2Geom)) hb
  have hfun :
      (fun m : ℕ => (sectorL2 m).starProjection y) =
        fun m : ℕ => if m = n then (sectorL2 n).starProjection y else 0 := by
    funext m
    by_cases hm : m = n
    · simp [hm]
    · simp [hm, hterms m hm]
  have hsum' :
      HasSum (fun m : ℕ => if m = n then (sectorL2 n).starProjection y else 0) y := by
    simpa [hfun] using hsum
  have hsingle :
      HasSum (fun m : ℕ => if m = n then (sectorL2 n).starProjection y else 0)
        ((sectorL2 n).starProjection y) := by
    exact hasSum_ite_eq n ((sectorL2 n).starProjection y)
  have hy : (sectorL2 n).starProjection y = y := hsingle.unique hsum'
  exact (sectorL2 n).starProjection_eq_self_iff.mp hy

theorem ClosedSubmodule.sectorL2_starProjection_commute_of_isRotationInvariant
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K)
    (n : ℕ) (x : L2S2Geom) :
    (sectorL2 n).starProjection (K.toSubmodule.starProjection x) =
      K.toSubmodule.starProjection ((sectorL2 n).starProjection x) := by
  refine (sectorL2 n).eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact
      ClosedSubmodule.starProjection_mem_sectorL2_of_isRotationInvariant K hK
        ((sectorL2 n).starProjection_apply_mem x)
  · intro v hv
    have hvK :
        K.toSubmodule.starProjection v ∈ sectorL2 n :=
      ClosedSubmodule.starProjection_mem_sectorL2_of_isRotationInvariant K hK hv
    have hproj :
        inner ℝ ((sectorL2 n).starProjection x) (K.toSubmodule.starProjection v) =
          inner ℝ x (K.toSubmodule.starProjection v) := by
      calc
        inner ℝ ((sectorL2 n).starProjection x) (K.toSubmodule.starProjection v)
            = inner ℝ x ((sectorL2 n).starProjection (K.toSubmodule.starProjection v)) := by
                exact
                  (sectorL2 n).inner_starProjection_left_eq_right x
                    (K.toSubmodule.starProjection v)
        _ = inner ℝ x (K.toSubmodule.starProjection v) := by
              rw [(sectorL2 n).starProjection_eq_self_iff.mpr hvK]
    calc
      inner ℝ
          (K.toSubmodule.starProjection x -
            K.toSubmodule.starProjection ((sectorL2 n).starProjection x)) v
          =
        inner ℝ (K.toSubmodule.starProjection x) v -
          inner ℝ (K.toSubmodule.starProjection ((sectorL2 n).starProjection x)) v := by
            rw [inner_sub_left]
      _ =
        inner ℝ x (K.toSubmodule.starProjection v) -
          inner ℝ ((sectorL2 n).starProjection x) (K.toSubmodule.starProjection v) := by
            rw [K.toSubmodule.inner_starProjection_left_eq_right,
              K.toSubmodule.inner_starProjection_left_eq_right]
      _ = 0 := by simpa [hproj]

theorem ClosedSubmodule.sectorL2_starProjection_mem_of_isRotationInvariant
    (K : ClosedSubmodule ℝ L2S2Geom) (hK : ClosedSubmodule.IsRotationInvariant K)
    (n : ℕ) {x : L2S2Geom} (hx : x ∈ K.toSubmodule) :
    (sectorL2 n).starProjection x ∈ K.toSubmodule := by
  have hxfix : K.toSubmodule.starProjection x = x :=
    (K.toSubmodule.starProjection_eq_self_iff).mpr hx
  have hz_fix :
      K.toSubmodule.starProjection ((sectorL2 n).starProjection x) =
        (sectorL2 n).starProjection x := by
    calc
      K.toSubmodule.starProjection ((sectorL2 n).starProjection x)
          = (sectorL2 n).starProjection (K.toSubmodule.starProjection x) := by
              symm
              exact
                ClosedSubmodule.sectorL2_starProjection_commute_of_isRotationInvariant K hK n x
      _ = (sectorL2 n).starProjection x := by rw [hxfix]
  exact (K.toSubmodule.starProjection_eq_self_iff).mp hz_fix

end SphericalHarmonics
