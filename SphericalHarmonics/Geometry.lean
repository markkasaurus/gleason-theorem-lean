import Mathlib

open scoped MeasureTheory Pointwise

namespace SphericalHarmonics

/-- The ambient Euclidean space `ℝ^3`, encoded as `EuclideanSpace ℝ (Fin 3)`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The real unit `2`-sphere `S² ⊂ ℝ^3`. -/
abbrev S2 := ↥(Metric.sphere (0 : E3) 1)

/-- The full orthogonal action on `ℝ^3`. This contains the usual rotation group. -/
abbrev Rotation := E3 ≃ₗᵢ[ℝ] E3

namespace S2

@[simp] theorem norm_eq_one (x : S2) : ‖(x : E3)‖ = 1 := by
  simpa [Metric.mem_sphere, dist_eq_norm] using x.2

@[simp] theorem norm_sq_eq_one (x : S2) : ‖(x : E3)‖ ^ 2 = (1 : ℝ) := by
  rw [norm_eq_one]
  norm_num

end S2

instance : CompactSpace S2 :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E3) 1)

/-- The natural surface measure on `S²`, defined as the `2`-dimensional Hausdorff measure on the
sphere itself. -/
noncomputable abbrev surfaceMeasure : MeasureTheory.Measure S2 := MeasureTheory.Measure.hausdorffMeasure 2

/-- A finite rotation-invariant surface measure on `S²`, obtained from the polar decomposition of
Lebesgue measure on `ℝ^3`. This is the measure used for the `L²` theory. -/
noncomputable abbrev rotationMeasure : MeasureTheory.Measure S2 :=
  (MeasureTheory.volume : MeasureTheory.Measure E3).toSphere

instance : MeasureTheory.IsFiniteMeasure rotationMeasure := by
  infer_instance

instance : rotationMeasure.WeaklyRegular := by
  infer_instance

instance : rotationMeasure.IsOpenPosMeasure := by
  infer_instance

namespace Rotation

/-- The orthogonal action restricted to the sphere. -/
@[simps]
def toSphere (ρ : Rotation) (x : S2) : S2 := by
  refine ⟨ρ x, ?_⟩
  have hx : (ρ x : E3) ∈ ρ '' Metric.sphere (0 : E3) 1 := ⟨x, x.2, rfl⟩
  rw [ρ.image_sphere, ρ.map_zero] at hx
  exact hx

/-- The orthogonal action as an isometry equivalence of `S²`. -/
noncomputable def toSphereEquiv (ρ : Rotation) : S2 ≃ᵢ S2 where
  toEquiv :=
    { toFun := Rotation.toSphere ρ
      invFun := Rotation.toSphere ρ.symm
      left_inv := by
        intro x
        apply Subtype.ext
        simp [Rotation.toSphere]
      right_inv := by
        intro x
        apply Subtype.ext
        simp [Rotation.toSphere] }
  isometry_toFun := by
    intro x y
    change edist (ρ x : E3) (ρ y : E3) = edist (x : E3) (y : E3)
    exact ρ.isometry.edist_eq (x : E3) (y : E3)

@[simp] theorem toSphereEquiv_apply (ρ : Rotation) (x : S2) :
    (ρ.toSphereEquiv x : E3) = ρ x := rfl

@[simp] theorem map_surfaceMeasure (ρ : Rotation) :
    MeasureTheory.Measure.map ρ.toSphereEquiv surfaceMeasure = surfaceMeasure := by
  simp [surfaceMeasure]

/-- Orthogonal maps preserve the surface measure on `S²`. -/
theorem measurePreserving (ρ : Rotation) :
    MeasureTheory.MeasurePreserving ρ.toSphereEquiv surfaceMeasure surfaceMeasure := by
  simpa [surfaceMeasure] using (ρ.toSphereEquiv).measurePreserving_hausdorffMeasure 2

theorem image_subtype_preimage_toSphereEquiv (ρ : Rotation) (s : Set S2) :
    ((↑) '' (ρ.toSphereEquiv ⁻¹' s : Set S2)) = ρ.symm '' ((↑) '' s) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨↑(ρ.toSphereEquiv y), ⟨ρ.toSphereEquiv y, hy, rfl⟩, ?_⟩
    simp
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨ρ.toSphereEquiv.symm z, ?_, ?_⟩
    · simpa using hz
    · change ((Rotation.toSphere ρ.symm z : S2) : E3) = ρ.symm (z : E3)
      rfl

@[simp] theorem map_rotationMeasure (ρ : Rotation) :
    MeasureTheory.Measure.map ρ.toSphereEquiv rotationMeasure = rotationMeasure := by
  let e : S2 ≃ᵐ S2 := ρ.toSphereEquiv.toHomeomorph.toMeasurableEquiv
  ext s hs
  rw [show MeasureTheory.Measure.map ρ.toSphereEquiv rotationMeasure =
      MeasureTheory.Measure.map e rotationMeasure by rfl,
    MeasurableEquiv.map_apply e,
    MeasureTheory.Measure.toSphere_apply' (μ := (MeasureTheory.volume : MeasureTheory.Measure E3))
      (e.measurable hs),
    MeasureTheory.Measure.toSphere_apply' (μ := (MeasureTheory.volume : MeasureTheory.Measure E3))
      hs]
  congr 1
  have hpre :
      ((↑) '' (e ⁻¹' s : Set S2)) = ρ.symm '' ((↑) '' s) := by
    simpa [e] using image_subtype_preimage_toSphereEquiv ρ s
  rw [hpre]
  have hsmul :
      Set.Ioo (0 : ℝ) 1 • (ρ.symm '' ((↑) '' s)) =
        ρ.symm '' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨r • z, ⟨r, hr, z, hz, rfl⟩, ?_⟩
      simp
    · rintro ⟨y, ⟨r, hr, z, hz, rfl⟩, rfl⟩
      refine ⟨r, hr, ρ.symm z, ⟨z, hz, rfl⟩, ?_⟩
      simp
  rw [hsmul]
  let eE : E3 ≃ᵐ E3 := ρ.toHomeomorph.toMeasurableEquiv
  calc
    (MeasureTheory.volume : MeasureTheory.Measure E3)
        (ρ.symm '' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s))) =
        (MeasureTheory.Measure.map eE (MeasureTheory.volume : MeasureTheory.Measure E3))
          (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
            rw [MeasurableEquiv.map_apply eE]
            congr 1
            ext x
            change (x ∈ ρ.symm '' (Set.Ioo (0 : ℝ) 1 • ((↑) '' s))) ↔
              (ρ x ∈ Set.Ioo (0 : ℝ) 1 • ((↑) '' s))
            constructor
            · intro hx
              rcases hx with ⟨y, hy, rfl⟩
              simpa using hy
            · intro hx
              exact ⟨ρ x, hx, by simp [eE]⟩
    _ = (MeasureTheory.volume : MeasureTheory.Measure E3)
          (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
            simpa [eE] using congrArg
              (fun μ : MeasureTheory.Measure E3 => μ (Set.Ioo (0 : ℝ) 1 • ((↑) '' s)))
              (LinearIsometryEquiv.measurePreserving ρ).map_eq

section ContinuousAction

variable {𝕜 : Type*} [NormedRing 𝕜] [NormedSpace ℝ 𝕜]

/-- Pullback action of an orthogonal map on continuous functions on `S²`. -/
noncomputable def compContinuous (ρ : Rotation) : C(S2, 𝕜) →ₗ[𝕜] C(S2, 𝕜) where
  toFun f := f.comp ⟨ρ.toSphereEquiv.symm, ρ.toSphereEquiv.symm.continuous⟩
  map_add' f g := by
    ext x
    rfl
  map_smul' c f := by
    ext x
    rfl

omit [NormedSpace ℝ 𝕜] in
@[simp] theorem compContinuous_apply (ρ : Rotation) (f : C(S2, 𝕜)) (x : S2) :
    compContinuous ρ f x = f (ρ.toSphereEquiv.symm x) := rfl

end ContinuousAction

section L2Action

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Pullback action of an orthogonal map on `L²(S²)`. -/
noncomputable def compL2 (ρ : Rotation) :
    MeasureTheory.Lp 𝕜 2 surfaceMeasure →ₗᵢ[𝕜] MeasureTheory.Lp 𝕜 2 surfaceMeasure := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  simpa using MeasureTheory.Lp.compMeasurePreservingₗᵢ 𝕜 ρ.toSphereEquiv ρ.measurePreserving

/-- Pullback action of an orthogonal map on `L²(S²)` for the rotation-invariant measure
`rotationMeasure`. -/
noncomputable def compL2Rotation (ρ : Rotation) :
    MeasureTheory.Lp 𝕜 2 rotationMeasure →ₗᵢ[𝕜] MeasureTheory.Lp 𝕜 2 rotationMeasure := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  let e : S2 ≃ᵐ S2 := ρ.toSphereEquiv.toHomeomorph.toMeasurableEquiv
  simpa using
    MeasureTheory.Lp.compMeasurePreservingₗᵢ 𝕜 e
      (by simpa [map_rotationMeasure] using
        (show MeasureTheory.MeasurePreserving e rotationMeasure rotationMeasure from
          ⟨e.measurable, by simpa [e] using map_rotationMeasure ρ⟩))

end L2Action

end Rotation

/-- The `i`-th coordinate function on the sphere. -/
noncomputable def coord (i : Fin 3) : C(S2, ℝ) where
  toFun x := x.1 i
  continuous_toFun :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp continuous_subtype_val

@[simp] theorem coord_apply (i : Fin 3) (x : S2) : coord i x = x.1 i := rfl

/-- The north pole `(0,0,1) ∈ S²`. -/
noncomputable def northPole : S2 := by
  refine ⟨EuclideanSpace.single (2 : Fin 3) (1 : ℝ), ?_⟩
  simp [EuclideanSpace.norm_single]

/-- The height function `x ↦ x₃` on `S²`. -/
noncomputable def height : C(S2, ℝ) := coord (2 : Fin 3)

@[simp] theorem height_apply (x : S2) : height x = x.1 (2 : Fin 3) := rfl

@[simp] theorem inner_northPole (x : E3) :
    inner ℝ (northPole : E3) x = x (2 : Fin 3) := by
  simp [northPole, EuclideanSpace.inner_single_left]

/-- A function on `S²` is zonal with pole `u` if it depends only on `⟪u, x⟫`. -/
def IsZonal {α : Type*} (pole : S2) (f : S2 → α) : Prop :=
  ∀ ⦃x y : S2⦄, inner ℝ (pole : E3) x = inner ℝ (pole : E3) y → f x = f y

@[simp] theorem isZonal_const {α : Type*} (pole : S2) (c : α) :
    IsZonal pole (fun _ : S2 => c) := by
  unfold IsZonal
  intro x y hxy
  rfl

theorem IsZonal.add {f g : S2 → ℝ} {pole : S2} (hf : IsZonal pole f) (hg : IsZonal pole g) :
    IsZonal pole (fun x => f x + g x) := by
  unfold IsZonal at hf hg ⊢
  intro x y hxy
  simp [hf hxy, hg hxy]

theorem IsZonal.smul {f : S2 → ℝ} {pole : S2} (c : ℝ) (hf : IsZonal pole f) :
    IsZonal pole (fun x => c * f x) := by
  unfold IsZonal at hf ⊢
  intro x y hxy
  simp [hf hxy]

@[simp] theorem height_isZonal : IsZonal northPole height := by
  unfold IsZonal
  intro x y hxy
  simpa [height, inner_northPole] using hxy

end SphericalHarmonics
