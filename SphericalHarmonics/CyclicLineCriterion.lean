import SphericalHarmonics.CyclicIrreducibility
import SphericalHarmonics.RotationInvariant
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

noncomputable section

open scoped ENNReal

namespace SphericalHarmonics

private theorem measurePreserving_toSphereEquiv_rotationMeasure (ρ : Rotation) :
    MeasureTheory.MeasurePreserving
      ((Rotation.toSphereEquiv ρ).toHomeomorph.toMeasurableEquiv)
      rotationMeasure rotationMeasure := by
  refine ⟨((Rotation.toSphereEquiv ρ).toHomeomorph.toMeasurableEquiv).measurable, ?_⟩
  simpa using Rotation.map_rotationMeasure ρ

@[simp] private theorem compL2Rotation_mul_apply
    (ρ σ : Rotation) (f : L2S2Geom) :
    Rotation.compL2Rotation ρ (Rotation.compL2Rotation σ f) =
      Rotation.compL2Rotation (σ * ρ) f := by
  apply Subtype.ext
  apply MeasureTheory.AEEqFun.ext
  have houter :
      (Rotation.compL2Rotation ρ (Rotation.compL2Rotation σ f) : MeasureTheory.Lp ℝ 2 rotationMeasure)
        =ᵐ[rotationMeasure]
      (Rotation.compL2Rotation σ f : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘
        (Rotation.toSphereEquiv ρ) := by
    simpa [Rotation.compL2Rotation] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving
        (g := Rotation.compL2Rotation σ f)
        (hf := measurePreserving_toSphereEquiv_rotationMeasure ρ))
  have hinner :
      (Rotation.compL2Rotation σ f : MeasureTheory.Lp ℝ 2 rotationMeasure) =ᵐ[rotationMeasure]
        (f : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘ (Rotation.toSphereEquiv σ) := by
    simpa [Rotation.compL2Rotation] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving
        (g := f)
        (hf := measurePreserving_toSphereEquiv_rotationMeasure σ))
  have hcomp :
      (Rotation.compL2Rotation σ f : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘
          (Rotation.toSphereEquiv ρ) =ᵐ[rotationMeasure]
        (f : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘
          (Rotation.toSphereEquiv σ) ∘ (Rotation.toSphereEquiv ρ) :=
    Filter.EventuallyEq.comp_tendsto hinner
      (measurePreserving_toSphereEquiv_rotationMeasure ρ).quasiMeasurePreserving.tendsto_ae
  have hmul :
      ((f : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘
          (Rotation.toSphereEquiv σ) ∘ (Rotation.toSphereEquiv ρ)) =ᵐ[rotationMeasure]
        (f : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘ (Rotation.toSphereEquiv (σ * ρ)) := by
    filter_upwards with x
    change f ((Rotation.toSphereEquiv σ) ((Rotation.toSphereEquiv ρ) x)) =
      f ((Rotation.toSphereEquiv (σ * ρ)) x)
    simp [Rotation.toSphereEquiv, Rotation.toSphere]
  have htarget :
      (Rotation.compL2Rotation (σ * ρ) f : MeasureTheory.Lp ℝ 2 rotationMeasure) =ᵐ[rotationMeasure]
        (f : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘ (Rotation.toSphereEquiv (σ * ρ)) := by
    simpa [Rotation.compL2Rotation] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving
        (g := f)
        (hf := measurePreserving_toSphereEquiv_rotationMeasure (σ * ρ)))
  exact houter.trans <| hcomp.trans <| hmul.trans htarget.symm

@[simp] theorem sectorCompL2Rotation_mul_apply
    (ρ σ : Rotation) (n : ℕ) (x : sectorL2 n) :
    sectorCompL2Rotation ρ n (sectorCompL2Rotation σ n x) =
      sectorCompL2Rotation (σ * ρ) n x := by
  apply Subtype.ext
  simpa [sectorCompL2Rotation] using compL2Rotation_mul_apply ρ σ (x : L2S2Geom)

@[simp] theorem sectorCompL2Rotation_one_apply
    (n : ℕ) (x : sectorL2 n) :
    sectorCompL2Rotation (1 : Rotation) n x = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply MeasureTheory.AEEqFun.ext
  have hone :
      (Rotation.compL2Rotation (1 : Rotation) (x : L2S2Geom) :
          MeasureTheory.Lp ℝ 2 rotationMeasure) =ᵐ[rotationMeasure]
        (x : MeasureTheory.Lp ℝ 2 rotationMeasure) ∘ (Rotation.toSphereEquiv (1 : Rotation)) := by
    simpa [Rotation.compL2Rotation] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving
        (g := (x : L2S2Geom))
        (hf := measurePreserving_toSphereEquiv_rotationMeasure (1 : Rotation)))
  filter_upwards [hone] with y hy
  simpa [Rotation.toSphereEquiv, Rotation.toSphere] using hy

@[simp] theorem sectorCompL2Rotation_symm_apply
    (ρ : Rotation) (n : ℕ) (x : sectorL2 n) :
    sectorCompL2Rotation ρ n (sectorCompL2Rotation ρ.symm n x) = x := by
  have hmul : ρ.symm * ρ = (1 : Rotation) := inv_mul_cancel ρ
  calc
    sectorCompL2Rotation ρ n (sectorCompL2Rotation ρ.symm n x)
        = sectorCompL2Rotation (ρ.symm * ρ) n x := sectorCompL2Rotation_mul_apply ρ ρ.symm n x
    _ = x := by simpa [hmul] using sectorCompL2Rotation_one_apply n x

@[simp] theorem sectorCompL2Rotation_apply_symm
    (ρ : Rotation) (n : ℕ) (x : sectorL2 n) :
    sectorCompL2Rotation ρ.symm n (sectorCompL2Rotation ρ n x) = x := by
  have hmul : ρ * ρ.symm = (1 : Rotation) := mul_inv_cancel ρ
  calc
    sectorCompL2Rotation ρ.symm n (sectorCompL2Rotation ρ n x)
        = sectorCompL2Rotation (ρ * ρ.symm) n x := sectorCompL2Rotation_mul_apply ρ.symm ρ n x
    _ = x := by simpa [hmul] using sectorCompL2Rotation_one_apply n x

theorem sectorRotationOrbitSpan_isRotationInvariant
    (n : ℕ) (u : sectorL2 n) :
    SectorSubmodule.IsRotationInvariant n (sectorRotationOrbitSpan n u) := by
  intro ρ x hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨σ, rfl⟩
    exact Submodule.subset_span ⟨σ * ρ, (sectorCompL2Rotation_mul_apply ρ σ n u).symm⟩
  · simp
  · intro x y _ _ hx hy
    simpa using Submodule.add_mem (sectorRotationOrbitSpan n u) hx hy
  · intro a x _ hx
    simpa using Submodule.smul_mem (sectorRotationOrbitSpan n u) a hx

namespace SectorSubmodule

theorem orthogonal_isRotationInvariant
    {n : ℕ} {W : Submodule ℝ (sectorL2 n)}
    (hW : IsRotationInvariant n W) :
    IsRotationInvariant n Wᗮ := by
  intro ρ x hx
  rw [Submodule.mem_orthogonal'] at hx ⊢
  intro y hy
  have hy' : sectorCompL2Rotation ρ.symm n y ∈ W := hW ρ.symm y hy
  have hx' := hx _ hy'
  calc
    inner ℝ (sectorCompL2Rotation ρ n x) y =
      inner ℝ (sectorCompL2Rotation ρ n x)
        (sectorCompL2Rotation ρ n (sectorCompL2Rotation ρ.symm n y)) := by
          rw [sectorCompL2Rotation_symm_apply]
    _ = inner ℝ x (sectorCompL2Rotation ρ.symm n y) := by
          simpa using
            (sectorCompL2Rotation ρ n).inner_map_map x (sectorCompL2Rotation ρ.symm n y)
    _ = 0 := hx'

end SectorSubmodule

/-- The distinguished line generated by a chosen vector in a harmonic sector. -/
def cyclicLine {n : ℕ} (u : sectorL2 n) : Submodule ℝ (sectorL2 n) :=
  Submodule.span ℝ ({u} : Set (sectorL2 n))

theorem cyclicLine_le_sectorRotationOrbitSpan {n : ℕ} (u : sectorL2 n) :
    cyclicLine u ≤ sectorRotationOrbitSpan n u := by
  refine Submodule.span_le.mpr ?_
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact Submodule.subset_span ⟨1, by simp⟩

/-- If every nonzero rotation-invariant subspace of a sector meets a distinguished line, then the
generator of that line is cyclic. -/
theorem sectorRotationOrbitSpan_eq_top_of_cyclicLine_meets_every_nonzero_invariant_submodule
    {n : ℕ} {u : sectorL2 n}
    (hhit :
      ∀ W : Submodule ℝ (sectorL2 n),
        SectorSubmodule.IsRotationInvariant n W →
        W ≠ ⊥ →
        cyclicLine u ⊓ W ≠ ⊥) :
    sectorRotationOrbitSpan n u = ⊤ := by
  by_contra horbit
  have hperp_nonbot : (sectorRotationOrbitSpan n u)ᗮ ≠ ⊥ := by
    intro hbot
    exact horbit (Submodule.orthogonal_eq_bot_iff.mp hbot)
  have hperp_hit :
      cyclicLine u ⊓ (sectorRotationOrbitSpan n u)ᗮ ≠ ⊥ :=
    hhit _ (SectorSubmodule.orthogonal_isRotationInvariant
      (sectorRotationOrbitSpan_isRotationInvariant n u)) hperp_nonbot
  have hline_bot :
      cyclicLine u ⊓ (sectorRotationOrbitSpan n u)ᗮ = ⊥ := by
    apply bot_unique
    calc
      cyclicLine u ⊓ (sectorRotationOrbitSpan n u)ᗮ
          ≤ sectorRotationOrbitSpan n u ⊓ (sectorRotationOrbitSpan n u)ᗮ := by
            exact inf_le_inf (cyclicLine_le_sectorRotationOrbitSpan u) le_rfl
      _ = ⊥ := (sectorRotationOrbitSpan n u).inf_orthogonal_eq_bot
  exact hperp_hit hline_bot

end SphericalHarmonics
