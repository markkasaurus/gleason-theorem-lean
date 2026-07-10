import Mathlib

import Gleason.Finite.Projection
import Gleason.Finite.RankOneProjection
import Gleason.Finite.FrameFunction

import Gleason.Finite.Quadratic.Basic
import Gleason.Finite.Quadratic.Homogeneity
import Gleason.Finite.Quadratic.Orthonormal
import Gleason.Finite.Quadratic.OrthogonalParallelogram
import Gleason.Finite.OrthogonalComplement
import Gleason.Finite.Quadratic.Parallelogram

import Gleason.Finite.Polarization.BoundedQuadraticForm
import Gleason.Finite.Polarization.Definition
import Gleason.Finite.Polarization.Symmetry
import Gleason.Finite.Polarization.Additivity
import Gleason.Finite.Polarization.LeftScalar
import Gleason.Finite.Polarization.RightScalar
import Gleason.Finite.Polarization.Bound
import Gleason.Finite.Polarization.Continuity
import Gleason.Finite.Polarization.OperatorRepresentation
import Gleason.Finite.Quadratic.Bound
import Gleason.Finite.OperatorPositivity
import Gleason.Finite.TraceNormalization

import Gleason.Finite.ProjectionSum
import Gleason.Finite.ProjectionDecomposition
import Gleason.Finite.RankOneTrace

noncomputable section

open scoped BigOperators
open RankOne Complex

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

/-!
## Density operators and finite-dimensional assembly

This file constructs the representing operator by polarization, proves its
positivity and trace normalization, decomposes arbitrary projections into
rank-one projections, and derives the trace representation from finite
orthogonal additivity.
-/

/-- A density operator: positive and with trace `1`. -/
structure DensityOperator (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H] where
  ρ : H →L[ℂ] H
  positive : ∀ x : H, 0 ≤ (inner (𝕜 := ℂ) (ρ x) x).re
  trace_one : LinearMap.trace ℂ H ρ.toLinearMap = 1

namespace DensityOperator

variable (ρ : DensityOperator H)

/-- Convenience lemma: `ρ.ρ` as a linear map. -/
@[simp] lemma coe_toLinearMap : ρ.ρ.toLinearMap = (ρ.ρ : H →L[ℂ] H).toLinearMap := rfl

end DensityOperator

namespace GleasonAssembly

/-!
### Trace linearity for compositions
-/

lemma trace_comp_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : H →L[ℂ] H) (P : ι → (H →L[ℂ] H)) :
    LinearMap.trace ℂ H (A.toLinearMap.comp (∑ i : ι, (P i).toLinearMap))
      =
    ∑ i : ι, LinearMap.trace ℂ H (A.toLinearMap.comp (P i).toLinearMap) := by
  classical
  -- `trace` is linear, so it suffices to push `comp` over the sum.
  have hcomp :
      A.toLinearMap.comp (∑ i : ι, (P i).toLinearMap)
        =
      ∑ i : ι, A.toLinearMap.comp (P i).toLinearMap := by
    ext x
    simp [LinearMap.comp_apply]
  -- apply linearity of trace
  simpa [hcomp] using (map_sum (LinearMap.trace ℂ H) (fun i : ι => A.toLinearMap.comp (P i).toLinearMap)
    (Finset.univ : Finset ι))

/-!
### Main assembly lemma: from a parallelogram identity for `frame_quadratic μ`
-/

theorem gleason_theorem_of_parallelogram
    (μ : FrameFunction H)
    (h_para :
      ∀ x y : H,
        frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
          = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y) :
    ∃ ρ : DensityOperator H, ∀ P : Projection H,
      μ.μ P = (LinearMap.trace ℂ H (ρ.ρ.toLinearMap.comp P.1.toLinearMap)).re := by
  classical
  -- Build `T` from polarization.
  let hq : IsBoundedQuadraticForm (H := H) (frame_quadratic (H := H) μ) :=
    frame_quadratic_is_bounded_quadratic (H := H) μ h_para
  let T : H →L[ℂ] H :=
    (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ) hq).choose

  -- Positivity and trace normalization of the polarized operator.
  have hpos : ∀ x : H, 0 ≤ (inner (𝕜 := ℂ) (T x) x).re := by
    simpa [T] using (frame_operator_positive (H := H) (μ := μ) (h_para := h_para))

  have htr : LinearMap.trace ℂ H T.toLinearMap = 1 := by
    simpa [T] using (frame_operator_trace_one (H := H) (μ := μ) (h_para := h_para))

  let ρ : DensityOperator H := ⟨T, hpos, htr⟩
  refine ⟨ρ, ?_⟩

  intro P
  -- Decompose `P` as a sum of rank-one projections.
  rcases (Projection.projection_eq_sum_rankOne (H := H) P) with
    ⟨ι, instF, instD, b, hb, horth, hPsum⟩
  classical
  -- Use additivity of `μ` over the finite orthogonal sum.
  have hμ :
      μ.μ P
        =
      ∑ i : ι, μ.μ (rankOneProjection (H := H) (b i) (hb i)) := by
    -- `FrameFunction.map_sum` expects a finset; for a fintype it is `Finset.univ`.
    -- Rewrite `P` using the decomposition.
    have : P = Projection.sum (H := H) (ι := ι) Finset.univ
        (fun i => rankOneProjection (H := H) (b i) (hb i)) horth := hPsum
    -- Turn it into a statement about `μ.μ`.
    simpa [this] using (FrameFunction.map_sum (H := H) (μ := μ) (s := (Finset.univ : Finset ι))
      (P := fun i => rankOneProjection (H := H) (b i) (hb i)) horth)

  -- Split the trace side as a sum, then use the rank-one formula.
  have htrsum :
      (LinearMap.trace ℂ H (ρ.ρ.toLinearMap.comp P.1.toLinearMap)).re
        =
      ∑ i : ι,
        (LinearMap.trace ℂ H
          (ρ.ρ.toLinearMap.comp (rankOneProjection (H := H) (b i) (hb i)).1.toLinearMap)).re := by
    -- First, identify `P.1` as a sum of underlying operators.
    have hPcoe :
        P.1 = ∑ i : ι, (rankOneProjection (H := H) (b i) (hb i)).1 := by
      -- take coercions of `hPsum` and unfold `Projection.sum` via `sum_coe`.
      have := congrArg (fun Q : Projection H => Q.1) hPsum
      -- `sum_coe` provides the underlying operator as a sum.
      simpa [Projection.sum_coe] using this

    -- Move `ρ ∘ (∑ P_i)` to `∑ (ρ ∘ P_i)` and apply trace linearity.
    calc
      (LinearMap.trace ℂ H (ρ.ρ.toLinearMap.comp P.1.toLinearMap)).re
          = (LinearMap.trace ℂ H (ρ.ρ.toLinearMap.comp (∑ i : ι,
                (rankOneProjection (H := H) (b i) (hb i)).1.toLinearMap))).re := by
              simpa [hPcoe]
      _ = (∑ i : ι,
              LinearMap.trace ℂ H
                (ρ.ρ.toLinearMap.comp (rankOneProjection (H := H) (b i) (hb i)).1.toLinearMap)).re := by
              -- trace of composition with a sum
              have h :=
                trace_comp_sum (H := H) (A := ρ.ρ) (P := fun i : ι => (rankOneProjection (H := H) (b i) (hb i)).1)
              simpa using congrArg Complex.re h
      _ = ∑ i : ι,
            (LinearMap.trace ℂ H
              (ρ.ρ.toLinearMap.comp (rankOneProjection (H := H) (b i) (hb i)).1.toLinearMap)).re := by
              simpa [Complex.re_sum]

  -- Combine: both sides are sums over the same index set.
  rw [hμ, htrsum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  -- Apply the rank-one representation with the same chosen operator.
  have h_rank :
      μ.μ (rankOneProjection (H := H) (b i) (hb i))
        =
      (LinearMap.trace ℂ H
        (ρ.ρ.toLinearMap.comp (rankOneProjection (H := H) (b i) (hb i)).1.toLinearMap)).re := by
    -- Match the operator by definitional unfolding (`ρ.ρ = T`).
    simpa [ρ] using
      (Gleason.gleason_rank_one (H := H) (μ := μ) (h_para := h_para) (x := (b i)) (hx := (hb i)))
  simpa using h_rank


/-!
### Representation theorems
-/

theorem gleason_theorem
    (h_para :
      ∀ (μ : FrameFunction H) (x y : H),
        frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
          = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y)
    (μ : FrameFunction H) (hdim : 3 ≤ Module.finrank ℂ H) :
    ∃ ρ : DensityOperator H, ∀ P : Projection H,
      μ.μ P = (LinearMap.trace ℂ H (ρ.ρ.toLinearMap.comp P.1.toLinearMap)).re := by
  -- `hdim` is not needed once the parallelogram identity is assumed.
  simpa using gleason_theorem_of_parallelogram (H := H) μ (fun x y => h_para μ x y)


theorem gleason_theorem_with_regularity
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H) (hquad : μ.HasQuad2D) :
    ∃ ρ : DensityOperator H, ∀ P : Projection H,
      μ.μ P = (LinearMap.trace ℂ H (ρ.ρ.toLinearMap.comp P.1.toLinearMap)).re := by
  -- Derive the parallelogram identity from `HasQuad2D` and `dim ≥ 3`.
  refine gleason_theorem_of_parallelogram (H := H) μ (fun x y => ?_) 
  simpa using frame_quadratic_parallelogram (H := H) hdim μ hquad x y

end GleasonAssembly
