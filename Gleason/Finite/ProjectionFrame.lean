import Gleason.Finite.Statement
import Gleason.Finite.Assembly

/-!
This file states the finite-dimensional projection-frame representation.

The assembly theorem takes the parallelogram identity for `frame_quadratic` as
its regularity input; that identity is established in the continuity layer.
-/

noncomputable section

open scoped BigOperators
open Complex RankOne

namespace ClassicalGleason

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

omit [FiniteDimensional ℂ H] in
lemma inner_left_eq_inner_right_of_isSelfAdjoint
    {P : H →L[ℂ] H} (hP : IsSelfAdjoint P) (x y : H) :
    inner (𝕜 := ℂ) (P x) y = inner (𝕜 := ℂ) x (P y) := by
  have hadj : ContinuousLinearMap.adjoint P = P := by
    simpa using hP
  calc
    inner (𝕜 := ℂ) (P x) y
        = inner (𝕜 := ℂ) x ((ContinuousLinearMap.adjoint P) y) := by
          exact (ContinuousLinearMap.adjoint_inner_right (𝕜 := ℂ) P x y).symm
    _ = inner (𝕜 := ℂ) x (P y) := by
          rw [hadj]

lemma isSelfAdjoint_of_projection (P : Projection H) : IsSelfAdjoint P.1 := by
  have hadj : ContinuousLinearMap.adjoint P.1 = P.1 := by
    ext x
    apply ext_inner_left ℂ
    intro y
    calc
      inner (𝕜 := ℂ) y ((ContinuousLinearMap.adjoint P.1) x)
          = inner (𝕜 := ℂ) (P.1 y) x := by
            exact ContinuousLinearMap.adjoint_inner_right (𝕜 := ℂ) P.1 y x
      _ = inner (𝕜 := ℂ) y (P.1 x) := by
            exact Projection.selfAdjointOp (H := H) P y x
  simpa using hadj

lemma isOrthProj_of_projection (P : Projection H) : IsOrthProj P.1 := by
  exact ⟨by simp [IsIdempotentElem, P.2.1], isSelfAdjoint_of_projection (H := H) P⟩

/-- Convert an orthogonal projection predicate into the bundled projection type. -/
def toProjection (P : H →L[ℂ] H) (hP : IsOrthProj P) : Projection H :=
  ⟨P, by
    refine ⟨by simpa [IsIdempotentElem] using hP.1, ?_⟩
    intro x y
    have hxy : inner (𝕜 := ℂ) (P x) y = inner (𝕜 := ℂ) x (P y) :=
      inner_left_eq_inner_right_of_isSelfAdjoint (H := H) hP.2 x y
    have hxPy : inner (𝕜 := ℂ) (P x) (P y) = inner (𝕜 := ℂ) x (P (P y)) :=
      inner_left_eq_inner_right_of_isSelfAdjoint (H := H) hP.2 x (P y)
    have hidem_apply : P (P y) = P y := by
      have h := congrArg (fun T : H →L[ℂ] H => T y) (by simpa [IsIdempotentElem] using hP.1)
      simpa [ContinuousLinearMap.mul_apply] using h
    calc
      inner (𝕜 := ℂ) (P x) (y - P y)
          = inner (𝕜 := ℂ) (P x) y - inner (𝕜 := ℂ) (P x) (P y) := by
            simp
      _ = inner (𝕜 := ℂ) x (P y) - inner (𝕜 := ℂ) x (P (P y)) := by
            rw [hxy, hxPy]
      _ = 0 := by
            rw [hidem_apply]
            simp⟩

/-- Restrict a projection-frame function to the bundled projection type. -/
def toBundledFrameFunction (f : ProjectionFrameFunction H) : FrameFunction H where
  μ P := f.μ P.1
  nonneg P := f.nonneg P.1 (isOrthProj_of_projection (H := H) P)
  additive P Q h := by
    have hP : IsOrthProj P.1 := isOrthProj_of_projection (H := H) P
    have hQ : IsOrthProj Q.1 := isOrthProj_of_projection (H := H) Q
    have hadd := f.additive P.1 Q.1 hP hQ h
    simpa [Projection.add] using hadd
  normalized := by
    simpa [Projection.one] using f.normalized

lemma polarization_operator_isSelfAdjoint
    (μ : FrameFunction H)
    (h_para :
      ∀ x y : H,
        frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
          = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y) :
    let hq : IsBoundedQuadraticForm (H := H) (frame_quadratic (H := H) μ) :=
      frame_quadratic_is_bounded_quadratic (H := H) μ h_para
    let T : H →L[ℂ] H :=
      (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ) hq).choose
    IsSelfAdjoint T := by
  classical
  dsimp
  let hq : IsBoundedQuadraticForm (H := H) (frame_quadratic (H := H) μ) :=
    frame_quadratic_is_bounded_quadratic (H := H) μ h_para
  let T : H →L[ℂ] H :=
    (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ) hq).choose
  have hrepr :
      ∀ x y : H, polarization (frame_quadratic (H := H) μ) x y = inner (𝕜 := ℂ) y (T x) := by
    intro x y
    simpa [T, hq] using
      (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ) hq).choose_spec.1 x y
  have hadj : ContinuousLinearMap.adjoint T = T := by
    ext x
    apply ext_inner_left ℂ
    intro y
    have hconj :=
      polarization_conj_symm (H := H) (q := frame_quadratic (H := H) μ) hq x y
    calc
      inner (𝕜 := ℂ) y ((ContinuousLinearMap.adjoint T) x)
          = inner (𝕜 := ℂ) (T y) x := by
            exact ContinuousLinearMap.adjoint_inner_right (𝕜 := ℂ) T y x
      _ = star (inner (𝕜 := ℂ) x (T y)) := by
            simp
      _ = star (polarization (frame_quadratic (H := H) μ) y x) := by
            rw [hrepr y x]
      _ = polarization (frame_quadratic (H := H) μ) x y := by
            rw [hconj]
            simp
      _ = inner (𝕜 := ℂ) y (T x) := hrepr x y
  simpa using hadj

lemma polarization_operator_isPositive
    (μ : FrameFunction H)
    (h_para :
      ∀ x y : H,
        frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
          = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y) :
    let hq : IsBoundedQuadraticForm (H := H) (frame_quadratic (H := H) μ) :=
      frame_quadratic_is_bounded_quadratic (H := H) μ h_para
    let T : H →L[ℂ] H :=
      (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ) hq).choose
    T.IsPositive := by
  classical
  dsimp
  let hq : IsBoundedQuadraticForm (H := H) (frame_quadratic (H := H) μ) :=
    frame_quadratic_is_bounded_quadratic (H := H) μ h_para
  let T : H →L[ℂ] H :=
    (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ) hq).choose
  refine (ContinuousLinearMap.isPositive_def' (T := T)).2 ⟨?_, ?_⟩
  · simpa [T, hq] using polarization_operator_isSelfAdjoint (H := H) μ h_para
  · intro x
    simpa [T, hq, ContinuousLinearMap.reApplyInnerSelf] using
      (frame_operator_positive (H := H) (μ := μ) (h_para := h_para) x)

/-- Conditional density-operator assembly from the parallelogram identity. -/
theorem gleason_bundled_of_parallelogram_positive
    (μ : FrameFunction H)
    (h_para :
      ∀ x y : H,
        frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
          = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y) :
    ∃ ρ : H →L[ℂ] H,
      ρ.IsPositive ∧
      LinearMap.trace ℂ H ρ.toLinearMap = 1 ∧
      ∀ P : Projection H,
        μ.μ P = (LinearMap.trace ℂ H (ρ.toLinearMap.comp P.1.toLinearMap)).re := by
  classical
  let hq : IsBoundedQuadraticForm (H := H) (frame_quadratic (H := H) μ) :=
    frame_quadratic_is_bounded_quadratic (H := H) μ h_para
  let T : H →L[ℂ] H :=
    (polarization_eq_inner_product (H := H) (q := frame_quadratic (H := H) μ) hq).choose
  have hpos : T.IsPositive := by
    simpa [T, hq] using polarization_operator_isPositive (H := H) μ h_para
  have htr : LinearMap.trace ℂ H T.toLinearMap = 1 := by
    simpa [T] using (frame_operator_trace_one (H := H) (μ := μ) (h_para := h_para))
  refine ⟨T, hpos, htr, ?_⟩

  intro P
  rcases (Projection.projection_eq_sum_rankOne (H := H) P) with
    ⟨ι, instF, instD, b, hb, horth, hPsum⟩
  classical
  have hμ :
      μ.μ P = ∑ i : ι, μ.μ (rankOneProjection (H := H) (b i) (hb i)) := by
    have : P = Projection.sum (H := H) (ι := ι) Finset.univ
        (fun i => rankOneProjection (H := H) (b i) (hb i)) horth := hPsum
    simpa [this] using
      (FrameFunction.map_sum (H := H) (μ := μ) (s := (Finset.univ : Finset ι))
        (P := fun i => rankOneProjection (H := H) (b i) (hb i)) horth)
  have htrsum :
      (LinearMap.trace ℂ H (T.toLinearMap.comp P.1.toLinearMap)).re
        =
      ∑ i : ι,
        (LinearMap.trace ℂ H
          (T.toLinearMap.comp (rankOneProjection (H := H) (b i) (hb i)).1.toLinearMap)).re := by
    have hPcoe :
        P.1 = ∑ i : ι, (rankOneProjection (H := H) (b i) (hb i)).1 := by
      have := congrArg (fun Q : Projection H => Q.1) hPsum
      simpa [Projection.sum_coe] using this
    calc
      (LinearMap.trace ℂ H (T.toLinearMap.comp P.1.toLinearMap)).re
          = (LinearMap.trace ℂ H (T.toLinearMap.comp (∑ i : ι,
                (rankOneProjection (H := H) (b i) (hb i)).1.toLinearMap))).re := by
              simp [hPcoe]
      _ = (∑ i : ι,
              LinearMap.trace ℂ H
                (T.toLinearMap.comp (rankOneProjection (H := H) (b i) (hb i)).1.toLinearMap)).re := by
              have h :=
                GleasonAssembly.trace_comp_sum (H := H) (A := T)
                  (P := fun i : ι => (rankOneProjection (H := H) (b i) (hb i)).1)
              simpa using congrArg Complex.re h
      _ = ∑ i : ι,
            (LinearMap.trace ℂ H
              (T.toLinearMap.comp (rankOneProjection (H := H) (b i) (hb i)).1.toLinearMap)).re := by
              simp [Complex.re_sum]
  rw [hμ, htrsum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  simpa [T] using
    (Gleason.gleason_rank_one (H := H) (μ := μ) (h_para := h_para) (x := b i) (hx := hb i))

/-- Finite-dimensional projection-frame Gleason statement, conditional on the parallelogram step. -/
theorem gleason_theorem_finite_of_parallelogram
    (h_para :
      ∀ (μ : FrameFunction H) (x y : H),
        frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
          = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y)
    (_hdim : 3 ≤ Module.finrank ℂ H)
    (f : ProjectionFrameFunction H) :
    ∃ ρ : H →L[ℂ] H,
      ρ.IsPositive ∧
      reTr ρ = 1 ∧
      ∀ P : H →L[ℂ] H, IsOrthProj P → f.μ P = reTr (ρ * P) := by
  classical
  let μ : FrameFunction H := toBundledFrameFunction (H := H) f
  rcases gleason_bundled_of_parallelogram_positive (H := H) μ (fun x y => h_para μ x y) with
    ⟨ρ, hpos, htr, hρ⟩
  refine ⟨ρ, hpos, ?_, ?_⟩
  · simpa [reTr] using congrArg Complex.re htr
  · intro P hP
    have h := hρ (toProjection (H := H) P hP)
    simpa [μ, toBundledFrameFunction, toProjection, reTr, ContinuousLinearMap.mul_apply] using h

end ClassicalGleason
