import Gleason.Continuity.KernelInterface
import Gleason.Finite.Quadratic.Lipschitz
import Gleason.Finite.ProjectionDecomposition
import Gleason.Finite.RankOneTrace
import Gleason.Continuity.Auxiliary.GreatCircleContinuity
import Gleason.Harmonic.HighDegree.HighEvenUnionReduction
import Gleason.Harmonic.HighDegree.HighEvenUnionSquaredQuotientExtension
import Gleason.Harmonic.Sphere.S2FinalWitnessReduction
import Gleason.Harmonic.Sphere.S2L2EvenReduction
import Gleason.Harmonic.PoleAverage.PoleAverageL2Bound
import Gleason.Continuity.GeometricControl
import Gleason.Harmonic.ProjectionStability
import Gleason.Harmonic.Sphere.EquatorialReferencePoint

/-!
# Gleason's Theorem: Oscillation and Continuity

This file proves continuity of nonnegative frame functions on the two-sphere by a
near-infimum oscillation argument. Rotation equivariance propagates a local bound to
the whole sphere. The resulting continuity theorem feeds the spectral decomposition,
local quadraticity, and the global parallelogram identity used in the
finite-dimensional complex Gleason theorem.
-/

noncomputable section

open GleasonBridge RankOne Complex InnerProductSpace Polynomial SphericalHarmonics

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

private lemma frame_quadratic_eq_mu_rankOne_of_unit
    (μ : FrameFunction H) (x : H) (hx : ‖x‖ = 1) :
    frame_quadratic (H := H) μ x =
      μ.μ (RankOne.rankOneProjection (H := H) x (by
        intro hx0
        simpa [hx0] using hx)) := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simpa [hx0] using hx
  have hnorm_sq : ‖x‖ ^ 2 = 1 := by
    rw [hx]
    norm_num
  simp [frame_quadratic, hx0, hnorm_sq]

private lemma rankOne_normalize_norm_eq_one
    (x : H) (hx : x ≠ 0) :
    ‖Gleason.RankOne.normalize (H := H) x‖ = 1 := by
  have hnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  calc
    ‖Gleason.RankOne.normalize (H := H) x‖
        = ‖(((‖x‖ : ℝ) : ℂ)⁻¹)‖ * ‖x‖ := by
            simp [Gleason.RankOne.normalize, norm_smul, mul_comm]
    _ = (‖x‖)⁻¹ * ‖x‖ := by simp
    _ = 1 := by field_simp [hnorm_ne]

private lemma trace_finset_sum {ι : Type*}
    (s : Finset ι) (f : ι → H →L[ℂ] H) :
    LinearMap.trace ℂ H ((Finset.sum s f).toLinearMap) =
      Finset.sum s (fun i => LinearMap.trace ℂ H (f i).toLinearMap) := by
  simpa using map_sum (LinearMap.trace ℂ H) f s

private def projectionTrace (P : Projection H) : ℝ :=
  (LinearMap.trace ℂ H P.1.toLinearMap).re

private lemma projectionTrace_sum {ι : Type*}
    (s : Finset ι) (P : ι → Projection H)
    (h : ∀ i j, i ≠ j → Projection.orthogonal (P i) (P j)) :
      projectionTrace (Projection.sum (H := H) (ι := ι) s P h) =
      Finset.sum s (fun i => projectionTrace (P i)) := by
  have htrace :
      LinearMap.trace ℂ H ((Finset.sum s fun i => (P i).1).toLinearMap) =
        Finset.sum s (fun i => LinearMap.trace ℂ H ((P i).1.toLinearMap)) :=
    trace_finset_sum (H := H) s (fun i => (P i).1)
  have hre := congrArg Complex.re htrace
  simpa [projectionTrace, Projection.sum_coe]
    using hre

private lemma projectionTrace_rankOne
    (x : H) (hx : x ≠ 0) :
    projectionTrace (RankOne.rankOneProjection (H := H) x hx) = 1 := by
  unfold projectionTrace
  have htrace :=
    Gleason.trace_comp_rankOneProjection (H := H) (A := (1 : H →L[ℂ] H)) x hx
  have hxx : inner (𝕜 := ℂ) x x ≠ 0 := by
    exact inner_self_ne_zero.mpr hx
  have htrace' :
      LinearMap.trace ℂ H ((RankOne.rankOneProjection (H := H) x hx).1.toLinearMap) = 1 := by
    have htrace'' :
        LinearMap.trace ℂ H ((RankOne.rankOneProjection (H := H) x hx).1.toLinearMap) =
          inner (𝕜 := ℂ) x x / inner (𝕜 := ℂ) x x := by
      simpa using htrace
    rw [div_self hxx] at htrace''
    exact htrace''
  have hre := congrArg Complex.re htrace'
  simpa using hre

private lemma frame_function_value_ge_inf_mul_projectionTrace
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (P : Projection H) :
    sInf (Q_sphere_set μ) * projectionTrace P ≤ μ.μ P := by
  classical
  rcases Projection.projection_eq_sum_rankOne (H := H) P with
    ⟨ι, _, _, b, hb, horth, rfl⟩
  have hmu_sum :
      μ.μ (Projection.sum (H := H) (ι := ι) (Finset.univ : Finset ι)
        (fun i => RankOne.rankOneProjection (H := H) (b i) (hb i)) horth)
        =
      ∑ i : ι, μ.μ (RankOne.rankOneProjection (H := H) (b i) (hb i)) := by
    simpa using
      (FrameFunction.map_sum (H := H) μ (s := (Finset.univ : Finset ι))
        (P := fun i => RankOne.rankOneProjection (H := H) (b i) (hb i)) horth)
  have htrace_sum :
      projectionTrace (Projection.sum (H := H) (ι := ι) (Finset.univ : Finset ι)
        (fun i => RankOne.rankOneProjection (H := H) (b i) (hb i)) horth)
        =
      ∑ i : ι, projectionTrace (RankOne.rankOneProjection (H := H) (b i) (hb i)) := by
    simpa using
      (projectionTrace_sum (H := H) (s := (Finset.univ : Finset ι))
        (P := fun i => RankOne.rankOneProjection (H := H) (b i) (hb i)) horth)
  have hterm :
      ∀ i : ι,
        sInf (Q_sphere_set μ) *
            projectionTrace (RankOne.rankOneProjection (H := H) (b i) (hb i))
          ≤
        μ.μ (RankOne.rankOneProjection (H := H) (b i) (hb i)) := by
    intro i
    let u : H := Gleason.RankOne.normalize (H := H) (b i)
    have hu_ne : u ≠ 0 :=
      Gleason.RankOne.normalize_ne_zero (H := H) (hb i)
    have hu : ‖u‖ = 1 :=
      rankOne_normalize_norm_eq_one (H := H) (b i) (hb i)
    have h_inf : sInf (Q_sphere_set μ) ≤ frame_quadratic (H := H) μ u :=
      Q_sphere_inf_le μ u hu
    have h_frame :
        frame_quadratic (H := H) μ u =
          μ.μ (RankOne.rankOneProjection (H := H) u hu_ne) :=
      frame_quadratic_eq_mu_rankOne_of_unit μ u hu
    have h_proj :
        RankOne.rankOneProjection (H := H) u hu_ne =
          RankOne.rankOneProjection (H := H) (b i) (hb i) :=
      Gleason.RankOne.rankOneProjection_normalize (H := H) (b i) (hb i)
    have h_trace :
        projectionTrace (RankOne.rankOneProjection (H := H) (b i) (hb i)) = 1 :=
      projectionTrace_rankOne (H := H) (b i) (hb i)
    rw [h_trace]
    have h_inf' : sInf (Q_sphere_set μ) * 1 ≤ frame_quadratic (H := H) μ u := by
      simpa using h_inf
    calc
      sInf (Q_sphere_set μ) * 1 ≤ frame_quadratic (H := H) μ u := h_inf'
      _ = μ.μ (RankOne.rankOneProjection (H := H) u hu_ne) := h_frame
      _ = μ.μ (RankOne.rankOneProjection (H := H) (b i) (hb i)) := by
            rw [h_proj]
  have hsum :
      ∑ i : ι,
          sInf (Q_sphere_set μ) *
            projectionTrace (RankOne.rankOneProjection (H := H) (b i) (hb i))
        ≤
      ∑ i : ι, μ.μ (RankOne.rankOneProjection (H := H) (b i) (hb i)) := by
    exact Finset.sum_le_sum (fun i _hi => hterm i)
  calc
    sInf (Q_sphere_set μ) *
        projectionTrace (Projection.sum (H := H) (ι := ι) (Finset.univ : Finset ι)
          (fun i => RankOne.rankOneProjection (H := H) (b i) (hb i)) horth)
        =
      sInf (Q_sphere_set μ) *
        ∑ i : ι, projectionTrace (RankOne.rankOneProjection (H := H) (b i) (hb i)) := by
            rw [htrace_sum]
    _ =
      ∑ i : ι,
        sInf (Q_sphere_set μ) *
          projectionTrace (RankOne.rankOneProjection (H := H) (b i) (hb i)) := by
            rw [Finset.mul_sum]
    _ ≤
      ∑ i : ι, μ.μ (RankOne.rankOneProjection (H := H) (b i) (hb i)) := hsum
    _ =
      μ.μ (Projection.sum (H := H) (ι := ι) (Finset.univ : Finset ι)
        (fun i => RankOne.rankOneProjection (H := H) (b i) (hb i)) horth) := by
            symm
            exact hmu_sum

private lemma projectionTrace_one :
    projectionTrace (Projection.one (H := H)) = Module.finrank ℂ H := by
  change ((LinearMap.trace ℂ H) ((1 : H →L[ℂ] H).toLinearMap)).re =
      Module.finrank ℂ H
  have h :
      ((LinearMap.trace ℂ H) ((1 : H →L[ℂ] H).toLinearMap)).re =
        ((Module.finrank ℂ H : ℂ)).re := by
    exact congrArg Complex.re (LinearMap.trace_one (R := ℂ) (M := H))
  simpa using h

private lemma sphere_inf_mul_finrank_le_one
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H) :
    sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) ≤ 1 := by
  simpa [projectionTrace_one, μ.normalized] using
    frame_function_value_ge_inf_mul_projectionTrace (H := H) hdim μ (Projection.one (H := H))

private lemma projectionTrace_add
    (P Q : Projection H) (hPQ : Projection.orthogonal P Q) :
    projectionTrace (Projection.add (H := H) P Q hPQ) =
      projectionTrace P + projectionTrace Q := by
  unfold projectionTrace
  simp [Projection.add, map_add]

private def shiftedNormalizedFrameFunction
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) ≠ 0) :
    FrameFunction H where
  μ := fun P =>
    (μ.μ P - sInf (Q_sphere_set μ) * projectionTrace P) /
      (1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ))
  nonneg := by
    intro P
    have hnum :
        0 ≤ μ.μ P - sInf (Q_sphere_set μ) * projectionTrace P := by
      exact sub_nonneg.mpr
        (frame_function_value_ge_inf_mul_projectionTrace (H := H) hdim μ P)
    have hden_nonneg :
        0 ≤ 1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) := by
      linarith [sphere_inf_mul_finrank_le_one (H := H) hdim μ]
    have hden_pos :
        0 <
          1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) :=
      lt_of_le_of_ne hden_nonneg hden.symm
    exact div_nonneg hnum (le_of_lt hden_pos)
  additive := by
    intro P Q hPQ
    rw [μ.additive P Q hPQ, projectionTrace_add (H := H) P Q hPQ]
    field_simp [hden]
    ring
  normalized := by
    have htrace1 : projectionTrace (Projection.one (H := H)) = Module.finrank ℂ H :=
      projectionTrace_one (H := H)
    rw [μ.normalized, htrace1]
    field_simp [hden]

private lemma frame_quadratic_shiftedNormalizedFrameFunction_of_unit
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) ≠ 0)
    (x : H) (hx : ‖x‖ = 1) :
    frame_quadratic (H := H) (shiftedNormalizedFrameFunction (H := H) hdim μ hden) x =
      (frame_quadratic (H := H) μ x - sInf (Q_sphere_set μ)) /
        (1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ)) := by
  have hx0 : x ≠ 0 := by
    intro hx0
    simpa [hx0] using hx
  rw [frame_quadratic_eq_mu_rankOne_of_unit
    (μ := shiftedNormalizedFrameFunction (H := H) hdim μ hden) (x := x) hx]
  simp [shiftedNormalizedFrameFunction, projectionTrace_rankOne, hden,
    frame_quadratic_eq_mu_rankOne_of_unit, hx, hx0]

private lemma frame_quadratic_shiftedNormalizedFrameFunction
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) ≠ 0)
    (x : H) :
    frame_quadratic (H := H) (shiftedNormalizedFrameFunction (H := H) hdim μ hden) x =
      (frame_quadratic (H := H) μ x - sInf (Q_sphere_set μ) * ‖x‖ ^ 2) /
        (1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ)) := by
  by_cases hx : x = 0
  · subst hx
    simp [frame_quadratic_zero]
  · let u := Gleason.RankOne.normalize (H := H) x
    have hu : ‖u‖ = 1 := rankOne_normalize_norm_eq_one (H := H) x hx
    have hnorm_ne : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hx)
    have hx_repr : (((‖x‖ : ℝ) : ℂ) • u) = x := by
      dsimp [u, Gleason.RankOne.normalize]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rw [smul_smul]
      have hmul : ((‖x‖ : ℂ) * ((‖x‖ : ℂ)⁻¹)) = (1 : ℂ) := by
        field_simp [hnorm_ne]
      simpa [hmul]
    have hshift_scale :
        frame_quadratic (H := H) (shiftedNormalizedFrameFunction (H := H) hdim μ hden) x =
          ‖x‖ ^ 2 * frame_quadratic (H := H)
            (shiftedNormalizedFrameFunction (H := H) hdim μ hden) u := by
      have htmp :=
        frame_quadratic_sq_hom
          (μ := shiftedNormalizedFrameFunction (H := H) hdim μ hden) (((‖x‖ : ℝ) : ℂ)) u
      have htmp' :
          frame_quadratic (H := H) (shiftedNormalizedFrameFunction (H := H) hdim μ hden)
              ((((‖x‖ : ℝ) : ℂ)) • u) =
            ‖x‖ ^ 2 * frame_quadratic (H := H)
              (shiftedNormalizedFrameFunction (H := H) hdim μ hden) u := by
        simpa [Complex.norm_real, sq_abs, abs_of_nonneg (norm_nonneg x)] using htmp
      simpa [hx_repr] using htmp'
    have horig_scale :
        frame_quadratic (H := H) μ x = ‖x‖ ^ 2 * frame_quadratic (H := H) μ u := by
      have htmp := frame_quadratic_sq_hom (μ := μ) (((‖x‖ : ℝ) : ℂ)) u
      have htmp' :
          frame_quadratic (H := H) μ ((((‖x‖ : ℝ) : ℂ)) • u) =
            ‖x‖ ^ 2 * frame_quadratic (H := H) μ u := by
        simpa [Complex.norm_real, sq_abs, abs_of_nonneg (norm_nonneg x)] using htmp
      simpa [hx_repr] using htmp'
    have hunit :
        frame_quadratic (H := H) (shiftedNormalizedFrameFunction (H := H) hdim μ hden) u =
          (frame_quadratic (H := H) μ u - sInf (Q_sphere_set μ)) /
            (1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ)) :=
      frame_quadratic_shiftedNormalizedFrameFunction_of_unit (H := H) hdim μ hden u hu
    calc
      frame_quadratic (H := H) (shiftedNormalizedFrameFunction (H := H) hdim μ hden) x
          = ‖x‖ ^ 2 * frame_quadratic (H := H)
              (shiftedNormalizedFrameFunction (H := H) hdim μ hden) u := hshift_scale
      _ =
          ‖x‖ ^ 2 *
            ((frame_quadratic (H := H) μ u - sInf (Q_sphere_set μ)) /
              (1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ))) := by
              rw [hunit]
      _ =
          (frame_quadratic (H := H) μ x - sInf (Q_sphere_set μ) * ‖x‖ ^ 2) /
            (1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ)) := by
              field_simp [hden]
              linarith [horig_scale]

private lemma local_quad2DDefect_shiftedNormalizedFrameFunction
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) ≠ 0)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    local_quad2DDefect (shiftedNormalizedFrameFunction (H := H) hdim μ hden) u v a b =
      local_quad2DDefect μ u v a b /
        (1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ)) := by
  have hinner : inner (𝕜 := ℂ) (a • u) (b • v) = 0 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a u, RCLike.real_smul_eq_coe_smul (K := ℂ) b v]
    simp [huv]
  have hnorm_smul_u : ‖a • u‖ ^ 2 = a ^ 2 := by
    simp [norm_smul, hu, Real.norm_eq_abs, pow_two]
  have hnorm_smul_v : ‖b • v‖ ^ 2 = b ^ 2 := by
    simp [norm_smul, hv, Real.norm_eq_abs, pow_two]
  have hnorm_plus_real : ‖a • u + b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    have hmul :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := a • u) (y := b • v) hinner
    have hsq :
        ‖a • u + b • v‖ ^ 2 = ‖a • u‖ ^ 2 + ‖b • v‖ ^ 2 := by
      simpa [pow_two] using hmul
    simpa [hnorm_smul_u, hnorm_smul_v, add_comm, add_left_comm, add_assoc] using hsq
  have hnorm_minus_real : ‖a • u - b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    have hinner' : inner (𝕜 := ℂ) (a • u) (-(b • v)) = 0 := by
      simp [inner_neg_right, hinner]
    have hmul :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := a • u) (y := -(b • v)) hinner'
    have hsq :
        ‖a • u + -(b • v)‖ ^ 2 = ‖a • u‖ ^ 2 + ‖-(b • v)‖ ^ 2 := by
      simpa [pow_two] using hmul
    simpa [sub_eq_add_neg, hnorm_smul_u, hnorm_smul_v, add_comm, add_left_comm, add_assoc] using hsq
  have hnorm_plus : ‖(a : ℂ) • u + (b : ℂ) • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using hnorm_plus_real
  have hnorm_minus : ‖(a : ℂ) • u - (b : ℂ) • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using hnorm_minus_real
  have hplus :=
    frame_quadratic_shiftedNormalizedFrameFunction
      (H := H) hdim μ hden ((a : ℂ) • u + (b : ℂ) • v)
  have hminus :=
    frame_quadratic_shiftedNormalizedFrameFunction
      (H := H) hdim μ hden ((a : ℂ) • u - (b : ℂ) • v)
  have hu' :=
    frame_quadratic_shiftedNormalizedFrameFunction (H := H) hdim μ hden u
  have hv' :=
    frame_quadratic_shiftedNormalizedFrameFunction (H := H) hdim μ hden v
  unfold local_quad2DDefect local_quad2DExpr
  rw [hplus, hminus, hu', hv']
  field_simp [hden]
  rw [hnorm_plus, hnorm_minus, hu, hv]
  ring

private lemma local_defect_g_shiftedNormalizedFrameFunction
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) ≠ 0)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    local_defect_g (shiftedNormalizedFrameFunction (H := H) hdim μ hden) u v t =
      local_defect_g μ u v t /
        (1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ)) := by
  simpa [local_defect_g] using
    local_quad2DDefect_shiftedNormalizedFrameFunction (H := H) hdim μ hden u v hu hv huv 1 t

private lemma Q_sphere_inf_shiftedNormalizedFrameFunction_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) ≠ 0) :
    sInf (Q_sphere_set (shiftedNormalizedFrameFunction (H := H) hdim μ hden)) = 0 := by
  let ν := shiftedNormalizedFrameFunction (H := H) hdim μ hden
  have hν_nonneg : 0 ≤ sInf (Q_sphere_set ν) :=
    Q_sphere_inf_nonneg hdim ν
  refine le_antisymm ?_ hν_nonneg
  by_contra hpos
  have hν_pos : 0 < sInf (Q_sphere_set ν) := lt_of_not_ge hpos
  let ε : ℝ := sInf (Q_sphere_set ν) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hden_nonneg :
      0 ≤ 1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) := by
    linarith [sphere_inf_mul_finrank_le_one (H := H) hdim μ]
  have hden_pos :
      0 < 1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) :=
    lt_of_le_of_ne hden_nonneg hden.symm
  obtain ⟨p, hp, hp_lt⟩ :=
    exists_near_infimum (H := H) hdim μ
      (ε * (1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ)))
      (mul_pos hε hden_pos)
  let den : ℝ := 1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ)
  have hpν :=
    frame_quadratic_shiftedNormalizedFrameFunction_of_unit
      (H := H) hdim μ hden p hp
  have hν_lt : frame_quadratic (H := H) ν p < ε := by
    rw [hpν]
    have hnum_lt : frame_quadratic (H := H) μ p - sInf (Q_sphere_set μ) < ε * den := by
      dsimp [den]
      linarith [hp_lt]
    apply (div_lt_iff₀ hden_pos).2
    simpa [den]
  have hν_ge : sInf (Q_sphere_set ν) ≤ frame_quadratic (H := H) ν p :=
    Q_sphere_inf_le ν p hp
  have hcontra : sInf (Q_sphere_set ν) < ε := lt_of_le_of_lt hν_ge hν_lt
  dsimp [ε] at hcontra
  linarith

private lemma sum_rankOneProjection_eq_one_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H) :
    ∑ i, (RankOne.rankOneProjection (H := H) (b i) (b.orthonormal.ne_zero i)).1 = 1 := by
  convert b.sum_repr
  constructor <;> intro h
  · exact fun x => b.sum_repr x
  · ext x
    generalize_proofs at *
    convert h x using 1
    unfold RankOne.rankOneProjection
    simp +decide [Submodule.starProjection_singleton, b.repr_apply_apply]

private lemma sum_frame_quadratic_onb_local
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : FrameFunction H) (b : OrthonormalBasis ι ℂ H) :
    ∑ i, frame_quadratic (H := H) μ (b i) = 1 := by
  let P : ι → Projection H :=
    fun i => RankOne.rankOneProjection (H := H) (b i) (b.orthonormal.ne_zero i)
  have horth : ∀ i j, i ≠ j → Projection.orthogonal (P i) (P j) := by
    intro i j hij
    exact Projection.rankOneProjection_orthogonal_of_orthogonal
      (u := b i) (v := b j) (hu := b.orthonormal.ne_zero i) (hv := b.orthonormal.ne_zero j)
      (OrthonormalBasis.inner_eq_zero (b := b) hij)
  have hsum :
      μ.μ (Projection.sum (H := H) (ι := ι) Finset.univ P horth) =
        ∑ i, μ.μ (P i) := by
    simpa [P] using FrameFunction.map_sum (H := H) μ (s := Finset.univ) (P := P) horth
  have hproj :
      Projection.sum (H := H) (ι := ι) Finset.univ P horth = Projection.one (H := H) := by
    apply Subtype.ext
    simpa [P, Projection.sum_coe] using sum_rankOneProjection_eq_one_local (H := H) b
  calc
    ∑ i, frame_quadratic (H := H) μ (b i)
        = ∑ i, μ.μ (P i) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            dsimp [P]
            exact frame_quadratic_eq_mu_rankOne_of_unit
              (H := H) μ (b i) (b.orthonormal.norm_eq_one i)
    _ = μ.μ (Projection.sum (H := H) (ι := ι) Finset.univ P horth) := by
          symm
          exact hsum
    _ = 1 := by simpa [hproj] using μ.normalized

private lemma frame_quadratic_eq_sInf_of_den_eq_zero_on_unit
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden0 :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) = 0)
    (x : H) (hx : ‖x‖ = 1) :
    frame_quadratic (H := H) μ x = sInf (Q_sphere_set μ) := by
  classical
  let v : Set H := {x}
  have hv : Orthonormal ℂ ((↑) : v → H) := by
    rw [orthonormal_iff_ite]
    intro a b
    have ha : (a : H) = x := by
      have : (a : H) ∈ ({x} : Set H) := by simpa [v] using a.property
      exact Set.mem_singleton_iff.mp this
    have hb : (b : H) = x := by
      have : (b : H) ∈ ({x} : Set H) := by simpa [v] using b.property
      exact Set.mem_singleton_iff.mp this
    have hab : a = b := by
      ext
      simpa [ha, hb]
    subst hab
    have hnorm_a : ‖(a : H)‖ = 1 := by
      simpa [ha] using hx
    have hxx : inner (𝕜 := ℂ) (a : H) (a : H) = (1 : ℂ) := by
      calc
        inner (𝕜 := ℂ) (a : H) (a : H) = ((‖(a : H)‖ : ℝ) : ℂ) ^ 2 := by
          simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (a : H))
        _ = (((1 : ℝ) : ℂ) ^ 2) := by rw [hnorm_a]
        _ = 1 := by norm_num
    simpa using hxx
  obtain ⟨s, b, hvsub, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension (𝕜 := ℂ) (E := H) (v := v) hv
  have hx_mem : x ∈ s := by
    have : x ∈ (v : Set H) := by simp [v]
    exact hvsub this
  let ix : s := ⟨x, hx_mem⟩
  have hbx : b ix = x := by
    have := congrArg (fun f => f ix) hb
    simpa [ix] using this
  have hsum : ∑ i : s, frame_quadratic (H := H) μ (b i) = 1 :=
    sum_frame_quadratic_onb_local (H := H) μ b
  let P : s → Projection H :=
    fun i => RankOne.rankOneProjection (H := H) (b i) (b.orthonormal.ne_zero i)
  have horth : ∀ i j, i ≠ j → Projection.orthogonal (P i) (P j) := by
    intro i j hij
    exact Projection.rankOneProjection_orthogonal_of_orthogonal
      (u := b i) (v := b j) (hu := b.orthonormal.ne_zero i) (hv := b.orthonormal.ne_zero j)
      (OrthonormalBasis.inner_eq_zero (b := b) hij)
  have hproj :
      Projection.sum (H := H) (ι := s) Finset.univ P horth = Projection.one (H := H) := by
    apply Subtype.ext
    simpa [P, Projection.sum_coe] using sum_rankOneProjection_eq_one_local (H := H) b
  have hcard : (Fintype.card s : ℝ) = Module.finrank ℂ H := by
    have htrace :
        projectionTrace (Projection.one (H := H)) = (Fintype.card s : ℝ) := by
      rw [← hproj]
      rw [projectionTrace_sum (H := H) (s := Finset.univ) (P := P) horth]
      simp [P, projectionTrace_rankOne]
    linarith [projectionTrace_one (H := H)]
  have hprod : sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) = 1 := by
    linarith
  have hsum_inf : ∑ i : s, sInf (Q_sphere_set μ) = 1 := by
    calc
      ∑ i : s, sInf (Q_sphere_set μ)
          = (Fintype.card s : ℝ) * sInf (Q_sphere_set μ) := by simp
      _ = (Module.finrank ℂ H : ℝ) * sInf (Q_sphere_set μ) := by rw [hcard]
      _ = sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) := by ring
      _ = 1 := hprod
  have hix : ix ∈ (Finset.univ : Finset s) := by simp
  let rest : Finset s := (Finset.univ : Finset s) \ {ix}
  have hsplit :=
    Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ : Finset s))
      (f := fun i : s => frame_quadratic (H := H) μ (b i)) hix
  have hsplit_inf :=
    Finset.sum_eq_add_sum_diff_singleton
      (s := (Finset.univ : Finset s))
      (f := fun _ : s => sInf (Q_sphere_set μ)) hix
  have hsplit_rest :
      ∑ i : s, frame_quadratic (H := H) μ (b i) =
        frame_quadratic (H := H) μ (b ix) +
          Finset.sum rest (fun i => frame_quadratic (H := H) μ (b i)) := by
    simpa [rest] using hsplit
  have hsplit_inf_rest :
      ∑ i : s, sInf (Q_sphere_set μ) =
        sInf (Q_sphere_set μ) + Finset.sum rest (fun _ => sInf (Q_sphere_set μ)) := by
    simpa [rest] using hsplit_inf
  have hrest_lb :
      Finset.sum rest (fun _ => sInf (Q_sphere_set μ)) ≤
        Finset.sum rest (fun i => frame_quadratic (H := H) μ (b i)) := by
    exact Finset.sum_le_sum (fun i _hi =>
      Q_sphere_inf_le μ (b i) (b.orthonormal.norm_eq_one i))
  have hx_le : frame_quadratic (H := H) μ (b ix) ≤ sInf (Q_sphere_set μ) := by
    by_contra hlt
    have hlt_sum :
        sInf (Q_sphere_set μ) + Finset.sum rest (fun _ => sInf (Q_sphere_set μ)) <
          frame_quadratic (H := H) μ (b ix) +
            Finset.sum rest (fun i => frame_quadratic (H := H) μ (b i)) := by
      exact add_lt_add_of_lt_of_le (lt_of_not_ge hlt) hrest_lb
    have hleft :
        sInf (Q_sphere_set μ) + Finset.sum rest (fun _ => sInf (Q_sphere_set μ)) = 1 := by
      calc
        sInf (Q_sphere_set μ) + Finset.sum rest (fun _ => sInf (Q_sphere_set μ))
            = ∑ i : s, sInf (Q_sphere_set μ) := by
                symm
                exact hsplit_inf_rest
        _ = 1 := hsum_inf
    have hright :
        frame_quadratic (H := H) μ (b ix) +
            Finset.sum rest (fun i => frame_quadratic (H := H) μ (b i)) = 1 := by
      calc
        frame_quadratic (H := H) μ (b ix) +
            Finset.sum rest (fun i => frame_quadratic (H := H) μ (b i))
            = ∑ i : s, frame_quadratic (H := H) μ (b i) := by
                symm
                exact hsplit_rest
        _ = 1 := hsum
    have : (1 : ℝ) < 1 := by
      calc
        (1 : ℝ)
            = sInf (Q_sphere_set μ) + Finset.sum rest (fun _ => sInf (Q_sphere_set μ)) := hleft.symm
        _ < frame_quadratic (H := H) μ (b ix) +
              Finset.sum rest (fun i => frame_quadratic (H := H) μ (b i)) := hlt_sum
        _ = 1 := hright
    exact lt_irrefl _ this
  have hx_ge : sInf (Q_sphere_set μ) ≤ frame_quadratic (H := H) μ x :=
    Q_sphere_inf_le μ x hx
  have hx_le' : frame_quadratic (H := H) μ x ≤ sInf (Q_sphere_set μ) := by
    simpa [hbx] using hx_le
  exact le_antisymm hx_le' hx_ge

private lemma frame_quadratic_eq_inf_mul_sq_norm_of_den_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden0 :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) = 0)
    (x : H) :
    frame_quadratic (H := H) μ x =
      sInf (Q_sphere_set μ) * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · subst hx
    simp [frame_quadratic_zero]
  · let u := Gleason.RankOne.normalize (H := H) x
    have hu : ‖u‖ = 1 := rankOne_normalize_norm_eq_one (H := H) x hx
    have hu_val :
        frame_quadratic (H := H) μ u = sInf (Q_sphere_set μ) :=
      frame_quadratic_eq_sInf_of_den_eq_zero_on_unit (H := H) hdim μ hden0 u hu
    have hnorm_ne : ((‖x‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hx)
    have hx_repr : (((‖x‖ : ℝ) : ℂ) • u) = x := by
      dsimp [u, Gleason.RankOne.normalize]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rw [smul_smul]
      have hmul : ((‖x‖ : ℂ) * ((‖x‖ : ℂ)⁻¹)) = (1 : ℂ) := by
        field_simp [hnorm_ne]
      simpa [hmul]
    have hscale := frame_quadratic_sq_hom (μ := μ) (((‖x‖ : ℝ) : ℂ)) u
    calc
      frame_quadratic (H := H) μ x
          = frame_quadratic (H := H) μ ((((‖x‖ : ℝ) : ℂ)) • u) := by
              rw [hx_repr]
      _ = ‖x‖ ^ 2 * frame_quadratic (H := H) μ u := by
            simpa [Complex.norm_real, sq_abs, abs_of_nonneg (norm_nonneg x)] using hscale
      _ = sInf (Q_sphere_set μ) * ‖x‖ ^ 2 := by rw [hu_val, mul_comm]

private lemma local_quad2DDefect_eq_zero_of_den_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden0 :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) = 0)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    local_quad2DDefect μ u v a b = 0 := by
  have hinner : inner (𝕜 := ℂ) (a • u) (b • v) = 0 := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a u, RCLike.real_smul_eq_coe_smul (K := ℂ) b v]
    simp [huv]
  have hnorm_smul_u : ‖a • u‖ ^ 2 = a ^ 2 := by
    simp [norm_smul, hu, Real.norm_eq_abs, pow_two]
  have hnorm_smul_v : ‖b • v‖ ^ 2 = b ^ 2 := by
    simp [norm_smul, hv, Real.norm_eq_abs, pow_two]
  have hnorm_plus_real : ‖a • u + b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    have hmul :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := a • u) (y := b • v) hinner
    have hsq :
        ‖a • u + b • v‖ ^ 2 = ‖a • u‖ ^ 2 + ‖b • v‖ ^ 2 := by
      simpa [pow_two] using hmul
    simpa [hnorm_smul_u, hnorm_smul_v, add_comm, add_left_comm, add_assoc] using hsq
  have hnorm_minus_real : ‖a • u - b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    have hinner' : inner (𝕜 := ℂ) (a • u) (-(b • v)) = 0 := by
      simp [inner_neg_right, hinner]
    have hmul :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := a • u) (y := -(b • v)) hinner'
    have hsq :
        ‖a • u + -(b • v)‖ ^ 2 = ‖a • u‖ ^ 2 + ‖-(b • v)‖ ^ 2 := by
      simpa [pow_two] using hmul
    simpa [sub_eq_add_neg, hnorm_smul_u, hnorm_smul_v, add_comm, add_left_comm, add_assoc] using hsq
  have hnorm_plus : ‖(a : ℂ) • u + (b : ℂ) • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using hnorm_plus_real
  have hnorm_minus : ‖(a : ℂ) • u - (b : ℂ) • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using hnorm_minus_real
  have hplus :=
    frame_quadratic_eq_inf_mul_sq_norm_of_den_eq_zero
      (H := H) hdim μ hden0 ((a : ℂ) • u + (b : ℂ) • v)
  have hminus :=
    frame_quadratic_eq_inf_mul_sq_norm_of_den_eq_zero
      (H := H) hdim μ hden0 ((a : ℂ) • u - (b : ℂ) • v)
  have hu' := frame_quadratic_eq_inf_mul_sq_norm_of_den_eq_zero (H := H) hdim μ hden0 u
  have hv' := frame_quadratic_eq_inf_mul_sq_norm_of_den_eq_zero (H := H) hdim μ hden0 v
  unfold local_quad2DDefect local_quad2DExpr
  rw [hplus, hminus, hu', hv']
  rw [hnorm_plus, hnorm_minus, hu, hv]
  ring

private lemma local_defect_g_eq_zero_of_den_eq_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden0 :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) = 0)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  simpa [local_defect_g] using
    local_quad2DDefect_eq_zero_of_den_eq_zero (H := H) hdim μ hden0 u v hu hv huv 1 t

private lemma frame_quadratic_add_real_smul_eq_scaled_greatCircleRestriction
    (μ : FrameFunction H) (u v : H) (t : ℝ) :
    frame_quadratic (H := H) μ (u + (t : ℂ) • v) =
      (1 + t ^ 2) * greatCircleRestriction μ u v (Real.arctan t) := by
  let r : ℝ := Real.sqrt (1 + t ^ 2)
  have hr_sq : r ^ 2 = 1 + t ^ 2 := by
    dsimp [r]
    rw [Real.sq_sqrt]
    positivity
  have hr_pos : 0 < r := by
    dsimp [r]
    apply Real.sqrt_pos.2
    positivity
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hcos : r * Real.cos (Real.arctan t) = 1 := by
    dsimp [r]
    rw [Real.cos_arctan]
    field_simp [hr_ne]
  have hsin : r * Real.sin (Real.arctan t) = t := by
    dsimp [r]
    rw [Real.sin_arctan]
    field_simp [hr_ne]
  have hscale :
      ((r : ℂ) •
          (((Real.cos (Real.arctan t) : ℝ) : ℂ) • u +
            ((Real.sin (Real.arctan t) : ℝ) : ℂ) • v)) =
        u + (t : ℂ) • v := by
    rw [smul_add, smul_smul, smul_smul]
    have hcos' : ((r : ℂ) * ((Real.cos (Real.arctan t) : ℝ) : ℂ)) = 1 := by
      exact_mod_cast hcos
    have hsin' : ((r : ℂ) * ((Real.sin (Real.arctan t) : ℝ) : ℂ)) = (t : ℂ) := by
      exact_mod_cast hsin
    rw [hcos', hsin']
    simp
  calc
    frame_quadratic (H := H) μ (u + (t : ℂ) • v)
        = frame_quadratic (H := H) μ
            ((r : ℂ) •
              (((Real.cos (Real.arctan t) : ℝ) : ℂ) • u +
                ((Real.sin (Real.arctan t) : ℝ) : ℂ) • v)) := by
            rw [hscale.symm]
    _ =
      ‖(r : ℂ)‖ ^ 2 * frame_quadratic (H := H) μ
        ((((Real.cos (Real.arctan t) : ℝ) : ℂ) • u +
          ((Real.sin (Real.arctan t) : ℝ) : ℂ) • v)) := by
            rw [frame_quadratic_sq_hom]
    _ = (1 + t ^ 2) * greatCircleRestriction μ u v (Real.arctan t) := by
      simp [greatCircleRestriction, r, hr_sq]

private lemma frame_quadratic_sub_real_smul_eq_scaled_greatCircleRestriction
    (μ : FrameFunction H) (u v : H) (t : ℝ) :
    frame_quadratic (H := H) μ (u - (t : ℂ) • v) =
      (1 + t ^ 2) * greatCircleRestriction μ u v (-Real.arctan t) := by
  simpa [sub_eq_add_neg, Real.arctan_neg]
    using frame_quadratic_add_real_smul_eq_scaled_greatCircleRestriction
      (μ := μ) (u := u) (v := v) (-t)

private lemma local_defect_g_continuous_of_zero_at_orthogonal_p
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0) :
    Continuous (fun t : ℝ => local_defect_g μ u v t) := by
  have hgc :
      Continuous (greatCircleRestriction μ u v) :=
    continuous_greatCircleRestriction_of_zero_at_p
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hp0
  have hplus :
      Continuous (fun t : ℝ => frame_quadratic (H := H) μ (u + (t : ℂ) • v)) := by
    have hscale : Continuous fun t : ℝ => 1 + t ^ 2 :=
      continuous_const.add (continuous_id.pow 2)
    have hEq :
        (fun t : ℝ => frame_quadratic (H := H) μ (u + (t : ℂ) • v)) =
          (fun t : ℝ => (1 + t ^ 2) * greatCircleRestriction μ u v (Real.arctan t)) := by
      funext t
      exact frame_quadratic_add_real_smul_eq_scaled_greatCircleRestriction
        (μ := μ) (u := u) (v := v) t
    rw [hEq]
    exact hscale.mul (hgc.comp Real.continuous_arctan)
  have hminus :
      Continuous (fun t : ℝ => frame_quadratic (H := H) μ (u - (t : ℂ) • v)) := by
    have hscale : Continuous fun t : ℝ => 1 + t ^ 2 :=
      continuous_const.add (continuous_id.pow 2)
    have hatanNeg : Continuous fun t : ℝ => -Real.arctan t :=
      Real.continuous_arctan.neg
    have hEq :
        (fun t : ℝ => frame_quadratic (H := H) μ (u - (t : ℂ) • v)) =
          (fun t : ℝ => (1 + t ^ 2) * greatCircleRestriction μ u v (-Real.arctan t)) := by
      funext t
      exact frame_quadratic_sub_real_smul_eq_scaled_greatCircleRestriction
        (μ := μ) (u := u) (v := v) t
    rw [hEq]
    exact hscale.mul (hgc.comp hatanNeg)
  have ht2 : Continuous fun t : ℝ => 2 * t ^ 2 * frame_quadratic (H := H) μ v := by
    exact (continuous_const.mul (continuous_id.pow 2)).mul continuous_const
  unfold local_defect_g local_quad2DDefect local_quad2DExpr
  simpa [one_smul] using (hplus.add hminus).sub
    ((continuous_const.add ht2))

private lemma local_defect_g_continuous_of_sphere_continuous
    (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1)) :
    Continuous (fun t : ℝ => local_defect_g μ u v t) := by
  let sfun : ℝ → ℝ := fun t => Real.sqrt (1 + t ^ 2)
  let xplus : ℝ → H := fun t =>
    (((sfun t)⁻¹ : ℝ) : ℂ) • (u + (t : ℂ) • v)
  let xminus : ℝ → H := fun t =>
    (((sfun t)⁻¹ : ℝ) : ℂ) • (u - (t : ℂ) • v)
  have hsfun_pos : ∀ t : ℝ, 0 < sfun t := by
    intro t
    dsimp [sfun]
    apply Real.sqrt_pos.2
    positivity
  have hsfun_ne : ∀ t : ℝ, sfun t ≠ 0 := fun t => ne_of_gt (hsfun_pos t)
  have hxplus_mem : ∀ t : ℝ, xplus t ∈ Metric.sphere (0 : H) 1 := by
    intro t
    have hnorm_sq :
        ‖u + (t : ℂ) • v‖ ^ 2 = 1 + t ^ 2 :=
      norm_sq_add_smul_of_orthonormal u v hu hv huv t
    have hnorm_formula :
        ‖xplus t‖ = (sfun t)⁻¹ * ‖u + (t : ℂ) • v‖ := by
      dsimp [xplus]
      rw [norm_smul, Real.norm_eq_abs]
      simp [sfun, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    have hnorm_sq' :
        ‖xplus t‖ ^ 2 = 1 := by
      rw [hnorm_formula]
      have hsqrt_sq : (sfun t) ^ 2 = 1 + t ^ 2 := by
        dsimp [sfun]
        rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)]
      have hs2_ne : (sfun t) ^ 2 ≠ 0 := by
        exact pow_ne_zero 2 (hsfun_ne t)
      apply (mul_right_cancel₀ hs2_ne)
      calc
        (((sfun t)⁻¹ * ‖u + (t : ℂ) • v‖) ^ 2) * (sfun t) ^ 2
            = ‖u + (t : ℂ) • v‖ ^ 2 := by
                field_simp [pow_two, hsfun_ne t]
        _ = (1 : ℝ) * (sfun t) ^ 2 := by
              rw [hnorm_sq, hsqrt_sq]
              ring
    have hnorm : ‖xplus t‖ = 1 := by
      nlinarith [norm_nonneg (xplus t), hnorm_sq']
    simpa [Metric.mem_sphere] using hnorm
  have hxminus_mem : ∀ t : ℝ, xminus t ∈ Metric.sphere (0 : H) 1 := by
    intro t
    have hnorm_sq :
        ‖u - (t : ℂ) • v‖ ^ 2 = 1 + t ^ 2 :=
      norm_sq_sub_smul_of_orthonormal u v hu hv huv t
    have hnorm_formula :
        ‖xminus t‖ = (sfun t)⁻¹ * ‖u - (t : ℂ) • v‖ := by
      dsimp [xminus]
      rw [norm_smul, Real.norm_eq_abs]
      simp [sfun, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    have hnorm_sq' :
        ‖xminus t‖ ^ 2 = 1 := by
      rw [hnorm_formula]
      have hsqrt_sq : (sfun t) ^ 2 = 1 + t ^ 2 := by
        dsimp [sfun]
        rw [Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)]
      have hs2_ne : (sfun t) ^ 2 ≠ 0 := by
        exact pow_ne_zero 2 (hsfun_ne t)
      apply (mul_right_cancel₀ hs2_ne)
      calc
        (((sfun t)⁻¹ * ‖u - (t : ℂ) • v‖) ^ 2) * (sfun t) ^ 2
            = ‖u - (t : ℂ) • v‖ ^ 2 := by
                field_simp [pow_two, hsfun_ne t]
        _ = (1 : ℝ) * (sfun t) ^ 2 := by
              rw [hnorm_sq, hsqrt_sq]
              ring
    have hnorm : ‖xminus t‖ = 1 := by
      nlinarith [norm_nonneg (xminus t), hnorm_sq']
    simpa [Metric.mem_sphere] using hnorm
  have hsfun_inv_cont : Continuous fun t : ℝ => (sfun t)⁻¹ := by
    apply Continuous.inv₀
    · dsimp [sfun]
      exact Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))
    · exact hsfun_ne
  have hxplus_cont : Continuous xplus := by
    dsimp [xplus]
    refine (Complex.continuous_ofReal.comp hsfun_inv_cont).smul ?_
    exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_id).smul continuous_const)
  have hxminus_cont : Continuous xminus := by
    dsimp [xminus]
    refine (Complex.continuous_ofReal.comp hsfun_inv_cont).smul ?_
    exact continuous_const.sub ((Complex.continuous_ofReal.comp continuous_id).smul continuous_const)
  have hQplus_unit_cont : Continuous fun t : ℝ => frame_quadratic (H := H) μ (xplus t) := by
    exact hcont.comp_continuous hxplus_cont hxplus_mem
  have hQminus_unit_cont : Continuous fun t : ℝ => frame_quadratic (H := H) μ (xminus t) := by
    exact hcont.comp_continuous hxminus_cont hxminus_mem
  have hQplus_cont :
      Continuous fun t : ℝ => frame_quadratic (H := H) μ (u + (t : ℂ) • v) := by
    have hrepr :
        (fun t : ℝ => frame_quadratic (H := H) μ (u + (t : ℂ) • v))
          =
        fun t : ℝ => (1 + t ^ 2) * frame_quadratic (H := H) μ (xplus t) := by
      funext t
      have hsmul :
          ((sfun t : ℝ) : ℂ) • xplus t = u + (t : ℂ) • v := by
        dsimp [xplus]
        rw [smul_smul]
        simp [sfun, hsfun_ne t]
      calc
        frame_quadratic (H := H) μ (u + (t : ℂ) • v)
            = frame_quadratic (H := H) μ (((sfun t : ℝ) : ℂ) • xplus t) := by
                rw [hsmul]
        _ = ‖(((sfun t : ℝ) : ℂ))‖ ^ 2 * frame_quadratic (H := H) μ (xplus t) := by
              exact frame_quadratic_sq_hom μ (((sfun t : ℝ) : ℂ)) (xplus t)
        _ = (1 + t ^ 2) * frame_quadratic (H := H) μ (xplus t) := by
              simp [sfun, Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)]
    rw [hrepr]
    exact (continuous_const.add (continuous_id.pow 2)).mul hQplus_unit_cont
  have hQminus_cont :
      Continuous fun t : ℝ => frame_quadratic (H := H) μ (u - (t : ℂ) • v) := by
    have hrepr :
        (fun t : ℝ => frame_quadratic (H := H) μ (u - (t : ℂ) • v))
          =
        fun t : ℝ => (1 + t ^ 2) * frame_quadratic (H := H) μ (xminus t) := by
      funext t
      have hsmul :
          ((sfun t : ℝ) : ℂ) • xminus t = u - (t : ℂ) • v := by
        dsimp [xminus]
        rw [smul_smul]
        simp [sfun, hsfun_ne t]
      calc
        frame_quadratic (H := H) μ (u - (t : ℂ) • v)
            = frame_quadratic (H := H) μ (((sfun t : ℝ) : ℂ) • xminus t) := by
                rw [hsmul]
        _ = ‖(((sfun t : ℝ) : ℂ))‖ ^ 2 * frame_quadratic (H := H) μ (xminus t) := by
              exact frame_quadratic_sq_hom μ (((sfun t : ℝ) : ℂ)) (xminus t)
        _ = (1 + t ^ 2) * frame_quadratic (H := H) μ (xminus t) := by
              simp [sfun, Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)]
    rw [hrepr]
    exact (continuous_const.add (continuous_id.pow 2)).mul hQminus_unit_cont
  have hconst1 : Continuous fun _ : ℝ => 2 * frame_quadratic (H := H) μ u := continuous_const
  have hconst2 : Continuous fun t : ℝ => 2 * t ^ 2 * frame_quadratic (H := H) μ v := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (continuous_const.mul ((continuous_id.pow 2).mul continuous_const) :
        Continuous fun t : ℝ => (2 : ℝ) * (t ^ 2 * frame_quadratic (H := H) μ v))
  have hmain :
      Continuous fun t : ℝ =>
        frame_quadratic (H := H) μ (u + (t : ℂ) • v) +
          frame_quadratic (H := H) μ (u - (t : ℂ) • v) -
          (2 * frame_quadratic (H := H) μ u + 2 * t ^ 2 * frame_quadratic (H := H) μ v) :=
    hQplus_cont.add hQminus_cont |>.sub (hconst1.add hconst2)
  simpa [local_defect_g, local_quad2DDefect, local_quad2DExpr, one_smul,
    mul_assoc, mul_left_comm, mul_comm] using hmain

private lemma exists_frame_quadratic_sphere_minimizer
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1)) :
    ∃ p₀ : H,
      ‖p₀‖ = 1 ∧
      frame_quadratic μ p₀ = sInf (Q_sphere_set μ) := by
  haveI : ProperSpace H := FiniteDimensional.proper_rclike ℂ H
  have hcpt : IsCompact (Metric.sphere (0 : H) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : H) 1).Nonempty := by
    have hdim_pos : 0 < Module.finrank ℂ H := by omega
    haveI : Nontrivial H := Module.nontrivial_of_finrank_pos hdim_pos
    obtain ⟨w, hw⟩ := exists_ne (0 : H)
    exact ⟨(‖w‖⁻¹ : ℝ) • w, by
      simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]⟩
  obtain ⟨p₀, hp₀_mem, hp₀_min⟩ := hcpt.exists_isMinOn hne hcont
  have hp₀_norm : ‖p₀‖ = 1 := by simpa [Metric.mem_sphere] using hp₀_mem
  have hp₀_val : frame_quadratic μ p₀ = sInf (Q_sphere_set μ) := by
    apply le_antisymm
    · exact le_csInf (Q_sphere_set_nonempty hdim μ) (fun y hy => by
        rcases hy with ⟨x, hx_mem, rfl⟩
        exact hp₀_min hx_mem)
    · exact csInf_le (Q_sphere_set_bddBelow μ) ⟨p₀, by simp [hp₀_norm], rfl⟩
  exact ⟨p₀, hp₀_norm, hp₀_val⟩

private lemma minimizer_rotation_sum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p₀ v : H) (hp₀ : ‖p₀‖ = 1) (hv : ‖v‖ = 1)
    (hpv : inner (𝕜 := ℂ) p₀ v = 0) :
    frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ + v)) +
      frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ - v)) =
      frame_quadratic μ p₀ + frame_quadratic μ v := by
  simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
    rp_split_sum hdim μ p₀ v hp₀ hv hpv

private lemma minimizer_rotation_each_le
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p₀ v : H) (hp₀ : ‖p₀‖ = 1) (hv : ‖v‖ = 1)
    (hpv : inner (𝕜 := ℂ) p₀ v = 0)
    (hp₀_min : frame_quadratic μ p₀ = sInf (Q_sphere_set μ)) :
    frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ + v)) ≤ frame_quadratic μ v
      ∧
    frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ - v)) ≤ frame_quadratic μ v := by
  have hsum := minimizer_rotation_sum hdim μ p₀ v hp₀ hv hpv
  have hpv_plus :
      ‖((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ + v) )‖ = 1 := by
    simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      oscillation_transferred_norm p₀ v hp₀ hv hpv
  have hpv_minus :
      ‖((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ - v) )‖ = 1 := by
    simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      oscillation_transferred_norm_sub p₀ v hp₀ hv hpv
  have hplus_ge :
      sInf (Q_sphere_set μ) ≤ frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ + v)) :=
    Q_sphere_inf_le μ _ hpv_plus
  have hminus_ge :
      sInf (Q_sphere_set μ) ≤ frame_quadratic μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ - v)) :=
    Q_sphere_inf_le μ _ hpv_minus
  constructor
  · linarith [hsum, hminus_ge, hp₀_min]
  · linarith [hsum, hplus_ge, hp₀_min]

private def minimizer_delta
    (μ : FrameFunction H) (x : H) : ℝ :=
  frame_quadratic μ x - sInf (Q_sphere_set μ)

private lemma minimizer_delta_nonneg_of_unit
    (μ : FrameFunction H) (x : H) (hx : ‖x‖ = 1) :
    0 ≤ minimizer_delta μ x := by
  unfold minimizer_delta
  exact sub_nonneg.mpr (Q_sphere_inf_le μ x hx)

private lemma minimizer_delta_rotation_sum
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p₀ v : H) (hp₀ : ‖p₀‖ = 1) (hv : ‖v‖ = 1)
    (hpv : inner (𝕜 := ℂ) p₀ v = 0)
    (hp₀_min : frame_quadratic μ p₀ = sInf (Q_sphere_set μ)) :
    minimizer_delta μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ + v)) +
      minimizer_delta μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ - v)) =
      minimizer_delta μ v := by
  have hsum := minimizer_rotation_sum hdim μ p₀ v hp₀ hv hpv
  unfold minimizer_delta
  linarith [hsum, hp₀_min]

private lemma minimizer_delta_rotation_each_le
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p₀ v : H) (hp₀ : ‖p₀‖ = 1) (hv : ‖v‖ = 1)
    (hpv : inner (𝕜 := ℂ) p₀ v = 0)
    (hp₀_min : frame_quadratic μ p₀ = sInf (Q_sphere_set μ)) :
    minimizer_delta μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ + v)) ≤ minimizer_delta μ v
      ∧
    minimizer_delta μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ - v)) ≤ minimizer_delta μ v := by
  have hsum := minimizer_delta_rotation_sum hdim μ p₀ v hp₀ hv hpv hp₀_min
  have hplus_nonneg :
      0 ≤ minimizer_delta μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ + v)) := by
    have hnorm : ‖((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ + v) )‖ = 1 := by
      simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
        oscillation_transferred_norm p₀ v hp₀ hv hpv
    exact minimizer_delta_nonneg_of_unit μ _ hnorm
  have hminus_nonneg :
      0 ≤ minimizer_delta μ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ - v)) := by
    have hnorm : ‖((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (p₀ - v) )‖ = 1 := by
      simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
        oscillation_transferred_norm_sub p₀ v hp₀ hv hpv
    exact minimizer_delta_nonneg_of_unit μ _ hnorm
  constructor
  · linarith [hsum, hminus_nonneg]
  · linarith [hsum, hplus_nonneg]

private lemma exists_orthogonal_partner_minimizer_of_continuity
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1))
    (p₀ : H) (hp₀ : ‖p₀‖ = 1) :
    ∃ v₀ : H,
      ‖v₀‖ = 1 ∧
      inner (𝕜 := ℂ) p₀ v₀ = 0 ∧
      (∀ x : H, ‖x‖ = 1 → inner (𝕜 := ℂ) p₀ x = 0 →
        frame_quadratic μ v₀ ≤ frame_quadratic μ x) := by
  haveI : ProperSpace H := FiniteDimensional.proper_rclike ℂ H
  let K : Set H :=
    {x : H | x ∈ Metric.sphere (0 : H) 1 ∧ inner (𝕜 := ℂ) p₀ x = 0}
  have hsphere_cpt : IsCompact (Metric.sphere (0 : H) 1) := isCompact_sphere 0 1
  have horth_closed : IsClosed {x : H | inner (𝕜 := ℂ) p₀ x = 0} := by
    have hcont_inner : Continuous fun x : H => inner (𝕜 := ℂ) p₀ x :=
      continuous_const.inner continuous_id
    simpa using isClosed_eq hcont_inner continuous_const
  have hK_cpt : IsCompact K := by
    have hK_eq : K = (Metric.sphere (0 : H) 1) ∩ {x : H | inner (𝕜 := ℂ) p₀ x = 0} := by
      ext x
      simp [K]
    rw [hK_eq]
    exact hsphere_cpt.inter_right horth_closed
  have hK_nonempty : K.Nonempty := by
    rcases exists_unit_orthogonal_to_pair (H := H) hdim p₀ p₀ with ⟨w, hw, hpw, _⟩
    refine ⟨w, ?_⟩
    exact ⟨by simpa [Metric.mem_sphere] using hw, hpw⟩
  have hcontK : ContinuousOn (fun x => frame_quadratic (H := H) μ x) K :=
    hcont.mono (by
      intro x hx
      exact hx.1)
  obtain ⟨v₀, hv₀_mem, hv₀_min⟩ := hK_cpt.exists_isMinOn hK_nonempty hcontK
  refine ⟨v₀, ?_, ?_, ?_⟩
  · simpa [K, Metric.mem_sphere] using hv₀_mem.1
  · simpa [K] using hv₀_mem.2
  · intro x hx hpx
    exact hv₀_min ⟨by simpa [Metric.mem_sphere] using hx, hpx⟩

private lemma minimizer_delta_le_of_orthogonal_partner_minimizer
    (μ : FrameFunction H)
    (p₀ v₀ x : H)
    (_hv₀ : ‖v₀‖ = 1) (_hpv₀ : inner (𝕜 := ℂ) p₀ v₀ = 0)
    (hx : ‖x‖ = 1) (hpx : inner (𝕜 := ℂ) p₀ x = 0)
    (hv₀_min :
      ∀ y : H, ‖y‖ = 1 → inner (𝕜 := ℂ) p₀ y = 0 →
        frame_quadratic μ v₀ ≤ frame_quadratic μ y) :
    minimizer_delta μ v₀ ≤ minimizer_delta μ x := by
  unfold minimizer_delta
  have hle : frame_quadratic μ v₀ ≤ frame_quadratic μ x :=
    hv₀_min x hx hpx
  linarith [hle]

private def Q_orth_sphere_set
    (μ : FrameFunction H) (p₀ : H) : Set ℝ :=
  Set.image (fun x => frame_quadratic μ x)
    {x : H | x ∈ Metric.sphere (0 : H) 1 ∧ inner (𝕜 := ℂ) p₀ x = 0}

private lemma Q_orth_sphere_set_nonempty
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p₀ : H) (hp₀ : ‖p₀‖ = 1) :
    (Q_orth_sphere_set μ p₀).Nonempty := by
  rcases exists_unit_orthogonal_to_pair (H := H) hdim p₀ p₀ with ⟨w, hw, hpw, _⟩
  refine ⟨frame_quadratic μ w, w, ?_, rfl⟩
  exact ⟨by simpa [Metric.mem_sphere] using hw, hpw⟩

private lemma Q_orth_sphere_set_bddBelow
    (μ : FrameFunction H) (p₀ : H) :
    BddBelow (Q_orth_sphere_set μ p₀) := by
  refine ⟨0, ?_⟩
  intro y hy
  rcases hy with ⟨x, _, rfl⟩
  exact frame_quadratic_nonneg μ x

private lemma exists_orthogonal_infimum_witness_of_continuity
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1))
    (p₀ : H) (hp₀ : ‖p₀‖ = 1) :
    ∃ v₀ : H,
      ‖v₀‖ = 1 ∧
      inner (𝕜 := ℂ) p₀ v₀ = 0 ∧
      frame_quadratic μ v₀ = sInf (Q_orth_sphere_set μ p₀) := by
  obtain ⟨v₀, hv₀, hp₀v₀, hv₀_min⟩ :=
    exists_orthogonal_partner_minimizer_of_continuity hdim μ hcont p₀ hp₀
  refine ⟨v₀, hv₀, hp₀v₀, ?_⟩
  apply le_antisymm
  · exact le_csInf (Q_orth_sphere_set_nonempty hdim μ p₀ hp₀) (by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hv₀_min x (by simpa [Metric.mem_sphere] using hx.1) hx.2)
  · exact csInf_le (Q_orth_sphere_set_bddBelow μ p₀) ⟨v₀, ⟨by simpa [Metric.mem_sphere] using hv₀, hp₀v₀⟩, rfl⟩

private lemma minimizer_delta_eq_orth_inf_gap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1))
    (p₀ : H) (hp₀ : ‖p₀‖ = 1) :
    ∃ v₀ : H,
      ‖v₀‖ = 1 ∧
      inner (𝕜 := ℂ) p₀ v₀ = 0 ∧
      minimizer_delta μ v₀ = sInf (Q_orth_sphere_set μ p₀) - sInf (Q_sphere_set μ) := by
  obtain ⟨v₀, hv₀, hp₀v₀, hv₀_inf⟩ :=
    exists_orthogonal_infimum_witness_of_continuity hdim μ hcont p₀ hp₀
  refine ⟨v₀, hv₀, hp₀v₀, ?_⟩
  unfold minimizer_delta
  linarith [hv₀_inf]

private lemma minimizer_delta_eq_zero_iff_orth_inf_eq_global_inf
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1))
    (p₀ : H) (hp₀ : ‖p₀‖ = 1) :
    ∃ v₀ : H,
      ‖v₀‖ = 1 ∧
      inner (𝕜 := ℂ) p₀ v₀ = 0 ∧
      (minimizer_delta μ v₀ = 0 ↔ sInf (Q_orth_sphere_set μ p₀) = sInf (Q_sphere_set μ)) := by
  obtain ⟨v₀, hv₀, hp₀v₀, hgap⟩ :=
    minimizer_delta_eq_orth_inf_gap hdim μ hcont p₀ hp₀
  refine ⟨v₀, hv₀, hp₀v₀, ?_⟩
  constructor
  · intro hδ0
    linarith [hgap, hδ0]
  · intro hEq
    linarith [hgap, hEq]

private lemma local_defect_g_eq_zero_of_infimum_left_and_delta_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p₀ v : H) (hp₀ : ‖p₀‖ = 1) (hv : ‖v‖ = 1)
    (hpv : inner (𝕜 := ℂ) p₀ v = 0)
    (hp₀_min : frame_quadratic μ p₀ = sInf (Q_sphere_set μ))
    (hδv0 : minimizer_delta μ v = 0)
    (s : ℝ) :
    local_defect_g μ p₀ v s = 0 := by
  have hub :
      local_defect_g μ p₀ v s
        ≤
      2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) +
        2 * s ^ 2 * (frame_quadratic μ p₀ - sInf (Q_sphere_set μ)) := by
    simpa using local_defect_g_upper_bound_infimum hdim μ p₀ v hp₀ hv hpv s
  have hlb :
      - (2 * (frame_quadratic μ p₀ - sInf (Q_sphere_set μ)) +
        2 * s ^ 2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)))
        ≤
      local_defect_g μ p₀ v s := by
    simpa using local_defect_g_lower_bound_infimum μ p₀ v hp₀ hv hpv s
  have hp₀_inf : frame_quadratic μ p₀ - sInf (Q_sphere_set μ) = 0 := by
    rw [hp₀_min]
    ring
  have hδv : frame_quadratic μ v - sInf (Q_sphere_set μ) = 0 := by
    simpa [minimizer_delta] using hδv0
  have hnonneg : 0 ≤ local_defect_g μ p₀ v s := by
    have :
        - (2 * (frame_quadratic μ p₀ - sInf (Q_sphere_set μ)) +
          2 * s ^ 2 * (frame_quadratic μ v - sInf (Q_sphere_set μ))) = 0 := by
      rw [hp₀_inf, hδv]
      ring
    linarith [hlb, this]
  have hnonpos : local_defect_g μ p₀ v s ≤ 0 := by
    have :
        2 * (frame_quadratic μ v - sInf (Q_sphere_set μ)) +
          2 * s ^ 2 * (frame_quadratic μ p₀ - sInf (Q_sphere_set μ)) = 0 := by
      rw [hδv, hp₀_inf]
      ring
    linarith [hub, this]
  exact le_antisymm hnonpos hnonneg

private lemma local_defect_g_zero_all_of_infimum_left_and_delta_zero
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p₀ v : H) (hp₀ : ‖p₀‖ = 1) (hv : ‖v‖ = 1)
    (hpv : inner (𝕜 := ℂ) p₀ v = 0)
    (hp₀_min : frame_quadratic μ p₀ = sInf (Q_sphere_set μ))
    (hδv0 : minimizer_delta μ v = 0) :
    ∀ s : ℝ, local_defect_g μ p₀ v s = 0 := by
  intro s
  exact
    local_defect_g_eq_zero_of_infimum_left_and_delta_zero
      hdim μ p₀ v hp₀ hv hpv hp₀_min hδv0 s

private lemma minimizer_delta_eq_zero_of_orthogonal_infimum_witness
    (μ : FrameFunction H)
    (p₀ v₀ x : H)
    (hv₀ : ‖v₀‖ = 1) (hpv₀ : inner (𝕜 := ℂ) p₀ v₀ = 0)
    (hx : ‖x‖ = 1) (hpx : inner (𝕜 := ℂ) p₀ x = 0)
    (hv₀_min :
      ∀ y : H, ‖y‖ = 1 → inner (𝕜 := ℂ) p₀ y = 0 →
        frame_quadratic μ v₀ ≤ frame_quadratic μ y)
    (hx_inf : frame_quadratic μ x = sInf (Q_sphere_set μ)) :
    minimizer_delta μ v₀ = 0 := by
  have hδ_nonneg : 0 ≤ minimizer_delta μ v₀ :=
    minimizer_delta_nonneg_of_unit μ v₀ hv₀
  have hδ_le : minimizer_delta μ v₀ ≤ minimizer_delta μ x :=
    minimizer_delta_le_of_orthogonal_partner_minimizer
      μ p₀ v₀ x hv₀ hpv₀ hx hpx hv₀_min
  have hδx0 : minimizer_delta μ x = 0 := by
    simpa [minimizer_delta] using sub_eq_zero.mpr hx_inf
  exact le_antisymm (by simpa [hδx0] using hδ_le) hδ_nonneg

private lemma local_defect_g_zero_all_of_infimum_left_and_orthogonal_infimum_witness
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p₀ v₀ x : H)
    (hp₀ : ‖p₀‖ = 1) (hv₀ : ‖v₀‖ = 1) (hx : ‖x‖ = 1)
    (hp₀v₀ : inner (𝕜 := ℂ) p₀ v₀ = 0) (hp₀x : inner (𝕜 := ℂ) p₀ x = 0)
    (hp₀_min : frame_quadratic μ p₀ = sInf (Q_sphere_set μ))
    (hv₀_min :
      ∀ y : H, ‖y‖ = 1 → inner (𝕜 := ℂ) p₀ y = 0 →
        frame_quadratic μ v₀ ≤ frame_quadratic μ y)
    (hx_inf : frame_quadratic μ x = sInf (Q_sphere_set μ)) :
    ∀ s : ℝ, local_defect_g μ p₀ v₀ s = 0 := by
  have hδv₀0 : minimizer_delta μ v₀ = 0 :=
    minimizer_delta_eq_zero_of_orthogonal_infimum_witness
      μ p₀ v₀ x hv₀ hp₀v₀ hx hp₀x hv₀_min hx_inf
  exact
    local_defect_g_zero_all_of_infimum_left_and_delta_zero
      hdim μ p₀ v₀ hp₀ hv₀ hp₀v₀ hp₀_min hδv₀0

private lemma swapped_kernel_s0_zero_of_infimum_left_and_orthogonal_infimum_witness
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p₀ v₀ x : H)
    (hp₀ : ‖p₀‖ = 1) (hv₀ : ‖v₀‖ = 1) (hx : ‖x‖ = 1)
    (hp₀v₀ : inner (𝕜 := ℂ) p₀ v₀ = 0) (hp₀x : inner (𝕜 := ℂ) p₀ x = 0)
    (hp₀_min : frame_quadratic μ p₀ = sInf (Q_sphere_set μ))
    (hv₀_min :
      ∀ y : H, ‖y‖ = 1 → inner (𝕜 := ℂ) p₀ y = 0 →
        frame_quadratic μ v₀ ≤ frame_quadratic μ y)
    (hx_inf : frame_quadratic μ x = sInf (Q_sphere_set μ)) :
    ∀ t : ℝ, swapped_bridge_kernel μ v₀ p₀ 0 t = 0 := by
  intro t
  have hg0 : ∀ s : ℝ, local_defect_g μ p₀ v₀ s = 0 :=
    local_defect_g_zero_all_of_infimum_left_and_orthogonal_infimum_witness
      hdim μ p₀ v₀ x hp₀ hv₀ hx hp₀v₀ hp₀x hp₀_min hv₀_min hx_inf
  have hz : swapped_bridge_kernel μ v₀ p₀ 0 t = -2 * local_defect_g μ p₀ v₀ t :=
    swapped_bridge_kernel_zero_s hdim μ v₀ p₀ hv₀ hp₀
      (by simpa [inner_eq_zero_symm] using hp₀v₀) t
  rw [hz, hg0 t]
  ring

private lemma hard_kernel_transport_s0_of_local_defect_g_zero_all_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hg0 : ∀ t : ℝ, local_defect_g μ u v t = 0) :
    hard_kernel_transport_s0 hdim μ u v hu hv huv := by
  intro r hr0 hr1
  have hgr : local_defect_g μ u v r = 0 := hg0 r
  have hgphi : local_defect_g μ u v ((1 - r) / (1 + r)) = 0 :=
    hg0 ((1 - r) / (1 + r))
  rw [hgr, hgphi]
  simp

private lemma hard_kernel_gap_positive_anchor_s0_of_local_defect_g_zero_all_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (hg0 : ∀ t : ℝ, local_defect_g μ u v t = 0) :
    hard_kernel_gap_positive_anchor_s0 hdim μ u v hu hv huv := by
  intro hker_nz
  have hg_nz : ∃ t : ℝ, local_defect_g μ u v t ≠ 0 :=
    (exists_swapped_bridge_kernel_s0_ne_zero_iff_exists_local_defect_g_ne_zero
      hdim μ u v hu hv huv).1 hker_nz
  rcases hg_nz with ⟨t, ht⟩
  exact False.elim (ht (hg0 t))

private lemma hard_kernel_pair_of_infimum_pair_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (huM : frame_quadratic μ u = sInf (Q_sphere_set μ))
    (hvM : frame_quadratic μ v = sInf (Q_sphere_set μ)) :
    hard_kernel_transport_s0 hdim μ u v hu hv huv
      ∧
    hard_kernel_gap_positive_anchor_s0 hdim μ u v hu hv huv := by
  have hg0 : ∀ t : ℝ, local_defect_g μ u v t = 0 := by
    intro t
    exact local_defect_g_eq_zero_of_infimum_pair hdim μ u v hu hv huv huM hvM t
  constructor
  · exact
      hard_kernel_transport_s0_of_local_defect_g_zero_all_osc
        hdim μ u v hu hv huv hg0
  · exact
      hard_kernel_gap_positive_anchor_s0_of_local_defect_g_zero_all_osc
        hdim μ u v hu hv huv hg0

private lemma hard_kernel_pair_of_infimum_left_and_orthogonal_infimum_witness_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p₀ v₀ x : H)
    (hp₀ : ‖p₀‖ = 1) (hv₀ : ‖v₀‖ = 1) (hx : ‖x‖ = 1)
    (hp₀v₀ : inner (𝕜 := ℂ) p₀ v₀ = 0) (hp₀x : inner (𝕜 := ℂ) p₀ x = 0)
    (hp₀_min : frame_quadratic μ p₀ = sInf (Q_sphere_set μ))
    (hv₀_min :
      ∀ y : H, ‖y‖ = 1 → inner (𝕜 := ℂ) p₀ y = 0 →
        frame_quadratic μ v₀ ≤ frame_quadratic μ y)
    (hx_inf : frame_quadratic μ x = sInf (Q_sphere_set μ)) :
    hard_kernel_transport_s0 hdim μ p₀ v₀ hp₀ hv₀ hp₀v₀
      ∧
    hard_kernel_gap_positive_anchor_s0 hdim μ p₀ v₀ hp₀ hv₀ hp₀v₀ := by
  have hg0 : ∀ s : ℝ, local_defect_g μ p₀ v₀ s = 0 :=
    local_defect_g_zero_all_of_infimum_left_and_orthogonal_infimum_witness
      hdim μ p₀ v₀ x hp₀ hv₀ hx hp₀v₀ hp₀x hp₀_min hv₀_min hx_inf
  constructor
  · exact
      hard_kernel_transport_s0_of_local_defect_g_zero_all_osc
        hdim μ p₀ v₀ hp₀ hv₀ hp₀v₀ hg0
  · exact
      hard_kernel_gap_positive_anchor_s0_of_local_defect_g_zero_all_osc
        hdim μ p₀ v₀ hp₀ hv₀ hp₀v₀ hg0

private lemma hadamard_bridge_error_zero_all_of_infimum_pair_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (huM : frame_quadratic μ u = sInf (Q_sphere_set μ))
    (hvM : frame_quadratic μ v = sInf (Q_sphere_set μ)) :
    ∀ x : ℝ, hadamard_bridge_error μ u v x = 0 := by
  have hk :=
    hard_kernel_pair_of_infimum_pair_osc hdim μ u v hu hv huv huM hvM
  exact
    hadamard_bridge_error_zero_all_of_hard_kernel_s0
      hdim μ u v hu hv huv hk.1 hk.2

private lemma hadamard_bridge_error_zero_all_of_infimum_left_and_orthogonal_infimum_witness_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (p₀ v₀ x : H)
    (hp₀ : ‖p₀‖ = 1) (hv₀ : ‖v₀‖ = 1) (hx : ‖x‖ = 1)
    (hp₀v₀ : inner (𝕜 := ℂ) p₀ v₀ = 0) (hp₀x : inner (𝕜 := ℂ) p₀ x = 0)
    (hp₀_min : frame_quadratic μ p₀ = sInf (Q_sphere_set μ))
    (hv₀_min :
      ∀ y : H, ‖y‖ = 1 → inner (𝕜 := ℂ) p₀ y = 0 →
        frame_quadratic μ v₀ ≤ frame_quadratic μ y)
    (hx_inf : frame_quadratic μ x = sInf (Q_sphere_set μ)) :
    ∀ t : ℝ, hadamard_bridge_error μ p₀ v₀ t = 0 := by
  have hk :=
    hard_kernel_pair_of_infimum_left_and_orthogonal_infimum_witness_osc
      hdim μ p₀ v₀ x hp₀ hv₀ hx hp₀v₀ hp₀x hp₀_min hv₀_min hx_inf
  exact
    hadamard_bridge_error_zero_all_of_hard_kernel_s0
      hdim μ p₀ v₀ hp₀ hv₀ hp₀v₀ hk.1 hk.2

private lemma local_defect_g_eq_zero_of_second_diff_global_nonneg_local_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hE2_nonneg :
      ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
        ∀ s t : ℝ, 0 ≤ hadamard_bridge_error_second_diff μ a b s t)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) : local_defect_g μ u v t = 0 := by
  have hnonneg :
      ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
        ∀ s t : ℝ, 0 ≤ swapped_bridge_kernel μ a b s t := by
    intro a b ha hb hab s t
    have hba : inner (𝕜 := ℂ) b a = 0 := by
      simpa [inner_eq_zero_symm] using hab
    have hE2_nonneg_ba :
        ∀ s t : ℝ, 0 ≤ hadamard_bridge_error_second_diff μ b a s t :=
      hE2_nonneg b a hb ha hba
    exact
      swapped_bridge_kernel_nonneg_of_hadamard_bridge_error_second_diff_nonneg
        hdim μ a b ha hb hab hE2_nonneg_ba s t
  have hvu : inner (𝕜 := ℂ) v u = 0 := by
    simpa [inner_eq_zero_symm] using huv
  have hker0 :
      ∀ s t : ℝ, swapped_bridge_kernel μ v u s t = 0 := by
    intro s t
    exact
      swapped_bridge_kernel_eq_zero_of_global_nonneg
        hdim μ hnonneg v u hv hu hvu s t
  have hsym :
      ∀ s t : ℝ, swapped_bridge_kernel μ v u s t = swapped_bridge_kernel μ v u t s := by
    intro s t
    rw [hker0 s t, hker0 t s]
  exact
    local_defect_g_zero_of_swapped_kernel_symmetry
      hdim μ v u hv hu hvu hsym t

private lemma local_defect_g_zero_all_of_second_diff_global_nonneg_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hE2_nonneg :
      ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
        ∀ s t : ℝ, 0 ≤ hadamard_bridge_error_second_diff μ a b s t) :
    ∀ (a b : H), ‖a‖ = 1 → ‖b‖ = 1 → inner (𝕜 := ℂ) a b = 0 →
      ∀ t : ℝ, local_defect_g μ a b t = 0 := by
  intro a b ha hb hab t
  exact
    local_defect_g_eq_zero_of_second_diff_global_nonneg_local_osc
      hdim μ hE2_nonneg a b ha hb hab t

private lemma frame_quadratic_eq_inf_mul_sq_norm_on_infimum_plane_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (huM : frame_quadratic μ u = sInf (Q_sphere_set μ))
    (hvM : frame_quadratic μ v = sInf (Q_sphere_set μ))
    (a b : ℝ) :
    frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) =
      sInf (Q_sphere_set μ) * (a ^ 2 + b ^ 2) := by
  have hnorm_plus_real : ‖a • u + b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    have hinner : inner (𝕜 := ℂ) (a • u) (b • v) = 0 := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) a u,
        RCLike.real_smul_eq_coe_smul (K := ℂ) b v,
        inner_smul_left, inner_smul_right, huv]
      simp
    have hmul :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := a • u) (y := b • v) hinner
    have hsq :
        ‖a • u + b • v‖ ^ 2 = ‖a • u‖ ^ 2 + ‖b • v‖ ^ 2 := by
      simpa [pow_two] using hmul
    simpa [norm_smul, hu, hv, Real.norm_eq_abs, pow_two, add_comm, add_left_comm, add_assoc] using
      hsq
  have hnorm_minus_real : ‖a • u - b • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    have hinner : inner (𝕜 := ℂ) (a • u) (-(b • v)) = 0 := by
      rw [inner_neg_right, RCLike.real_smul_eq_coe_smul (K := ℂ) a u,
        RCLike.real_smul_eq_coe_smul (K := ℂ) b v,
        inner_smul_left, inner_smul_right, huv]
      simp
    have hmul :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x := a • u) (y := -(b • v)) hinner
    have hsq :
        ‖a • u + -(b • v)‖ ^ 2 = ‖a • u‖ ^ 2 + ‖-(b • v)‖ ^ 2 := by
      simpa [pow_two] using hmul
    simpa [sub_eq_add_neg, norm_smul, hu, hv, Real.norm_eq_abs, pow_two,
      add_comm, add_left_comm, add_assoc] using hsq
  have hnorm_plus : ‖(a : ℂ) • u + (b : ℂ) • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using hnorm_plus_real
  have hnorm_minus : ‖(a : ℂ) • u - (b : ℂ) • v‖ ^ 2 = a ^ 2 + b ^ 2 := by
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using hnorm_minus_real
  have hg0 :
      ∀ s : ℝ, local_defect_g μ u v s = 0 :=
    fun s => local_defect_g_eq_zero_of_infimum_pair hdim μ u v hu hv huv huM hvM s
  have hD0 : local_quad2DDefect μ u v a b = 0 :=
    defect_zero_of_g_zero μ u v hg0 a b
  have hsum :
      frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) +
        frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v) =
          2 * sInf (Q_sphere_set μ) * (a ^ 2 + b ^ 2) := by
    unfold local_quad2DDefect local_quad2DExpr at hD0
    rw [huM, hvM] at hD0
    nlinarith [hD0]
  have hplus_lb :
      sInf (Q_sphere_set μ) * (a ^ 2 + b ^ 2) ≤
        frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) := by
    have hplus_lb0 :=
      frame_quadratic_ge_inf_mul_norm_sq μ ((a : ℂ) • u + (b : ℂ) • v)
    rw [hnorm_plus] at hplus_lb0
    exact hplus_lb0
  have hminus_lb :
      sInf (Q_sphere_set μ) * (a ^ 2 + b ^ 2) ≤
        frame_quadratic (H := H) μ ((a : ℂ) • u - (b : ℂ) • v) := by
    have hminus_lb0 :=
      frame_quadratic_ge_inf_mul_norm_sq μ ((a : ℂ) • u - (b : ℂ) • v)
    rw [hnorm_minus] at hminus_lb0
    exact hminus_lb0
  have hplus_le :
      frame_quadratic (H := H) μ ((a : ℂ) • u + (b : ℂ) • v) ≤
        sInf (Q_sphere_set μ) * (a ^ 2 + b ^ 2) := by
    linarith [hsum, hminus_lb]
  exact le_antisymm hplus_le hplus_lb

private lemma frame_quadratic_eq_zero_on_complex_infimum_plane_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hu0 : frame_quadratic μ u = 0)
    (hv0 : frame_quadratic μ v = 0)
    (hzeroInf : sInf (Q_sphere_set μ) = 0)
    (a b : ℂ) :
    frame_quadratic (H := H) μ (a • u + b • v) = 0 := by
  by_cases ha : a = 0
  · subst ha
    rw [zero_smul, zero_add, frame_quadratic_sq_hom]
    simp [hv0]
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, add_zero, frame_quadratic_sq_hom]
    simp [hu0]
  let pa : ℂ := ((‖a‖ : ℝ) : ℂ)⁻¹ * a
  let pb : ℂ := ((‖b‖ : ℝ) : ℂ)⁻¹ * b
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hnb : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hpa_unit : ‖pa‖ = 1 := by
    calc
      ‖pa‖ = ‖(((‖a‖ : ℝ) : ℂ)⁻¹ * a)‖ := rfl
      _ = ‖(((‖a‖ : ℝ) : ℂ)⁻¹)‖ * ‖a‖ := by rw [norm_mul]
      _ = ‖a‖⁻¹ * ‖a‖ := by simp
      _ = 1 := by field_simp [hna]
  have hpb_unit : ‖pb‖ = 1 := by
    calc
      ‖pb‖ = ‖(((‖b‖ : ℝ) : ℂ)⁻¹ * b)‖ := rfl
      _ = ‖(((‖b‖ : ℝ) : ℂ)⁻¹)‖ * ‖b‖ := by rw [norm_mul]
      _ = ‖b‖⁻¹ * ‖b‖ := by simp
      _ = 1 := by field_simp [hnb]
  have hpa_ne : pa ≠ 0 := by
    intro hpa0
    have : ‖pa‖ = 0 := by simpa [hpa0]
    linarith [hpa_unit]
  let θ : ℂ := pa⁻¹ * pb
  let v' : H := θ • v
  have hθ_unit : ‖θ‖ = 1 := by
    calc
      ‖θ‖ = ‖pa⁻¹ * pb‖ := rfl
      _ = ‖pa⁻¹‖ * ‖pb‖ := by rw [norm_mul]
      _ = ‖pa‖⁻¹ * ‖pb‖ := by simp
      _ = 1 := by simp [hpa_unit, hpb_unit]
  have hv'_norm : ‖v'‖ = 1 := by
    simp [v', norm_smul, hθ_unit, hv]
  have huv' : inner (𝕜 := ℂ) u v' = 0 := by
    simp [v', huv]
  have hv'0 : frame_quadratic (H := H) μ v' = 0 := by
    dsimp [v']
    rw [frame_quadratic_sq_hom]
    simp [hθ_unit, hv0]
  have huM : frame_quadratic μ u = sInf (Q_sphere_set μ) := by simpa [hzeroInf] using hu0
  have hv'M : frame_quadratic μ v' = sInf (Q_sphere_set μ) := by simpa [hzeroInf] using hv'0
  have hreal0 :
      frame_quadratic (H := H) μ
          ((((‖a‖ : ℝ) : ℂ) • u) + (((‖b‖ : ℝ) : ℂ) • v')) = 0 := by
    have hreal :=
      frame_quadratic_eq_inf_mul_sq_norm_on_infimum_plane_osc
        hdim μ u v' hu hv'_norm huv' huM hv'M ‖a‖ ‖b‖
    simpa [hzeroInf] using hreal
  have ha_repr : (((‖a‖ : ℝ) : ℂ) * pa) = a := by
    dsimp [pa]
    field_simp [hna]
  have ha_mul_inv : a * pa⁻¹ = (((‖a‖ : ℝ) : ℂ)) := by
    calc
      a * pa⁻¹ = ((((‖a‖ : ℝ) : ℂ) * pa) * pa⁻¹) := by simpa [ha_repr]
      _ = (((‖a‖ : ℝ) : ℂ)) := by rw [mul_assoc, mul_inv_cancel₀ hpa_ne, mul_one]
  have hb_repr0 : (((‖b‖ : ℝ) : ℂ) * pb) = b := by
    dsimp [pb]
    field_simp [hnb]
  have hb_repr : pa * ((((‖b‖ : ℝ) : ℂ)) * θ) = b := by
    have hpaθ : pa * θ = pb := by
      calc
        ((↑‖a‖ : ℂ)⁻¹ * a) * (pa⁻¹ * pb)
            = (((↑‖a‖ : ℂ)⁻¹ * (a * pa⁻¹)) * pb) := by ring
        _ = (((↑‖a‖ : ℂ)⁻¹ * ((↑‖a‖ : ℂ))) * pb) := by rw [ha_mul_inv]
        _ = pb := by field_simp [hna]
    calc
      pa * ((((‖b‖ : ℝ) : ℂ)) * θ)
          = (((‖b‖ : ℝ) : ℂ) * (pa * θ)) := by ring
      _ = (((‖b‖ : ℝ) : ℂ) * pb) := by rw [hpaθ]
      _ = b := hb_repr0
  let expr : H := (((‖a‖ : ℝ) : ℂ) • u) + (((‖b‖ : ℝ) : ℂ) • v')
  have hexpr :
      pa • expr = a • u + b • v := by
    calc
      pa • expr
          = (pa * (((‖a‖ : ℝ) : ℂ))) • u + (pa * ((((‖b‖ : ℝ) : ℂ) * θ))) • v := by
              change pa • ((((‖a‖ : ℝ) : ℂ) • u) + (((‖b‖ : ℝ) : ℂ) • (θ • v))) =
                (pa * (((‖a‖ : ℝ) : ℂ))) • u + (pa * ((((‖b‖ : ℝ) : ℂ) * θ))) • v
              rw [smul_add, smul_smul, smul_smul, smul_smul]
              simpa [mul_assoc]
      _ = a • u + b • v := by
          rw [show pa * (((‖a‖ : ℝ) : ℂ) ) = a by simpa [mul_comm] using ha_repr]
          rw [hb_repr]
  have hphase :
      frame_quadratic (H := H) μ (pa • expr) =
        frame_quadratic (H := H) μ expr := by
    have h := frame_quadratic_sq_hom (H := H) μ pa expr
    simpa [hpa_unit] using h
  calc
    frame_quadratic (H := H) μ (a • u + b • v)
        = frame_quadratic (H := H) μ (pa • expr) := by rw [hexpr]
    _ = frame_quadratic (H := H) μ expr := hphase
    _ = 0 := hreal0

private lemma exists_zero_orthogonal_to_unit_of_zero_infimum_plane_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v y : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hy : ‖y‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hu0 : frame_quadratic μ u = 0)
    (hv0 : frame_quadratic μ v = 0)
    (hzeroInf : sInf (Q_sphere_set μ) = 0) :
    ∃ z : H, ‖z‖ = 1 ∧ inner (𝕜 := ℂ) z y = 0 ∧ frame_quadratic μ z = 0 := by
  by_cases huyv : inner (𝕜 := ℂ) u y = 0 ∧ inner (𝕜 := ℂ) v y = 0
  · exact ⟨u, hu, huyv.1, hu0⟩
  · let au : ℂ := inner (𝕜 := ℂ) u y
    let av : ℂ := inner (𝕜 := ℂ) v y
    let z0 : H := ((starRingEnd ℂ) av) • u - ((starRingEnd ℂ) au) • v
    have hz0_orth : inner (𝕜 := ℂ) z0 y = 0 := by
      dsimp [z0, au, av]
      rw [inner_sub_left, inner_smul_left, inner_smul_left]
      simp [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
    have hz0_ne : z0 ≠ 0 := by
      intro hz0
      have hvu : inner (𝕜 := ℂ) v u = 0 := by
        simpa [inner_eq_zero_symm] using huv
      have huv0 : inner (𝕜 := ℂ) u z0 = 0 := by simpa [hz0]
      have hvv0 : inner (𝕜 := ℂ) v z0 = 0 := by simpa [hz0]
      have hyv0 : inner (𝕜 := ℂ) y v = 0 := by
        simpa [z0, au, av, hu, huv, inner_sub_right, inner_smul_right,
          inner_self_eq_norm_sq_to_K] using huv0
      have hyu0 : inner (𝕜 := ℂ) y u = 0 := by
        have hyu0' : -(inner (𝕜 := ℂ) y u) = 0 := by
          simpa [z0, au, av, hv, hvu, inner_sub_right, inner_smul_right,
            inner_self_eq_norm_sq_to_K] using hvv0
        simpa using hyu0'
      have hav : inner (𝕜 := ℂ) v y = 0 := by
        simpa [inner_eq_zero_symm] using hyv0
      have hau : inner (𝕜 := ℂ) u y = 0 := by
        simpa [inner_eq_zero_symm] using hyu0
      exact huyv ⟨hau, hav⟩
    let z : H := Gleason.RankOne.normalize (H := H) z0
    have hz : ‖z‖ = 1 := rankOne_normalize_norm_eq_one (H := H) z0 hz0_ne
    have hzy : inner (𝕜 := ℂ) z y = 0 := by
      dsimp [z, Gleason.RankOne.normalize]
      simp [hz0_orth]
    have hz0_val : frame_quadratic μ z0 = 0 := by
      simpa [z0, sub_eq_add_neg] using
        frame_quadratic_eq_zero_on_complex_infimum_plane_osc
          hdim μ u v hu hv huv hu0 hv0 hzeroInf ((starRingEnd ℂ) av) (-((starRingEnd ℂ) au))
    have hz_val : frame_quadratic μ z = 0 := by
      dsimp [z, Gleason.RankOne.normalize]
      rw [frame_quadratic_sq_hom]
      simp [hz0_val]
    exact ⟨z, hz, hzy, hz_val⟩

private lemma local_defect_g_zero_all_of_zero_infimum_pair_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hu0 : frame_quadratic μ u = 0)
    (hv0 : frame_quadratic μ v = 0)
    (hzeroInf : sInf (Q_sphere_set μ) = 0) :
    ∀ s : ℝ, local_defect_g μ u v s = 0 := by
  have huM : frame_quadratic μ u = sInf (Q_sphere_set μ) := by
    simpa [hzeroInf] using hu0
  have hvM : frame_quadratic μ v = sInf (Q_sphere_set μ) := by
    simpa [hzeroInf] using hv0
  intro s
  exact local_defect_g_eq_zero_of_infimum_pair hdim μ u v hu hv huv huM hvM s

private lemma exists_zero_infimum_pair_with_first_orthogonal_to_unit_of_zero_infimum_plane_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v y : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hy : ‖y‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hu0 : frame_quadratic μ u = 0)
    (hv0 : frame_quadratic μ v = 0)
    (hzeroInf : sInf (Q_sphere_set μ) = 0) :
    ∃ z w : H,
      ‖z‖ = 1 ∧
      ‖w‖ = 1 ∧
      inner (𝕜 := ℂ) z y = 0 ∧
      inner (𝕜 := ℂ) z w = 0 ∧
      frame_quadratic μ z = 0 ∧
      frame_quadratic μ w = 0 := by
  rcases
      exists_zero_orthogonal_to_unit_of_zero_infimum_plane_osc
        hdim μ u v y hu hv hy huv hu0 hv0 hzeroInf with
    ⟨z, hz, hzy, hz0⟩
  rcases
      exists_zero_orthogonal_to_unit_of_zero_infimum_plane_osc
        hdim μ u v z hu hv hz huv hu0 hv0 hzeroInf with
    ⟨w, hw, hwz, hw0⟩
  refine ⟨z, w, hz, hw, hzy, ?_, hz0, hw0⟩
  simpa [inner_eq_zero_symm] using hwz

private lemma exists_zero_infimum_pair_with_first_orthogonal_to_unit_and_g_zero_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v y : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hy : ‖y‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hu0 : frame_quadratic μ u = 0)
    (hv0 : frame_quadratic μ v = 0)
    (hzeroInf : sInf (Q_sphere_set μ) = 0) :
    ∃ z w : H,
      ‖z‖ = 1 ∧
      ‖w‖ = 1 ∧
      inner (𝕜 := ℂ) z y = 0 ∧
      inner (𝕜 := ℂ) z w = 0 ∧
      frame_quadratic μ z = 0 ∧
      frame_quadratic μ w = 0 ∧
      (∀ s : ℝ, local_defect_g μ z w s = 0) := by
  rcases
      exists_zero_infimum_pair_with_first_orthogonal_to_unit_of_zero_infimum_plane_osc
        hdim μ u v y hu hv hy huv hu0 hv0 hzeroInf with
    ⟨z, w, hz, hw, hzy, hzw, hz0, hw0⟩
  refine ⟨z, w, hz, hw, hzy, hzw, hz0, hw0, ?_⟩
  exact
    local_defect_g_zero_all_of_zero_infimum_pair_osc
      hdim μ z w hz hw hzw hz0 hw0 hzeroInf

private lemma exists_zero_infimum_pair_with_first_orthogonal_to_unit_and_hard_kernel_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v y : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hy : ‖y‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hu0 : frame_quadratic μ u = 0)
    (hv0 : frame_quadratic μ v = 0)
    (hzeroInf : sInf (Q_sphere_set μ) = 0) :
    ∃ z w : H, ∃ hz : ‖z‖ = 1, ∃ hw : ‖w‖ = 1,
      ∃ hzy : inner (𝕜 := ℂ) z y = 0, ∃ hzw : inner (𝕜 := ℂ) z w = 0,
      ∃ hz0 : frame_quadratic μ z = 0, ∃ hw0 : frame_quadratic μ w = 0,
        hard_kernel_transport_s0 hdim μ z w hz hw hzw ∧
        hard_kernel_gap_positive_anchor_s0 hdim μ z w hz hw hzw := by
  rcases
      exists_zero_infimum_pair_with_first_orthogonal_to_unit_of_zero_infimum_plane_osc
        hdim μ u v y hu hv hy huv hu0 hv0 hzeroInf with
    ⟨z, w, hz, hw, hzy, hzw, hz0, hw0⟩
  have hzM : frame_quadratic μ z = sInf (Q_sphere_set μ) := by
    simpa [hzeroInf] using hz0
  have hwM : frame_quadratic μ w = sInf (Q_sphere_set μ) := by
    simpa [hzeroInf] using hw0
  have hk :=
    hard_kernel_pair_of_infimum_pair_osc hdim μ z w hz hw hzw hzM hwM
  exact ⟨z, w, hz, hw, hzy, hzw, hz0, hw0, hk.1, hk.2⟩

private lemma local_defect_g_eq_zero_of_cross_plane_components_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v w : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0) (huw : inner (𝕜 := ℂ) u w = 0)
    (hvw : inner (𝕜 := ℂ) v w = 0)
    (s c : ℝ) (hc : c ^ 2 = 1 + s ^ 2)
    (huw_zero : local_defect_g μ u w c = 0)
    (hplus_zero : local_defect_g μ (u + (c : ℂ) • w) v s = 0)
    (hminus_zero : local_defect_g μ (u - (c : ℂ) • w) v s = 0) :
    local_defect_g μ u v s = 0 := by
  have htransfer :=
    cross_plane_transfer_g hdim μ u v w hu hv hw huv huw hvw s c hc
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  apply mul_left_cancel₀ htwo
  linarith [htransfer, huw_zero, hplus_zero, hminus_zero]

private lemma local_defect_g_real_smul_left_osc
    (μ : FrameFunction H)
    (u v : H) (r s : ℝ)
    (hr : r ≠ 0) :
    local_defect_g μ ((r : ℂ) • u) v s =
      r ^ 2 * local_defect_g μ u v (s / r) := by
  have hExpr :
      local_quad2DExpr μ ((r : ℂ) • u) v 1 s =
        local_quad2DExpr μ u v r s := by
    unfold local_quad2DExpr
    simp [smul_add, smul_sub, smul_smul, mul_comm, mul_left_comm, mul_assoc]
  have hQu :
      frame_quadratic (H := H) μ ((r : ℂ) • u) =
        r ^ 2 * frame_quadratic (H := H) μ u := by
    simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      (frame_quadratic_sq_hom (H := H) μ (r : ℂ) u)
  calc
    local_defect_g μ ((r : ℂ) • u) v s
        = local_quad2DDefect μ u v r s := by
            unfold local_defect_g local_quad2DDefect
            rw [hExpr, hQu]
            ring
    _ = r ^ 2 * local_defect_g μ u v (s / r) := by
      simpa [local_defect_g] using
        (local_quad2DDefect_ratio_reduction (μ := μ) (u := u) (v := v) (a := r) (b := s) hr)

private lemma local_defect_g_eq_zero_of_normed_left_osc
    (μ : FrameFunction H)
    (x v u : H) (c s : ℝ)
    (hc : 0 < c)
    (hx : x = ((c : ℂ) • u))
    (hzero : local_defect_g μ u v (s / c) = 0) :
    local_defect_g μ x v s = 0 := by
  rw [hx, local_defect_g_real_smul_left_osc (μ := μ) (u := u) (v := v) (r := c) (s := s)
    (by linarith : c ≠ 0)]
  simp [hzero]

private lemma local_defect_g_eq_zero_of_exists_cross_plane_components_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (s c : ℝ) (hc : c ^ 2 = 1 + s ^ 2)
    (hcomponents :
      ∀ w : H, ‖w‖ = 1 → inner (𝕜 := ℂ) u w = 0 → inner (𝕜 := ℂ) v w = 0 →
        local_defect_g μ u w c = 0
          ∧ local_defect_g μ (u + (c : ℂ) • w) v s = 0
          ∧ local_defect_g μ (u - (c : ℂ) • w) v s = 0) :
    local_defect_g μ u v s = 0 := by
  rcases exists_unit_orthogonal_to_pair (H := H) hdim u v with ⟨w, hw, huw, hvw⟩
  rcases hcomponents w hw huw hvw with ⟨huw_zero, hplus_zero, hminus_zero⟩
  exact
    local_defect_g_eq_zero_of_cross_plane_components_osc
      hdim μ u v w hu hv hw huv huw hvw s c hc huw_zero hplus_zero hminus_zero

private lemma local_defect_g_eq_zero_of_shiftedNormalized_zero_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) ≠ 0)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ)
    (hzero :
      local_defect_g
        (shiftedNormalizedFrameFunction (H := H) hdim μ hden) u v t = 0) :
    local_defect_g μ u v t = 0 := by
  have hshift :=
    local_defect_g_shiftedNormalizedFrameFunction
      (H := H) hdim μ hden u v hu hv huv t
  rw [hshift] at hzero
  field_simp [hden] at hzero
  simpa using hzero

private lemma local_defect_g_eq_zero_of_exists_shiftedNormalized_cross_plane_components_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden :
      1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) ≠ 0)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (s c : ℝ) (hc : c ^ 2 = 1 + s ^ 2)
    (hcomponents :
      ∀ w : H, ‖w‖ = 1 → inner (𝕜 := ℂ) u w = 0 → inner (𝕜 := ℂ) v w = 0 →
        local_defect_g
            (shiftedNormalizedFrameFunction (H := H) hdim μ hden) u w c = 0
          ∧ local_defect_g
              (shiftedNormalizedFrameFunction (H := H) hdim μ hden)
              (u + (c : ℂ) • w) v s = 0
          ∧ local_defect_g
              (shiftedNormalizedFrameFunction (H := H) hdim μ hden)
              (u - (c : ℂ) • w) v s = 0) :
    local_defect_g μ u v s = 0 := by
  let ν := shiftedNormalizedFrameFunction (H := H) hdim μ hden
  have hν0 :
      local_defect_g ν u v s = 0 :=
    local_defect_g_eq_zero_of_exists_cross_plane_components_osc
      hdim ν u v hu hv huv s c hc hcomponents
  exact
    local_defect_g_eq_zero_of_shiftedNormalized_zero_osc
      (H := H) hdim μ hden u v hu hv huv s hν0

private lemma spherePointCoord_equatorSpherePoint
    (θ : ℝ) :
    spherePointCoord (equatorSpherePoint θ) =
      (Real.cos θ, (Real.sin θ, 0)) := by
  apply Prod.ext
  · simp [spherePointCoord, equatorSpherePoint, WithLp.toLp_fst, WithLp.toLp_snd]
    exact (congrArg Complex.re (Complex.ofReal_cos θ)).symm
  · apply Prod.ext
    · simp [spherePointCoord, equatorSpherePoint, WithLp.toLp_fst, WithLp.toLp_snd]
      exact (congrArg Complex.re (Complex.ofReal_sin θ)).symm
    · simp [spherePointCoord, equatorSpherePoint, WithLp.toLp_fst, WithLp.toLp_snd]

private theorem coordSphereFrameFun_mem_sphereFrameSubmodule_osc
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0) :
    coordSphereFrameFun μ u v p ∈ sphereFrameSubmodule := by
  intro x y z hxy hxz hyz
  let xH : H := coordPoint u v p (spherePointCoord x)
  let yH : H := coordPoint u v p (spherePointCoord y)
  let zH : H := coordPoint u v p (spherePointCoord z)
  let K : Submodule ℂ H := Submodule.span ℂ ({u, v, p} : Set H)
  let S : Submodule ℂ H := Submodule.span ℂ ({xH, yH, zH} : Set H)
  have huvp_on : Orthonormal ℂ (uvpVec u v p) :=
    uvpVec_orthonormal hu hv hp huv hup hvp
  have hxyz_on : Orthonormal ℂ (coordSphereVec u v p x y z) :=
    coordSphereVec_orthonormal hu hv hp huv hup hvp x y z hxy hxz hyz
  have hKfin : Module.finrank ℂ K = 3 := by
    dsimp [K]
    rw [← span_range_uvpVec u v p]
    simpa using finrank_span_eq_card huvp_on.linearIndependent
  have hSfin : Module.finrank ℂ S = 3 := by
    dsimp [S, xH, yH, zH]
    rw [← span_range_coordSphereVec u v p x y z]
    simpa using finrank_span_eq_card hxyz_on.linearIndependent
  have hSle : S ≤ K := by
    have hsubset : ({xH, yH, zH} : Set H) ⊆ K := by
      intro q hq
      simp at hq
      rcases hq with rfl | rfl | rfl
      · dsimp [xH, K]
        exact coordPoint_mem_span u v p (spherePointCoord x)
      · dsimp [yH, K]
        exact coordPoint_mem_span u v p (spherePointCoord y)
      · dsimp [zH, K]
        exact coordPoint_mem_span u v p (spherePointCoord z)
    dsimp [S]
    exact Submodule.span_le.mpr hsubset
  have hSK : S = K := by
    apply Submodule.eq_of_le_of_finrank_le hSle
    simp [hKfin, hSfin]
  have hxH_norm : ‖xH‖ = 1 := by
    dsimp [xH]
    exact coordPoint_norm hu hv hp huv hup hvp (spherePointCoord_sq_sum x)
  have hyH_norm : ‖yH‖ = 1 := by
    dsimp [yH]
    exact coordPoint_norm hu hv hp huv hup hvp (spherePointCoord_sq_sum y)
  have hzH_norm : ‖zH‖ = 1 := by
    dsimp [zH]
    exact coordPoint_norm hu hv hp huv hup hvp (spherePointCoord_sq_sum z)
  have hxyH : inner (𝕜 := ℂ) xH yH = 0 := by
    dsimp [xH, yH]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    simp [coordDot_spherePointCoord, hxy]
  have hxzH : inner (𝕜 := ℂ) xH zH = 0 := by
    dsimp [xH, zH]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    simp [coordDot_spherePointCoord, hxz]
  have hyzH : inner (𝕜 := ℂ) yH zH = 0 := by
    dsimp [yH, zH]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    simp [coordDot_spherePointCoord, hyz]
  have hsum_xyz :
      frame_quadratic μ xH + frame_quadratic μ yH + frame_quadratic μ zH =
        μ.μ (GleasonRankOne.projectionOntoSpan (H := H) ({xH, yH, zH} : Set H)) :=
    GleasonRankOne.three_vector_sum (H := H) μ xH yH zH
      hxH_norm hyH_norm hzH_norm hxyH hxzH hyzH
  have hsum_uvp :
      frame_quadratic μ u + frame_quadratic μ v + frame_quadratic μ p =
        μ.μ (GleasonRankOne.projectionOntoSpan (H := H) ({u, v, p} : Set H)) :=
    GleasonRankOne.three_vector_sum (H := H) μ u v p hu hv hp huv hup hvp
  have hproj :
      GleasonRankOne.projectionOntoSpan (H := H) ({xH, yH, zH} : Set H) =
        GleasonRankOne.projectionOntoSpan (H := H) ({u, v, p} : Set H) := by
    dsimp [S, K] at hSK
    simpa [GleasonRankOne.projectionOntoSpan] using
      congrArg (GleasonRankOne.projectionOntoSubmodule (H := H)) hSK
  have hsum :
      frame_quadratic μ xH + frame_quadratic μ yH + frame_quadratic μ zH =
        frame_quadratic μ u + frame_quadratic μ v + frame_quadratic μ p := by
    rw [hsum_xyz, hsum_uvp, hproj]
  simpa [coordSphereFrameFun, xH, yH, zH, coordPoint_base, coordPoint_vCoord,
    coordPoint_poleCoord, spherePointCoord_sphereE1, spherePointCoord_sphereE2,
    spherePointCoord_sphereE3] using hsum

private theorem sphereFrameSubmodule_eq_sup_zero_two_of_sector_decomposition_noindep_osc
    {s : Set ℕ}
    (hF : sphereFrameSubmodule = ⨆ i : s, harmonicSphereDegreeSubmodule i) :
    sphereFrameSubmodule =
      harmonicSphereDegreeSubmodule 0 ⊔
        harmonicSphereDegreeSubmodule 2 := by
  have hs_subset : s ⊆ ({0, 2} : Set ℕ) := by
    intro n hn
    have hQn : harmonicSphereDegreeSubmodule n ≤ sphereFrameSubmodule := by
      rw [hF]
      exact le_iSup (fun i : s => harmonicSphereDegreeSubmodule i) ⟨n, hn⟩
    cases n with
    | zero =>
        simp
    | succ n =>
        cases n with
        | zero =>
            exact
              (not_harmonicSphereDegreeSubmodule_one_le_sphereFrameSubmodule hQn).elim
        | succ n' =>
            cases n' with
            | zero =>
                simp
            | succ n'' =>
                have hgt : 2 < Nat.succ (Nat.succ (Nat.succ n'')) := by omega
                exact
                  (not_harmonicSphereDegreeSubmodule_gt_two_le_sphereFrameSubmodule hgt hQn).elim
  have hs0 : 0 ∈ s := by
    by_contra h0
    have hFle : sphereFrameSubmodule ≤ harmonicSphereDegreeSubmodule 2 := by
      rw [hF]
      refine iSup_le ?_
      intro i
      have hi02 : (i : ℕ) = 0 ∨ (i : ℕ) = 2 := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hs_subset i.2
      rcases hi02 with hi | hi
      · exact False.elim (h0 (hi ▸ i.2))
      · simpa [hi]
    have h02 : harmonicSphereDegreeSubmodule 0 ≤ harmonicSphereDegreeSubmodule 2 :=
      harmonicSphereDegreeSubmodule_zero_le_sphereFrameSubmodule.trans hFle
    have hnot02 : ¬ harmonicSphereDegreeSubmodule 0 ≤ harmonicSphereDegreeSubmodule 2 := by
      intro hle
      exact continuousHarmonicSphereDegreeSubmodule_zero_not_le_two <| by
        intro g hg
        exact hle hg
    exact hnot02 h02
  have hs2 : 2 ∈ s := by
    by_contra h2
    have hFle : sphereFrameSubmodule ≤ harmonicSphereDegreeSubmodule 0 := by
      rw [hF]
      refine iSup_le ?_
      intro i
      have hi02 : (i : ℕ) = 0 ∨ (i : ℕ) = 2 := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hs_subset i.2
      rcases hi02 with hi | hi
      · simpa [hi]
      · exact False.elim (h2 (hi ▸ i.2))
    have h20 : harmonicSphereDegreeSubmodule 2 ≤ harmonicSphereDegreeSubmodule 0 :=
      harmonicSphereDegreeSubmodule_two_le_sphereFrameSubmodule.trans hFle
    have hnot20 : ¬ harmonicSphereDegreeSubmodule 2 ≤ harmonicSphereDegreeSubmodule 0 := by
      intro hle
      exact continuousHarmonicSphereDegreeSubmodule_two_not_le_zero <| by
        intro g hg
        exact hle hg
    exact hnot20 h20
  have hs_eq : s = ({0, 2} : Set ℕ) := by
    ext n
    constructor
    · intro hn
      exact hs_subset hn
    · intro hn
      rcases hn with rfl | rfl
      · exact hs0
      · exact hs2
  rw [hF, hs_eq]
  refine le_antisymm ?_ ?_
  · refine iSup_le ?_
    rintro ⟨i, hi⟩
    rcases hi with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · rw [sup_le_iff]
    constructor
    · exact le_iSup (fun i : ({0, 2} : Set ℕ) => harmonicSphereDegreeSubmodule i)
        ⟨0, by simp⟩
    · exact le_iSup (fun i : ({0, 2} : Set ℕ) => harmonicSphereDegreeSubmodule i)
        ⟨2, by simp⟩

private theorem sphereFrameSubmodule_le_sphereQuadraticSubmodule_of_decomposition_noindep_osc
    {s : Set ℕ}
    (hF : sphereFrameSubmodule = ⨆ i : s, harmonicSphereDegreeSubmodule i) :
    sphereFrameSubmodule ≤ sphereQuadraticSubmodule := by
  apply eq_sup_zero_two_imp_le_sphereQuadraticSubmodule
  exact sphereFrameSubmodule_eq_sup_zero_two_of_sector_decomposition_noindep_osc hF

private lemma coordSphereFrameContinuousMap_mem_continuousSphereGreatCirclePointConstraintSubmodule_of_zero_at_p
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0) :
    coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
      continuousSphereGreatCirclePointConstraintSubmodule := by
  rw [continuousSphereGreatCirclePointConstraintSubmodule_eq_continuousSphereFrameSubmodule]
  exact
    coordSphereFrameContinuousMap_mem_continuousSphereFrameSubmodule_of_zero_at_p
      hdim μ hu hv hp huv hup hvp hp0

private lemma coordSphere_pairSum_eq_of_same_pole_of_zero_at_p
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (x y x' y' z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (hxy' : inner (𝕜 := ℝ) x'.1 y'.1 = 0)
    (hxz' : inner (𝕜 := ℝ) x'.1 z.1 = 0)
    (hyz' : inner (𝕜 := ℝ) y'.1 z.1 = 0) :
    frame_quadratic (H := H) μ (coordPoint u v p (spherePointCoord x)) +
        frame_quadratic (H := H) μ (coordPoint u v p (spherePointCoord y)) =
      frame_quadratic (H := H) μ (coordPoint u v p (spherePointCoord x')) +
        frame_quadratic (H := H) μ (coordPoint u v p (spherePointCoord y')) := by
  have hmem :
      coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
        continuousSphereGreatCirclePointConstraintSubmodule :=
    coordSphereFrameContinuousMap_mem_continuousSphereGreatCirclePointConstraintSubmodule_of_zero_at_p
      (H := H) hdim μ hu hv hp huv hup hvp hp0
  have hsum :=
    pairSum_eq_of_same_pole_of_mem_continuousSphereGreatCirclePointConstraintSubmodule
      hmem x y x' y' z hxy hxz hyz hxy' hxz' hyz'
  simpa [coordSphereFrameContinuousMap, coordSphereFrameFun] using hsum

private lemma greatCircleRestriction_eq_of_coordSphere_quadraticMap
    (μ : FrameFunction H) (u v p : H)
    {Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ}
    (hQ : ∀ x : spherePoint3, coordSphereFrameFun μ u v p x = Q x.1)
    (θ : ℝ) :
    greatCircleRestriction μ u v θ = Q (equatorSpherePoint θ).1 := by
  calc
    greatCircleRestriction μ u v θ
      = coordSphereFrameFun μ u v p (equatorSpherePoint θ) := by
          simp [greatCircleRestriction, coordSphereFrameFun, spherePointCoord_equatorSpherePoint,
            coordPoint, realFramePoint, add_assoc]
    _ = Q (equatorSpherePoint θ).1 := hQ _

private lemma quadraticMap_add_sub_eq
    (Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ)
    (x y : WithLp 2 (ℂ × ℝ)) :
    Q (x + y) + Q (x - y) = 2 * Q x + 2 * Q y := by
  obtain ⟨B, hB⟩ := Q.exists_companion
  have hBneg : B x (-y) = -B x y := by
    simpa using (LinearMap.map_neg (B x) y)
  calc
    Q (x + y) + Q (x - y)
      = (Q x + Q y + B x y) + (Q x + Q (-y) + B x (-y)) := by
          rw [sub_eq_add_neg, hB x y, hB x (-y)]
    _ = (Q x + Q y + B x y) + (Q x + Q y - B x y) := by
          rw [Q.map_neg, hBneg]
          simp [sub_eq_add_neg]
    _ = (Q x + Q y) + (Q x + Q y) + (B x y + -B x y) := by
          abel_nf
    _ = (Q x + Q y) + (Q x + Q y) := by
          simp
    _ = 2 * Q x + 2 * Q y := by
          ring

private lemma local_defect_g_eq_zero_of_coordSphere_quadraticMap
    (μ : FrameFunction H) (u v p : H)
    {Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ}
    (hQ : ∀ x : spherePoint3, coordSphereFrameFun μ u v p x = Q x.1)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  let r : ℝ := Real.sqrt (1 + t ^ 2)
  have hr_sq : r ^ 2 = 1 + t ^ 2 := by
    dsimp [r]
    rw [Real.sq_sqrt]
    positivity
  have hr_pos : 0 < r := by
    dsimp [r]
    apply Real.sqrt_pos.2
    positivity
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hcos : r * Real.cos (Real.arctan t) = 1 := by
    dsimp [r]
    rw [Real.cos_arctan]
    field_simp [hr_ne]
  have hsin : r * Real.sin (Real.arctan t) = t := by
    dsimp [r]
    rw [Real.sin_arctan]
    field_simp [hr_ne]
  have hplus_vec :
      r • (equatorSpherePoint (Real.arctan t)).1 = sphereE1.1 + t • sphereE2.1 := by
    rw [equatorSpherePoint_val_eq_combo, smul_add, smul_smul, smul_smul, hcos, hsin]
    simp
  have hminus_vec :
      r • (equatorSpherePoint (-Real.arctan t)).1 = sphereE1.1 - t • sphereE2.1 := by
    rw [equatorSpherePoint_val_eq_combo, Real.cos_neg, Real.sin_neg, smul_add, smul_smul, smul_smul]
    have hsin_neg : r * (-Real.sin (Real.arctan t)) = -t := by
      linarith
    rw [hcos, hsin_neg]
    simp [sub_eq_add_neg]
  have hu :
      frame_quadratic (H := H) μ u = Q sphereE1.1 := by
    simpa [coordSphereFrameFun, coordPoint_base] using hQ sphereE1
  have hv :
      frame_quadratic (H := H) μ v = Q sphereE2.1 := by
    simpa [coordSphereFrameFun, coordPoint_vCoord] using hQ sphereE2
  have hgc :
      greatCircleRestriction μ u v (Real.arctan t) =
        Q (equatorSpherePoint (Real.arctan t)).1 :=
    greatCircleRestriction_eq_of_coordSphere_quadraticMap
      (μ := μ) (u := u) (v := v) (p := p) hQ (Real.arctan t)
  have hgc_neg :
      greatCircleRestriction μ u v (-Real.arctan t) =
        Q (equatorSpherePoint (-Real.arctan t)).1 :=
    greatCircleRestriction_eq_of_coordSphere_quadraticMap
      (μ := μ) (u := u) (v := v) (p := p) hQ (-Real.arctan t)
  have hplus :
      frame_quadratic (H := H) μ (u + (t : ℂ) • v) =
        Q (sphereE1.1 + t • sphereE2.1) := by
    rw [frame_quadratic_add_real_smul_eq_scaled_greatCircleRestriction, hgc]
    have hscale :
        Q (r • (equatorSpherePoint (Real.arctan t)).1) =
          (1 + t ^ 2) * Q (equatorSpherePoint (Real.arctan t)).1 := by
      calc
        Q (r • (equatorSpherePoint (Real.arctan t)).1)
            = r ^ 2 * Q (equatorSpherePoint (Real.arctan t)).1 := by
                simpa [pow_two, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
                  (Q.map_smul r (equatorSpherePoint (Real.arctan t)).1)
        _ = (1 + t ^ 2) * Q (equatorSpherePoint (Real.arctan t)).1 := by
              rw [hr_sq]
    rw [← hscale, hplus_vec]
  have hminus :
      frame_quadratic (H := H) μ (u - (t : ℂ) • v) =
        Q (sphereE1.1 - t • sphereE2.1) := by
    rw [frame_quadratic_sub_real_smul_eq_scaled_greatCircleRestriction, hgc_neg]
    have hscale :
        Q (r • (equatorSpherePoint (-Real.arctan t)).1) =
          (1 + t ^ 2) * Q (equatorSpherePoint (-Real.arctan t)).1 := by
      calc
        Q (r • (equatorSpherePoint (-Real.arctan t)).1)
            = r ^ 2 * Q (equatorSpherePoint (-Real.arctan t)).1 := by
                simpa [pow_two, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
                  (Q.map_smul r (equatorSpherePoint (-Real.arctan t)).1)
        _ = (1 + t ^ 2) * Q (equatorSpherePoint (-Real.arctan t)).1 := by
              rw [hr_sq]
    rw [← hscale, hminus_vec]
  have htv :
      Q (t • sphereE2.1) = t ^ 2 * Q sphereE2.1 := by
    simpa [pow_two, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      (Q.map_smul t sphereE2.1)
  have hpar :
      Q (sphereE1.1 + t • sphereE2.1) + Q (sphereE1.1 - t • sphereE2.1) =
        2 * Q sphereE1.1 + 2 * Q (t • sphereE2.1) :=
    quadraticMap_add_sub_eq Q sphereE1.1 (t • sphereE2.1)
  have hplus' :
      frame_quadratic (H := H) μ ((1 : ℂ) • u + (t : ℂ) • v) =
        Q (sphereE1.1 + t • sphereE2.1) := by
    simpa using hplus
  have hminus' :
      frame_quadratic (H := H) μ ((1 : ℂ) • u - (t : ℂ) • v) =
        Q (sphereE1.1 - t • sphereE2.1) := by
    simpa using hminus
  unfold local_defect_g local_quad2DDefect local_quad2DExpr
  change
    frame_quadratic (H := H) μ ((1 : ℂ) • u + (t : ℂ) • v) +
        frame_quadratic (H := H) μ ((1 : ℂ) • u - (t : ℂ) • v) -
        (2 * 1 ^ 2 * frame_quadratic (H := H) μ u +
          2 * t ^ 2 * frame_quadratic (H := H) μ v) =
      0
  rw [hplus', hminus', hu, hv]
  linarith

private lemma local_defect_g_eq_zero_of_coordSphere_quadratic_submodule_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (hq :
      coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
        continuousSphereQuadraticSubmodule)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  rcases hq with ⟨Q, hQ⟩
  exact
    local_defect_g_eq_zero_of_coordSphere_quadraticMap
      (μ := μ) (u := u) (v := v) (p := p)
      (Q := Q)
      (by
        intro x
        simpa [coordSphereFrameContinuousMap] using hQ x)
      t

private lemma norm_inv_smul_mem_spherePoint3_osc
    {x : WithLp 2 (ℂ × ℝ)} (hx : x ≠ 0) :
    ‖‖x‖⁻¹ • x‖ = 1 := by
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
  field_simp [hnx]

private lemma quadraticMap_eq_frame_quadratic_everywhere_of_coordSphere_quadraticMap_osc
    (μ : FrameFunction H) (u v p : H)
    {Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ}
    (hQ : ∀ x : spherePoint3, coordSphereFrameFun μ u v p x = Q x.1) :
    ∀ x : WithLp 2 (ℂ × ℝ),
      Q x =
        frame_quadratic (H := H) μ
          (coordPoint u v p (x.fst.re, (x.fst.im, x.snd))) := by
  intro x
  by_cases hx : x = 0
  · subst hx
    simp [coordPoint, frame_quadratic_zero]
  · let y : spherePoint3 := ⟨‖x‖⁻¹ • x, norm_inv_smul_mem_spherePoint3_osc hx⟩
    have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hx_eq : x = ‖x‖ • y.1 := by
      change x = ‖x‖ • (‖x‖⁻¹ • x)
      rw [smul_smul]
      field_simp [hnx]
      simp
    have hQy :
        Q y.1 =
          frame_quadratic (H := H) μ
            (coordPoint u v p (spherePointCoord y)) := by
      simpa [coordSphereFrameFun] using (hQ y).symm
    have hcoord :
        coordPoint u v p (spherePointCoord y) =
          ((((‖x‖⁻¹ : ℝ) : ℂ)) •
            coordPoint u v p (x.fst.re, (x.fst.im, x.snd))) := by
      change
        ((((‖x‖⁻¹ • x).fst.re : ℝ) : ℂ) • u +
            (((((‖x‖⁻¹ • x).fst.im : ℝ) : ℂ) • v) +
              ((((‖x‖⁻¹ • x).snd : ℝ) : ℂ) • p))) =
          ((((‖x‖⁻¹ : ℝ) : ℂ)) •
            (((x.fst.re : ℂ) • u) + (((x.fst.im : ℂ) • v) + ((x.snd : ℂ) • p))))
      rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul]
      simp [coordPoint, y, mul_assoc, mul_comm, mul_left_comm]
    have hQx : Q x = ‖x‖ ^ 2 * Q y.1 := by
      have htmp := Q.map_smul ‖x‖ y.1
      rw [← hx_eq] at htmp
      simpa [pow_two, mul_assoc] using htmp
    have hnorm_inv :
        ‖((‖x‖⁻¹ : ℝ) : ℂ)‖ ^ 2 = (‖x‖ ^ 2)⁻¹ := by
      have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [Complex.norm_real, Real.norm_eq_abs]
      simp [abs_of_pos (inv_pos.mpr hpos), pow_two]
    calc
      Q x = ‖x‖ ^ 2 * Q y.1 := hQx
      _ = ‖x‖ ^ 2 *
            frame_quadratic (H := H) μ
              (coordPoint u v p (spherePointCoord y)) := by rw [hQy]
      _ = ‖x‖ ^ 2 *
            frame_quadratic (H := H) μ
              ((((‖x‖⁻¹ : ℝ) : ℂ)) •
                coordPoint u v p (x.fst.re, (x.fst.im, x.snd))) := by rw [hcoord]
      _ = ‖x‖ ^ 2 *
            (‖((‖x‖⁻¹ : ℝ) : ℂ)‖ ^ 2 *
              frame_quadratic (H := H) μ
                (coordPoint u v p (x.fst.re, (x.fst.im, x.snd)))) := by
              rw [frame_quadratic_sq_hom]
      _ = frame_quadratic (H := H) μ
            (coordPoint u v p (x.fst.re, (x.fst.im, x.snd))) := by
            rw [hnorm_inv]
            field_simp [pow_ne_zero 2 hnx]

private lemma quadraticMap_nonneg_everywhere_of_coordSphere_quadraticMap_osc
    (μ : FrameFunction H) (u v p : H)
    {Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ}
    (hQ : ∀ x : spherePoint3, coordSphereFrameFun μ u v p x = Q x.1) :
    ∀ x : WithLp 2 (ℂ × ℝ), 0 ≤ Q x := by
  intro x
  rw [quadraticMap_eq_frame_quadratic_everywhere_of_coordSphere_quadraticMap_osc
    (H := H) μ u v p hQ x]
  exact frame_quadratic_nonneg (H := H) μ _

private lemma frame_quadratic_real_line_eq_sq_mul_of_coordSphere_quadratic_submodule_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u w p : H}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hp : ‖p‖ = 1)
    (huw : inner (𝕜 := ℂ) u w = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hwp : inner (𝕜 := ℂ) w p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (hq :
      coordSphereFrameContinuousMap hdim μ u w p hu hw hp huw hup hwp hp0 ∈
        continuousSphereQuadraticSubmodule)
    (r s : ℝ) :
    frame_quadratic (H := H) μ (((r : ℂ) • p) + ((s : ℂ) • u)) =
      s ^ 2 * frame_quadratic (H := H) μ u := by
  rcases hq with ⟨Q, hQ⟩
  have hQall :=
    quadraticMap_eq_frame_quadratic_everywhere_of_coordSphere_quadraticMap_osc
      (H := H) μ u w p
      (fun x => by simpa [coordSphereFrameContinuousMap] using hQ x)
  have hQnn :=
    quadraticMap_nonneg_everywhere_of_coordSphere_quadraticMap_osc
      (H := H) μ u w p
      (fun x => by simpa [coordSphereFrameContinuousMap] using hQ x)
  have hQe1 :
      Q sphereE1.1 = frame_quadratic (H := H) μ u := by
    simpa [sphereE1, coordPoint, coordBase] using hQall sphereE1.1
  have hQe3 :
      Q sphereE3.1 = 0 := by
    simpa [sphereE3, coordPoint, poleCoord, hp0] using hQall sphereE3.1
  have hline :
      ∀ a b : ℝ,
        Q (a • sphereE3.1 + b • sphereE1.1) =
          a ^ 2 * Q sphereE3.1 +
            b ^ 2 * Q sphereE1.1 +
              (a * b) * QuadraticMap.polar (⇑Q) sphereE3.1 sphereE1.1 := by
    intro a b
    calc
      Q (a • sphereE3.1 + b • sphereE1.1)
          = Q (a • sphereE3.1) + Q (b • sphereE1.1) +
              QuadraticMap.polar (⇑Q) (a • sphereE3.1) (b • sphereE1.1) := by
                simpa using (QuadraticMap.map_add (f := Q) (a • sphereE3.1) (b • sphereE1.1))
      _ = a ^ 2 * Q sphereE3.1 + b ^ 2 * Q sphereE1.1 +
            (a * b) * QuadraticMap.polar (⇑Q) sphereE3.1 sphereE1.1 := by
              rw [Q.map_smul, Q.map_smul,
                QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
              simp [smul_eq_mul]
              ring
  have hnn :
      ∀ t : ℝ,
        0 ≤
          Q sphereE1.1 * t ^ 2 +
            QuadraticMap.polar (⇑Q) sphereE3.1 sphereE1.1 * t +
              Q sphereE3.1 := by
    intro t
    have htmp := hQnn (sphereE3.1 + t • sphereE1.1)
    have hrewrite :
        Q (sphereE3.1 + t • sphereE1.1) =
          Q sphereE1.1 * t ^ 2 +
            QuadraticMap.polar (⇑Q) sphereE3.1 sphereE1.1 * t +
              Q sphereE3.1 := by
      calc
        Q (sphereE3.1 + t • sphereE1.1)
            = 1 ^ 2 * Q sphereE3.1 +
                t ^ 2 * Q sphereE1.1 +
                  (1 * t) * QuadraticMap.polar (⇑Q) sphereE3.1 sphereE1.1 := by
                    simpa using hline 1 t
        _ = Q sphereE1.1 * t ^ 2 +
              QuadraticMap.polar (⇑Q) sphereE3.1 sphereE1.1 * t +
                Q sphereE3.1 := by ring
    rwa [hrewrite] at htmp
  have hdisc :=
    discriminant_bound_of_nonneg
      (Q sphereE1.1)
      (QuadraticMap.polar (⇑Q) sphereE3.1 sphereE1.1)
      (Q sphereE3.1)
      (by simpa [hQe1] using hQnn sphereE1.1)
      (by simpa [hQe3])
      hnn
  have hpolar_zero :
      QuadraticMap.polar (⇑Q) sphereE3.1 sphereE1.1 = 0 := by
    rw [hQe3] at hdisc
    nlinarith
  have hcoords :
      ((r : ℂ) • p) + ((s : ℂ) • u) =
        coordPoint u w p (s, (0, r)) := by
    simp [coordPoint, add_comm, add_left_comm, add_assoc]
  calc
    frame_quadratic (H := H) μ (((r : ℂ) • p) + ((s : ℂ) • u))
        = frame_quadratic (H := H) μ (coordPoint u w p (s, (0, r))) := by rw [hcoords]
    _ = Q (s • sphereE1.1 + r • sphereE3.1) := by
          symm
          simpa [sphereE1, sphereE3, coordPoint, add_comm, add_left_comm, add_assoc] using
            hQall (s • sphereE1.1 + r • sphereE3.1)
    _ = s ^ 2 * Q sphereE1.1 := by
          have htmp := hline r s
          simpa [add_comm, add_left_comm, add_assoc, hQe3, hpolar_zero] using htmp
    _ = s ^ 2 * frame_quadratic (H := H) μ u := by rw [hQe1]

private lemma local_defect_g_eq_zero_of_coordSphere_quadratic_submodule_mixed_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u w p : H}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hp : ‖p‖ = 1)
    (huw : inner (𝕜 := ℂ) u w = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hwp : inner (𝕜 := ℂ) w p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (hq :
      coordSphereFrameContinuousMap hdim μ u w p hu hw hp huw hup hwp hp0 ∈
        continuousSphereQuadraticSubmodule)
    (s : ℝ) :
    local_defect_g μ p u s = 0 := by
  have hplus :=
    frame_quadratic_real_line_eq_sq_mul_of_coordSphere_quadratic_submodule_osc
      (H := H) hdim μ hu hw hp huw hup hwp hp0 hq 1 s
  have hminus :=
    frame_quadratic_real_line_eq_sq_mul_of_coordSphere_quadratic_submodule_osc
      (H := H) hdim μ hu hw hp huw hup hwp hp0 hq 1 (-s)
  have hplus' :
      frame_quadratic (H := H) μ (1 • p + (s : ℂ) • u) =
        s ^ 2 * frame_quadratic (H := H) μ u := by
    simpa using hplus
  have hminus' :
      frame_quadratic (H := H) μ (1 • p - (s : ℂ) • u) =
        (-s) ^ 2 * frame_quadratic (H := H) μ u := by
    simpa [sub_eq_add_neg] using hminus
  unfold local_defect_g local_quad2DDefect local_quad2DExpr
  change
    frame_quadratic (H := H) μ ((1 : ℂ) • p + (s : ℂ) • u) +
        frame_quadratic (H := H) μ ((1 : ℂ) • p - (s : ℂ) • u) -
        (2 * 1 ^ 2 * frame_quadratic (H := H) μ p +
          2 * s ^ 2 * frame_quadratic (H := H) μ u) =
      0
  set A := frame_quadratic (H := H) μ ((1 : ℂ) • p + (s : ℂ) • u)
  set B := frame_quadratic (H := H) μ ((1 : ℂ) • p - (s : ℂ) • u)
  have hA : A = s ^ 2 * frame_quadratic (H := H) μ u := by
    unfold A
    exact hplus
  have hB : B = s ^ 2 * frame_quadratic (H := H) μ u := by
    unfold B
    simpa [sub_eq_add_neg] using hminus
  calc
    A + B -
        (2 * 1 ^ 2 * frame_quadratic (H := H) μ p +
          2 * s ^ 2 * frame_quadratic (H := H) μ u)
      = s ^ 2 * frame_quadratic (H := H) μ u +
          s ^ 2 * frame_quadratic (H := H) μ u -
          (2 * 1 ^ 2 * frame_quadratic (H := H) μ p +
            2 * s ^ 2 * frame_quadratic (H := H) μ u) := by rw [hA, hB]
    _ = 0 := by rw [hp0]; ring

private theorem lowHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereQuadraticSubmodule_osc :
    lowHarmonicPolyHomogeneousImageSubmodule ≤ continuousSphereQuadraticSubmodule := by
  rw [lowHarmonicPolyHomogeneousImageSubmodule]
  refine sup_le ?_ ?_
  · exact
      (harmonicPolyHomogeneousImage_le_continuousHarmonicSphereDegreeSubmodule 0).trans
        continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereQuadraticSubmodule
  · exact
      (harmonicPolyHomogeneousImage_le_continuousHarmonicSphereDegreeSubmodule 2).trans
        continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereQuadraticSubmodule

private theorem continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_s2_low_osc
    (hS2 :
      GleasonS2Bridge.continuousSphereFrameSubmoduleS2 =
        GleasonS2Bridge.lowSectorS2) :
    continuousSphereFrameSubmodule ≤ continuousSphereQuadraticSubmodule := by
  intro f hf
  have hfS2 :
      GleasonS2Bridge.s2Pullback.symm f ∈ GleasonS2Bridge.continuousSphereFrameSubmoduleS2 := by
    simpa [GleasonS2Bridge.continuousSphereFrameSubmoduleS2] using hf
  rw [hS2, GleasonS2Bridge.lowSectorS2] at hfS2
  rcases Submodule.mem_sup.mp hfS2 with ⟨f0, hf0, f2, hf2, hsum⟩
  have hf0' :
      GleasonS2Bridge.s2Pullback f0 ∈ continuousHarmonicSphereDegreeSubmodule 0 :=
    GleasonS2Bridge.s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule hf0
  have hf2' :
      GleasonS2Bridge.s2Pullback f2 ∈ continuousHarmonicSphereDegreeSubmodule 2 :=
    GleasonS2Bridge.s2Pullback_mem_continuousHarmonicSphereDegreeSubmodule hf2
  have hsum' :
      GleasonS2Bridge.s2Pullback f0 + GleasonS2Bridge.s2Pullback f2 = f := by
    simpa using congrArg GleasonS2Bridge.s2Pullback hsum
  have hq02 :
      f ∈ continuousHarmonicSphereDegreeSubmodule 0 ⊔
        continuousHarmonicSphereDegreeSubmodule 2 := by
    exact Submodule.mem_sup.mpr
      ⟨GleasonS2Bridge.s2Pullback f0, hf0',
        GleasonS2Bridge.s2Pullback f2, hf2', hsum'⟩
  exact continuousHarmonicSphereDegreeSup_zero_two_le_continuousSphereQuadraticSubmodule hq02

private theorem
    continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_highEvenClosure_bot_osc
    (hbot :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule = ⊥) :
    continuousSphereFrameSubmodule ≤ continuousSphereQuadraticSubmodule := by
  have hclosure :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≤
          lowHarmonicPolyHomogeneousImageSubmodule := by
    simpa [hbot] using
      (bot_le : (⊥ : Submodule ℝ C(spherePoint3, ℝ)) ≤
        lowHarmonicPolyHomogeneousImageSubmodule)
  have hframeLow :
      continuousSphereFrameSubmodule = lowHarmonicPolyHomogeneousImageSubmodule :=
    continuousSphereFrameSubmodule_eq_low_of_topologicalClosure_highEvenUnion_inf_frame_le_low
      hclosure
  intro f hf
  have hlow : f ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
    simpa [hframeLow] using hf
  exact lowHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereQuadraticSubmodule_osc hlow

private lemma local_defect_g_eq_zero_of_s2_frame_eq_low_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hS2 :
      GleasonS2Bridge.continuousSphereFrameSubmoduleS2 =
        GleasonS2Bridge.lowSectorS2)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  have hframe :
      coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
        continuousSphereFrameSubmodule :=
    coordSphereFrameContinuousMap_mem_continuousSphereFrameSubmodule_of_zero_at_p
      hdim μ hu hv hp huv hup hvp hp0
  have hq :
      coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
        continuousSphereQuadraticSubmodule :=
    continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_s2_low_osc hS2 hframe
  exact
    local_defect_g_eq_zero_of_coordSphere_quadratic_submodule_osc
      (H := H) hdim μ hu hv hp huv hup hvp hp0 hq t

private lemma local_defect_g_eq_zero_of_frame_eq_low_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hframeLow :
      continuousSphereFrameSubmodule = lowHarmonicPolyHomogeneousImageSubmodule)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  have hframe :
      coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
        continuousSphereFrameSubmodule :=
    coordSphereFrameContinuousMap_mem_continuousSphereFrameSubmodule_of_zero_at_p
      hdim μ hu hv hp huv hup hvp hp0
  have hlow :
      coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
        lowHarmonicPolyHomogeneousImageSubmodule := by
    simpa [hframeLow] using hframe
  have hq :
      coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
        continuousSphereQuadraticSubmodule :=
    lowHarmonicPolyHomogeneousImageSubmodule_le_continuousSphereQuadraticSubmodule_osc hlow
  exact
    local_defect_g_eq_zero_of_coordSphere_quadratic_submodule_osc
      (H := H) hdim μ hu hv hp huv hup hvp hp0 hq t

private lemma local_defect_g_eq_zero_of_topologicalClosure_highEvenUnion_inf_frame_le_low_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hclosure :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≤
          lowHarmonicPolyHomogeneousImageSubmodule)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  have hframeLow :
      continuousSphereFrameSubmodule = lowHarmonicPolyHomogeneousImageSubmodule :=
    continuousSphereFrameSubmodule_eq_low_of_topologicalClosure_highEvenUnion_inf_frame_le_low
      hclosure
  exact
    local_defect_g_eq_zero_of_frame_eq_low_osc
      (H := H) hdim μ hframeLow hu hv hp huv hup hvp hp0 t

private lemma local_defect_g_eq_zero_of_topologicalClosure_highEvenUnion_inf_frame_eq_bot_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hbot :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule = ⊥)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  have hclosure :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≤
          lowHarmonicPolyHomogeneousImageSubmodule := by
    simpa [hbot] using (bot_le : (⊥ : Submodule ℝ C(spherePoint3, ℝ)) ≤
      lowHarmonicPolyHomogeneousImageSubmodule)
  exact
    local_defect_g_eq_zero_of_topologicalClosure_highEvenUnion_inf_frame_le_low_osc
      (H := H) hdim μ hclosure hu hv hp huv hup hvp hp0 t

private lemma local_defect_g_eq_zero_of_sqquotientRaw_continuousAt_zero_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hzeroCont :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ContinuousAt (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  have hbot :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule = ⊥ :=
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqquotientRaw_continuousAt_zero
      hzeroCont
  exact
    local_defect_g_eq_zero_of_topologicalClosure_highEvenUnion_inf_frame_eq_bot_osc
      (H := H) hdim μ hbot hu hv hp huv hup hvp hp0 t

private lemma
    mem_topologicalClosure_highEvenUnion_of_mem_continuousSphereFrameSubmodule_of_ambientLowProjection_zero_osc
    {g : C(spherePoint3, ℝ)}
    (hgFrame : g ∈ continuousSphereFrameSubmodule)
    (hproj : GleasonS2Bridge.ambientLowHarmonicProjectionContinuous g = 0) :
    g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure := by
  have hsum :
      g ∈ lowHarmonicPolyHomogeneousImageSubmodule ⊔
        highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure :=
    continuousSphereFrameSubmodule_le_low_sup_topologicalClosure_highEvenUnion hgFrame
  rcases Submodule.mem_sup.mp hsum with ⟨l, hlLow, h, hhHigh, rfl⟩
  have hlproj :
      GleasonS2Bridge.ambientLowHarmonicProjectionContinuous l = l :=
    GleasonS2Bridge.ambientLowHarmonicProjectionContinuous_eq_self_of_mem_lowHarmonicPolyHomogeneousImageSubmodule
      hlLow
  have hhproj :
      GleasonS2Bridge.ambientLowHarmonicProjectionContinuous h = 0 :=
    GleasonS2Bridge.ambientLowHarmonicProjectionContinuous_eq_zero_of_mem_topologicalClosure_highEvenUnion
      hhHigh
  have hlzero : l = 0 := by
    simpa [map_add, hlproj, hhproj] using hproj
  simpa [hlzero] using hhHigh

private lemma
    eq_zero_of_mem_continuousSphereFrameSubmodule_of_isNorthZonal_of_ambientLowProjection_zero_of_sqquotientRaw_continuousAt_zero_osc
    {g : C(spherePoint3, ℝ)}
    (hgFrame : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hproj : GleasonS2Bridge.ambientLowHarmonicProjectionContinuous g = 0)
    (hzero : ContinuousAt (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc) :
    g = 0 := by
  have hgHigh :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure :=
    mem_topologicalClosure_highEvenUnion_of_mem_continuousSphereFrameSubmodule_of_ambientLowProjection_zero_osc
      hgFrame hproj
  exact
    eq_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal_of_sqquotientRaw_continuousAt_zero
      ⟨hgHigh, hgFrame⟩ hgz hzero

private lemma
    mem_lowHarmonicPolyHomogeneousImageSubmodule_of_isNorthZonal_mem_frame_of_mem_quadratic_osc
    {g : C(spherePoint3, ℝ)}
    (hgFrame : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hgquad : g ∈ continuousSphereQuadraticSubmodule) :
    g ∈ lowHarmonicPolyHomogeneousImageSubmodule := by
  have hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
    rw [continuousSphereGreatCirclePointConstraintSubmodule_eq_continuousSphereFrameSubmodule]
    exact hgFrame
  rcases exists_const_add_sq_of_isNorthZonal_mem_quadratic_pointConstraint hgquad hgpc hgz with
    ⟨a, b, hab⟩
  have hdecomp :
      g = (a + b / 3) • (1 : C(spherePoint3, ℝ)) + (-b / 3) • zonalQuadraticMode := by
    ext x
    rw [hab x]
    simp [Pi.smul_apply, zonalQuadraticMode_apply]
    ring
  rw [hdecomp]
  apply Submodule.add_mem_sup
  · exact
      Submodule.smul_mem _ (a + b / 3)
        one_mem_harmonicPolyHomogeneousImageSubmodule_zero
  · exact
      Submodule.smul_mem _ (-b / 3)
        zonalQuadraticMode_mem_harmonicPolyHomogeneousImageSubmodule_two

private lemma
    eq_zero_of_mem_continuousSphereFrameSubmodule_of_isNorthZonal_of_ambientLowProjection_zero_of_mem_quadratic_osc
    {g : C(spherePoint3, ℝ)}
    (hgFrame : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hproj : GleasonS2Bridge.ambientLowHarmonicProjectionContinuous g = 0)
    (hgquad : g ∈ continuousSphereQuadraticSubmodule) :
    g = 0 := by
  have hlow :
      g ∈ lowHarmonicPolyHomogeneousImageSubmodule :=
    mem_lowHarmonicPolyHomogeneousImageSubmodule_of_isNorthZonal_mem_frame_of_mem_quadratic_osc
      hgFrame hgz hgquad
  have hself :
      GleasonS2Bridge.ambientLowHarmonicProjectionContinuous g = g :=
    GleasonS2Bridge.ambientLowHarmonicProjectionContinuous_eq_self_of_mem_lowHarmonicPolyHomogeneousImageSubmodule
      hlow
  rw [hself] at hproj
  exact hproj

private lemma
    eq_value_at_one_near_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_osc
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g) :
    ∀ {δ : ℝ}, 0 < δ →
      ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧
        sqCenteredNorthZonalQuotientRaw g u =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  intro δ hδ
  by_cases hconst :
      ∀ {u : unitIcc}, 0 < u.1 →
        sqCenteredNorthZonalQuotientRaw g u =
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  · have hlim :
        Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
          (nhdsWithin zeroUnitIcc {u : unitIcc | 0 < u.1})
          (nhds (sqCenteredNorthZonalQuotientRaw g oneUnitIcc)) := by
      apply tendsto_sqCenteredNorthZonalQuotientRaw_zero_of_uniform_near
      intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro u hu _hu1
      rw [hconst hu]
      simpa using hε
    exact False.elim <|
      False_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_of_sqquotientRaw_tendsto_zero
        hg hgne hgz hlim
  · push_neg at hconst
    exact
      exists_eq_value_at_one_near_zero_of_not_const_of_mem_frame
        hg.2 hgz hconst hδ

private lemma
    dyadic_shell_eq_value_at_one_arbitrarily_far_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_osc
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g) :
    ∀ N : ℕ,
      ∃ n : ℕ, n ≥ N ∧
        ∃ v : unitIcc, (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) =
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  intro N
  let δ : ℝ := (1 / 2 : ℝ) ^ (N + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  rcases
      eq_value_at_one_near_zero_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_osc
        hg hgne hgz hδ with
    ⟨u, huPos, huLt, huEq⟩
  rcases
      exists_nat_dyadic_shell_mem_from (N := N) huPos
        (by simpa [δ, dyadicUnitIcc_val] using huLt) with
    ⟨n, hnN, v, hvHalf, hvEq⟩
  refine ⟨n, hnN, v, hvHalf, ?_⟩
  simpa [hvEq] using huEq

private lemma
    dyadic_shell_bracket_value_at_one_arbitrarily_far_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_osc
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgne : g ≠ 0)
    (hgz : IsNorthZonal g) :
    ∀ N : ℕ,
      ∃ n : ℕ, n ≥ N ∧
        ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) u) ≤
            sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap (dyadicUnitIcc n) v) := by
  intro N
  rcases
      dyadic_shell_eq_value_at_one_arbitrarily_far_of_mem_topologicalClosure_highEvenUnion_inf_frame_nonzero_of_isNorthZonal_osc
        hg hgne hgz N with
    ⟨n, hnN, v, hvHalf, hvEq⟩
  refine ⟨n, hnN, v, v, hvHalf, hvHalf, ?_, ?_⟩
  · simpa [hvEq]
  · simpa [hvEq]

private theorem
    exists_lowSqProfileMode_uniform_near_with_stage_factor_degree_defect_osc
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
        h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
        IsNorthZonal h ∧
        (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
        q ∈ Polynomial.degreeLT ℝ N ∧
        l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
        ‖h - g‖ < ε ∧
        sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε ∧
        ‖h - l‖ ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
  intro ε hε
  rcases
      exists_northZonal_mem_highEvenUnion_close_of_mem_topologicalClosure_highEvenUnion_of_isNorthZonal
        hg.1 hgz hε with
    ⟨h, hhHigh, hhz, hdist⟩
  have hmono : Directed (· ≤ ·) highEvenBoundedHarmonicPolyHomogeneousImageSubmodule := by
    intro N M
    exact ⟨max N M,
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_left _ _),
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _)⟩
  rw [highEvenUnionHarmonicPolyHomogeneousImageSubmodule] at hhHigh
  rcases
      (Submodule.mem_iSup_of_directed highEvenBoundedHarmonicPolyHomogeneousImageSubmodule hmono).mp
        hhHigh with
    ⟨N0, hhN0⟩
  let N : ℕ := max 1 N0
  have hN : 1 ≤ N := le_max_left _ _
  have hhN : h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _) hhN0
  rcases exists_sqquotient_poly_degree_and_tail_bound_of_mem_highEvenBounded_of_isNorthZonal hhN hhz with
    ⟨q, hqdeg, hq, _htail⟩
  let l : C(spherePoint3, ℝ) := lowSqProfileMode (h sphereE1) (q.coeff 0)
  have hpoly :
      sqCenteredNorthZonalContinuousMap h = sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) := by
    ext u
    change sqCenteredNorthZonalProfile h u = ((Polynomial.X : Polynomial ℝ) * q).eval u.1
    rw [hq u]
    simp
  have hframe : g ∈ continuousSphereFrameSubmodule := hg.2
  have hfixProfile :
      northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap g) =
        sqCenteredNorthZonalContinuousMap g :=
    northZonalSqProfileAverage_sqCenteredNorthZonalContinuousMap_of_mem_frame hframe hgz
  have hdistProf :
      dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g) <
        2 * ε := by
    calc
      dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g)
        = ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ := by
            simp [dist_eq_norm]
      _ ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
      _ < 2 * ε := by
            gcongr
  have hdefect :
      sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε := by
    calc
      sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q)
        = dist (northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h))
            (sqCenteredNorthZonalContinuousMap h) := by
              simp [sqProfilePolynomialDefect, hpoly]
      _ ≤ dist (northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h))
            (northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap g)) +
          dist (sqCenteredNorthZonalContinuousMap g) (sqCenteredNorthZonalContinuousMap h) := by
              simpa [hfixProfile] using
                dist_triangle
                  (northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h))
                  (northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap g))
                  (sqCenteredNorthZonalContinuousMap h)
      _ ≤
          2 * dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g) +
            dist (sqCenteredNorthZonalContinuousMap g) (sqCenteredNorthZonalContinuousMap h) := by
              gcongr
              exact dist_northZonalSqProfileAverage_le _ _
      _ < 2 * (2 * ε) + 2 * ε := by
            have hdistProf' :
                dist (sqCenteredNorthZonalContinuousMap g) (sqCenteredNorthZonalContinuousMap h) <
                  2 * ε := by
              simpa [dist_comm] using hdistProf
            nlinarith
      _ = 6 * ε := by ring
  have hlin :
      ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖ ≤
        24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    calc
      ‖sqCenteredNorthZonalContinuousMap h - sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖
        = ‖sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) -
            sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖ := by
              rw [hpoly]
      _ ≤
          4 * degreeLTSqProfileTailBoundConst (N + 1) *
            sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) := by
              exact
                norm_sqProfilePolynomialMap_X_mul_sub_linear_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect
                  hqdeg
      _ ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) * (6 * ε) := by
            have hconst_nonneg : 0 ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) := by
              have htail_nonneg : 0 ≤ degreeLTSqProfileTailBoundConst (N + 1) := by
                unfold degreeLTSqProfileTailBoundConst
                positivity
              nlinarith
            exact mul_le_mul_of_nonneg_left (le_of_lt hdefect) hconst_nonneg
      _ = 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by ring
  have hnear :
      ‖h - l‖ ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    have hhHigh' : h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule :=
      Submodule.mem_iSup_of_mem N hhN
    change ‖h - lowSqProfileMode (h sphereE1) (q.coeff 0)‖ ≤
      24 * degreeLTSqProfileTailBoundConst (N + 1) * ε
    rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh' hhz]
    simpa [l, sqProfileLinearPart] using hlin
  exact ⟨N, hN, h, q, l, hhN, hhz, hq, hqdeg,
    lowSqProfileMode_mem_lowHarmonicPolyHomogeneousImageSubmodule _ _, hdist, hdefect, hnear⟩

private theorem
    exists_lowSqProfileMode_uniform_near_with_stage_factor_degree_bothDefects_osc
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
        h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
        IsNorthZonal h ∧
        (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
        q ∈ Polynomial.degreeLT ℝ N ∧
        l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
        ‖h - g‖ < ε ∧
        sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε ∧
        dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
            (q.toContinuousMapOn unitIcc) ≤
          degreeLTSqMulNormConst N * (6 * ε) ∧
        ‖h - l‖ ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
  intro ε hε
  rcases exists_lowSqProfileMode_uniform_near_with_stage_factor_degree_defect_osc hg hgz hε with
    ⟨N, hN, h, q, l, hhN, hhz, hq, hqdeg, hl, hdist, hdefect, hnear⟩
  have hqdefect :
      dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
          (q.toContinuousMapOn unitIcc) ≤
        degreeLTSqMulNormConst N * (6 * ε) := by
    calc
      dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
          (q.toContinuousMapOn unitIcc)
        ≤ degreeLTSqMulNormConst N * sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) :=
          norm_quotientDefect_le_degreeLTSqMulNormConst_mul_sqprofileDefect hqdeg
      _ ≤ degreeLTSqMulNormConst N * (6 * ε) := by
          have hconst_nonneg : 0 ≤ degreeLTSqMulNormConst N := by
            unfold degreeLTSqMulNormConst
            positivity
          exact mul_le_mul_of_nonneg_left (le_of_lt hdefect) hconst_nonneg
  exact
    ⟨N, hN, h, q, l, hhN, hhz, hq, hqdeg, hl, hdist, hdefect, hqdefect, hnear⟩

private theorem
    exists_sqquotientPoly_shell_pair_uniform_near_osc
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
        h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
        IsNorthZonal h ∧
        (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
        q ∈ Polynomial.degreeLT ℝ N ∧
        l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
        ‖h - g‖ < ε ∧
        ∀ m : ℕ, ∀ {a u v : unitIcc},
          |(sqQuotientRescalePolynomial a q).eval u.1 -
              (sqQuotientRescalePolynomial a q).eval v.1|
            ≤
              2 *
                ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                    (degreeLTSqMulNormConst N * (6 * ε)) +
                  (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by
  intro ε hε
  rcases exists_lowSqProfileMode_uniform_near_with_stage_factor_degree_bothDefects_osc hg hgz hε with
    ⟨N, hN, h, q, l, hhN, hhz, hq, hqdeg, hl, hdist, hsqdef, hqdef, hnorm⟩
  refine ⟨N, hN, h, q, l, hhN, hhz, hq, hqdeg, hl, hdist, ?_⟩
  intro m a u v
  exact
    abs_sqQuotientRescalePolynomial_eval_sub_eval_le_of_almost_fixed
      a q
      (hδ := by
        have hconst_nonneg : 0 ≤ degreeLTSqMulNormConst N := by
          unfold degreeLTSqMulNormConst
          positivity
        positivity)
      (halmost := by
        calc
          dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
              (q.toContinuousMapOn unitIcc)
            ≤ degreeLTSqMulNormConst N * (6 * ε) := hqdef)
      m u v

private theorem
    exists_sqquotientRaw_shell_pair_uniform_near_v2_osc
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
        h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
        IsNorthZonal h ∧
        (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
        q ∈ Polynomial.degreeLT ℝ N ∧
        l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
        ‖h - g‖ < ε ∧
        ∀ m : ℕ, ∀ {a u v : unitIcc}, 0 < a.1 → (1 / 2 : ℝ) ≤ u.1 → (1 / 2 : ℝ) ≤ v.1 →
          |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
              sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)|
            ≤
              8 * ε / a.1 +
                2 *
                  ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                      (degreeLTSqMulNormConst N * (6 * ε)) +
                    (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by
  intro ε hε
  rcases exists_sqquotientPoly_shell_pair_uniform_near_osc hg hgz hε with
    ⟨N, hN, h, q, l, hhN, hhz, hq, hqdeg, hl, hdist, hshell⟩
  refine ⟨N, hN, h, q, l, hhN, hhz, hq, hqdeg, hl, hdist, ?_⟩
  intro m a u v ha hu hv
  have hprof :
      ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < 2 * ε := by
    calc
      ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖
        ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
      _ < 2 * ε := by
          gcongr
  have huShell : a.1 / 2 ≤ (sqScaleMap a u).1 := by
    simp [sqScaleMap_apply]
    nlinarith
  have hvShell : a.1 / 2 ≤ (sqScaleMap a v).1 := by
    simp [sqScaleMap_apply]
    nlinarith
  have huErr :
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
          sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u)|
        ≤ 4 * ε / a.1 := by
    have hle :
        |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
            sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u)|
          ≤ ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ / (a.1 / 2) :=
      abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_profile_dist g h (by positivity) huShell
    have hnorm :
        ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ ≤ 2 * ε := by
      have hle' :
          ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ ≤ 2 * ε :=
        le_of_lt hprof
      simpa [norm_sub_rev] using hle'
    calc
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
          sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u)|
        ≤ ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ / (a.1 / 2) := hle
      _ ≤ (2 * ε) / (a.1 / 2) := by
          have hden : 0 ≤ a.1 / 2 := by positivity
          exact div_le_div_of_nonneg_right hnorm hden
      _ = 4 * ε / a.1 := by
          field_simp [show (a.1 : ℝ) ≠ 0 by exact ne_of_gt ha]
          ring
  have hvErr :
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v) -
          sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)|
        ≤ 4 * ε / a.1 := by
    have hle :
        |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v) -
            sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)|
          ≤ ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ / (a.1 / 2) :=
      abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_profile_dist g h (by positivity) hvShell
    have hnorm :
        ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ ≤ 2 * ε := by
      have hle' :
          ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ ≤ 2 * ε :=
        le_of_lt hprof
      simpa [norm_sub_rev] using hle'
    calc
      |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v) -
          sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)|
        ≤ ‖sqCenteredNorthZonalContinuousMap g - sqCenteredNorthZonalContinuousMap h‖ / (a.1 / 2) := hle
      _ ≤ (2 * ε) / (a.1 / 2) := by
          have hden : 0 ≤ a.1 / 2 := by positivity
          exact div_le_div_of_nonneg_right hnorm hden
      _ = 4 * ε / a.1 := by
          field_simp [show (a.1 : ℝ) ≠ 0 by exact ne_of_gt ha]
          ring
  have hpairh :
      |sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u) -
          sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)|
        ≤
          2 *
            ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                (degreeLTSqMulNormConst N * (6 * ε)) +
              (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by
    have huPos : 0 < (sqScaleMap a u).1 := by
      simp [sqScaleMap_apply]
      nlinarith
    have hvPos : 0 < (sqScaleMap a v).1 := by
      simp [sqScaleMap_apply]
      nlinarith
    simpa [sqCenteredNorthZonalQuotientRaw_eq_eval_of_factor hq huPos,
      sqCenteredNorthZonalQuotientRaw_eq_eval_of_factor hq hvPos] using
      hshell m (a := a) (u := u) (v := v)
  calc
    |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)|
      ≤ |sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
            sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u)| +
          |sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u) -
            sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)| +
          |sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v) -
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)| := by
              let x :=
                sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) -
                  sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u)
              let y :=
                sqCenteredNorthZonalQuotientRaw h (sqScaleMap a u) -
                  sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v)
              let z :=
                sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v) -
                  sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)
              have habs : |x + y + z| ≤ |x| + |y| + |z| := by
                have hxy : |x + y| ≤ |x| + |y| := by
                  simpa [Real.norm_eq_abs] using norm_add_le x y
                have hxyz : |(x + y) + z| ≤ |x + y| + |z| := by
                  simpa [Real.norm_eq_abs] using norm_add_le (x + y) z
                calc
                  |x + y + z| = |(x + y) + z| := by ring
                  _ ≤ |x + y| + |z| := hxyz
                  _ ≤ (|x| + |y|) + |z| := by linarith
                  _ = |x| + |y| + |z| := by ring
              simpa [x, y, z] using habs
    _ ≤ 4 * ε / a.1 +
          (2 *
            ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                (degreeLTSqMulNormConst N * (6 * ε)) +
              (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q))) +
          4 * ε / a.1 := by
            have hvErr' :
                |sqCenteredNorthZonalQuotientRaw h (sqScaleMap a v) -
                    sqCenteredNorthZonalQuotientRaw g (sqScaleMap a v)|
                  ≤ 4 * ε / a.1 := by
              simpa [abs_sub_comm] using hvErr
            linarith
    _ = 8 * ε / a.1 +
          2 *
            ((Finset.sum (Finset.range m) fun _ => (1 : ℝ)) *
                (degreeLTSqMulNormConst N * (6 * ε)) +
              (3 / 4 : ℝ) ^ m * (a.1 * polyTailAbsSum q)) := by ring

private theorem
    sqProfileTailAbsSum_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect_osc
    {N : ℕ} {p : ℝ[X]}
    (hpdeg : p ∈ Polynomial.degreeLT ℝ N) :
    sqProfileTailAbsSum p ≤
      4 * degreeLTSqProfileTailBoundConst N * sqProfilePolynomialDefect p := by
  let d : ℝ[X] := northZonalSqProfilePolynomial p - p
  have hTdeg : northZonalSqProfilePolynomial p ∈ Polynomial.degreeLT ℝ N := by
    rw [Polynomial.mem_degreeLT]
    refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
    intro n hn
    have hpcoeff : p.coeff n = 0 := by
      exact (Polynomial.degree_lt_iff_coeff_zero _ _).1 ((Polynomial.mem_degreeLT).1 hpdeg) n hn
    simp [coeff_northZonalSqProfilePolynomial, hpcoeff]
  have hddeg : d ∈ Polynomial.degreeLT ℝ N := by
    exact Submodule.sub_mem _ hTdeg hpdeg
  have htaild :
      sqProfileTailAbsSum d ≤
        degreeLTSqProfileTailBoundConst N * ‖d.toContinuousMapOn unitIcc‖ :=
    sqProfileTailAbsSum_le_degreeLTSqProfileTailBoundConst_mul_norm hddeg
  have hmapd :
      d.toContinuousMapOn unitIcc =
        northZonalSqProfileAverage (sqProfilePolynomialMap p) -
          sqProfilePolynomialMap p := by
    ext u
    simp [d, sqProfilePolynomialMap, northZonalSqProfileAverage_toContinuousMapOn]
  calc
    sqProfileTailAbsSum p
      ≤ 4 * sqProfileTailAbsSum d := sqProfileTailAbsSum_le_four_mul_sqProfileTailAbsSum_defect p
    _ ≤ 4 * (degreeLTSqProfileTailBoundConst N * ‖d.toContinuousMapOn unitIcc‖) := by
          gcongr
    _ = 4 * degreeLTSqProfileTailBoundConst N * sqProfilePolynomialDefect p := by
          rw [hmapd]
          simp [sqProfilePolynomialDefect, dist_eq_norm, mul_assoc]

private theorem
    sqProfileTailAbsSum_X_mul_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect_osc
    {N : ℕ} {q : ℝ[X]}
    (hqdeg : q ∈ Polynomial.degreeLT ℝ N) :
    sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) ≤
      4 * degreeLTSqProfileTailBoundConst (N + 1) *
        sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) := by
  refine
    sqProfileTailAbsSum_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect_osc
      (N := N + 1) ?_
  rw [Polynomial.mem_degreeLT]
  refine (Polynomial.degree_lt_iff_coeff_zero _ _).2 ?_
  intro n hn
  by_cases h0 : n = 0
  · subst h0
    simp
  · rcases Nat.exists_eq_succ_of_ne_zero h0 with ⟨m, rfl⟩
    have hm : N ≤ m := by omega
    have hzero : q.coeff m = 0 := by
      exact (Polynomial.degree_lt_iff_coeff_zero _ _).1
        ((Polynomial.mem_degreeLT).1 hqdeg) m hm
    rw [Polynomial.coeff_X_mul, hzero]

private theorem
    exists_lowSqProfileMode_uniform_near_with_stage_factor_degree_defect_tail_osc
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ N : ℕ, ∃ hN : 1 ≤ N, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X], ∃ l : C(spherePoint3, ℝ),
        h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
        IsNorthZonal h ∧
        (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
        q ∈ Polynomial.degreeLT ℝ N ∧
        l ∈ lowHarmonicPolyHomogeneousImageSubmodule ∧
        ‖h - g‖ < ε ∧
        sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε ∧
        sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) ≤
          24 * degreeLTSqProfileTailBoundConst (N + 1) * ε ∧
        ‖h - l‖ ≤ 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
  intro ε hε
  rcases
      exists_lowSqProfileMode_uniform_near_with_stage_factor_degree_defect_osc hg hgz hε with
    ⟨N, hN, h, q, l, hhN, hhz, hq, hqdeg, hl, hdist, hdefect, hnear⟩
  have htail_le :
      sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) ≤
        24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by
    calc
      sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)
        ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) *
            sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) := by
              exact
                sqProfileTailAbsSum_X_mul_le_four_mul_degreeLTSqProfileTailBoundConst_mul_defect_osc
                  hqdeg
      _ ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) * (6 * ε) := by
            have hconst_nonneg : 0 ≤ 4 * degreeLTSqProfileTailBoundConst (N + 1) := by
              unfold degreeLTSqProfileTailBoundConst
              positivity
            exact mul_le_mul_of_nonneg_left (le_of_lt hdefect) hconst_nonneg
      _ = 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε := by ring
  exact
    ⟨N, hN, h, q, l, hhN, hhz, hq, hqdeg, hl, hdist, hdefect, htail_le, hnear⟩

private theorem
    exists_sqprofile_uniform_near_linear_osc
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε : ℝ}, 0 < ε →
      ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
        h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
        IsNorthZonal h ∧
        (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
        ‖h - g‖ < ε ∧
        ∀ m : ℕ,
          ‖sqCenteredNorthZonalContinuousMap g - sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖ ≤
            2 * ε +
              (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
  intro ε hε
  rcases
      exists_lowSqProfileMode_uniform_near_with_stage_factor_degree_defect_osc
        hg hgz hε with
    ⟨N, _hN, h, q, _l, hhN, hhz, hq, _hqdeg, _hl, hdist, hdefect, _hnear⟩
  have hhHigh : h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule :=
    Submodule.mem_iSup_of_mem N hhN
  let l0 : C(spherePoint3, ℝ) := lowSqProfileMode (h sphereE1) (q.coeff 0)
  refine ⟨h, q, hhHigh, hhz, hq, hdist, ?_⟩
  intro m
  have hlow :
      ‖h - l0‖ ≤
        (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
          (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
    dsimp [l0]
    rw [norm_sub_lowSqProfileMode_eq_sqprofile hhHigh hhz]
    have hp0 : (((Polynomial.X : Polynomial ℝ) * q) : Polynomial ℝ).eval 0 = 0 := by
      simp
    have hpoly :
        sqCenteredNorthZonalContinuousMap h =
          sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) := by
      ext u
      change sqCenteredNorthZonalProfile h u =
        (((Polynomial.X : Polynomial ℝ) * q) : Polynomial ℝ).eval u.1
      rw [hq u]
      simp
    calc
      ‖sqCenteredNorthZonalContinuousMap h -
          sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖
        = ‖sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) -
            sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖ := by
              rw [hpoly]
      _ ≤
          (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) *
              sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) +
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
              exact
                norm_polynomial_sub_linear_le_of_sqprofile_almost_fixed
                  ((Polynomial.X : Polynomial ℝ) * q) m hp0
      _ ≤
          (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
              have hsum_nonneg :
                  0 ≤ (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) := by
                positivity
              nlinarith [le_of_lt hdefect]
  have hgl :
      ‖g - lowSqProfileMode (g sphereE1) (q.coeff 0)‖ ≤
        2 * ε +
          (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
    have hglDist :
        dist g (lowSqProfileMode (g sphereE1) (q.coeff 0)) ≤
          2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
      calc
        dist g (lowSqProfileMode (g sphereE1) (q.coeff 0))
          ≤ dist g h + dist h l0 +
              dist l0 (lowSqProfileMode (g sphereE1) (q.coeff 0)) := by
                calc
                  dist g (lowSqProfileMode (g sphereE1) (q.coeff 0))
                    ≤ dist g h + dist h (lowSqProfileMode (g sphereE1) (q.coeff 0)) :=
                      dist_triangle _ _ _
                  _ ≤ dist g h + (dist h l0 + dist l0 (lowSqProfileMode (g sphereE1) (q.coeff 0))) := by
                        gcongr
                        exact dist_triangle _ _ _
                  _ = dist g h + dist h l0 + dist l0 (lowSqProfileMode (g sphereE1) (q.coeff 0)) := by
                        ring
        _ ≤ dist g h + dist h l0 + dist h g := by
              gcongr
              simpa [l0, dist_eq_norm] using
                norm_lowSqProfileMode_sub_leftParam_le_of_dist (h := h) (g := g) (q.coeff 0)
        _ ≤ 2 * ε +
              (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
              have hlow' :
                  dist h l0 ≤
                    (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                      (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
                simpa [dist_eq_norm] using hlow
              have hdist' : dist h g < ε := by
                simpa [dist_eq_norm] using hdist
              have hdist'' : dist g h < ε := by
                simpa [dist_comm] using hdist'
              linarith
    simpa [dist_eq_norm] using hglDist
  rw [norm_sub_lowSqProfileMode_eq_sqprofile_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    (hg := hg) (hgz := hgz) (b := q.coeff 0)] at hgl
  simpa [sqProfileLinearPart] using hgl

private theorem
    exists_sqquotientRaw_uniform_near_value_at_one_of_sqprofile_linearApprox_uniform_osc
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g) :
    ∀ {ε δ : ℝ}, 0 < ε → 0 < δ →
      ∃ h : C(spherePoint3, ℝ), ∃ q : Polynomial ℝ,
        h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
        IsNorthZonal h ∧
        (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
        ‖h - g‖ < ε ∧
        ∀ m : ℕ, ∀ {u : unitIcc}, δ ≤ u.1 →
          |sqCenteredNorthZonalQuotientRaw g u -
              sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
            ≤
              2 *
                ((2 * ε +
                  (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                    (3 / 4 : ℝ) ^ m *
                      sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) := by
  intro ε δ hε hδ
  rcases exists_sqprofile_uniform_near_linear_osc hg hgz hε with
    ⟨h, q, hhHigh, hhz, hq, hdist, hsqLin⟩
  refine ⟨h, q, hhHigh, hhz, hq, hdist, ?_⟩
  intro m u hu
  have hsqLin' :
      ‖sqCenteredNorthZonalContinuousMap g -
          (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖
        ≤
          2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q) := by
    simpa [sqProfileLinearPart] using hsqLin m
  have hraw :
      |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0|
        ≤
          (2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ := by
    calc
      |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0|
        ≤ ‖sqCenteredNorthZonalContinuousMap g -
            (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ / δ :=
          abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_sqprofile_linear g hδ hu
      _ ≤
          (2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ := by
            have hδnonneg : 0 ≤ δ := le_of_lt hδ
            exact div_le_div_of_nonneg_right hsqLin' hδnonneg
  have hδ1 : δ ≤ 1 := le_trans hu u.2.2
  have hone :
      |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0|
        ≤
          (2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ := by
    calc
      |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0|
        ≤ ‖sqCenteredNorthZonalContinuousMap g -
            (((Polynomial.C (q.coeff 0) * (Polynomial.X : Polynomial ℝ)) : Polynomial ℝ).toContinuousMapOn unitIcc)‖ / δ :=
          abs_sqCenteredNorthZonalQuotientRaw_sub_le_div_of_sqprofile_linear g hδ hδ1
      _ ≤
          (2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ := by
            have hδnonneg : 0 ≤ δ := le_of_lt hδ
            exact div_le_div_of_nonneg_right hsqLin' hδnonneg
  calc
    |sqCenteredNorthZonalQuotientRaw g u - sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
      ≤ |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
          |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0| := by
            have htri :=
              abs_sub_le (sqCenteredNorthZonalQuotientRaw g u) (q.coeff 0)
                (sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
            calc
              |sqCenteredNorthZonalQuotientRaw g u - sqCenteredNorthZonalQuotientRaw g oneUnitIcc|
                ≤ |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
                    |q.coeff 0 - sqCenteredNorthZonalQuotientRaw g oneUnitIcc| := by
                      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htri
              _ = |sqCenteredNorthZonalQuotientRaw g u - q.coeff 0| +
                    |sqCenteredNorthZonalQuotientRaw g oneUnitIcc - q.coeff 0| := by
                      congr 1
                      exact abs_sub_comm _ _
    _ ≤
        ((2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) +
          ((2 * ε +
            (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
              (3 / 4 : ℝ) ^ m *
                sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) := by
          gcongr
    _ =
        2 *
          ((2 * ε +
              (Finset.sum (Finset.range m) fun j => (2 : ℝ) ^ j) * (6 * ε) +
                (3 / 4 : ℝ) ^ m *
                  sqProfileTailAbsSum ((Polynomial.X : Polynomial ℝ) * q)) / δ) := by
          ring

private theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_fixed_g_degreeControlled_approx_osc
    (hstage :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {η : ℝ}, 0 < η →
          ∃ N : ℕ, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
            h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
            IsNorthZonal h ∧
            (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
            q ∈ Polynomial.degreeLT ℝ N ∧
            dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g) <
              η / 32 ∧
            dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
                (q.toContinuousMapOn unitIcc) <
              η / (128 * (degreeLTPolyTailBoundConst N + 1))) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  refine
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_linearized_fixedpart_approx ?_
  intro g hg hgz η hη
  rcases hstage hg hgz hη with
    ⟨N, h, q, hhN, hhz, hq, hqdeg, hprof, hdefect⟩
  refine ⟨(Polynomial.X : Polynomial ℝ) * q, by simp, ?_⟩
  have hprofileEq :
      sqCenteredNorthZonalContinuousMap h =
        sqMulContinuousMap (q.toContinuousMapOn unitIcc) := by
    ext u
    change sqCenteredNorthZonalProfile h u = u.1 * (q.toContinuousMapOn unitIcc) u
    rw [hq u]
    rfl
  have hlinearEq :
      sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q) =
        sqMulContinuousMap (ContinuousMap.const unitIcc (q.coeff 0)) := by
    have hcoeff :
        (((Polynomial.X : Polynomial ℝ) * q).coeff 1) = q.coeff 0 := by
      simp [Polynomial.coeff_X_mul]
    ext u
    rw [sqProfileLinearPart, sqMulContinuousMap_apply]
    change
      ((Polynomial.C ((((Polynomial.X : Polynomial ℝ) * q).coeff 1)) * Polynomial.X).eval u.1) =
        u.1 * q.coeff 0
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, hcoeff]
    ring
  have hconst_le :
      ‖q.toContinuousMapOn unitIcc - ContinuousMap.const unitIcc (q.coeff 0)‖ ≤
        4 * degreeLTPolyTailBoundConst N *
          dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
            (q.toContinuousMapOn unitIcc) :=
    norm_toContinuousMapOn_sub_const_le_four_mul_degreeLTPolyTailBoundConst_mul_defect hqdeg
  have hlin_to_h_le :
      dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
          (sqCenteredNorthZonalContinuousMap h) ≤
        ‖q.toContinuousMapOn unitIcc - ContinuousMap.const unitIcc (q.coeff 0)‖ := by
    rw [dist_eq_norm, hprofileEq, hlinearEq]
    have hsub :
        sqMulContinuousMap (ContinuousMap.const unitIcc (q.coeff 0)) -
            sqMulContinuousMap (q.toContinuousMapOn unitIcc) =
          sqMulContinuousMap
            (ContinuousMap.const unitIcc (q.coeff 0) - q.toContinuousMapOn unitIcc) := by
      ext u
      simp [sqMulContinuousMap_apply]
      ring
    rw [hsub]
    simpa [dist_eq_norm, norm_sub_rev] using
      norm_sqMulContinuousMap_le
        (ContinuousMap.const unitIcc (q.coeff 0) - q.toContinuousMapOn unitIcc)
  have hlin_to_h :
      dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
          (sqCenteredNorthZonalContinuousMap h) < η / 32 := by
    let K : ℝ := degreeLTPolyTailBoundConst N
    have hK_nonneg : 0 ≤ K := by
      dsimp [K]
      unfold degreeLTPolyTailBoundConst
      positivity
    let ratio : ℝ := η / (128 * (K + 1))
    have hratio_pos : 0 < ratio := by
      dsimp [ratio]
      positivity
    calc
      dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
          (sqCenteredNorthZonalContinuousMap h)
        ≤ ‖q.toContinuousMapOn unitIcc - ContinuousMap.const unitIcc (q.coeff 0)‖ :=
          hlin_to_h_le
      _ ≤ 4 * K *
            dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
              (q.toContinuousMapOn unitIcc) := by
            simpa [K] using hconst_le
      _ ≤ 4 * K * ratio := by
            have hdefect' :
                dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
                    (q.toContinuousMapOn unitIcc) <
                  ratio := by
              dsimp [ratio]
              simpa [K] using hdefect
            gcongr
      _ < 4 * (K + 1) * ratio := by
            have hK_lt : K < K + 1 := by linarith
            have hmul :=
              mul_lt_mul_of_pos_right hK_lt (by positivity : 0 < 4 * ratio)
            simpa [ratio, mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = η / 32 := by
            dsimp [ratio]
            field_simp [show K + 1 ≠ 0 by linarith]
            ring
  calc
    dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
        (sqCenteredNorthZonalContinuousMap g)
      ≤
        dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
            (sqCenteredNorthZonalContinuousMap h) +
          dist (sqCenteredNorthZonalContinuousMap h)
            (sqCenteredNorthZonalContinuousMap g) := by
              exact dist_triangle _ _ _
    _ < η / 32 + η / 32 := by
          exact add_lt_add hlin_to_h hprof
    _ = η / 16 := by ring

private theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_linearized_degree_defect_approx_osc
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {η : ℝ}, 0 < η →
          ∃ ε : ℝ, 0 < ε ∧
          ∃ N : ℕ, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
            h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
            IsNorthZonal h ∧
            (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
            q ∈ Polynomial.degreeLT ℝ N ∧
            ‖h - g‖ < ε ∧
            sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε ∧
            2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε < η / 16) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  exact
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_linearized_degree_defect_approx
      htame

private theorem
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_preiter_tameApprox_linearized_fixedpart_tailonly_osc
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {η : ℝ}, 0 < η →
          ∃ p : ℝ[X], ∃ m : ℕ,
            p.eval 0 = 0 ∧
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16 ∧
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 16) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  exact
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_preiter_tameApprox_linearized_fixedpart_tailonly
      htame

private theorem topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_linearized_fixedpart_approx_osc
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {η : ℝ}, 0 < η →
          ∃ p : ℝ[X],
            p.eval 0 = 0 ∧
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  exact
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_linearized_fixedpart_approx
      htame

private lemma exists_sqProfileTailAbsSum_iter_lt_osc
    (p : ℝ[X]) {η : ℝ} (hη : 0 < η) :
    ∃ m : ℕ, (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 16 := by
  by_cases htail : sqProfileTailAbsSum p = 0
  · refine ⟨0, ?_⟩
    simp [htail, hη]
  · have htail_nonneg : 0 ≤ sqProfileTailAbsSum p := by
      unfold sqProfileTailAbsSum
      positivity
    have htail_ne : sqProfileTailAbsSum p ≠ 0 := by
      exact htail
    have htail_pos : 0 < sqProfileTailAbsSum p := by
      have hzero_ne : (0 : ℝ) ≠ sqProfileTailAbsSum p := by
        simpa [ne_comm] using htail_ne
      exact lt_of_le_of_ne htail_nonneg hzero_ne
    obtain ⟨m, hm⟩ :=
      exists_pow_lt_of_lt_one
        (show 0 < (η / 16) / sqProfileTailAbsSum p by positivity)
        (by norm_num : (3 / 4 : ℝ) < 1)
    refine ⟨m, ?_⟩
    have hmul := mul_lt_mul_of_pos_right hm htail_pos
    have hdivmul : ((η / 16) / sqProfileTailAbsSum p) * sqProfileTailAbsSum p = η / 16 := by
      field_simp [ne_of_gt htail_pos]
    calc
      (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p
          < ((η / 16) / sqProfileTailAbsSum p) * sqProfileTailAbsSum p := hmul
      _ = η / 16 := hdivmul

private lemma dist_sqProfilePolynomialMap_X_mul_to_target_lt_two_mul_osc
    {g h : C(spherePoint3, ℝ)} {q : ℝ[X]} {ε : ℝ}
    (hq : ∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1)
    (hdist : ‖h - g‖ < ε) :
    dist (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q))
        (sqCenteredNorthZonalContinuousMap g) < 2 * ε := by
  have hpoly :
      sqCenteredNorthZonalContinuousMap h =
        sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) := by
    ext u
    change sqCenteredNorthZonalProfile h u =
      (((Polynomial.X : Polynomial ℝ) * q) : Polynomial ℝ).eval u.1
    rw [hq u]
    simp
  calc
    dist (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q))
        (sqCenteredNorthZonalContinuousMap g)
      = dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g) := by
          rw [hpoly]
    _ = ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ := by
          simp [dist_eq_norm]
    _ ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
    _ < 2 * ε := by
          gcongr

private lemma dist_sqProfileLinearPart_X_mul_to_target_lt_of_poly_lt_osc
    {g : C(spherePoint3, ℝ)} {q : ℝ[X]} {B ε : ℝ}
    (hpoly :
      dist (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q))
          (sqCenteredNorthZonalContinuousMap g) < ε)
    (hlin :
      ‖sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) -
          sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖ ≤ B) :
    dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
        (sqCenteredNorthZonalContinuousMap g) < B + ε := by
  calc
    dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
        (sqCenteredNorthZonalContinuousMap g)
      ≤
        dist (sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q))
            (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q)) +
          dist (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q))
            (sqCenteredNorthZonalContinuousMap g) := by
              exact dist_triangle _ _ _
    _ ≤
        ‖sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q) -
            sqProfileLinearPart ((Polynomial.X : Polynomial ℝ) * q)‖ +
          dist (sqProfilePolynomialMap ((Polynomial.X : Polynomial ℝ) * q))
            (sqCenteredNorthZonalContinuousMap g) := by
              gcongr
              simpa [dist_eq_norm, norm_sub_rev]
    _ < B + ε := by
          exact add_lt_add_of_le_of_lt hlin hpoly

private lemma local_defect_g_eq_zero_of_fixed_g_degreeControlled_approx_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hstage :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {η : ℝ}, 0 < η →
          ∃ N : ℕ, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
            h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
            IsNorthZonal h ∧
            (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
            q ∈ Polynomial.degreeLT ℝ N ∧
            dist (sqCenteredNorthZonalContinuousMap h) (sqCenteredNorthZonalContinuousMap g) <
              η / 32 ∧
            dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
                (q.toContinuousMapOn unitIcc) <
              η / (128 * (degreeLTPolyTailBoundConst N + 1)))
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  have hbot :=
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_fixed_g_degreeControlled_approx_osc
      hstage
  exact
    local_defect_g_eq_zero_of_topologicalClosure_highEvenUnion_inf_frame_eq_bot_osc
      (H := H) hdim μ hbot hu hv hp huv hup hvp hp0 t

private lemma local_defect_g_eq_zero_of_sqprofile_linearized_degree_defect_approx_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {η : ℝ}, 0 < η →
          ∃ ε : ℝ, 0 < ε ∧
          ∃ N : ℕ, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
            h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
            IsNorthZonal h ∧
            (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
            q ∈ Polynomial.degreeLT ℝ N ∧
            ‖h - g‖ < ε ∧
            sqProfilePolynomialDefect ((Polynomial.X : Polynomial ℝ) * q) < 6 * ε ∧
            2 * ε + 24 * degreeLTSqProfileTailBoundConst (N + 1) * ε < η / 16)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  have hbot :=
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_linearized_degree_defect_approx_osc
      htame
  exact
    local_defect_g_eq_zero_of_topologicalClosure_highEvenUnion_inf_frame_eq_bot_osc
      (H := H) hdim μ hbot hu hv hp huv hup hvp hp0 t

private lemma
    local_defect_g_eq_zero_of_sqprofile_preiter_tameApprox_linearized_fixedpart_tailonly_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {η : ℝ}, 0 < η →
          ∃ p : ℝ[X], ∃ m : ℕ,
            p.eval 0 = 0 ∧
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16 ∧
            (3 / 4 : ℝ) ^ m * sqProfileTailAbsSum p < η / 16)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  have hbot :=
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_preiter_tameApprox_linearized_fixedpart_tailonly_osc
      htame
  exact
    local_defect_g_eq_zero_of_topologicalClosure_highEvenUnion_inf_frame_eq_bot_osc
      (H := H) hdim μ hbot hu hv hp huv hup hvp hp0 t

private lemma local_defect_g_eq_zero_of_sqprofile_linearized_fixedpart_approx_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (htame :
      ∀ {g : C(spherePoint3, ℝ)},
        g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
              continuousSphereFrameSubmodule →
        IsNorthZonal g →
        ∀ {η : ℝ}, 0 < η →
          ∃ p : ℝ[X],
            p.eval 0 = 0 ∧
            dist (sqProfileLinearPart p) (sqCenteredNorthZonalContinuousMap g) < η / 16)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  have hbot :=
    topologicalClosure_highEvenUnion_inf_frame_eq_bot_of_sqprofile_linearized_fixedpart_approx_osc
      htame
  exact
    local_defect_g_eq_zero_of_topologicalClosure_highEvenUnion_inf_frame_eq_bot_osc
      (H := H) hdim μ hbot hu hv hp huv hup hvp hp0 t

private lemma local_defect_g_eq_zero_of_coordSphere_quadratic_decomposition_osc
    {s : Set ℕ}
    (hF : continuousSphereFrameSubmodule = ⨆ i : s, continuousHarmonicSphereDegreeSubmodule i)
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic (H := H) μ p = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  have hq :
      coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
        continuousSphereQuadraticSubmodule :=
    coordSphereFrameContinuousMap_mem_continuousSphereQuadraticSubmodule_of_decomposition_noindep
      (H := H) hF hdim μ hu hv hp huv hup hvp hp0
  exact
    local_defect_g_eq_zero_of_coordSphere_quadratic_submodule_osc
      (H := H) hdim μ hu hv hp huv hup hvp hp0 hq t

/-! ## Continuity and spectral reduction

The finite-dimensional argument combines the oscillation estimate with the
rotation-equivariant spherical harmonic decomposition. Continuity places the
coordinate-sphere frame function in the closed frame submodule; exclusion of
higher harmonic sectors then yields quadraticity and the vanishing of the local
defect. This route does not require a frame function to attain its infimum. -/

/-- The coord sphere function is continuous when Q is continuous on the sphere.

The coordSphereFrameFun maps spherePoint3 → ℝ via the chain:
  spherePoint3 →[spherePointCoord] S² ⊂ ℝ³ →[coordPoint u v p] sphere(H) →[Q] ℝ
When u,v,p are orthonormal, coordPoint maps unit 3-vectors isometrically
to unit H-vectors, so Q continuous on sphere(H) implies the composition
is continuous. -/
private lemma continuous_coordSphereFrameFun_of_cont_on_sphere
    (μ : FrameFunction H)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1))
    {u v p : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0) :
    Continuous (coordSphereFrameFun μ u v p) := by
  -- Proof: composition of continuous maps
  -- coordPoint u v p maps coordSphereSet ⊂ ℝ³ into Metric.sphere 0 1 ⊂ H
  -- (since ‖au+bv+cp‖² = a²+b²+c² = 1 for orthonormal u,v,p)
  -- Q = frame_quadratic μ is continuous on sphere (from hcont)
  -- spherePointCoord maps spherePoint3 into coordSphereSet
  -- The full composition is continuous.
  have hcontOnCoord :
      ContinuousOn
        (fun x : ℝ × ℝ × ℝ => frame_quadratic (H := H) μ (coordPoint u v p x))
        coordSphereSet := by
    apply ContinuousOn.comp (t := Metric.sphere (0 : H) 1) hcont
      (continuous_coordPoint u v p).continuousOn
    intro x hx
    exact Metric.mem_sphere.mpr (by
      rw [dist_zero_right]
      exact coordPoint_norm hu hv hp huv hup hvp hx)
  have hmaps : Set.MapsTo spherePointCoord (Set.univ : Set spherePoint3) coordSphereSet :=
    fun x _ => spherePointCoord_mem_coordSphereSet x
  have hcomp : ContinuousOn (coordSphereFrameFun μ u v p) Set.univ := by
    simpa [coordSphereFrameFun] using
      ContinuousOn.comp hcontOnCoord continuous_spherePointCoord.continuousOn hmaps
  simpa [continuousOn_univ] using hcomp

/-- Coord sphere as ContinuousMap using Q continuous (no zero-at-pole needed). -/
private def coordSphereFrameCMap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1))
    (u v p : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0) :
    C(spherePoint3, ℝ) :=
  ⟨coordSphereFrameFun μ u v p,
    continuous_coordSphereFrameFun_of_cont_on_sphere μ hcont hu hv hp huv hup hvp⟩

/-- The coord sphere (without zero-at-pole) is in the frame submodule. -/
private lemma coordSphereFrameCMap_mem_frame
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1))
    {u v p : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0) :
    coordSphereFrameCMap hdim μ hcont u v p hu hv hp huv hup hvp ∈
      continuousSphereFrameSubmodule := by
  show (coordSphereFrameFun μ u v p : spherePoint3 → ℝ) ∈ sphereFrameSubmodule
  exact coordSphereFrameFun_mem_sphereFrameSubmodule_osc μ hu hv hp huv hup hvp

private lemma local_defect_g_eq_zero_of_coordSphereCMap_quadratic_submodule_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1))
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hq :
      coordSphereFrameCMap hdim μ hcont u v p hu hv hp huv hup hvp ∈
        continuousSphereQuadraticSubmodule)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  rcases hq with ⟨Q, hQ⟩
  exact
    local_defect_g_eq_zero_of_coordSphere_quadraticMap
      (μ := μ) (u := u) (v := v) (p := p)
      (Q := Q)
      (by
        intro x
        simpa [coordSphereFrameCMap] using hQ x)
      t

private lemma local_defect_g_eq_zero_of_s2_frame_eq_low_of_sphere_continuous_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1))
    (hS2 :
      GleasonS2Bridge.continuousSphereFrameSubmoduleS2 =
        GleasonS2Bridge.lowSectorS2)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  have hframe :
      coordSphereFrameCMap hdim μ hcont u v p hu hv hp huv hup hvp ∈
        continuousSphereFrameSubmodule :=
    coordSphereFrameCMap_mem_frame hdim μ hcont hu hv hp huv hup hvp
  have hq :
      coordSphereFrameCMap hdim μ hcont u v p hu hv hp huv hup hvp ∈
        continuousSphereQuadraticSubmodule :=
    continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_s2_low_osc
      hS2 hframe
  exact
    local_defect_g_eq_zero_of_coordSphereCMap_quadratic_submodule_osc
      (H := H) hdim μ hcont hu hv hp huv hup hvp hq t

/-- The frame-center is invariant under ambient sphere isometries on frame functions. -/
private lemma sphereFrameCenter_spherePrecomp_eq_of_mem_continuousSphereFrameSubmodule_osc
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    sphereFrameCenter (spherePrecomp e f) = sphereFrameCenter f := by
  have hframe : IsSphereFrameFunction (f : spherePoint3 → ℝ) := hf
  have h12 :
      inner (𝕜 := ℝ) (sphereMap e sphereE1).1 (sphereMap e sphereE2).1 = 0 := by
    simpa [sphereMap_inner] using sphereE1_inner_sphereE2
  have h13 :
      inner (𝕜 := ℝ) (sphereMap e sphereE1).1 (sphereMap e sphereE3).1 = 0 := by
    simpa [sphereMap_inner] using sphereE1_inner_sphereE3
  have h23 :
      inner (𝕜 := ℝ) (sphereMap e sphereE2).1 (sphereMap e sphereE3).1 = 0 := by
    simpa [sphereMap_inner] using sphereE2_inner_sphereE3
  have hsum :=
    hframe (sphereMap e sphereE1) (sphereMap e sphereE2) (sphereMap e sphereE3) h12 h13 h23
  unfold sphereFrameCenter
  simp [spherePrecomp_apply, hsum]

/-- Centering commutes with ambient sphere isometries on frame functions. -/
private lemma sphereFrameCentered_spherePrecomp_eq_of_mem_continuousSphereFrameSubmodule_osc
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereFrameSubmodule)
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    spherePrecomp e (sphereFrameCentered f) =
      sphereFrameCentered (spherePrecomp e f) := by
  ext x
  simp [sphereFrameCentered_apply, spherePrecomp_apply,
    sphereFrameCenter_spherePrecomp_eq_of_mem_continuousSphereFrameSubmodule_osc hf e]

/-- Local oscillation continuity obligation for the active proof path. -/
private lemma continuousOn_of_geometricControl_on_sphere_osc
    {f : H → ℝ} {ρ θ C : ℝ}
    (hρ0 : 0 < ρ)
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcontrol :
      ∀ n {x y : Metric.sphere (0 : H) 1},
        dist x y < ρ ^ n → dist (f x) (f y) ≤ C * θ ^ n) :
    ContinuousOn f (Metric.sphere (0 : H) 1) := by
  rw [continuousOn_iff_continuous_restrict]
  exact
    GleasonGeometricOscillation.continuous_of_geometricControl
      (f := fun x : Metric.sphere (0 : H) 1 => f x)
      hρ0 hθ0 hθ1 <| by
        intro n x y hxy
        exact hcontrol n hxy

private lemma frame_quadratic_continuous_on_sphere_of_geometricControl_osc
    (μ : FrameFunction H) {ρ θ C : ℝ}
    (hρ0 : 0 < ρ)
    (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1)
    (hcontrol :
      ∀ n {x y : Metric.sphere (0 : H) 1},
        dist x y < ρ ^ n →
          dist (frame_quadratic (H := H) μ x) (frame_quadratic (H := H) μ y) ≤
            C * θ ^ n) :
    ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1) :=
  continuousOn_of_geometricControl_on_sphere_osc hρ0 hθ0 hθ1 hcontrol

private lemma frame_quadratic_unit_le_one_osc
    (μ : FrameFunction H) {x : H} (hx : ‖x‖ = 1) :
    frame_quadratic (H := H) μ x ≤ 1 := by
  have h := GleasonBridge.frame_quadratic_abs_le_norm_sq_local (H := H) μ x
  have hx2 : ‖x‖ ^ 2 = 1 := by
    rw [hx]
    norm_num
  have hnonneg : 0 ≤ frame_quadratic (H := H) μ x :=
    frame_quadratic_nonneg (H := H) μ x
  have habs : |frame_quadratic (H := H) μ x| =
      frame_quadratic (H := H) μ x := abs_of_nonneg hnonneg
  nlinarith

private def UniformHorizontalBridgeOscillation
    (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H} {z : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic (H := H) μ p ≤ η →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        horizontalRadius z ≠ 0 →
        dist (coordPoint u v p z) p < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p (horizontalUnitCoord z)) -
          frame_quadratic (H := H) μ (coordPoint u v p (targetBridgeCoord z))| ≤
          88 * η

private def UniformHorizontalBridgeOscillationWith
    (C : ℝ) (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H} {z : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic (H := H) μ p ≤ η →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        horizontalRadius z ≠ 0 →
        dist (coordPoint u v p z) p < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p (horizontalUnitCoord z)) -
          frame_quadratic (H := H) μ (coordPoint u v p (targetBridgeCoord z))| ≤
          C * η

private def UniformHorizontalBridgeUpperWith
    (C : ℝ) (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H} {z : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic (H := H) μ p ≤ η →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        horizontalRadius z ≠ 0 →
        dist (coordPoint u v p z) p < δ →
        frame_quadratic (H := H) μ (coordPoint u v p (horizontalUnitCoord z)) -
          frame_quadratic (H := H) μ (coordPoint u v p (targetBridgeCoord z)) ≤
          C * η

private def SmallUniformHorizontalBridgeOscillation
    (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η → η ≤ (1 : ℝ) / 90 →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H} {z : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic (H := H) μ p ≤ η →
        z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 →
        horizontalRadius z ≠ 0 →
        dist (coordPoint u v p z) p < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p (horizontalUnitCoord z)) -
          frame_quadratic (H := H) μ (coordPoint u v p (targetBridgeCoord z))| ≤
          88 * η

private def UniformPoleCapOscillation
    (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H} {x y : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic (H := H) μ p ≤ η →
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p x) -
          frame_quadratic (H := H) μ (coordPoint u v p y)| ≤
          88 * η

private def UniformPoleCapOscillationWith
    (C : ℝ) (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H} {x y : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic (H := H) μ p ≤ η →
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p x) -
          frame_quadratic (H := H) μ (coordPoint u v p y)| ≤
          C * η

private def SmallUniformPoleCapOscillation
    (μ : FrameFunction H) : Prop :=
  ∀ {η : ℝ}, 0 < η → η ≤ (1 : ℝ) / 90 →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H} {x y : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic (H := H) μ p ≤ η →
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p x) -
          frame_quadratic (H := H) μ (coordPoint u v p y)| ≤
          88 * η

private lemma exists_pole_cap_oscillation_of_large_eta
    (μ : FrameFunction H) {η : ℝ} (hη : (1 : ℝ) / 88 ≤ η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {u v p : H} {x y : ℝ × ℝ × ℝ},
        ‖u‖ = 1 → ‖v‖ = 1 → ‖p‖ = 1 →
        inner (𝕜 := ℂ) u v = 0 →
        inner (𝕜 := ℂ) u p = 0 →
        inner (𝕜 := ℂ) v p = 0 →
        frame_quadratic (H := H) μ p ≤ η →
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p x) -
          frame_quadratic (H := H) μ (coordPoint u v p y)| ≤
          88 * η := by
  refine ⟨1, by norm_num, ?_⟩
  intro u v p x y hu hv hp huv hup hvp _ hx hy _ _
  have hxnorm : ‖coordPoint u v p x‖ = 1 :=
    coordPoint_norm hu hv hp huv hup hvp hx
  have hynorm : ‖coordPoint u v p y‖ = 1 :=
    coordPoint_norm hu hv hp huv hup hvp hy
  have hx_nonneg : 0 ≤ frame_quadratic (H := H) μ (coordPoint u v p x) :=
    frame_quadratic_nonneg (H := H) μ _
  have hy_nonneg : 0 ≤ frame_quadratic (H := H) μ (coordPoint u v p y) :=
    frame_quadratic_nonneg (H := H) μ _
  have hx_le : frame_quadratic (H := H) μ (coordPoint u v p x) ≤ 1 :=
    frame_quadratic_unit_le_one_osc (H := H) μ hxnorm
  have hy_le : frame_quadratic (H := H) μ (coordPoint u v p y) ≤ 1 :=
    frame_quadratic_unit_le_one_osc (H := H) μ hynorm
  have hdiff :
      |frame_quadratic (H := H) μ (coordPoint u v p x) -
        frame_quadratic (H := H) μ (coordPoint u v p y)| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  nlinarith

private lemma small_uniform_horizontal_bridge_of_uniform_horizontal_bridge
    (μ : FrameFunction H)
    (hUniform : UniformHorizontalBridgeOscillation (H := H) μ) :
    SmallUniformHorizontalBridgeOscillation (H := H) μ := by
  intro η hη _
  exact hUniform hη

private lemma uniform_horizontal_bridge_with_of_uniform_horizontal_bridge
    (μ : FrameFunction H)
    (hUniform : UniformHorizontalBridgeOscillation (H := H) μ) :
    UniformHorizontalBridgeOscillationWith (H := H) 88 μ := by
  intro η hη
  exact hUniform hη

private lemma uniform_horizontal_bridge_upper_with_of_uniform_horizontal_bridge_with
    (μ : FrameFunction H) {C : ℝ}
    (hUniform : UniformHorizontalBridgeOscillationWith (H := H) C μ) :
    UniformHorizontalBridgeUpperWith (H := H) C μ := by
  intro η hη
  rcases hUniform hη with ⟨δ, hδ, hbridge⟩
  refine ⟨δ, hδ, ?_⟩
  intro u v p z hu hv hp huv hup hvp hpη hz hρ hzdist
  exact (abs_le.mp (hbridge hu hv hp huv hup hvp hpη hz hρ hzdist)).2

private lemma uniform_horizontal_bridge_of_uniform_pole_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hPole : UniformPoleCapOscillation (H := H) μ) :
    UniformHorizontalBridgeOscillation (H := H) μ := by
  intro η hη
  rcases hPole hη with ⟨δ, hδ, hcap⟩
  refine ⟨δ, hδ, ?_⟩
  intro u v p z hu hv hp huv hup hvp hpη hz hρ hzdist
  have hcap' :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p x) -
          frame_quadratic (H := H) μ (coordPoint u v p y)| ≤
          88 * η := by
    intro x y hx hy hdx hdy
    exact hcap hu hv hp huv hup hvp hpη hx hy hdx hdy
  exact
    horizontal_bridge_oscillation_of_pole_cap
      (H := H) hdim μ hu hv hp huv hup hvp
      (η := η) (δ := δ) hcap' hz hρ hzdist

private lemma uniform_horizontal_bridge_upper_with_of_uniform_pole_cap_with
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H) {C : ℝ}
    (hPole : UniformPoleCapOscillationWith (H := H) C μ) :
    UniformHorizontalBridgeUpperWith (H := H) C μ := by
  intro η hη
  rcases hPole hη with ⟨δ, hδ, hcap⟩
  refine ⟨δ, hδ, ?_⟩
  intro u v p z hu hv hp huv hup hvp hpη hz hρ hzdist
  have hcap' :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p x) -
          frame_quadratic (H := H) μ (coordPoint u v p y)| ≤
          C * η := by
    intro x y hx hy hdx hdy
    exact hcap hu hv hp huv hup hvp hpη hx hy hdx hdy
  exact
    horizontal_bridge_upper_of_pole_cap_bound
      (H := H) hdim μ hu hv hp huv hup hvp
      (η := η) (δ := δ) (C := C) hcap' hz hρ hzdist

private lemma small_uniform_horizontal_bridge_of_small_uniform_pole_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hPole : SmallUniformPoleCapOscillation (H := H) μ) :
    SmallUniformHorizontalBridgeOscillation (H := H) μ := by
  intro η hη hηsmall
  rcases hPole hη hηsmall with ⟨δ, hδ, hcap⟩
  refine ⟨δ, hδ, ?_⟩
  intro u v p z hu hv hp huv hup hvp hpη hz hρ hzdist
  have hcap' :
      ∀ {x y : ℝ × ℝ × ℝ},
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 →
        y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 →
        dist (coordPoint u v p x) p < δ →
        dist (coordPoint u v p y) p < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p x) -
          frame_quadratic (H := H) μ (coordPoint u v p y)| ≤
          88 * η := by
    intro x y hx hy hdx hdy
    exact hcap hu hv hp huv hup hvp hpη hx hy hdx hdy
  exact
    horizontal_bridge_oscillation_of_pole_cap
      (H := H) hdim μ hu hv hp huv hup hvp
      (η := η) (δ := δ) hcap' hz hρ hzdist

private lemma exists_zero_pole_of_sInf_zero_osc_of_uniform_horizontal_bridge_with
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ} (hC : 0 ≤ C)
    (hInf : sInf (Q_sphere_set μ) = 0)
    (hUniform : UniformHorizontalBridgeUpperWith (H := H) C μ) :
    ∃ p₀ : H, ‖p₀‖ = 1 ∧ frame_quadratic (H := H) μ p₀ = 0 := by
  haveI : ProperSpace H := FiniteDimensional.proper_rclike ℂ H
  have hcpt : IsCompact (Metric.sphere (0 : H) 1) := isCompact_sphere 0 1
  suffices h : ∀ η : ℝ, 0 < η → ∃ p₀ : H, ‖p₀‖ = 1 ∧ frame_quadratic (H := H) μ p₀ ≤ η by
    have hseq : ∀ k : ℕ, ∃ p : H, p ∈ Metric.sphere (0 : H) 1 ∧
        frame_quadratic (H := H) μ p ≤ 1 / (↑k + 1) := by
      intro k
      rcases h (1 / (↑k + 1)) (by positivity) with ⟨p, hp, hQp⟩
      exact ⟨p, by simp [Metric.mem_sphere, hp], hQp⟩
    choose pseq hpseq_mem hpseq_bound using hseq
    rcases hcpt.tendsto_subseq hpseq_mem with ⟨p₀, hp₀_mem, φ, hφ, hconv⟩
    have hp₀_norm : ‖p₀‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hp₀_mem
    refine ⟨p₀, hp₀_norm, ?_⟩
    have hQp₀_nn := frame_quadratic_nonneg (H := H) μ p₀
    suffices hle : frame_quadratic (H := H) μ p₀ ≤ 0 by linarith
    by_contra hgt
    push_neg at hgt
    have hC2_pos : 0 < C + 2 := by nlinarith
    set η₀ := frame_quadratic (H := H) μ p₀ / (C + 2) with hη₀_def
    have hη₀_pos : 0 < η₀ := by
      rw [hη₀_def]
      exact div_pos hgt hC2_pos
    have hQ_univ : ∃ K_Q : ℕ, ∀ k ≥ K_Q,
        frame_quadratic (H := H) μ (pseq (φ k)) ≤ η₀ := by
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / η₀)
      refine ⟨N, fun k hk => le_trans (hpseq_bound (φ k)) (le_of_lt ?_)⟩
      have hφk : (N : ℝ) ≤ (φ k : ℝ) :=
        Nat.cast_le.mpr (le_trans hk (hφ.id_le k))
      have hφk_pos : (0 : ℝ) < ↑(φ k) + 1 := by positivity
      have h_mul2 : 1 < η₀ * (↑(φ k) + 1) := by
        nlinarith [(div_lt_iff₀ hη₀_pos).mp hN]
      linarith [(div_lt_iff₀ hφk_pos).mpr
        (by linarith : 1 * 1 < η₀ * (↑(φ k) + 1))]
    obtain ⟨K_Q, hK_Q⟩ := hQ_univ
    rcases hUniform hη₀_pos with ⟨δ₁, hδ₁, hbridgeUniform⟩
    obtain ⟨K_dist, hK_dist⟩ := Metric.tendsto_atTop.mp hconv δ₁ hδ₁
    set k₀ := max K_Q K_dist with hk₀_def
    have hQk₀ : frame_quadratic (H := H) μ (pseq (φ k₀)) ≤ η₀ :=
      hK_Q k₀ (le_max_left _ _)
    have hpk₀_norm : ‖pseq (φ k₀)‖ = 1 := by
      have := hpseq_mem (φ k₀); rwa [Metric.mem_sphere, dist_zero_right] at this
    rcases exists_phase_coordSphere_data_of_unit hdim hpk₀_norm hp₀_norm with
      ⟨ck, uk, vk, zk, hck, huk, hvk, huvk, hukp, hvkp, hzk, hzk_nonneg, hcoordk⟩
    by_cases hzk_polar : horizontalRadius zk = 0
    · have hzk_eq_pole : zk = poleCoord :=
        eq_poleCoord_of_horizontalRadius_eq_zero_of_nonneg
          (by simpa [coordSphereSet] using hzk) hzk_polar hzk_nonneg
      have hcoord_pole : ck • p₀ = pseq (φ k₀) := by
        simpa [hzk_eq_pole, coordPoint_poleCoord] using hcoordk
      have hQ_phase :
          frame_quadratic (H := H) μ (pseq (φ k₀)) =
            frame_quadratic (H := H) μ p₀ := by
        rw [← hcoord_pole]
        exact frame_quadratic_unit_smul_eq μ hck p₀
      have hQp₀_le : frame_quadratic (H := H) μ p₀ ≤ η₀ := by
        linarith
      have hη_mul : η₀ * (C + 2) = frame_quadratic (H := H) μ p₀ := by
        rw [hη₀_def]
        field_simp [ne_of_gt hC2_pos]
      have hmul := mul_le_mul_of_nonneg_right hQp₀_le (le_of_lt hC2_pos)
      rw [hη_mul] at hmul
      nlinarith
    have hdist_phase : dist (coordPoint uk vk (pseq (φ k₀)) zk)
        (coordPoint uk vk (pseq (φ k₀)) poleCoord) ≤ dist p₀ (pseq (φ k₀)) := by
      rw [← hcoordk, coordPoint_poleCoord]
      rw [dist_eq_norm, dist_eq_norm]
      set pk := pseq (φ k₀) with hpk_def
      have hinner_ck_eq : inner (𝕜 := ℂ) (ck • p₀) pk = (zk.2.2 : ℂ) := by
        rw [show ck • p₀ = coordPoint uk vk pk zk from hcoordk, coordPoint]
        simp only [inner_add_left, inner_smul_left, hukp, hvkp, mul_zero, zero_add]
        rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hpk₀_norm]
        simp [starRingEnd_self_apply, Complex.conj_ofReal]
      have hre_p₀_le : RCLike.re (inner (𝕜 := ℂ) p₀ pk) ≤ zk.2.2 := by
        have hval : starRingEnd ℂ ck * inner (𝕜 := ℂ) p₀ pk = (zk.2.2 : ℂ) := by
          have hsml : inner (𝕜 := ℂ) (ck • p₀) pk =
              starRingEnd ℂ ck * inner (𝕜 := ℂ) p₀ pk := by
            rw [inner_smul_left]
          rw [← hsml]; exact hinner_ck_eq
        have hnorm_prod : ‖inner (𝕜 := ℂ) p₀ pk‖ = zk.2.2 := by
          have h1 : ‖starRingEnd ℂ ck * inner (𝕜 := ℂ) p₀ pk‖ = zk.2.2 := by
            rw [hval]; simp [Complex.norm_real, abs_of_nonneg hzk_nonneg]
          rwa [norm_mul, RCLike.norm_conj, hck, one_mul] at h1
        calc RCLike.re (inner (𝕜 := ℂ) p₀ pk)
            = (inner (𝕜 := ℂ) p₀ pk : ℂ).re := rfl
          _ ≤ ‖(inner (𝕜 := ℂ) p₀ pk : ℂ)‖ := Complex.re_le_norm _
          _ = zk.2.2 := hnorm_prod
      have hre_ck_eq : RCLike.re (inner (𝕜 := ℂ) (ck • p₀) pk) = zk.2.2 := by
        rw [hinner_ck_eq]; simp
      have hns1 := @norm_sub_sq ℂ H _ _ _ (ck • p₀) pk
      have hns2 := @norm_sub_sq ℂ H _ _ _ p₀ pk
      have hck_norm : ‖ck • p₀‖ = 1 := by rw [norm_smul, hck, one_mul, hp₀_norm]
      nlinarith [norm_nonneg (ck • p₀ - pk), norm_nonneg (p₀ - pk),
        sq_nonneg (‖p₀ - pk‖ - ‖ck • p₀ - pk‖),
        hns1, hns2, hck_norm, hp₀_norm, hpk₀_norm, hre_ck_eq, hre_p₀_le]
    let wk : H := coordPoint uk vk (pseq (φ k₀)) (horizontalUnitCoord zk)
    let bk : H := coordPoint uk vk (pseq (φ k₀)) (targetBridgeCoord zk)
    have hbridge_id :
        frame_quadratic (H := H) μ p₀ + frame_quadratic (H := H) μ bk =
          frame_quadratic (H := H) μ wk +
            frame_quadratic (H := H) μ (pseq (φ k₀)) := by
      have hbridge :=
        frame_quadratic_targetBridge_identity
          (H := H) hdim μ huk hvk hpk₀_norm huvk hukp hvkp hzk hzk_polar
      dsimp [wk, bk]
      rw [← hcoordk, frame_quadratic_unit_smul_eq μ hck p₀] at hbridge
      exact hbridge
    have hzk_dist_small :
        dist (coordPoint uk vk (pseq (φ k₀)) zk) (pseq (φ k₀)) < δ₁ := by
      have hpk_close : dist p₀ (pseq (φ k₀)) < δ₁ := by
        have := hK_dist k₀ (le_max_right K_Q K_dist)
        simpa [dist_comm] using this
      exact lt_of_le_of_lt (by simpa [coordPoint_poleCoord] using hdist_phase) hpk_close
    have hbridge_osc :
        frame_quadratic (H := H) μ wk -
          frame_quadratic (H := H) μ bk ≤ C * η₀ := by
      dsimp [wk, bk]
      exact hbridgeUniform huk hvk hpk₀_norm huvk hukp hvkp hQk₀ hzk hzk_polar hzk_dist_small
    have hQp₀_bound : frame_quadratic (H := H) μ p₀ ≤ (C + 1) * η₀ := by
      nlinarith [hbridge_osc, hbridge_id, hQk₀]
    have hη_mul : η₀ * (C + 2) = frame_quadratic (H := H) μ p₀ := by
      rw [hη₀_def]
      field_simp [ne_of_gt hC2_pos]
    have hmul := mul_le_mul_of_nonneg_right hQp₀_bound (le_of_lt hC2_pos)
    have hright : ((C + 1) * η₀) * (C + 2) =
        (C + 1) * (η₀ * (C + 2)) := by ring
    rw [hright, hη_mul] at hmul
    nlinarith
  intro η hη
  rcases exists_near_infimum hdim μ η hη with ⟨p₀, hp₀, hQp₀⟩
  exact ⟨p₀, hp₀, by rw [hInf] at hQp₀; linarith⟩

private lemma exists_zero_pole_of_sInf_zero_osc_of_uniform_horizontal_bridge_general
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hInf : sInf (Q_sphere_set μ) = 0)
    (hUniform : UniformHorizontalBridgeOscillation (H := H) μ) :
    ∃ p₀ : H, ‖p₀‖ = 1 ∧ frame_quadratic (H := H) μ p₀ = 0 :=
  exists_zero_pole_of_sInf_zero_osc_of_uniform_horizontal_bridge_with
    hdim μ (by norm_num : (0 : ℝ) ≤ 88) hInf
    (uniform_horizontal_bridge_upper_with_of_uniform_horizontal_bridge_with μ
      (uniform_horizontal_bridge_with_of_uniform_horizontal_bridge μ hUniform))

private lemma exists_zero_pole_of_sInf_zero_osc_of_uniform_horizontal_bridge
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hInf : sInf (Q_sphere_set μ) = 0)
    (hUniform : SmallUniformHorizontalBridgeOscillation (H := H) μ) :
    ∃ p₀ : H, ‖p₀‖ = 1 ∧ frame_quadratic (H := H) μ p₀ = 0 := by
  haveI : ProperSpace H := FiniteDimensional.proper_rclike ℂ H
  have hcpt : IsCompact (Metric.sphere (0 : H) 1) := isCompact_sphere 0 1
  suffices h : ∀ η : ℝ, 0 < η → ∃ p₀ : H, ‖p₀‖ = 1 ∧ frame_quadratic (H := H) μ p₀ ≤ η by
    have hseq : ∀ k : ℕ, ∃ p : H, p ∈ Metric.sphere (0 : H) 1 ∧
        frame_quadratic (H := H) μ p ≤ 1 / (↑k + 1) := by
      intro k
      rcases h (1 / (↑k + 1)) (by positivity) with ⟨p, hp, hQp⟩
      exact ⟨p, by simp [Metric.mem_sphere, hp], hQp⟩
    choose pseq hpseq_mem hpseq_bound using hseq
    rcases hcpt.tendsto_subseq hpseq_mem with ⟨p₀, hp₀_mem, φ, hφ, hconv⟩
    have hp₀_norm : ‖p₀‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hp₀_mem
    refine ⟨p₀, hp₀_norm, ?_⟩
    have hQp₀_nn := frame_quadratic_nonneg (H := H) μ p₀
    suffices hle : frame_quadratic (H := H) μ p₀ ≤ 0 by linarith
    by_contra hgt
    push_neg at hgt
    set η₀ := frame_quadratic (H := H) μ p₀ / 90 with hη₀_def
    have hη₀_pos : 0 < η₀ := by positivity
    have hη₀_small : η₀ ≤ (1 : ℝ) / 90 := by
      have hp₀_le_one := frame_quadratic_unit_le_one_osc (H := H) μ hp₀_norm
      rw [hη₀_def]
      nlinarith
    have hQ_univ : ∃ K_Q : ℕ, ∀ k ≥ K_Q,
        frame_quadratic (H := H) μ (pseq (φ k)) ≤ η₀ := by
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / η₀)
      refine ⟨N, fun k hk => le_trans (hpseq_bound (φ k)) (le_of_lt ?_)⟩
      have hφk : (N : ℝ) ≤ (φ k : ℝ) :=
        Nat.cast_le.mpr (le_trans hk (hφ.id_le k))
      have hφk_pos : (0 : ℝ) < ↑(φ k) + 1 := by positivity
      have h_mul2 : 1 < η₀ * (↑(φ k) + 1) := by
        nlinarith [(div_lt_iff₀ hη₀_pos).mp hN]
      linarith [(div_lt_iff₀ hφk_pos).mpr (by linarith : 1 * 1 < η₀ * (↑(φ k) + 1))]
    obtain ⟨K_Q, hK_Q⟩ := hQ_univ
    rcases hUniform hη₀_pos hη₀_small with ⟨δ₁, hδ₁, hbridgeUniform⟩
    obtain ⟨K_dist, hK_dist⟩ := Metric.tendsto_atTop.mp hconv δ₁ hδ₁
    set k₀ := max K_Q K_dist with hk₀_def
    have hQk₀ : frame_quadratic (H := H) μ (pseq (φ k₀)) ≤ η₀ :=
      hK_Q k₀ (le_max_left _ _)
    have hpk₀_norm : ‖pseq (φ k₀)‖ = 1 := by
      have := hpseq_mem (φ k₀); rwa [Metric.mem_sphere, dist_zero_right] at this
    rcases exists_phase_coordSphere_data_of_unit hdim hpk₀_norm hp₀_norm with
      ⟨ck, uk, vk, zk, hck, huk, hvk, huvk, hukp, hvkp, hzk, hzk_nonneg, hcoordk⟩
    by_cases hzk_polar : horizontalRadius zk = 0
    · have hzk_eq_pole : zk = poleCoord :=
        eq_poleCoord_of_horizontalRadius_eq_zero_of_nonneg
          (by simpa [coordSphereSet] using hzk) hzk_polar hzk_nonneg
      have hcoord_pole : ck • p₀ = pseq (φ k₀) := by
        simpa [hzk_eq_pole, coordPoint_poleCoord] using hcoordk
      have hQ_phase :
          frame_quadratic (H := H) μ (pseq (φ k₀)) =
            frame_quadratic (H := H) μ p₀ := by
        rw [← hcoord_pole]
        exact frame_quadratic_unit_smul_eq μ hck p₀
      have hQp₀_le : frame_quadratic (H := H) μ p₀ ≤ η₀ := by
        linarith
      linarith
    have hdist_phase : dist (coordPoint uk vk (pseq (φ k₀)) zk)
        (coordPoint uk vk (pseq (φ k₀)) poleCoord) ≤ dist p₀ (pseq (φ k₀)) := by
      rw [← hcoordk, coordPoint_poleCoord]
      rw [dist_eq_norm, dist_eq_norm]
      set pk := pseq (φ k₀) with hpk_def
      have hinner_ck_eq : inner (𝕜 := ℂ) (ck • p₀) pk = (zk.2.2 : ℂ) := by
        rw [show ck • p₀ = coordPoint uk vk pk zk from hcoordk, coordPoint]
        simp only [inner_add_left, inner_smul_left, hukp, hvkp, mul_zero, zero_add]
        rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), hpk₀_norm]
        simp [starRingEnd_self_apply, Complex.conj_ofReal]
      have hre_p₀_le : RCLike.re (inner (𝕜 := ℂ) p₀ pk) ≤ zk.2.2 := by
        have hval : starRingEnd ℂ ck * inner (𝕜 := ℂ) p₀ pk = (zk.2.2 : ℂ) := by
          have hsml : inner (𝕜 := ℂ) (ck • p₀) pk =
              starRingEnd ℂ ck * inner (𝕜 := ℂ) p₀ pk := by
            rw [inner_smul_left]
          rw [← hsml]; exact hinner_ck_eq
        have hnorm_prod : ‖inner (𝕜 := ℂ) p₀ pk‖ = zk.2.2 := by
          have h1 : ‖starRingEnd ℂ ck * inner (𝕜 := ℂ) p₀ pk‖ = zk.2.2 := by
            rw [hval]; simp [Complex.norm_real, abs_of_nonneg hzk_nonneg]
          rwa [norm_mul, RCLike.norm_conj, hck, one_mul] at h1
        calc RCLike.re (inner (𝕜 := ℂ) p₀ pk)
            = (inner (𝕜 := ℂ) p₀ pk : ℂ).re := rfl
          _ ≤ ‖(inner (𝕜 := ℂ) p₀ pk : ℂ)‖ := Complex.re_le_norm _
          _ = zk.2.2 := hnorm_prod
      have hre_ck_eq : RCLike.re (inner (𝕜 := ℂ) (ck • p₀) pk) = zk.2.2 := by
        rw [hinner_ck_eq]; simp
      have hns1 := @norm_sub_sq ℂ H _ _ _ (ck • p₀) pk
      have hns2 := @norm_sub_sq ℂ H _ _ _ p₀ pk
      have hck_norm : ‖ck • p₀‖ = 1 := by rw [norm_smul, hck, one_mul, hp₀_norm]
      nlinarith [norm_nonneg (ck • p₀ - pk), norm_nonneg (p₀ - pk),
        sq_nonneg (‖p₀ - pk‖ - ‖ck • p₀ - pk‖),
        hns1, hns2, hck_norm, hp₀_norm, hpk₀_norm, hre_ck_eq, hre_p₀_le]
    let wk : H := coordPoint uk vk (pseq (φ k₀)) (horizontalUnitCoord zk)
    let bk : H := coordPoint uk vk (pseq (φ k₀)) (targetBridgeCoord zk)
    have hbridge_id :
        frame_quadratic (H := H) μ p₀ + frame_quadratic (H := H) μ bk =
          frame_quadratic (H := H) μ wk +
            frame_quadratic (H := H) μ (pseq (φ k₀)) := by
      have hbridge :=
        frame_quadratic_targetBridge_identity
          (H := H) hdim μ huk hvk hpk₀_norm huvk hukp hvkp hzk hzk_polar
      dsimp [wk, bk]
      rw [← hcoordk, frame_quadratic_unit_smul_eq μ hck p₀] at hbridge
      exact hbridge
    have hzk_dist_small :
        dist (coordPoint uk vk (pseq (φ k₀)) zk) (pseq (φ k₀)) < δ₁ := by
      have hpk_close : dist p₀ (pseq (φ k₀)) < δ₁ := by
        have := hK_dist k₀ (le_max_right K_Q K_dist)
        simpa [dist_comm] using this
      exact lt_of_le_of_lt (by simpa [coordPoint_poleCoord] using hdist_phase) hpk_close
    have hbridge_osc :
        |frame_quadratic (H := H) μ wk -
          frame_quadratic (H := H) μ bk| ≤ 88 * η₀ := by
      dsimp [wk, bk]
      exact hbridgeUniform huk hvk hpk₀_norm huvk hukp hvkp hQk₀ hzk hzk_polar hzk_dist_small
    have hQp₀_bound : frame_quadratic (H := H) μ p₀ ≤ 89 * η₀ := by
      have hab := hbridge_osc
      rw [abs_le] at hab
      linarith [hab.2, hbridge_id, hQk₀]
    linarith
  intro η hη
  rcases exists_near_infimum hdim μ η hη with ⟨p₀, hp₀, hQp₀⟩
  exact ⟨p₀, hp₀, by rw [hInf] at hQp₀; linarith⟩

private lemma exists_zero_pole_of_sInf_zero_osc_of_uniform_pole_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hInf : sInf (Q_sphere_set μ) = 0)
    (hPole : UniformPoleCapOscillation (H := H) μ) :
    ∃ p₀ : H, ‖p₀‖ = 1 ∧ frame_quadratic (H := H) μ p₀ = 0 :=
  exists_zero_pole_of_sInf_zero_osc_of_uniform_horizontal_bridge
    hdim μ hInf <|
      small_uniform_horizontal_bridge_of_uniform_horizontal_bridge μ
        (uniform_horizontal_bridge_of_uniform_pole_cap hdim μ hPole)

private lemma exists_zero_pole_of_sInf_zero_osc_of_uniform_pole_cap_with
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ} (hC : 0 ≤ C)
    (hInf : sInf (Q_sphere_set μ) = 0)
    (hPole : UniformPoleCapOscillationWith (H := H) C μ) :
    ∃ p₀ : H, ‖p₀‖ = 1 ∧ frame_quadratic (H := H) μ p₀ = 0 :=
  exists_zero_pole_of_sInf_zero_osc_of_uniform_horizontal_bridge_with
    hdim μ hC hInf
    (uniform_horizontal_bridge_upper_with_of_uniform_pole_cap_with hdim μ hPole)

private lemma uniform_pole_cap_with_of_bound
    (μ : FrameFunction H) {C : ℝ}
    (hPole : UniformPoleCapOscillationBound (H := H) C μ) :
    UniformPoleCapOscillationWith (H := H) C μ := by
  intro η hη
  rcases hPole hη with ⟨δ, hδ, hcap⟩
  refine ⟨δ, hδ, ?_⟩
  intro u v p x y hu hv hp huv hup hvp hpη hx hy hdx hdy
  exact hcap hu hv hp huv hup hvp hpη hx hy hdx hdy

private lemma exists_zero_pole_of_sInf_zero_osc_of_endpoint_trace_near_with
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ} (hC : 0 ≤ C)
    (hInf : sInf (Q_sphere_set μ) = 0)
    (hTrace : EndpointTraceNearInfimumWith C μ) :
    ∃ p₀ : H, ‖p₀‖ = 1 ∧ frame_quadratic (H := H) μ p₀ = 0 := by
  have hPoleBound :
      UniformPoleCapOscillationBound (H := H)
        (3 * (22 * (C + 2) + 88)) μ :=
    uniform_pole_cap_of_trace_near_with hdim μ hC hTrace
  have hPole :
      UniformPoleCapOscillationWith (H := H)
        (3 * (22 * (C + 2) + 88)) μ :=
    uniform_pole_cap_with_of_bound μ hPoleBound
  have hConst : 0 ≤ 3 * (22 * (C + 2) + 88) := by nlinarith
  exact
    exists_zero_pole_of_sInf_zero_osc_of_uniform_pole_cap_with
      hdim μ hConst hInf hPole

private lemma exists_zero_pole_of_sInf_zero_osc_of_endpoint_rotated_targetBridge_near_with
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    {C : ℝ} (hC : 0 ≤ C)
    (hInf : sInf (Q_sphere_set μ) = 0)
    (hRot : EndpointRotatedTargetBridgeNearInfimumWith C μ) :
    ∃ p₀ : H, ‖p₀‖ = 1 ∧ frame_quadratic (H := H) μ p₀ = 0 := by
  have hPoleBound :
      UniformPoleCapOscillationBound (H := H)
        (3 * (22 * (C + 4) + 88)) μ :=
    uniform_pole_cap_of_rotated_targetBridge_near_with hdim μ hC hRot
  have hPole :
      UniformPoleCapOscillationWith (H := H)
        (3 * (22 * (C + 4) + 88)) μ :=
    uniform_pole_cap_with_of_bound μ hPoleBound
  have hConst : 0 ≤ 3 * (22 * (C + 4) + 88) := by nlinarith
  exact
    exists_zero_pole_of_sInf_zero_osc_of_uniform_pole_cap_with
      hdim μ hConst hInf hPole

private lemma exists_zero_pole_of_sInf_zero_osc_of_small_uniform_pole_cap
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hInf : sInf (Q_sphere_set μ) = 0)
    (hPole : SmallUniformPoleCapOscillation (H := H) μ) :
    ∃ p₀ : H, ‖p₀‖ = 1 ∧ frame_quadratic (H := H) μ p₀ = 0 :=
  exists_zero_pole_of_sInf_zero_osc_of_uniform_horizontal_bridge
    hdim μ hInf (small_uniform_horizontal_bridge_of_small_uniform_pole_cap hdim μ hPole)

/-- Local `S²` bad-degree projector preservation needed by the spectral route. -/
private theorem ambientSectorProjectionContinuous_eq_zero_of_odd_mem_frame_osc
    {n : ℕ} (hnodd : Odd n) {f : C(S2, ℝ)}
    (hf : f ∈ GleasonS2Bridge.continuousSphereFrameSubmoduleS2) :
    ambientSectorProjectionContinuous n f = 0 := by
  have hcompf :
      Rotation.compContinuous GleasonS2Bridge.antipodeRotation f = f := by
    ext x
    simpa [Rotation.compContinuous_apply, GleasonS2Bridge.s2Antipode,
      GleasonS2Bridge.antipodeRotation] using
      GleasonS2Bridge.mem_continuousSphereFrameSubmoduleS2_even hf x
  have hcomp_proj :
      Rotation.compContinuous GleasonS2Bridge.antipodeRotation
          (ambientSectorProjectionContinuous n f) =
        ambientSectorProjectionContinuous n f := by
    calc
      Rotation.compContinuous GleasonS2Bridge.antipodeRotation
          (ambientSectorProjectionContinuous n f)
          =
            ambientSectorProjectionContinuous n
              (Rotation.compContinuous GleasonS2Bridge.antipodeRotation f) := by
                symm
                simpa using
                  GleasonS2Bridge.ambientSectorProjectionContinuous_compContinuous
                    GleasonS2Bridge.antipodeRotation n f
      _ = ambientSectorProjectionContinuous n f := by rw [hcompf]
  have hsector :
      ambientSectorProjectionContinuous n f ∈ sector n :=
    sectorProjectionContinuous_apply_mem n f
  have hodd_action :
      Rotation.compContinuous GleasonS2Bridge.antipodeRotation
          (ambientSectorProjectionContinuous n f) =
        (-1 : ℝ) ^ n • ambientSectorProjectionContinuous n f :=
    GleasonS2Bridge.sector_compContinuous_antipode hsector
  have hsign : (-1 : ℝ) ^ n = (-1 : ℝ) := by
    rcases hnodd with ⟨k, hk⟩
    simp [hk, pow_add, mul_comm, mul_left_comm, mul_assoc]
  have hneg :
      ambientSectorProjectionContinuous n f =
        -ambientSectorProjectionContinuous n f := by
    calc
      ambientSectorProjectionContinuous n f
          = Rotation.compContinuous GleasonS2Bridge.antipodeRotation
              (ambientSectorProjectionContinuous n f) := by
              symm
              exact hcomp_proj
      _ = (-1 : ℝ) ^ n • ambientSectorProjectionContinuous n f := hodd_action
      _ = -ambientSectorProjectionContinuous n f := by simp [hsign]
  ext x
  have hx :=
    congrArg (fun g : C(S2, ℝ) => g x) hneg
  have hx' :
      (ambientSectorProjectionContinuous n f) x =
        -((ambientSectorProjectionContinuous n f) x) := by
    simpa using hx
  have hx0 : 2 * ((ambientSectorProjectionContinuous n f) x) = 0 := by
    linarith
  have hxzero : ((ambientSectorProjectionContinuous n f) x) = 0 := by
    nlinarith [hx0]
  simpa [hxzero]

private theorem
    s2PoleAverageContinuousOfPointConstraint_mem_northFixedSubmodule_osc
    {g : C(S2, ℝ)}
    (hgpc : g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgnorth : g ∈ northFixedSubmodule) :
    GleasonS2Bridge.s2PoleAverageContinuousOfGreatCircleConstraint g
        (by
          have hframe : g ∈ GleasonS2Bridge.continuousSphereFrameSubmoduleS2 := by
            simpa [GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
              using hgpc
          exact
            GleasonS2Bridge.continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
              hframe) ∈ northFixedSubmodule := by
  rw [mem_northFixedSubmodule_iff]
  intro t
  ext z
  rw [Rotation.compContinuous_apply]
  repeat rw [GleasonS2Bridge.s2PoleAverageContinuousOfGreatCircleConstraint_apply]
  have hrot :=
    congrArg (fun h : C(S2, ℝ) => h z) ((mem_northFixedSubmodule_iff g).1 hgnorth t)
  simp only [Rotation.compContinuous_apply] at hrot
  rw [hrot]

private theorem
    s2PoleAverageContinuousOfPointConstraint_eq_neg_half_of_center_zero_osc
    {g : C(S2, ℝ)}
    (hgpc : g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgcenter : sphereFrameCenter (GleasonS2Bridge.s2Pullback g) = 0) :
    GleasonS2Bridge.s2PoleAverageContinuousOfGreatCircleConstraint g
        (by
          have hframe : g ∈ GleasonS2Bridge.continuousSphereFrameSubmoduleS2 := by
            simpa
              [GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
              using hgpc
          exact
            GleasonS2Bridge.continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
              hframe) =
      (-((1 / 2 : ℝ))) • g := by
  ext z
  rw [GleasonS2Bridge.s2PoleAverageContinuousOfGreatCircleConstraint_apply]
  rw [hgcenter]
  simp
  ring

private theorem
    exists_centered_northFixed_pointConstraint_witness_even_osc
    {n : ℕ} (hn0 : n ≠ 0)
    (hw :
      ∃ g : C(S2, ℝ),
        g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2 ∧
        g ∈ northFixedSubmodule ∧
        ambientSectorProjectionContinuous n g =
          ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))) :
    ∃ g : C(S2, ℝ),
      g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2 ∧
      g ∈ northFixedSubmodule ∧
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) ∧
      sphereFrameCenter (GleasonS2Bridge.s2Pullback g) = 0 := by
  rcases hw with ⟨g, hgpc, hgnorth, hgproj⟩
  let c : ℝ := sphereFrameCenter (GleasonS2Bridge.s2Pullback g)
  let g0 : C(S2, ℝ) := g - ContinuousMap.const _ c
  have hconstpc : ContinuousMap.const _ c ∈
      GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2 := by
    have hconstframe : ContinuousMap.const _ c ∈
        GleasonS2Bridge.continuousSphereFrameSubmoduleS2 := by
      show GleasonS2Bridge.s2Pullback (ContinuousMap.const _ c) ∈
          continuousSphereFrameSubmodule
      intro x y z hxy hxz hyz
      simp
    simpa [GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
      using hconstframe
  have hg0pc : g0 ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2 := by
    exact Submodule.sub_mem _ hgpc hconstpc
  have hconstnorth : ContinuousMap.const _ c ∈ northFixedSubmodule := by
    rw [mem_northFixedSubmodule_iff]
    intro t
    ext z
    simp [Rotation.compContinuous_apply]
  have hg0north : g0 ∈ northFixedSubmodule := by
    exact Submodule.sub_mem _ hgnorth hconstnorth
  have hg0proj :
      ambientSectorProjectionContinuous n g0 =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) := by
    have hconst0 :
        ambientSectorProjectionContinuous n (ContinuousMap.const _ c) = 0 := by
      simpa using
        GleasonS2Bridge.ambientSectorProjectionContinuous_const_eq_zero_of_ne_zero hn0 c
    calc
      ambientSectorProjectionContinuous n g0
          = ambientSectorProjectionContinuous n g -
              ambientSectorProjectionContinuous n (ContinuousMap.const _ c) := by
              simp [g0]
      _ = ambientSectorProjectionContinuous n g := by rw [hconst0, sub_zero]
      _ = ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) := hgproj
  have hg0center : sphereFrameCenter (GleasonS2Bridge.s2Pullback g0) = 0 := by
    dsimp [g0, c]
    simp [GleasonS2Bridge.s2Pullback_apply, sphereFrameCenter, sub_eq_add_neg]
    ring
  exact ⟨g0, hg0pc, hg0north, hg0proj, hg0center⟩

private theorem
    poleAverageLinear_eq_neg_half_of_center_zero_pointConstraint_osc
    {g : C(S2, ℝ)}
    (hgpc : g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgcenter : sphereFrameCenter (GleasonS2Bridge.s2Pullback g) = 0) :
    poleAverageLinear (GleasonS2Bridge.s2Pullback g) =
      (-((1 / 2 : ℝ))) • GleasonS2Bridge.s2Pullback g := by
  have hframe : g ∈ GleasonS2Bridge.continuousSphereFrameSubmoduleS2 := by
    simpa
      [GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
      using hgpc
  have hframePull :
      GleasonS2Bridge.s2Pullback g ∈ continuousSphereFrameSubmodule := by
    simpa using hframe
  have hcentered :
      sphereFrameCentered (GleasonS2Bridge.s2Pullback g) =
        GleasonS2Bridge.s2Pullback g := by
    ext z
    simp [sphereFrameCentered_apply, hgcenter]
  ext z
  have hpole :=
    poleAverageLinear_centered_of_mem_continuousSphereFrameSubmodule hframePull z
  rw [hcentered] at hpole
  change poleAverageLinear (GleasonS2Bridge.s2Pullback g) z =
    (-((1 / 2 : ℝ))) * (GleasonS2Bridge.s2Pullback g z)
  calc
    poleAverageLinear (GleasonS2Bridge.s2Pullback g) z
      = -((GleasonS2Bridge.s2Pullback g) z) / 2 := hpole
    _ = (-((1 / 2 : ℝ))) * (GleasonS2Bridge.s2Pullback g z) := by
      ring

private theorem
    specialTriple_sum_eq_zero_of_center_zero_pointConstraint_osc
    {g : C(S2, ℝ)}
    (hgpc : g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgcenter : sphereFrameCenter (GleasonS2Bridge.s2Pullback g) = 0) :
    ∀ r : Set.Icc (0 : ℝ) 1,
      (GleasonS2Bridge.s2Pullback g) (specialZPoint r) +
        (GleasonS2Bridge.s2Pullback g) (specialXPoint r) +
        (GleasonS2Bridge.s2Pullback g) sphereE2 = 0 := by
  intro r
  have hpull :
      GleasonS2Bridge.s2Pullback g ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
    simpa using
      (GleasonS2Bridge.mem_continuousSphereGreatCirclePointConstraintSubmoduleS2_iff g).1 hgpc
  have hconstraint :
      2 *
          greatCircleAverageLinear
            (specialXPoint r) sphereE2 (specialZPoint r)
            (specialXPoint_inner_sphereE2 r)
            (specialXPoint_inner_specialZPoint r)
            (sphereE2_inner_specialZPoint r)
            (GleasonS2Bridge.s2Pullback g) =
        (GleasonS2Bridge.s2Pullback g) (specialXPoint r) +
          (GleasonS2Bridge.s2Pullback g) sphereE2 := by
    exact
      (mem_continuousSphereGreatCirclePointConstraintSubmodule_iff
          (GleasonS2Bridge.s2Pullback g)).1 hpull
        (specialXPoint r) sphereE2 (specialZPoint r)
        (specialXPoint_inner_sphereE2 r)
        (specialXPoint_inner_specialZPoint r)
        (sphereE2_inner_specialZPoint r)
  have hpole_eval :=
    congrArg
      (fun F : spherePoint3 → ℝ => F (specialZPoint r))
      (poleAverageLinear_eq_neg_half_of_center_zero_pointConstraint_osc hgpc hgcenter)
  have hpole_eval' :
      greatCircleAverageLinear
          (specialXPoint r) sphereE2 (specialZPoint r)
          (specialXPoint_inner_sphereE2 r)
          (specialXPoint_inner_specialZPoint r)
          (sphereE2_inner_specialZPoint r)
          (GleasonS2Bridge.s2Pullback g) =
        (-((1 / 2 : ℝ))) * (GleasonS2Bridge.s2Pullback g) (specialZPoint r) := by
    simpa [poleAverageLinear_eq_greatCircleAverageLinear
      (GleasonS2Bridge.s2Pullback g)
      (specialXPoint r) sphereE2 (specialZPoint r)
      (specialXPoint_inner_sphereE2 r)
      (specialXPoint_inner_specialZPoint r)
      (sphereE2_inner_specialZPoint r)] using hpole_eval
  linarith

private theorem
    sphereE1_eq_neg_half_sphereE3_of_center_zero_pointConstraint_northFixed_osc
    {g : C(S2, ℝ)}
    (hgpc : g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgnorth : g ∈ northFixedSubmodule)
    (hgcenter : sphereFrameCenter (GleasonS2Bridge.s2Pullback g) = 0) :
    (GleasonS2Bridge.s2Pullback g) sphereE1 =
      (-((1 / 2 : ℝ))) * (GleasonS2Bridge.s2Pullback g) sphereE3 := by
  have hhz :
      IsNorthZonal (GleasonS2Bridge.s2Pullback g) := by
    exact
      GleasonS2Bridge.isNorthZonal_s2Pullback_of_mem_northFixedSubmodule
        (by simpa using hgnorth)
  have havg :
      northEquatorAverageLinear (GleasonS2Bridge.s2Pullback g) =
        (GleasonS2Bridge.s2Pullback g) sphereE1 := by
    exact northEquatorAverageLinear_eq_of_isNorthZonal hhz
  have hpole_eval :
      poleAverageLinear (GleasonS2Bridge.s2Pullback g) sphereE3 =
        (-((1 / 2 : ℝ))) * (GleasonS2Bridge.s2Pullback g) sphereE3 := by
    have hpole_eval :=
      congrArg
        (fun F : spherePoint3 → ℝ => F sphereE3)
        (poleAverageLinear_eq_neg_half_of_center_zero_pointConstraint_osc hgpc hgcenter)
    simpa [Pi.smul_apply] using hpole_eval
  calc
    (GleasonS2Bridge.s2Pullback g) sphereE1
        = northEquatorAverageLinear (GleasonS2Bridge.s2Pullback g) := by
            symm
            exact havg
    _ = poleAverageLinear (GleasonS2Bridge.s2Pullback g) sphereE3 := by
          rw [poleAverageLinear_sphereE3]
    _ = (-((1 / 2 : ℝ))) * (GleasonS2Bridge.s2Pullback g) sphereE3 := hpole_eval

private theorem
    northOrbitAverage_sphereE1_osc
    (f : C(spherePoint3, ℝ)) :
    northOrbitAverage f sphereE1 = northEquatorAverageLinear f := by
  rw [northOrbitAverage_apply, northEquatorAverageLinear_apply]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  have hsphereE1 : sphereE1 = equatorSpherePoint 0 := by
    apply Subtype.ext
    simp [sphereE1, equatorSpherePoint]
  have hE1 : sphereMap (northRotation t) sphereE1 = equatorSpherePoint t := by
    calc
      sphereMap (northRotation t) sphereE1
          = sphereMap (northRotation t) (equatorSpherePoint 0) := by rw [hsphereE1]
      _ = equatorSpherePoint (0 + t) := by
            simpa using sphereMap_northRotation_equatorSpherePoint t 0
      _ = equatorSpherePoint t := by simp
  simpa [hE1]

private theorem
    harmonicDegreeProjectionContinuous_northOrbitAverage_osc
    (n : ℕ) (f : C(spherePoint3, ℝ)) :
    GleasonS2Bridge.harmonicDegreeProjectionContinuous n (northOrbitAverage f) =
      northOrbitAverage (GleasonS2Bridge.harmonicDegreeProjectionContinuous n f) := by
  let A : C(spherePoint3, ℝ) →L[ℝ] C(spherePoint3, ℝ) :=
    GleasonS2Bridge.harmonicDegreeProjectionContinuousCLM n
  have hcomm :=
    (ContinuousLinearMap.intervalIntegral_comp_comm A
      (northRotationOrbit_intervalIntegrable f)).symm
  have hs2north :
      ∀ t : ℝ,
        GleasonS2Bridge.s2Pullback.symm (spherePrecomp (northRotation t) f) =
          Rotation.compContinuous (rotation01 t) (GleasonS2Bridge.s2Pullback.symm f) := by
    intro t
    apply GleasonS2Bridge.s2Pullback.injective
    calc
      GleasonS2Bridge.s2Pullback
          (GleasonS2Bridge.s2Pullback.symm (spherePrecomp (northRotation t) f))
          = spherePrecomp (northRotation t) f :=
        LinearEquiv.apply_symm_apply GleasonS2Bridge.s2Pullback
          (spherePrecomp (northRotation t) f)
      _ =
          GleasonS2Bridge.s2Pullback
            (Rotation.compContinuous (rotation01 t)
              (GleasonS2Bridge.s2Pullback.symm f)) := by
            symm
            simpa using
              GleasonS2Bridge.s2Pullback_compContinuous_rotation01 t
                (GleasonS2Bridge.s2Pullback.symm f)
  calc
    GleasonS2Bridge.harmonicDegreeProjectionContinuous n (northOrbitAverage f)
        = A (northOrbitAverage f) := by
            simpa [A] using
              (GleasonS2Bridge.harmonicDegreeProjectionContinuousCLM_apply
                n (northOrbitAverage f)).symm
    _ =
        ((2 * Real.pi)⁻¹ : ℝ) •
          A (∫ t in 0..2 * Real.pi, spherePrecomp (northRotation t) f) := by
            simp [northOrbitAverage, A]
    _ =
        ((2 * Real.pi)⁻¹ : ℝ) •
          ∫ t in 0..2 * Real.pi, A (spherePrecomp (northRotation t) f) := by
            rw [hcomm]
    _ =
        ((2 * Real.pi)⁻¹ : ℝ) •
          ∫ t in 0..2 * Real.pi,
            spherePrecomp (northRotation t)
              (GleasonS2Bridge.harmonicDegreeProjectionContinuous n f) := by
              congr 2
              funext t
              calc
                A (spherePrecomp (northRotation t) f)
                    =
                      GleasonS2Bridge.harmonicDegreeProjectionContinuous n
                        (spherePrecomp (northRotation t) f) := by
                          simpa [A] using
                            (GleasonS2Bridge.harmonicDegreeProjectionContinuousCLM_apply
                              n (spherePrecomp (northRotation t) f)).symm
                _ =
                      spherePrecomp (northRotation t)
                        (GleasonS2Bridge.harmonicDegreeProjectionContinuous n f) := by
                      rw [GleasonS2Bridge.harmonicDegreeProjectionContinuous_apply, hs2north t]
                      rw [SphericalHarmonics.ambientSectorProjectionContinuous_compContinuous]
                      simpa [GleasonS2Bridge.harmonicDegreeProjectionContinuous] using
                        GleasonS2Bridge.s2Pullback_compContinuous_rotation01 t
                          (ambientSectorProjectionContinuous n
                            (GleasonS2Bridge.s2Pullback.symm f))
    _ = northOrbitAverage (GleasonS2Bridge.harmonicDegreeProjectionContinuous n f) := by
          simp [northOrbitAverage]

private theorem
    poleAverageLinear_harmonicDegreeProjectionContinuous_sphereE3_eq_projected_northAxisAverage_osc
    (n : ℕ) (f : C(S2, ℝ)) :
    poleAverageLinear
        (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
          (GleasonS2Bridge.s2Pullback f))
        sphereE3 =
      northAxisAverage (ambientSectorProjectionContinuous n f) GleasonS2Bridge.s2E1 := by
  calc
    poleAverageLinear
        (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
          (GleasonS2Bridge.s2Pullback f))
        sphereE3
        = northOrbitAverage
            (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
              (GleasonS2Bridge.s2Pullback f))
            sphereE1 := by
            rw [poleAverageLinear_sphereE3]
            rw [northOrbitAverage_sphereE1_osc]
    _ =
        GleasonS2Bridge.harmonicDegreeProjectionContinuous n
          (northOrbitAverage (GleasonS2Bridge.s2Pullback f))
          sphereE1 := by
          rw [harmonicDegreeProjectionContinuous_northOrbitAverage_osc]
    _ =
        GleasonS2Bridge.harmonicDegreeProjectionContinuous n
          (GleasonS2Bridge.s2Pullback (northAxisAverage f))
          sphereE1 := by
          rw [GleasonS2Bridge.s2Pullback_northAxisAverage]
    _ =
        GleasonS2Bridge.s2Pullback
          (ambientSectorProjectionContinuous n (northAxisAverage f))
          sphereE1 := by
          simp [GleasonS2Bridge.harmonicDegreeProjectionContinuous]
    _ =
        ambientSectorProjectionContinuous n (northAxisAverage f)
          GleasonS2Bridge.s2E1 := by
          rw [GleasonS2Bridge.s2Pullback_s2E1]
    _ =
        northAxisAverage (ambientSectorProjectionContinuous n f)
          GleasonS2Bridge.s2E1 := by
          rw [GleasonS2Bridge.ambientSectorProjectionContinuous_northAxisAverage]

private theorem
    poleAverageLinear_specialZ_eq_northOrbitAverage_precomp_sphereE1_osc
    (f : C(spherePoint3, ℝ))
    (r : Set.Icc (0 : ℝ) 1) :
    poleAverageLinear f (specialZPoint r) =
      northOrbitAverage
        (spherePrecomp
          (sphereTripleIsometryEquiv
            (specialXPoint r) sphereE2 (specialZPoint r)
            (specialXPoint_inner_sphereE2 r)
            (specialXPoint_inner_specialZPoint r)
            (sphereE2_inner_specialZPoint r))
          f)
        sphereE1 := by
  rw [poleAverageLinear_eq_greatCircleAverageLinear
    f (specialXPoint r) sphereE2 (specialZPoint r)
    (specialXPoint_inner_sphereE2 r)
    (specialXPoint_inner_specialZPoint r)
    (sphereE2_inner_specialZPoint r)]
  rw [northOrbitAverage_sphereE1_osc]
  rw [greatCircleAverageLinear_apply]

private theorem
    northOrbitAverage_precomp_specialZ_endpoints_osc
    (f : C(spherePoint3, ℝ))
    (r : Set.Icc (0 : ℝ) 1) :
    let e :=
      sphereTripleIsometryEquiv
        (specialXPoint r) sphereE2 (specialZPoint r)
        (specialXPoint_inner_sphereE2 r)
        (specialXPoint_inner_specialZPoint r)
        (sphereE2_inner_specialZPoint r)
    northOrbitAverage (spherePrecomp e f) sphereE1 = poleAverageLinear f (specialZPoint r) ∧
      northOrbitAverage (spherePrecomp e f) sphereE3 = f (specialZPoint r) := by
  dsimp
  constructor
  · symm
    exact poleAverageLinear_specialZ_eq_northOrbitAverage_precomp_sphereE1_osc f r
  · rw [northOrbitAverage_sphereE3]
    simp

private theorem
    poleAverageLinear_specialZ_eq_rotated_northAxisAverage_s2E1_osc
    (f : C(S2, ℝ))
    (r : Set.Icc (0 : ℝ) 1) :
    poleAverageLinear (GleasonS2Bridge.s2Pullback f) (specialZPoint r) =
      northAxisAverage
        (Rotation.compContinuous
          (GleasonProjectionStability.rotationOfSpherePrecomp
            (sphereTripleIsometryEquiv
              (specialXPoint r) sphereE2 (specialZPoint r)
              (specialXPoint_inner_sphereE2 r)
              (specialXPoint_inner_specialZPoint r)
              (sphereE2_inner_specialZPoint r))) f)
        GleasonS2Bridge.s2E1 := by
  let e :=
    sphereTripleIsometryEquiv
      (specialXPoint r) sphereE2 (specialZPoint r)
      (specialXPoint_inner_sphereE2 r)
      (specialXPoint_inner_specialZPoint r)
      (sphereE2_inner_specialZPoint r)
  let ρ := GleasonProjectionStability.rotationOfSpherePrecomp e
  change
      poleAverageLinear (GleasonS2Bridge.s2Pullback f) (specialZPoint r) =
        northAxisAverage (Rotation.compContinuous ρ f) GleasonS2Bridge.s2E1
  have hpre :
      spherePrecomp e (GleasonS2Bridge.s2Pullback f) =
        GleasonS2Bridge.s2Pullback
          (Rotation.compContinuous ρ f) := by
    symm
    simpa [e, ρ, GleasonProjectionStability.ambientRotation_rotationOfSpherePrecomp] using
      GleasonS2Bridge.s2Pullback_compContinuous_eq_spherePrecomp_ambientRotation
        ρ f
  calc
    poleAverageLinear (GleasonS2Bridge.s2Pullback f) (specialZPoint r)
        =
          northOrbitAverage
            (spherePrecomp e (GleasonS2Bridge.s2Pullback f))
            sphereE1 := by
              simpa [e] using
                (poleAverageLinear_specialZ_eq_northOrbitAverage_precomp_sphereE1_osc
                  (GleasonS2Bridge.s2Pullback f) r)
    _ =
        northOrbitAverage
          (GleasonS2Bridge.s2Pullback
            (Rotation.compContinuous ρ f))
          sphereE1 := by rw [hpre]
    _ =
        GleasonS2Bridge.s2Pullback
          (northAxisAverage
            (Rotation.compContinuous ρ f))
          sphereE1 := by
            rw [← GleasonS2Bridge.s2Pullback_northAxisAverage
              (Rotation.compContinuous ρ f)]
    _ =
        northAxisAverage
          (Rotation.compContinuous ρ f)
          (GleasonS2Bridge.spherePoint3ToS2 sphereE1) := by
              exact
                (GleasonS2Bridge.s2Pullback_s2E1
                  (northAxisAverage
                    (Rotation.compContinuous ρ f)))
    _ =
        northAxisAverage
          (Rotation.compContinuous ρ f) GleasonS2Bridge.s2E1 := by
              rw [show GleasonS2Bridge.s2E1 = GleasonS2Bridge.spherePoint3ToS2 sphereE1 by rfl]

private theorem
    poleAverageLinear_harmonicDegreeProjectionContinuous_specialZ_eq_rotated_projected_northAxisAverage_s2E1_osc
    (n : ℕ)
    (f : C(S2, ℝ))
    (r : Set.Icc (0 : ℝ) 1) :
    poleAverageLinear
        (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
          (GleasonS2Bridge.s2Pullback f))
        (specialZPoint r) =
      northAxisAverage
        (ambientSectorProjectionContinuous n
          (Rotation.compContinuous
            (GleasonProjectionStability.rotationOfSpherePrecomp
              (sphereTripleIsometryEquiv
                (specialXPoint r) sphereE2 (specialZPoint r)
                (specialXPoint_inner_sphereE2 r)
                (specialXPoint_inner_specialZPoint r)
                (sphereE2_inner_specialZPoint r))) f))
        GleasonS2Bridge.s2E1 := by
  let e :=
    sphereTripleIsometryEquiv
      (specialXPoint r) sphereE2 (specialZPoint r)
      (specialXPoint_inner_sphereE2 r)
      (specialXPoint_inner_specialZPoint r)
      (sphereE2_inner_specialZPoint r)
  let ρ := GleasonProjectionStability.rotationOfSpherePrecomp e
  change
      poleAverageLinear
          (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
            (GleasonS2Bridge.s2Pullback f))
          (specialZPoint r) =
        northAxisAverage
          (ambientSectorProjectionContinuous n
            (Rotation.compContinuous ρ f))
          GleasonS2Bridge.s2E1
  calc
    poleAverageLinear
        (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
          (GleasonS2Bridge.s2Pullback f))
        (specialZPoint r)
      =
        poleAverageLinear
          (GleasonS2Bridge.s2Pullback
            (ambientSectorProjectionContinuous n f))
          (specialZPoint r) := by
            simp [GleasonS2Bridge.harmonicDegreeProjectionContinuous]
    _ =
        northAxisAverage
          (Rotation.compContinuous
            ρ
            (ambientSectorProjectionContinuous n f))
          GleasonS2Bridge.s2E1 := by
            exact
              poleAverageLinear_specialZ_eq_rotated_northAxisAverage_s2E1_osc
                (ambientSectorProjectionContinuous n f) r
    _ =
        northAxisAverage
          (ambientSectorProjectionContinuous n
            (Rotation.compContinuous
              ρ f))
          GleasonS2Bridge.s2E1 := by
            rw [SphericalHarmonics.ambientSectorProjectionContinuous_compContinuous]

private noncomputable def distinguishedZonalSectorSphereFn_osc
    (n : ℕ) : C(spherePoint3, ℝ) :=
  GleasonS2Bridge.s2Pullback
    ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))

private theorem northFixed_mem_eq_smul_distinguishedZonalSector_osc
    {n : ℕ} {f : C(S2, ℝ)}
    (hfsec : f ∈ sector n)
    (hfnorth : f ∈ northFixedSubmodule) :
    ∃ c : ℝ,
      c • ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) = f := by
  obtain ⟨c, hc⟩ :
      ∃ c : ℝ, c • distinguishedZonalSector n = ⟨⟨f, hfsec⟩, hfnorth⟩ :=
    (finrank_eq_one_iff_of_nonzero' (distinguishedZonalSector n)
      (by
        intro hz
        exact GleasonS2Bridge.distinguishedZonalSector_ne_zero n <|
          congrArg (fun z : northFixedSector n => ((z : sector n))) hz)).mp
      (finrank_northFixedSector_eq_one n) ⟨⟨f, hfsec⟩, hfnorth⟩
  refine ⟨c, ?_⟩
  exact congrArg (fun z : northFixedSector n => ((z : sector n) : C(S2, ℝ))) hc

private theorem
    northOrbitAverage_precomp_distinguished_eq_smul_osc
    (n : ℕ)
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ)) :
    ∃ c : ℝ,
      northOrbitAverage (spherePrecomp e (distinguishedZonalSectorSphereFn_osc n)) =
        c • distinguishedZonalSectorSphereFn_osc n := by
  let d : C(S2, ℝ) :=
    ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ)))
  let g : C(S2, ℝ) :=
    Rotation.compContinuous (GleasonProjectionStability.rotationOfSpherePrecomp e)
      d
  have hgdef :
      GleasonS2Bridge.s2Pullback g =
        spherePrecomp e (distinguishedZonalSectorSphereFn_osc n) := by
    change
      GleasonS2Bridge.s2Pullback
          (Rotation.compContinuous (GleasonProjectionStability.rotationOfSpherePrecomp e) d) =
        spherePrecomp e (GleasonS2Bridge.s2Pullback d)
    simpa [d, distinguishedZonalSectorSphereFn_osc,
      GleasonProjectionStability.ambientRotation_rotationOfSpherePrecomp] using
      GleasonS2Bridge.s2Pullback_compContinuous_eq_spherePrecomp_ambientRotation
        (GleasonProjectionStability.rotationOfSpherePrecomp e) d
  have hgsec : g ∈ sector n := by
    simpa [g, d] using
      SphericalHarmonics.compContinuous_mem_sector
        (GleasonProjectionStability.rotationOfSpherePrecomp e) n
        (((distinguishedZonalSector n : northFixedSector n) : sector n).property)
  have havgsec : SphericalHarmonics.northAxisAverage g ∈ sector n := by
    exact SphericalHarmonics.northAxisAverage_mem_sector hgsec
  have havgnorth : SphericalHarmonics.northAxisAverage g ∈ northFixedSubmodule := by
    exact SphericalHarmonics.northAxisAverage_mem_northFixedSubmodule g
  rcases
      northFixed_mem_eq_smul_distinguishedZonalSector_osc
        havgsec havgnorth with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  calc
    northOrbitAverage (spherePrecomp e (distinguishedZonalSectorSphereFn_osc n))
        = northOrbitAverage (GleasonS2Bridge.s2Pullback g) := by rw [hgdef]
    _ = GleasonS2Bridge.s2Pullback (SphericalHarmonics.northAxisAverage g) := by
          symm
          exact GleasonS2Bridge.s2Pullback_northAxisAverage g
    _ = GleasonS2Bridge.s2Pullback (c • d) := by rw [← hc]
    _ = c • distinguishedZonalSectorSphereFn_osc n := by
          simp [d, distinguishedZonalSectorSphereFn_osc]

private theorem
    poleAverageLinear_specialZ_eq_endpoint_ratio_of_distinguished_osc
    (n : ℕ)
    (r : Set.Icc (0 : ℝ) 1) :
    ∃ c : ℝ,
      poleAverageLinear (distinguishedZonalSectorSphereFn_osc n) (specialZPoint r) =
        c * distinguishedZonalSectorSphereFn_osc n sphereE1 ∧
      distinguishedZonalSectorSphereFn_osc n (specialZPoint r) =
        c * distinguishedZonalSectorSphereFn_osc n sphereE3 := by
  let e :=
    sphereTripleIsometryEquiv
      (specialXPoint r) sphereE2 (specialZPoint r)
      (specialXPoint_inner_sphereE2 r)
      (specialXPoint_inner_specialZPoint r)
      (sphereE2_inner_specialZPoint r)
  rcases northOrbitAverage_precomp_distinguished_eq_smul_osc n e with ⟨c, hc⟩
  refine ⟨c, ?_, ?_⟩
  · have hend :=
      northOrbitAverage_precomp_specialZ_endpoints_osc
        (distinguishedZonalSectorSphereFn_osc n) r
    have hE1 :
        northOrbitAverage
            (spherePrecomp e (distinguishedZonalSectorSphereFn_osc n))
            sphereE1 =
          c * distinguishedZonalSectorSphereFn_osc n sphereE1 := by
      simpa [hc] using congrArg (fun h : C(spherePoint3, ℝ) => h sphereE1) hc
    rcases hend with ⟨hend1, _⟩
    calc
      poleAverageLinear (distinguishedZonalSectorSphereFn_osc n) (specialZPoint r)
          = northOrbitAverage
              (spherePrecomp e (distinguishedZonalSectorSphereFn_osc n)) sphereE1 := by
                symm
                exact hend1
      _ = c * distinguishedZonalSectorSphereFn_osc n sphereE1 := hE1
  · have hend :=
      northOrbitAverage_precomp_specialZ_endpoints_osc
        (distinguishedZonalSectorSphereFn_osc n) r
    have hE3 :
        northOrbitAverage
            (spherePrecomp e (distinguishedZonalSectorSphereFn_osc n))
            sphereE3 =
          c * distinguishedZonalSectorSphereFn_osc n sphereE3 := by
      simpa [hc] using congrArg (fun h : C(spherePoint3, ℝ) => h sphereE3) hc
    rcases hend with ⟨_, hend3⟩
    calc
      distinguishedZonalSectorSphereFn_osc n (specialZPoint r)
          = northOrbitAverage
              (spherePrecomp e (distinguishedZonalSectorSphereFn_osc n)) sphereE3 := by
                symm
                exact hend3
      _ = c * distinguishedZonalSectorSphereFn_osc n sphereE3 := hE3

private theorem
    poleAverageLinear_specialZ_eq_neg_half_of_distinguished_endpoint_osc
    (n : ℕ)
    (hendpoint :
      distinguishedZonalSectorSphereFn_osc n sphereE1 =
        (-((1 / 2 : ℝ))) * distinguishedZonalSectorSphereFn_osc n sphereE3) :
    ∀ r : Set.Icc (0 : ℝ) 1,
      poleAverageLinear (distinguishedZonalSectorSphereFn_osc n) (specialZPoint r) =
        (-((1 / 2 : ℝ))) * distinguishedZonalSectorSphereFn_osc n (specialZPoint r) := by
  intro r
  rcases
      poleAverageLinear_specialZ_eq_endpoint_ratio_of_distinguished_osc n r with
    ⟨c, hpole, hval⟩
  rw [hpole, hendpoint, hval]
  ring

private theorem
    distinguished_endpoint_of_projected_poleAverage_commutation_osc
    {n : ℕ} (hn0 : n ≠ 0) {g : C(S2, ℝ)}
    (hgpc : g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
    (hcomm :
      poleAverageLinear
          (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
            (GleasonS2Bridge.s2Pullback g))
          sphereE3 =
        GleasonS2Bridge.harmonicDegreeProjectionContinuous n
          (GleasonS2Bridge.s2Pullback
            (GleasonS2Bridge.s2PoleAverageContinuousOfGreatCircleConstraint g
              (by
                have hframe :
                    g ∈ GleasonS2Bridge.continuousSphereFrameSubmoduleS2 := by
                  simpa
                    [GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                    using hgpc
                exact
                  GleasonS2Bridge.continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                    hframe)))
          sphereE3) :
    distinguishedZonalSectorSphereFn_osc n sphereE1 =
      (-((1 / 2 : ℝ))) * distinguishedZonalSectorSphereFn_osc n sphereE3 := by
  let r0 : Set.Icc (0 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩
  have hsE3 : specialZPoint r0 = sphereE3 := by
    apply Subtype.ext
    simp [specialZPoint, northSection, sphereE3, r0]
  rcases
      GleasonS2Bridge.exists_nonzero_northMeridianPolynomial_with_bad_degree_specialXZ_system
        hn0 hgpc hgproj with
    ⟨p, hpProj, _hpMer, hspecialZavg, hspecialZval, _hspecialXval⟩
  have hpDist :
      sphereCoordMvEval p.1 = distinguishedZonalSectorSphereFn_osc n := by
    calc
      sphereCoordMvEval p.1
          = GleasonS2Bridge.harmonicDegreeProjectionContinuous n
              (GleasonS2Bridge.s2Pullback g) := hpProj.symm
      _ = GleasonS2Bridge.s2Pullback (ambientSectorProjectionContinuous n g) := by
            simp [GleasonS2Bridge.harmonicDegreeProjectionContinuous]
      _ = distinguishedZonalSectorSphereFn_osc n := by
            rw [hgproj]
            rfl
  have hhz : IsNorthZonal (sphereCoordMvEval p.1) := by
    rw [hpDist]
    exact GleasonS2Bridge.isNorthZonal_s2Pullback_distinguishedZonalSector n
  have hmer0 :
      distinguishedZonalSectorSphereFn_osc n sphereE1 =
        (northMeridianPolynomial p.1).eval 0 := by
    have hprofile :
        northZonalProfile (sphereCoordMvEval p.1) zeroIcc =
          (northMeridianPolynomial p.1).eval 0 := by
      simpa using
        northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal
          (g := sphereCoordMvEval p.1) (p := p.1) hhz rfl zeroIcc
    calc
      distinguishedZonalSectorSphereFn_osc n sphereE1
          = sphereCoordMvEval p.1 sphereE1 := by
              exact congrArg (fun f : C(spherePoint3, ℝ) => f sphereE1) hpDist.symm
      _ = sphereCoordMvEval p.1 sphereE2 := by
            apply eq_of_isNorthZonal_of_sphereCoordZ_eq hhz
            norm_num [sphereCoordZ, sphereE1, sphereE2]
      _ = northZonalProfile (sphereCoordMvEval p.1) zeroIcc := by
            exact (northZonalProfile_zero_of_isNorthZonal hhz).symm
      _ = (northMeridianPolynomial p.1).eval 0 := hprofile
  have hscalar0 :
      (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval 0 =
        2 * (northMeridianPolynomial p.1).eval 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      ← Polynomial.coeff_zero_eq_eval_zero]
    simpa [northZonalScalarCoeff_zero] using
      (coeff_northZonalScalarPolynomial (northMeridianPolynomial p.1) 0)
  have hpoleE3 :
      poleAverageLinear
          (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
            (GleasonS2Bridge.s2Pullback g))
          sphereE3 =
        distinguishedZonalSectorSphereFn_osc n sphereE1 := by
    have hspecial := hspecialZavg r0
    rw [hsE3, hscalar0] at hspecial
    linarith [hmer0]
  have hmer1 :
      distinguishedZonalSectorSphereFn_osc n sphereE3 =
        (northMeridianPolynomial p.1).eval (Real.sqrt (1 - r0.1 ^ 2)) := by
    calc
      distinguishedZonalSectorSphereFn_osc n sphereE3
          = sphereCoordMvEval p.1 (specialZPoint r0) := by
              rw [hsE3]
              exact congrArg (fun f : C(spherePoint3, ℝ) => f sphereE3) hpDist.symm
      _ = (northMeridianPolynomial p.1).eval (Real.sqrt (1 - r0.1 ^ 2)) := by
            exact
              GleasonS2Bridge.sphereCoordMvEval_specialZPoint_eq_northMeridianPolynomial_eval
                hhz rfl r0
  have hprojAvgE3 :
      GleasonS2Bridge.harmonicDegreeProjectionContinuous n
          (GleasonS2Bridge.s2Pullback
            (GleasonS2Bridge.s2PoleAverageContinuousOfGreatCircleConstraint g
              (by
                have hframe :
                    g ∈ GleasonS2Bridge.continuousSphereFrameSubmoduleS2 := by
                  simpa
                    [GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                    using hgpc
                exact
                  GleasonS2Bridge.continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                    hframe)))
          sphereE3 =
        (-((1 / 2 : ℝ))) * distinguishedZonalSectorSphereFn_osc n sphereE3 := by
    have hspecial := hspecialZval r0
    rw [hsE3] at hspecial
    rw [hmer1]
    exact hspecial
  calc
    distinguishedZonalSectorSphereFn_osc n sphereE1
        =
          poleAverageLinear
            (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
              (GleasonS2Bridge.s2Pullback g))
            sphereE3 := hpoleE3.symm
    _ =
        GleasonS2Bridge.harmonicDegreeProjectionContinuous n
          (GleasonS2Bridge.s2Pullback
            (GleasonS2Bridge.s2PoleAverageContinuousOfGreatCircleConstraint g
              (by
                have hframe :
                    g ∈ GleasonS2Bridge.continuousSphereFrameSubmoduleS2 := by
                  simpa
                    [GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                    using hgpc
                exact
                  GleasonS2Bridge.continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                    hframe)))
          sphereE3 := hcomm
    _ =
        (-((1 / 2 : ℝ))) * distinguishedZonalSectorSphereFn_osc n sphereE3 := hprojAvgE3

private theorem
    projected_poleAverage_commutation_of_distinguished_endpoint_osc
    {n : ℕ} (hn0 : n ≠ 0) {g : C(S2, ℝ)}
    (hgpc : g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2)
    (hgproj :
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
    (hendpoint :
      distinguishedZonalSectorSphereFn_osc n sphereE1 =
        (-((1 / 2 : ℝ))) * distinguishedZonalSectorSphereFn_osc n sphereE3) :
    poleAverageLinear
        (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
          (GleasonS2Bridge.s2Pullback g))
        sphereE3 =
      GleasonS2Bridge.harmonicDegreeProjectionContinuous n
        (GleasonS2Bridge.s2Pullback
          (GleasonS2Bridge.s2PoleAverageContinuousOfGreatCircleConstraint g
            (by
              have hframe :
                  g ∈ GleasonS2Bridge.continuousSphereFrameSubmoduleS2 := by
                simpa
                  [GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                  using hgpc
              exact
                GleasonS2Bridge.continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                  hframe)))
        sphereE3 := by
  have hleft :
      poleAverageLinear
          (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
            (GleasonS2Bridge.s2Pullback g))
          sphereE3 =
        distinguishedZonalSectorSphereFn_osc n sphereE1 := by
    calc
      poleAverageLinear
          (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
            (GleasonS2Bridge.s2Pullback g))
          sphereE3
          =
            northAxisAverage (ambientSectorProjectionContinuous n g)
              GleasonS2Bridge.s2E1 := by
              exact
                poleAverageLinear_harmonicDegreeProjectionContinuous_sphereE3_eq_projected_northAxisAverage_osc
                  n g
      _ =
          northAxisAverage
            (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
            GleasonS2Bridge.s2E1 := by
          rw [hgproj]
      _ =
          (((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))))
            GleasonS2Bridge.s2E1 := by
          rw [northAxisAverage_eq_self_of_mem_northFixedSubmodule]
          exact (distinguishedZonalSector n).property
      _ =
          distinguishedZonalSectorSphereFn_osc n sphereE1 := by
          rfl
  have hright :
      GleasonS2Bridge.harmonicDegreeProjectionContinuous n
          (GleasonS2Bridge.s2Pullback
            (GleasonS2Bridge.s2PoleAverageContinuousOfGreatCircleConstraint g
              (by
                have hframe :
                    g ∈ GleasonS2Bridge.continuousSphereFrameSubmoduleS2 := by
                  simpa
                    [GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                    using hgpc
                exact
                  GleasonS2Bridge.continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                    hframe)))
          sphereE3 =
        (-((1 / 2 : ℝ))) * distinguishedZonalSectorSphereFn_osc n sphereE3 := by
    have hprojAvg :=
      GleasonS2Bridge.harmonicDegreeProjectionContinuous_s2PoleAverageContinuousOfPointConstraint_eq_neg_half
        (n := n) hn0 hgpc
    have hpoint :=
      congrArg (fun F : C(spherePoint3, ℝ) => F sphereE3) hprojAvg
    have hprojDist :
        GleasonS2Bridge.harmonicDegreeProjectionContinuous n
            (GleasonS2Bridge.s2Pullback g) =
          distinguishedZonalSectorSphereFn_osc n := by
      calc
        GleasonS2Bridge.harmonicDegreeProjectionContinuous n
            (GleasonS2Bridge.s2Pullback g)
            = GleasonS2Bridge.s2Pullback (ambientSectorProjectionContinuous n g) := by
                simp [GleasonS2Bridge.harmonicDegreeProjectionContinuous]
        _ =
            distinguishedZonalSectorSphereFn_osc n := by
            rw [hgproj]
            rfl
    simpa [hprojDist] using hpoint
  rw [hleft, hright]
  exact hendpoint

private theorem
    northZonalSqQuotientAverage_toContinuousMapOn_ne_neg_half_self_of_even_distinguishedZonalSector_gt_two_osc
    {n : ℕ} (hnEven : Even n) (hn2 : 2 < n) :
    ∀ q : ℝ[X],
      (∀ u : unitIcc,
        sqCenteredNorthZonalProfile (distinguishedZonalSectorSphereFn_osc n) u =
          u.1 * q.eval u.1) →
      northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc) ≠
        (-((1 / 2 : ℝ))) • q.toContinuousMapOn unitIcc := by
  intro q hq hneg
  have hpoly :
      northZonalSqQuotientPolynomial q = (-((1 / 2 : ℝ))) • q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.Icc (0 : ℝ) 1) ?_
      (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num))
    intro x hx
    have hx' := congrArg (fun f : C(unitIcc, ℝ) => f ⟨x, hx⟩) hneg
    simpa [northZonalSqQuotientAverage_toContinuousMapOn] using hx'
  have hzero : q = 0 := by
    ext k
    cases k with
    | zero =>
        have hcoeff :
            q.coeff 0 = (-((1 / 2 : ℝ))) * q.coeff 0 := by
          simpa [coeff_northZonalSqQuotientPolynomial] using
            congrArg (fun p : ℝ[X] => p.coeff 0) hpoly
        have hmul : (3 / 2 : ℝ) * q.coeff 0 = 0 := by
          linarith
        have h32 : (3 / 2 : ℝ) ≠ 0 := by norm_num
        exact (mul_eq_zero.mp hmul).resolve_left h32
    | succ k =>
        have hcoeff :
            northZonalSqQuotientScalarCoeff (k.succ) * q.coeff (k.succ) =
              (-((1 / 2 : ℝ))) * q.coeff (k.succ) := by
          simpa [coeff_northZonalSqQuotientPolynomial] using
            congrArg (fun p : ℝ[X] => p.coeff (k.succ)) hpoly
        have hqzero : q.coeff (k.succ) = 0 := by
          by_contra hqnz
          have hscal : northZonalSqQuotientScalarCoeff (k.succ) = -((1 / 2 : ℝ)) := by
            exact mul_right_cancel₀ hqnz (by simpa using hcoeff)
          have hnonneg : 0 ≤ northZonalSqQuotientScalarCoeff (k.succ) :=
            northZonalSqQuotientScalarCoeff_nonneg (k.succ)
          linarith
        simp [hqzero]
  have hconst : q = Polynomial.C (q.coeff 0) := by
    simpa [hzero] using (show (0 : ℝ[X]) = Polynomial.C (0 : ℝ) by simp)
  exact
    GleasonS2Bridge.distinguishedSqquotientPolynomial_not_constant_of_even_gt_two hnEven hn2 q
      (by simpa [distinguishedZonalSectorSphereFn_osc] using hq) hconst

private theorem
    sqquotient_polynomial_identity_of_specialXZ_osc
    {m q : Polynomial ℝ}
    (hmfactor :
      ∀ r : Set.Icc (0 : ℝ) 1,
        m.eval r.1 - m.eval 0 = (r.1 ^ 2) * q.eval (r.1 ^ 2))
    (hsqop :
      ∀ r : Set.Icc (0 : ℝ) 1,
        (northZonalScalarPolynomial m).eval r.1 - 2 * m.eval 0 =
          (r.1 ^ 2) * (northZonalSqQuotientPolynomial q).eval (r.1 ^ 2))
    (hscalarneg :
      ∀ r : Set.Icc (0 : ℝ) 1,
        (northZonalScalarPolynomial m).eval r.1 =
          -m.eval (Real.sqrt (1 - r.1 ^ 2))) :
    Polynomial.X * northZonalSqQuotientPolynomial q =
      Polynomial.C (q.eval 1) -
        (Polynomial.C 1 - Polynomial.X) * (q.comp (Polynomial.C 1 - Polynomial.X)) := by
  have hscalar0 :
      (northZonalScalarPolynomial m).eval 0 = -m.eval 1 := by
    simpa using hscalarneg (⟨0, by constructor <;> norm_num⟩ : Set.Icc (0 : ℝ) 1)
  have hscalar0' :
      (northZonalScalarPolynomial m).eval 0 = 2 * m.eval 0 := by
    calc
      (northZonalScalarPolynomial m).eval 0
          = (northZonalScalarPolynomial m).coeff 0 := by
              simpa using (Polynomial.coeff_zero_eq_eval_zero (northZonalScalarPolynomial m)).symm
      _ = 2 * m.coeff 0 := by
            simp [coeff_northZonalScalarPolynomial, northZonalScalarCoeff_zero]
      _ = 2 * m.eval 0 := by
            simpa using
              congrArg (fun t : ℝ => 2 * t) (Polynomial.coeff_zero_eq_eval_zero m)
  have hm1 :
      m.eval 1 = -2 * m.eval 0 := by
    linarith
  have hq1 :
      q.eval 1 = -3 * m.eval 0 := by
    have hfactor1 :=
      hmfactor (⟨1, by constructor <;> norm_num⟩ : Set.Icc (0 : ℝ) 1)
    have hfactor1' : q.eval 1 = m.eval 1 - m.eval 0 := by
      simpa using hfactor1.symm
    linarith
  have hpoly_eval :
      ∀ x ∈ Set.Icc (0 : ℝ) 1,
        x * (northZonalSqQuotientPolynomial q).eval x =
          q.eval 1 - (1 - x) * q.eval (1 - x) := by
    intro x hx
    let r : Set.Icc (0 : ℝ) 1 := ⟨Real.sqrt x, by
      constructor
      · exact Real.sqrt_nonneg x
      · have hsq : (Real.sqrt x) ^ 2 = x := by
          exact Real.sq_sqrt hx.1
        nlinarith [hx.2, Real.sqrt_nonneg x, hsq]⟩
    have hr_sq : r.1 ^ 2 = x := by
      simp [r, Real.sq_sqrt, hx.1]
    have hsqop_r := hsqop r
    have hscalarneg_r := hscalarneg r
    have hnonneg : 0 ≤ 1 - r.1 ^ 2 := by
      nlinarith [r.2.1, r.2.2]
    have hmfactor_r :
        m.eval (Real.sqrt (1 - r.1 ^ 2)) - m.eval 0 =
          (1 - r.1 ^ 2) * q.eval (1 - r.1 ^ 2) := by
      have hs :
          Real.sqrt (1 - r.1 ^ 2) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact Real.sqrt_nonneg _
        · have hsq : (Real.sqrt (1 - r.1 ^ 2)) ^ 2 = 1 - r.1 ^ 2 := by
            exact Real.sq_sqrt hnonneg
          nlinarith [r.2.2, Real.sqrt_nonneg (1 - r.1 ^ 2), hsq]
      have hfac2 := hmfactor ⟨Real.sqrt (1 - r.1 ^ 2), hs⟩
      have hsimp :
          (⟨Real.sqrt (1 - r.1 ^ 2), hs⟩ : Set.Icc (0 : ℝ) 1).1 ^ 2 = 1 - r.1 ^ 2 := by
        simp [Real.sq_sqrt, hnonneg]
      simpa [hsimp] using hfac2
    have hmain :
        (r.1 ^ 2) * (northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) =
          q.eval 1 - (1 - r.1 ^ 2) * q.eval (1 - r.1 ^ 2) := by
      have :
          (r.1 ^ 2) * (northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) =
            -m.eval (Real.sqrt (1 - r.1 ^ 2)) - 2 * m.eval 0 := by
        linarith
      rw [this]
      have hmcomp :
          m.eval (Real.sqrt (1 - r.1 ^ 2)) =
            m.eval 0 + (1 - r.1 ^ 2) * q.eval (1 - r.1 ^ 2) := by
        linarith
      linarith
    simpa [hr_sq] using hmain
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.Icc (0 : ℝ) 1) ?_
    (Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num))
  intro x hx
  simpa [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_comp] using hpoly_eval x hx

private theorem
    impossible_sqquotient_polynomial_identity_of_nonconst_osc
    {q : Polynomial ℝ}
    (hqnonconst : ¬ ∃ c : ℝ, q = Polynomial.C c)
    (hpoly :
      Polynomial.X * northZonalSqQuotientPolynomial q =
        Polynomial.C (q.eval 1) -
          (Polynomial.C 1 - Polynomial.X) * (q.comp (Polynomial.C 1 - Polynomial.X))) :
    False := by
  have hq_ne_zero : q ≠ 0 := by
    intro hq0
    apply hqnonconst
    exact ⟨0, by simpa [hq0]⟩
  have hqd_ne_zero : q.natDegree ≠ 0 := by
    intro hdeg
    apply hqnonconst
    exact ⟨q.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hdeg⟩
  have hdpos : 0 < q.natDegree := Nat.pos_iff_ne_zero.mpr hqd_ne_zero
  let arg : Polynomial ℝ := Polynomial.C 1 - Polynomial.X
  have hCsubX :
      arg = -(Polynomial.X - Polynomial.C 1) := by
    dsimp [arg]
    ring
  have harg_deg :
      arg.natDegree = 1 := by
    rw [hCsubX, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
  have harg_lc :
      arg.leadingCoeff = -1 := by
    rw [hCsubX, Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_X_sub_C]
  have hcomp_deg :
      (q.comp arg).natDegree = q.natDegree := by
    rw [Polynomial.natDegree_comp, harg_deg, Nat.mul_one]
  have hcomp_succ_zero :
      (q.comp arg).coeff (q.natDegree + 1) = 0 := by
    have htmp := (Polynomial.coeff_natDegree_succ_eq_zero (p := q.comp arg))
    rw [hcomp_deg] at htmp
    simpa using htmp
  have hcomp_coeff :
      (q.comp arg).coeff q.natDegree =
        ((-1 : ℝ) ^ q.natDegree) * q.leadingCoeff := by
    have hraw :
        (q.comp arg).coeff (q.natDegree * arg.natDegree) =
          q.leadingCoeff * arg.leadingCoeff ^ q.natDegree := by
      simpa using
        (Polynomial.coeff_comp_degree_mul_degree (p := q) (q := arg)
          (by rw [harg_deg]; norm_num))
    simpa [harg_deg, harg_lc, mul_comm] using hraw
  have hcoeff :=
    congrArg (fun p : Polynomial ℝ => p.coeff (q.natDegree + 1)) hpoly
  have hcoeff' :
      northZonalSqQuotientScalarCoeff q.natDegree * q.leadingCoeff =
        ((-1 : ℝ) ^ q.natDegree) * q.leadingCoeff := by
    have hleft :
        (Polynomial.X * northZonalSqQuotientPolynomial q).coeff (q.natDegree + 1) =
          northZonalSqQuotientScalarCoeff q.natDegree * q.leadingCoeff := by
      rw [Polynomial.coeff_X_mul, coeff_northZonalSqQuotientPolynomial,
        Polynomial.coeff_natDegree]
    have hright :
        (Polynomial.C (q.eval 1) - arg * (q.comp arg)).coeff (q.natDegree + 1) =
          ((-1 : ℝ) ^ q.natDegree) * q.leadingCoeff := by
      have hmul :
          (arg * (q.comp arg)).coeff (q.natDegree + 1) =
            -(((-1 : ℝ) ^ q.natDegree) * q.leadingCoeff) := by
        have hmul' :
            ((-(Polynomial.X - Polynomial.C 1)) * (q.comp arg)).coeff (q.natDegree + 1) =
              -(((-1 : ℝ) ^ q.natDegree) * q.leadingCoeff) := by
          rw [neg_mul, Polynomial.coeff_neg, Polynomial.coeff_X_sub_C_mul]
          simp [hcomp_succ_zero, hcomp_coeff]
        simpa [hCsubX] using hmul'
      calc
        (Polynomial.C (q.eval 1) - arg * (q.comp arg)).coeff (q.natDegree + 1)
            = 0 - (arg * (q.comp arg)).coeff (q.natDegree + 1) := by
                rw [Polynomial.coeff_sub]
                simp
        _ = ((-1 : ℝ) ^ q.natDegree) * q.leadingCoeff := by
            rw [hmul]
            ring
    calc
      northZonalSqQuotientScalarCoeff q.natDegree * q.leadingCoeff
          = (Polynomial.X * northZonalSqQuotientPolynomial q).coeff (q.natDegree + 1) := by
              symm
              exact hleft
      _ = (Polynomial.C (q.eval 1) - arg * (q.comp arg)).coeff (q.natDegree + 1) := by
            simpa [arg] using hcoeff
      _ = ((-1 : ℝ) ^ q.natDegree) * q.leadingCoeff := hright
  have hlc_ne_zero : q.leadingCoeff ≠ 0 := by
    exact mt Polynomial.leadingCoeff_eq_zero.mp hq_ne_zero
  have hscal :
      northZonalSqQuotientScalarCoeff q.natDegree = (-1 : ℝ) ^ q.natDegree := by
    exact mul_right_cancel₀ hlc_ne_zero (by simpa [mul_comm] using hcoeff')
  rcases Nat.even_or_odd q.natDegree with hEven | hOdd
  · have hlt :
        northZonalSqQuotientScalarCoeff q.natDegree < 1 :=
      northZonalSqQuotientScalarCoeff_lt_one hdpos
    have hpow : (-1 : ℝ) ^ q.natDegree = 1 := by
      rcases hEven with ⟨k, hk⟩
      simp [hk]
    rw [hscal, hpow] at hlt
    linarith
  · have hnonneg :
        0 ≤ northZonalSqQuotientScalarCoeff q.natDegree :=
      northZonalSqQuotientScalarCoeff_nonneg q.natDegree
    have hpow : (-1 : ℝ) ^ q.natDegree = -1 := by
      rcases hOdd with ⟨k, hk⟩
      rw [hk, pow_add, pow_mul, pow_one]
      norm_num
    rw [hscal, hpow] at hnonneg
    linarith

private theorem
    northMeridian_factor_of_sqquotient_profile_osc
    {p : MvPolynomial (Fin 3) ℝ} {q : Polynomial ℝ}
    (hgz : IsNorthZonal (sphereCoordMvEval p))
    (hq :
      ∀ u : unitIcc,
        sqCenteredNorthZonalProfile (sphereCoordMvEval p) u = u.1 * q.eval u.1) :
    ∀ r : Set.Icc (0 : ℝ) 1,
      (northMeridianPolynomial p).eval r.1 - (northMeridianPolynomial p).eval 0 =
        (r.1 ^ 2) * q.eval (r.1 ^ 2) := by
  intro r
  let u : unitIcc := ⟨r.1 ^ 2, sq_mem_Icc (nonnegIccToIcc r)⟩
  have hcenter :
      centeredNorthZonalProfile (sphereCoordMvEval p) (nonnegIccToIcc r) =
        (northMeridianPolynomial p).eval r.1 -
          (northMeridianPolynomial p).eval 0 := by
    simpa [nonnegIccToIcc] using
      centeredNorthZonalProfile_eq_northMeridianPolynomial_sub_const_of_isNorthZonal
        (g := sphereCoordMvEval p) (p := p) hgz rfl (nonnegIccToIcc r)
  have hsq :
      sqCenteredNorthZonalProfile (sphereCoordMvEval p) u =
        (northMeridianPolynomial p).eval r.1 -
          (northMeridianPolynomial p).eval 0 := by
    rw [sqCenteredNorthZonalProfile_apply]
    have hu :
        (⟨Real.sqrt u.1, by
          constructor
          · have hsqrt := Real.sqrt_nonneg u.1
            nlinarith
          · have hsq' : (Real.sqrt u.1) ^ 2 = u.1 := by
              exact Real.sq_sqrt u.2.1
            have hle : Real.sqrt u.1 ≤ 1 := by
              nlinarith [u.2.2, Real.sqrt_nonneg u.1, hsq']
            simpa using hle⟩ : Set.Icc (-1 : ℝ) 1) = nonnegIccToIcc r := by
      apply Subtype.ext
      simp [u, nonnegIccToIcc, Real.sqrt_sq, r.2.1]
    rw [hu, hcenter]
  calc
    (northMeridianPolynomial p).eval r.1 - (northMeridianPolynomial p).eval 0
        = sqCenteredNorthZonalProfile (sphereCoordMvEval p) u := by
            symm
            exact hsq
    _ = u.1 * q.eval u.1 := hq u
    _ = (r.1 ^ 2) * q.eval (r.1 ^ 2) := by rfl

private theorem
    greatCirclePointConstraint_specialZ_eq_scalar_sub_meridian_sub_zero_of_isNorthZonal_osc
    {p : MvPolynomial (Fin 3) ℝ}
    (hgz : IsNorthZonal (sphereCoordMvEval p))
    (r : Set.Icc (0 : ℝ) 1) :
    greatCirclePointConstraintLinear
      (specialXPoint r) sphereE2 (specialZPoint r)
      (specialXPoint_inner_sphereE2 r)
      (specialXPoint_inner_specialZPoint r)
      (sphereE2_inner_specialZPoint r)
      (sphereCoordMvEval p) =
        (northZonalScalarPolynomial (northMeridianPolynomial p)).eval r.1 -
          (northMeridianPolynomial p).eval r.1 -
          (northMeridianPolynomial p).eval 0 := by
  have hvalX :
      sphereCoordMvEval p (specialXPoint r) =
        (northMeridianPolynomial p).eval r.1 := by
    exact
      GleasonS2Bridge.sphereCoordMvEval_specialXPoint_eq_northMeridianPolynomial_eval
        (hgz := hgz) (hpEval := rfl) r
  have hvalE2 :
      sphereCoordMvEval p sphereE2 =
        (northMeridianPolynomial p).eval 0 := by
    have hmer :
        northZonalProfile (sphereCoordMvEval p) zeroIcc =
          (northMeridianPolynomial p).eval 0 := by
      simpa using
        northZonalProfile_eq_northMeridianPolynomial_eval_of_isNorthZonal
          (g := sphereCoordMvEval p) (p := p) hgz rfl zeroIcc
    calc
      sphereCoordMvEval p sphereE2
          = northZonalProfile (sphereCoordMvEval p) zeroIcc := by
              symm
              exact northZonalProfile_zero_of_isNorthZonal hgz
      _ = (northMeridianPolynomial p).eval 0 := hmer
  rw [greatCirclePointConstraintLinear_apply]
  calc
    2 *
        greatCircleAverageLinear
          (specialXPoint r) sphereE2 (specialZPoint r)
          (specialXPoint_inner_sphereE2 r)
          (specialXPoint_inner_specialZPoint r)
          (sphereE2_inner_specialZPoint r)
          (sphereCoordMvEval p) -
        sphereCoordMvEval p (specialXPoint r) -
        sphereCoordMvEval p sphereE2
      =
        2 * poleAverageLinear (sphereCoordMvEval p) (specialZPoint r) -
          sphereCoordMvEval p (specialXPoint r) -
          sphereCoordMvEval p sphereE2 := by
            rw [← poleAverageLinear_eq_greatCircleAverageLinear
              (sphereCoordMvEval p) (specialXPoint r) sphereE2 (specialZPoint r)
              (specialXPoint_inner_sphereE2 r)
              (specialXPoint_inner_specialZPoint r)
              (sphereE2_inner_specialZPoint r)]
    _ =
        (northZonalScalarPolynomial (northMeridianPolynomial p)).eval r.1 -
          sphereCoordMvEval p (specialXPoint r) -
          sphereCoordMvEval p sphereE2 := by
            rw [two_mul_poleAverageLinear_specialZPoint_eq_northZonalScalarPolynomial
              (hgz := hgz) (hpEval := rfl) r]
    _ =
        (northZonalScalarPolynomial (northMeridianPolynomial p)).eval r.1 -
          (northMeridianPolynomial p).eval r.1 -
          (northMeridianPolynomial p).eval 0 := by
            rw [hvalX, hvalE2]

private theorem
    northZonalScalar_specialZ_of_sqquotient_residual_osc
    {p : MvPolynomial (Fin 3) ℝ} {q : Polynomial ℝ}
    (hgz : IsNorthZonal (sphereCoordMvEval p))
    (hq :
      ∀ u : unitIcc,
        sqCenteredNorthZonalProfile (sphereCoordMvEval p) u = u.1 * q.eval u.1)
    (hresid :
      ∀ r : Set.Icc (0 : ℝ) 1,
        greatCirclePointConstraintLinear
          (specialXPoint r) sphereE2 (specialZPoint r)
          (specialXPoint_inner_sphereE2 r)
          (specialXPoint_inner_specialZPoint r)
          (sphereE2_inner_specialZPoint r)
          (sphereCoordMvEval p) =
            (r.1 ^ 2) *
              ((northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) - q.eval (r.1 ^ 2))) :
    ∀ r : Set.Icc (0 : ℝ) 1,
      (northZonalScalarPolynomial (northMeridianPolynomial p)).eval r.1 -
          2 * (northMeridianPolynomial p).eval 0 =
        (r.1 ^ 2) * (northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) := by
  intro r
  have hfactor :=
    northMeridian_factor_of_sqquotient_profile_osc hgz hq r
  have hresid' :
      (northZonalScalarPolynomial (northMeridianPolynomial p)).eval r.1 -
          (northMeridianPolynomial p).eval r.1 -
          (northMeridianPolynomial p).eval 0 =
        (r.1 ^ 2) *
          ((northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) - q.eval (r.1 ^ 2)) := by
    calc
      (northZonalScalarPolynomial (northMeridianPolynomial p)).eval r.1 -
          (northMeridianPolynomial p).eval r.1 -
          (northMeridianPolynomial p).eval 0
        =
          greatCirclePointConstraintLinear
            (specialXPoint r) sphereE2 (specialZPoint r)
            (specialXPoint_inner_sphereE2 r)
            (specialXPoint_inner_specialZPoint r)
            (sphereE2_inner_specialZPoint r)
            (sphereCoordMvEval p) := by
              symm
              exact
                greatCirclePointConstraint_specialZ_eq_scalar_sub_meridian_sub_zero_of_isNorthZonal_osc
                  hgz r
      _ =
          (r.1 ^ 2) *
            ((northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) - q.eval (r.1 ^ 2)) := hresid r
  calc
    (northZonalScalarPolynomial (northMeridianPolynomial p)).eval r.1 -
        2 * (northMeridianPolynomial p).eval 0
      =
        ((northZonalScalarPolynomial (northMeridianPolynomial p)).eval r.1 -
          (northMeridianPolynomial p).eval r.1 -
          (northMeridianPolynomial p).eval 0) +
        ((northMeridianPolynomial p).eval r.1 -
          (northMeridianPolynomial p).eval 0) := by
            ring
    _ =
        (r.1 ^ 2) *
          ((northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) - q.eval (r.1 ^ 2)) +
        ((northMeridianPolynomial p).eval r.1 -
          (northMeridianPolynomial p).eval 0) := by
            rw [hresid']
    _ =
        (r.1 ^ 2) *
          ((northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) - q.eval (r.1 ^ 2)) +
        (r.1 ^ 2) * q.eval (r.1 ^ 2) := by
            rw [hfactor]
    _ = (r.1 ^ 2) * (northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) := by
          ring

private theorem
    sqquotient_polynomial_identity_of_sqquotient_residual_and_specialZNeg_osc
    {p : MvPolynomial (Fin 3) ℝ} {q : Polynomial ℝ}
    (hgz : IsNorthZonal (sphereCoordMvEval p))
    (hq :
      ∀ u : unitIcc,
        sqCenteredNorthZonalProfile (sphereCoordMvEval p) u = u.1 * q.eval u.1)
    (hresid :
      ∀ r : Set.Icc (0 : ℝ) 1,
        greatCirclePointConstraintLinear
          (specialXPoint r) sphereE2 (specialZPoint r)
          (specialXPoint_inner_sphereE2 r)
          (specialXPoint_inner_specialZPoint r)
          (sphereE2_inner_specialZPoint r)
          (sphereCoordMvEval p) =
            (r.1 ^ 2) *
              ((northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) - q.eval (r.1 ^ 2)))
    (hscalarneg :
      ∀ r : Set.Icc (0 : ℝ) 1,
        (northZonalScalarPolynomial (northMeridianPolynomial p)).eval r.1 =
          -(northMeridianPolynomial p).eval (Real.sqrt (1 - r.1 ^ 2))) :
    Polynomial.X * northZonalSqQuotientPolynomial q =
      Polynomial.C (q.eval 1) -
        (Polynomial.C 1 - Polynomial.X) * (q.comp (Polynomial.C 1 - Polynomial.X)) := by
  exact
    sqquotient_polynomial_identity_of_specialXZ_osc
      (northMeridian_factor_of_sqquotient_profile_osc hgz hq)
      (northZonalScalar_specialZ_of_sqquotient_residual_osc hgz hq hresid)
      hscalarneg

private theorem
    no_northFixed_pointConstraint_witness_even_osc
    (n : ℕ) (hnEven : Even n) (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    ¬ ∃ g : C(S2, ℝ),
      g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2 ∧
      g ∈ northFixedSubmodule ∧
        ambientSectorProjectionContinuous n g =
          ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) := by
  intro hw
  rcases exists_centered_northFixed_pointConstraint_witness_even_osc hn0 hw with
    ⟨g, hgpc, hgnorth, hgproj, hgcenter⟩
  have hpole :
      poleAverageLinear (GleasonS2Bridge.s2Pullback g) =
        (-((1 / 2 : ℝ))) • GleasonS2Bridge.s2Pullback g :=
    poleAverageLinear_eq_neg_half_of_center_zero_pointConstraint_osc hgpc hgcenter
  have hsum :=
    specialTriple_sum_eq_zero_of_center_zero_pointConstraint_osc hgpc hgcenter
  -- Remaining spectral core:
  -- use the centered witness and the exact pole-average eigenrelation on the full
  -- pullback to force the special-point sq-quotient residual to vanish.
  rcases
      GleasonS2Bridge.exists_special_sqquotient_residual_of_northFixed_pointConstraint_witness
        hn0 hnEven hgpc hgnorth hgproj with
    ⟨p, q, hpProj, hpMer, hq, hresid⟩
  rcases
      GleasonS2Bridge.exists_nonzero_northMeridianPolynomial_with_bad_degree_specialXZ_system
        hn0 hgpc hgproj with
    ⟨pXZ, hpProjXZ, hpMerXZ, hspecialZavg, hspecialZval, hspecialXval⟩
  have hpEq : p = pXZ := by
    apply Subtype.ext
    exact
      eq_of_sphereCoordMvEval_eq_of_mem_homogeneousSubmodule
        p.2.1 pXZ.2.1 (by simpa using hpProj.symm.trans hpProjXZ)
  subst hpEq
  have hhz : IsNorthZonal (sphereCoordMvEval p.1) := by
    have hhz :
        IsNorthZonal
          (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
            (GleasonS2Bridge.s2Pullback g)) := by
      exact
        GleasonS2Bridge.isNorthZonal_harmonicDegreeProjectionContinuous_of_mem_northFixedSubmodule
          (by simpa using hgnorth)
    simpa [hpProj] using hhz
  have hpDist :
      sphereCoordMvEval p.1 = distinguishedZonalSectorSphereFn_osc n := by
    calc
      sphereCoordMvEval p.1
          = GleasonS2Bridge.harmonicDegreeProjectionContinuous n
              (GleasonS2Bridge.s2Pullback g) := hpProj.symm
      _ = GleasonS2Bridge.s2Pullback (ambientSectorProjectionContinuous n g) := by
            simp [GleasonS2Bridge.harmonicDegreeProjectionContinuous]
      _ = distinguishedZonalSectorSphereFn_osc n := by
            rw [hgproj]
            rfl
  have hqDist :
      ∀ u : unitIcc,
        sqCenteredNorthZonalProfile (distinguishedZonalSectorSphereFn_osc n) u =
          u.1 * q.eval u.1 := by
    intro u
    simpa [hpDist] using hq u
  have hn_gt_two : 2 < n := by
    rcases hnEven with ⟨k, hk⟩
    subst hk
    cases k with
    | zero =>
        exact False.elim (hn0 rfl)
    | succ k =>
        cases k with
        | zero =>
            exact False.elim (hn2 rfl)
        | succ k =>
            omega
  exact
    by
      rcases
          GleasonS2Bridge.exists_nonzero_northMeridianPolynomial_with_bad_degree_sqquotient_specialZ_system
            hn0 hnEven hgpc hgproj with
        ⟨pSq, qSq, hpProjSq, hpMerSq, hqSq, hsqavgSq, hspecialZavgSq⟩
      have hpSqEq : p = pSq := by
        apply Subtype.ext
        exact
          eq_of_sphereCoordMvEval_eq_of_mem_homogeneousSubmodule
            p.2.1 pSq.2.1 (by simpa using hpProj.symm.trans hpProjSq)
      subst hpSqEq
      have hendpoint :
          distinguishedZonalSectorSphereFn_osc n sphereE1 =
            (-((1 / 2 : ℝ))) * distinguishedZonalSectorSphereFn_osc n sphereE3 := by
        exact
          distinguished_endpoint_of_projected_poleAverage_commutation_osc
            hn0 hgpc hgproj
            (GleasonS2Bridge.projected_poleAverage_commutation_unconditional_pointConstraint
              (n := n) (g := g) hgpc)
      have hpoleDist :
          ∀ r : Set.Icc (0 : ℝ) 1,
            poleAverageLinear (distinguishedZonalSectorSphereFn_osc n) (specialZPoint r) =
              (-((1 / 2 : ℝ))) * distinguishedZonalSectorSphereFn_osc n (specialZPoint r) := by
        exact
          poleAverageLinear_specialZ_eq_neg_half_of_distinguished_endpoint_osc
            n hendpoint
      have hscalarneg :
          ∀ r : Set.Icc (0 : ℝ) 1,
            (northZonalScalarPolynomial (northMeridianPolynomial p.1)).eval r.1 =
              -(northMeridianPolynomial p.1).eval (Real.sqrt (1 - r.1 ^ 2)) := by
        intro r
        have hpoleEval :
            poleAverageLinear
                (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
                  (GleasonS2Bridge.s2Pullback g))
                (specialZPoint r) =
              (-((1 / 2 : ℝ))) * distinguishedZonalSectorSphereFn_osc n (specialZPoint r) := by
          calc
            poleAverageLinear
                (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
                  (GleasonS2Bridge.s2Pullback g))
                (specialZPoint r)
              =
                poleAverageLinear (distinguishedZonalSectorSphereFn_osc n) (specialZPoint r) := by
                  rw [hpProj, hpDist]
            _ =
                (-((1 / 2 : ℝ))) * distinguishedZonalSectorSphereFn_osc n (specialZPoint r) := by
                  exact hpoleDist r
        have hspecialZvalDist :
            distinguishedZonalSectorSphereFn_osc n (specialZPoint r) =
              (northMeridianPolynomial p.1).eval (Real.sqrt (1 - r.1 ^ 2)) := by
          calc
            distinguishedZonalSectorSphereFn_osc n (specialZPoint r)
              = sphereCoordMvEval p.1 (specialZPoint r) := by
                  exact congrArg (fun f : C(spherePoint3, ℝ) => f (specialZPoint r)) hpDist.symm
            _ =
                (northMeridianPolynomial p.1).eval (Real.sqrt (1 - r.1 ^ 2)) := by
                  exact
                    GleasonS2Bridge.sphereCoordMvEval_specialZPoint_eq_northMeridianPolynomial_eval
                      hhz rfl r
        linarith [hspecialZavg r, hpoleEval, hspecialZvalDist]
      have hresidp :
          ∀ r : Set.Icc (0 : ℝ) 1,
            greatCirclePointConstraintLinear
              (specialXPoint r) sphereE2 (specialZPoint r)
              (specialXPoint_inner_sphereE2 r)
              (specialXPoint_inner_specialZPoint r)
              (sphereE2_inner_specialZPoint r)
              (sphereCoordMvEval p.1) =
                (r.1 ^ 2) *
                  ((northZonalSqQuotientPolynomial q).eval (r.1 ^ 2) - q.eval (r.1 ^ 2)) := by
        intro r
        simpa [hpProj] using hresid r
      have hpoly :
          Polynomial.X * northZonalSqQuotientPolynomial q =
            Polynomial.C (q.eval 1) -
              (Polynomial.C 1 - Polynomial.X) * (q.comp (Polynomial.C 1 - Polynomial.X)) := by
        exact
          sqquotient_polynomial_identity_of_sqquotient_residual_and_specialZNeg_osc
            hhz hq hresidp hscalarneg
      have hq_ne_Ccoeff : q ≠ Polynomial.C (q.coeff 0) := by
        exact
          GleasonS2Bridge.distinguishedSqquotientPolynomial_not_constant_of_even_gt_two
            hnEven hn_gt_two q
            (by simpa [distinguishedZonalSectorSphereFn_osc] using hqDist)
      have hqnonconst : ¬ ∃ c : ℝ, q = Polynomial.C c := by
        intro hconst
        rcases hconst with ⟨c, hc⟩
        apply hq_ne_Ccoeff
        rw [hc]
        simp
      exact impossible_sqquotient_polynomial_identity_of_nonconst_osc hqnonconst hpoly

private theorem
    special_pointConstraint_zero_even_osc
    (n : ℕ) (hnEven : Even n) (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    ∀ g : C(S2, ℝ),
      g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2 →
      g ∈ northFixedSubmodule →
      ambientSectorProjectionContinuous n g =
        ((((distinguishedZonalSector n : northFixedSector n) : sector n) : C(S2, ℝ))) →
      ∀ r : Set.Icc (0 : ℝ) 1,
        greatCirclePointConstraintLinear
          (specialXPoint r) sphereE2 (specialZPoint r)
          (specialXPoint_inner_sphereE2 r)
          (specialXPoint_inner_specialZPoint r)
          (sphereE2_inner_specialZPoint r)
          (GleasonS2Bridge.harmonicDegreeProjectionContinuous n
            (GleasonS2Bridge.s2Pullback g)) = 0 := by
  intro g hgpc hgnorth hgproj r
  exact False.elim <|
    no_northFixed_pointConstraint_witness_even_osc n hnEven hn0 hn2
      ⟨g, hgpc, hgnorth, hgproj⟩

private theorem continuousToLp_ambientSectorProjectionContinuous_osc
    (n : ℕ) (f : C(S2, ℝ)) :
    continuousToLp (ambientSectorProjectionContinuous n f) =
      (sectorL2 n).starProjection (continuousToLp f) := by
  simpa using GleasonS2Bridge.continuousToLp_ambientSectorProjectionContinuous n f

private theorem
    s2Pullback_mem_continuousSphereGreatCircleConstraintSubmodule_of_mem_pointConstraint_osc
    {g : C(S2, ℝ)}
    (hgpc : g ∈ GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2) :
    GleasonS2Bridge.s2Pullback g ∈ continuousSphereGreatCircleConstraintSubmodule := by
  have hframe : g ∈ GleasonS2Bridge.continuousSphereFrameSubmoduleS2 := by
    simpa [GleasonS2Bridge.continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
      using hgpc
  have hconstraint : g ∈ GleasonS2Bridge.continuousSphereGreatCircleConstraintSubmoduleS2 :=
    GleasonS2Bridge.continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
      hframe
  simpa using hconstraint

private theorem
    stdGreatCirclePointConstraintLinear_eq_zero_of_mem_continuousSphereGreatCircleConstraintSubmodule_osc
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereGreatCircleConstraintSubmodule) :
    stdGreatCirclePointConstraintLinear f = 0 := by
  have hstd :=
    (mem_continuousSphereGreatCircleConstraintSubmodule_iff f).1 hf
      sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  rw [greatCircleAverageLinear_std] at hstd
  have hcenter :
      3 * sphereFrameCenter f = f sphereE1 + f sphereE2 + f sphereE3 := by
    simp [sphereFrameCenter]
    ring
  have havg_centered :
      northEquatorAverageLinear (sphereFrameCentered f) =
        northEquatorAverageLinear f - sphereFrameCenter f := by
    calc
      northEquatorAverageLinear (sphereFrameCentered f)
          =
            northEquatorAverageLinear f -
              northEquatorAverageLinear (ContinuousMap.const _ (sphereFrameCenter f)) := by
                simp [sphereFrameCentered, map_sub]
      _ = northEquatorAverageLinear f - sphereFrameCenter f := by
            rw [northEquatorAverageLinear_const]
  have hcentered3 : sphereFrameCentered f sphereE3 = f sphereE3 - sphereFrameCenter f := by
    simp [sphereFrameCentered]
  rw [havg_centered, hcentered3] at hstd
  rw [stdGreatCirclePointConstraintLinear_apply]
  linarith

private theorem
    not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_mod_ne_two_osc
    {n : ℕ} (hn : 0 < n) (hmod : n % 4 ≠ 2) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤ stdGreatCirclePointConstraintSubmodule := by
  intro hle
  let g : C(spherePoint3, ℝ) :=
    ⟨sphereRestrictionLinear (surfaceModeAL2 n),
      continuous_sphereRestriction_of_harmonicHomogeneousDegree
        ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩⟩
  have hg : g ∈ continuousHarmonicSphereDegreeSubmodule n := by
    show sphereRestrictionLinear (surfaceModeAL2 n) ∈ harmonicSphereDegreeSubmodule n
    exact
      ⟨surfaceModeAL2 n,
        ⟨surfaceModeAL2_harmonicAt n, surfaceModeAL2_homogeneous n⟩, rfl⟩
  have hstd : stdGreatCirclePointConstraintLinear g = 0 := by
    exact hle hg
  have havg : northEquatorAverageLinear g = 0 := by
    simpa [g] using northEquatorAverage_surfaceModeAL2_zero_of_pos hn
  have hg1 : g sphereE1 = 1 := by
    simp [g, sphereRestrictionLinear, surfaceModeAL2, sphereE1]
  have hg2_ne_neg_one : g sphereE2 ≠ -1 := by
    by_cases h0 : n % 4 = 0
    · have hg2 : g sphereE2 = 1 := by
        simpa [g] using surfaceModeAL2_sphereE2_mod_zero n h0
      linarith
    by_cases h1 : n % 4 = 1
    · have hg2 : g sphereE2 = 0 := by
        simpa [g] using surfaceModeAL2_sphereE2_mod_one n h1
      linarith
    have h3 : n % 4 = 3 := by omega
    have hg2 : g sphereE2 = 0 := by
      simpa [g] using surfaceModeAL2_sphereE2_mod_three n h3
    linarith
  rw [stdGreatCirclePointConstraintLinear_apply] at hstd
  have hg2 : g sphereE2 = -1 := by
    linarith [hstd, havg, hg1]
  exact hg2_ne_neg_one hg2

private theorem
    not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_mod_eq_two_osc
    {n : ℕ} (hn : 2 < n) (hmod : n % 4 = 2) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤ stdGreatCirclePointConstraintSubmodule := by
  intro hle
  let g : C(spherePoint3, ℝ) :=
    ⟨sphereRestrictionLinear (surfaceModeBL2 n),
      continuous_sphereRestriction_of_harmonicHomogeneousDegree
        ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩⟩
  have hg : g ∈ continuousHarmonicSphereDegreeSubmodule n := by
    show sphereRestrictionLinear (surfaceModeBL2 n) ∈ harmonicSphereDegreeSubmodule n
    exact
      ⟨surfaceModeBL2 n,
        ⟨surfaceModeBL2_harmonicAt (by omega), surfaceModeBL2_homogeneous (by omega)⟩, rfl⟩
  have hstd : stdGreatCirclePointConstraintLinear g = 0 := by
    exact hle hg
  have havg : northEquatorAverageLinear g = 0 := by
    simpa [g] using northEquatorAverage_surfaceModeBL2_zero_of_gt_two hn
  have hg1 : g sphereE1 = 1 := by
    simp [g, sphereRestrictionLinear, surfaceModeBL2, sphereE1]
  have hg2 : g sphereE2 = 1 := by
    simpa [g] using surfaceModeBL2_sphereE2_mod_two_gt_two hn hmod
  rw [stdGreatCirclePointConstraintLinear_apply] at hstd
  linarith [hstd, havg, hg1, hg2]

private theorem
    not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_ne_zero_two_osc
    {n : ℕ} (hn0 : n ≠ 0) (hn2 : n ≠ 2) :
    ¬ continuousHarmonicSphereDegreeSubmodule n ≤ stdGreatCirclePointConstraintSubmodule := by
  cases n with
  | zero =>
      exact (hn0 rfl).elim
  | succ n =>
      cases n with
      | zero =>
          exact
            not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_mod_ne_two_osc
              (by norm_num) (by norm_num)
      | succ n' =>
          have hgt : 2 < Nat.succ (Nat.succ n') := by omega
          by_cases hmod : Nat.succ (Nat.succ n') % 4 = 2
          · exact
              not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_mod_eq_two_osc
                hgt hmod
          · exact
              not_continuousHarmonicSphereDegreeSubmodule_le_stdGreatCirclePointConstraintSubmodule_of_mod_ne_two_osc
                (by omega) hmod

/- Dead `std`-image branch removed.

The live proof path below goes through `no_northFixed_pointConstraint_witness_even_osc`
and `special_pointConstraint_zero_even_osc`, not through the abandoned global
`std`-kernel reduction. Keeping the dead branch out of the file avoids source
regressions while the active local gaps are being solved. -/

private theorem spectral_closure_theorem_of_s2_frame_eq_low_osc
    (hs2 :
      GleasonS2Bridge.continuousSphereFrameSubmoduleS2 =
        GleasonS2Bridge.lowSectorS2) :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  by_contra hne
  rcases
      exists_nonzero_northZonal_fixed_mem_topologicalClosure_highEvenUnion_inf_frame hne with
    ⟨g, hg, hgne, hgz, _hfixed⟩
  have hgFrame : g ∈ continuousSphereFrameSubmodule := hg.2
  have hgHigh : g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure := hg.1
  have hproj :
      GleasonS2Bridge.ambientLowHarmonicProjectionContinuous g = 0 :=
    GleasonS2Bridge.ambientLowHarmonicProjectionContinuous_eq_zero_of_mem_topologicalClosure_highEvenUnion
      hgHigh
  have hgquad : g ∈ continuousSphereQuadraticSubmodule :=
    continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_s2_low_osc
      hs2 hgFrame
  have hg0 :
      g = 0 :=
    eq_zero_of_mem_continuousSphereFrameSubmodule_of_isNorthZonal_of_ambientLowProjection_zero_of_mem_quadratic_osc
      hgFrame hgz hproj hgquad
  exact hgne hg0

/-- Local `S²` spectral input needed by the active proof path. -/
private theorem s2_frame_eq_low_theorem :
    GleasonS2Bridge.continuousSphereFrameSubmoduleS2 =
      GleasonS2Bridge.lowSectorS2 := by
  refine
    GleasonS2Bridge.continuousSphereFrameSubmoduleS2_eq_lowSectorS2_of_even_sector_intersections_bot
      ?_
  intro n hnEven hn0 hn2
  exact
    GleasonS2Bridge.continuousSphereFrameClosedSubmoduleL2S2_inf_sectorL2_eq_bot_of_no_northFixed_pointConstraint_witness
      (no_northFixed_pointConstraint_witness_even_osc n hnEven hn0 hn2)

private lemma coordSphereFrameFun_nonneg
    (μ : FrameFunction H) (u v p : H) :
    ∀ x : spherePoint3, 0 ≤ coordSphereFrameFun μ u v p x := by
  intro x
  exact frame_quadratic_nonneg (H := H) μ (coordPoint u v p (spherePointCoord x))

private lemma IsSphereFrameFunction_sub_const
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f) (c : ℝ) :
    IsSphereFrameFunction (fun x => f x - c) := by
  intro x y z hxy hxz hyz
  have hsum := hf x y z hxy hxz hyz
  dsimp
  linarith

private lemma IsSphereFrameFunction_add_const
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f) (c : ℝ) :
    IsSphereFrameFunction (fun x => f x + c) := by
  intro x y z hxy hxz hyz
  have hsum := hf x y z hxy hxz hyz
  dsimp
  linarith

private lemma IsSphereFrameFunction_nonneg_add_bound_of_abs_le
    {f : spherePoint3 → ℝ} {M : ℝ}
    (hM : ∀ x : spherePoint3, |f x| ≤ M) :
    ∀ x : spherePoint3, 0 ≤ f x + M := by
  intro x
  have hx := hM x
  linarith [(abs_le.mp hx).1]

private lemma s2_bounded_frame_continuity_of_nonnegative_frame_continuity
    (hnonnegCont :
      ∀ f : spherePoint3 → ℝ,
        IsSphereFrameFunction f →
        (∀ x : spherePoint3, 0 ≤ f x) →
        Continuous f) :
    ∀ f : spherePoint3 → ℝ,
      IsSphereFrameFunction f →
      (∃ M : ℝ, ∀ x : spherePoint3, |f x| ≤ M) →
      Continuous f := by
  intro f hf hbounded
  rcases hbounded with ⟨M, hM⟩
  let g : spherePoint3 → ℝ := fun x => f x + M
  have hgFrame : IsSphereFrameFunction g :=
    IsSphereFrameFunction_add_const hf M
  have hgNonneg : ∀ x : spherePoint3, 0 ≤ g x := by
    intro x
    exact IsSphereFrameFunction_nonneg_add_bound_of_abs_le hM x
  have hgCont : Continuous g := hnonnegCont g hgFrame hgNonneg
  have hf_eq : f = fun x => g x - M := by
    funext x
    simp [g]
  rw [hf_eq]
  exact hgCont.sub continuous_const

private lemma continuous_s2_of_pointwise_abs_oscillation
    {f : spherePoint3 → ℝ}
    (hosc :
      ∀ x : spherePoint3, ∀ {ε : ℝ}, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ y : spherePoint3, dist y x < δ → |f y - f x| ≤ ε) :
    Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  have hε2 : 0 < ε / 2 := by positivity
  rcases hosc x hε2 with ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  rw [Real.dist_eq]
  have hy' := hlocal y hy
  nlinarith

private lemma continuous_s2_of_uniform_abs_oscillation
    {f : spherePoint3 → ℝ}
    (hosc :
      ∀ {ε : ℝ}, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ x y : spherePoint3, dist x y < δ → |f x - f y| ≤ ε) :
    Continuous f := by
  apply continuous_s2_of_pointwise_abs_oscillation
  intro x ε hε
  rcases hosc hε with ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  exact hlocal y x hy

private lemma s2FrameRange_bddBelow_of_nonneg
    {f : spherePoint3 → ℝ} (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) :
    BddBelow (Set.range f) := by
  exact ⟨0, by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact hnonneg x⟩

private lemma s2FrameRange_sInf_le
    {f : spherePoint3 → ℝ} (hnonneg : ∀ x : spherePoint3, 0 ≤ f x)
    (x : spherePoint3) :
    sInf (Set.range f) ≤ f x := by
  exact csInf_le (s2FrameRange_bddBelow_of_nonneg hnonneg) ⟨x, rfl⟩

private lemma s2FrameRange_sInf_nonneg
    {f : spherePoint3 → ℝ} (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) :
    0 ≤ sInf (Set.range f) := by
  have hne : (Set.range f).Nonempty := ⟨f sphereE1, ⟨sphereE1, rfl⟩⟩
  exact le_csInf hne (by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact hnonneg x)

private lemma IsSphereFrameFunction_sub_sInf_nonneg
    {f : spherePoint3 → ℝ} (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) :
    ∀ x : spherePoint3, 0 ≤ f x - sInf (Set.range f) := by
  intro x
  exact sub_nonneg.mpr (s2FrameRange_sInf_le hnonneg x)

private lemma IsSphereFrameFunction_value_le_standard_sum_of_nonneg
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) (x : spherePoint3) :
    f x ≤ f sphereE1 + f sphereE2 + f sphereE3 := by
  rcases exists_orthonormal_completion_of_spherePoint x with
    ⟨y, z, hyz, hyx, hzx⟩
  have hsum := hf y z x hyz hyx hzx
  have hy_nonneg := hnonneg y
  have hz_nonneg := hnonneg z
  linarith

private lemma IsSphereFrameFunction_standard_sum_nonneg_of_nonneg
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) :
    0 ≤ f sphereE1 + f sphereE2 + f sphereE3 := by
  have hsum :=
    hf sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  have h1 := hnonneg sphereE1
  have h2 := hnonneg sphereE2
  have h3 := hnonneg sphereE3
  linarith

private lemma IsSphereFrameFunction_abs_le_standard_sum_of_nonneg
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) (x : spherePoint3) :
    |f x| ≤ f sphereE1 + f sphereE2 + f sphereE3 := by
  rw [abs_of_nonneg (hnonneg x)]
  exact IsSphereFrameFunction_value_le_standard_sum_of_nonneg hf hnonneg x

private lemma s2FrameRange_bddAbove_of_frame_nonneg
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) :
    BddAbove (Set.range f) := by
  refine ⟨f sphereE1 + f sphereE2 + f sphereE3, ?_⟩
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact IsSphereFrameFunction_value_le_standard_sum_of_nonneg hf hnonneg x

private lemma IsSphereFrameFunction_range_subset_Icc_standard_sum_of_nonneg
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) :
    Set.range f ⊆ Set.Icc 0 (f sphereE1 + f sphereE2 + f sphereE3) := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact ⟨hnonneg x, IsSphereFrameFunction_value_le_standard_sum_of_nonneg hf hnonneg x⟩

private lemma s2_frame_continuity_principle_of_bounded_frame_continuity
    (hbounded :
      ∀ f : spherePoint3 → ℝ,
        IsSphereFrameFunction f →
        (∃ M : ℝ, ∀ x : spherePoint3, |f x| ≤ M) →
        Continuous f) :
    ∀ f : spherePoint3 → ℝ,
      IsSphereFrameFunction f →
      (∀ x : spherePoint3, 0 ≤ f x) →
      Continuous f := by
  intro f hf hnonneg
  exact hbounded f hf
    ⟨f sphereE1 + f sphereE2 + f sphereE3,
      IsSphereFrameFunction_abs_le_standard_sum_of_nonneg hf hnonneg⟩

private lemma exists_s2Frame_near_sInf
    {f : spherePoint3 → ℝ}
    {η : ℝ} (hη : 0 < η) :
    ∃ p : spherePoint3, f p < sInf (Set.range f) + η := by
  have hlt : sInf (Set.range f) < sInf (Set.range f) + η := by linarith
  have hne : (Set.range f).Nonempty := ⟨f sphereE1, ⟨sphereE1, rfl⟩⟩
  rcases exists_lt_of_csInf_lt hne hlt with ⟨y, hy, hylt⟩
  rcases hy with ⟨p, rfl⟩
  exact ⟨p, hylt⟩

private lemma spherePointOfCoord_norm (x : ℝ × ℝ × ℝ)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    ‖WithLp.toLp 2 (((x.1 : ℂ) + Complex.I * (x.2.1 : ℂ)), x.2.2)‖ = 1 := by
  let w : WithLp 2 (ℂ × ℝ) :=
    WithLp.toLp 2 (((x.1 : ℂ) + Complex.I * (x.2.1 : ℂ)), x.2.2)
  have hinner := (WithLp.prod_inner_apply (𝕜 := ℝ) w w)
  have hnormsq : ‖w‖ ^ 2 = ‖w.fst‖ ^ 2 + w.snd ^ 2 := by
    simpa [inner_self_eq_norm_sq_to_K, pow_two] using hinner
  have hfst : w.fst = ((x.1 : ℂ) + Complex.I * (x.2.1 : ℂ)) := by rfl
  have hsnd : w.snd = x.2.2 := by rfl
  have hcomplex : ‖w.fst‖ ^ 2 = x.1 ^ 2 + x.2.1 ^ 2 := by
    rw [hfst]
    simp [Complex.normSq, Complex.sq_norm]
    ring
  rw [hsnd, hcomplex] at hnormsq
  have hsq : ‖w‖ ^ 2 = 1 := by nlinarith [hnormsq, hx]
  have hsq' : ‖w‖ ^ 2 = (1 : ℝ) ^ 2 := by simpa using hsq
  exact (sq_eq_sq₀ (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 1)).1 hsq'

private def spherePointOfCoord (x : ℝ × ℝ × ℝ)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) : spherePoint3 :=
  ⟨WithLp.toLp 2 (((x.1 : ℂ) + Complex.I * (x.2.1 : ℂ)), x.2.2),
    spherePointOfCoord_norm x hx⟩

private lemma spherePointOfCoord_congr
    {x y : ℝ × ℝ × ℝ}
    {hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1}
    {hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1}
    (hxy : x = y) :
    spherePointOfCoord x hx = spherePointOfCoord y hy := by
  subst y
  apply Subtype.ext
  rfl

private lemma spherePointCoord_spherePointOfCoord (x : ℝ × ℝ × ℝ)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    spherePointCoord (spherePointOfCoord x hx) = x := by
  ext <;> simp [spherePointOfCoord, spherePointCoord]

private lemma spherePointOfCoord_spherePointCoord (x : spherePoint3) :
    spherePointOfCoord (spherePointCoord x) (spherePointCoord_sq_sum x) = x := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  change ((x.1.fst.re : ℂ) + Complex.I * (x.1.fst.im : ℂ), x.1.snd) =
    (x.1.fst, x.1.snd)
  congr
  · apply Complex.ext <;> simp

private abbrev coordSpherePoint3 :=
  {x : ℝ × ℝ × ℝ // x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1}

private def coordSphereToSphere (x : coordSpherePoint3) : spherePoint3 :=
  spherePointOfCoord x.1 x.2

private lemma continuous_coordSphereToSphere : Continuous coordSphereToSphere := by
  apply Continuous.subtype_mk
  change Continuous fun x : coordSpherePoint3 =>
    WithLp.toLp 2 ((((x.1.1 : ℝ) : ℂ) + Complex.I * ((x.1.2.1 : ℝ) : ℂ)), x.1.2.2)
  apply (WithLp.prod_continuous_toLp 2 ℂ ℝ).comp
  fun_prop

private def sphereToCoordSphere (x : spherePoint3) : coordSpherePoint3 :=
  ⟨spherePointCoord x, spherePointCoord_sq_sum x⟩

private lemma continuous_sphereToCoordSphere : Continuous sphereToCoordSphere := by
  exact continuous_spherePointCoord.subtype_mk fun x => spherePointCoord_sq_sum x

private lemma coordSphereToSphere_sphereToCoordSphere (x : spherePoint3) :
    coordSphereToSphere (sphereToCoordSphere x) = x := by
  exact spherePointOfCoord_spherePointCoord x

private lemma sphereToCoordSphere_coordSphereToSphere (x : coordSpherePoint3) :
    sphereToCoordSphere (coordSphereToSphere x) = x := by
  apply Subtype.ext
  exact spherePointCoord_spherePointOfCoord x.1 x.2

private def sphereOrthonormalBasis (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    OrthonormalBasis (Fin 3) ℝ (WithLp 2 (ℂ × ℝ)) := by
  let v := sphereTripleVec x y z
  have hv : Orthonormal ℝ v := sphereTripleVec_orthonormal x y z hxy hxz hyz
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (WithLp 2 (ℂ × ℝ)) := by
    rw [finrank_real_withLp_complex_prod_real]
    norm_num
  let b : Module.Basis (Fin 3) ℝ (WithLp 2 (ℂ × ℝ)) :=
    basisOfOrthonormalOfCardEqFinrank hv hcard
  have hb : (b : Fin 3 → WithLp 2 (ℂ × ℝ)) = v := by
    simpa [b] using coe_basisOfOrthonormalOfCardEqFinrank hv hcard
  exact b.toOrthonormalBasis (by
    rw [hb]
    exact hv)

private lemma sphereOrthonormalBasis_apply_zero (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereOrthonormalBasis x y z hxy hxz hyz 0 = x.1 := by
  simp [sphereOrthonormalBasis, sphereTripleVec]

private lemma sphereOrthonormalBasis_apply_two (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    sphereOrthonormalBasis x y z hxy hxz hyz 2 = z.1 := by
  simp [sphereOrthonormalBasis, sphereTripleVec]

private lemma exists_sphere_isometry_map_standard_pair
    {x p : spherePoint3}
    (hxp : inner (𝕜 := ℝ) x.1 p.1 = 0) :
    ∃ e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ),
      sphereMap e sphereE1 = x ∧ sphereMap e sphereE3 = p := by
  rcases exists_common_orthogonal_spherePoint x p with ⟨y, hxy, hpy⟩
  have hyp : inner (𝕜 := ℝ) y.1 p.1 = 0 := (inner_eq_zero_symm).2 hpy
  let bstd := sphereOrthonormalBasis sphereE1 sphereE2 sphereE3
    sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  let btgt := sphereOrthonormalBasis x y p hxy hxp hyp
  let e := bstd.equiv btgt (Equiv.refl (Fin 3))
  refine ⟨e, ?_, ?_⟩
  · apply Subtype.ext
    change e sphereE1.1 = x.1
    have hstd : bstd 0 = sphereE1.1 := by
      exact sphereOrthonormalBasis_apply_zero sphereE1 sphereE2 sphereE3
        sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
    have htgt : btgt 0 = x.1 := by
      exact sphereOrthonormalBasis_apply_zero x y p hxy hxp hyp
    rw [← hstd, ← htgt]
    exact OrthonormalBasis.equiv_apply_basis bstd btgt (Equiv.refl (Fin 3)) 0
  · apply Subtype.ext
    change e sphereE3.1 = p.1
    have hstd : bstd 2 = sphereE3.1 := by
      exact sphereOrthonormalBasis_apply_two sphereE1 sphereE2 sphereE3
        sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
    have htgt : btgt 2 = p.1 := by
      exact sphereOrthonormalBasis_apply_two x y p hxy hxp hyp
    rw [← hstd, ← htgt]
    exact OrthonormalBasis.equiv_apply_basis bstd btgt (Equiv.refl (Fin 3)) 2

private lemma sphereMap_dist
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (x y : spherePoint3) :
    dist (sphereMap e x) (sphereMap e y) = dist x y := by
  exact e.dist_map x.1 y.1

private lemma sphereMap_apply_symm_osc
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (x : spherePoint3) :
    sphereMap e (sphereMap e.symm x) = x := by
  apply Subtype.ext
  exact e.apply_symm_apply x.1

private lemma sphereMap_symm_apply_osc
    (e : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ))
    (x : spherePoint3) :
    sphereMap e.symm (sphereMap e x) = x := by
  apply Subtype.ext
  exact e.symm_apply_apply x.1

private lemma coordDot_polarQuarterTurnCoord
    (x y : ℝ × ℝ × ℝ) :
    coordDot (polarQuarterTurnCoord x) (polarQuarterTurnCoord y) =
      coordDot x y := by
  unfold coordDot polarQuarterTurnCoord
  ring

private lemma coordDot_targetFrameReparamSwap
    {x y z : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0) :
    coordDot (targetFrameReparamSwap x y) (targetFrameReparamSwap x z) =
      coordDot y z := by
  have hxx : coordDot x x = 1 := by
    simpa [coordDot, pow_two] using hx
  have hpp : coordDot (targetPoleCoord x) (targetPoleCoord x) = 1 := by
    simpa [coordDot, pow_two] using targetPoleCoord_sq_sum hρ
  have hbb : coordDot (targetBridgeCoord x) (targetBridgeCoord x) = 1 := by
    simpa [coordDot, pow_two] using targetBridgeCoord_sq_sum hx hρ
  have hxp : coordDot x (targetPoleCoord x) = 0 :=
    coordDot_target_targetPoleCoord hρ
  have hxb : coordDot x (targetBridgeCoord x) = 0 :=
    coordDot_target_targetBridgeCoord hρ
  have hpb : coordDot (targetPoleCoord x) (targetBridgeCoord x) = 0 :=
    coordDot_targetPole_targetBridgeCoord hρ
  have hpx : coordDot (targetPoleCoord x) x = 0 := by
    rw [coordDot_comm]
    exact hxp
  have hbx : coordDot (targetBridgeCoord x) x = 0 := by
    rw [coordDot_comm]
    exact hxb
  have hbp : coordDot (targetBridgeCoord x) (targetPoleCoord x) = 0 := by
    rw [coordDot_comm]
    exact hpb
  have hdot_x :
      coordDot x (coordLinearCombo z.1 z.2.1 z.2.2
        x (targetPoleCoord x) (targetBridgeCoord x)) = z.1 := by
    rw [coordDot_comm, coordDot_coordLinearCombo_right]
    simp [hxx, hpx, hbx]
  have hdot_p :
      coordDot (targetPoleCoord x) (coordLinearCombo z.1 z.2.1 z.2.2
        x (targetPoleCoord x) (targetBridgeCoord x)) = z.2.1 := by
    rw [coordDot_comm, coordDot_coordLinearCombo_right]
    simp [hxp, hpp, hbp]
  have hdot_b :
      coordDot (targetBridgeCoord x) (coordLinearCombo z.1 z.2.1 z.2.2
        x (targetPoleCoord x) (targetBridgeCoord x)) = z.2.2 := by
    rw [coordDot_comm, coordDot_coordLinearCombo_right]
    simp [hxb, hpb, hbb]
  change
    coordDot
        (coordLinearCombo y.1 y.2.1 y.2.2
          x (targetPoleCoord x) (targetBridgeCoord x))
        (coordLinearCombo z.1 z.2.1 z.2.2
          x (targetPoleCoord x) (targetBridgeCoord x)) =
      coordDot y z
  rw [coordDot_coordLinearCombo_right, hdot_x, hdot_p, hdot_b]
  rfl

private lemma targetFrameReparamSwap_sq_sum_coord
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0) :
    (targetFrameReparamSwap x y).1 ^ 2 +
        (targetFrameReparamSwap x y).2.1 ^ 2 +
        (targetFrameReparamSwap x y).2.2 ^ 2 = 1 := by
  have hdot :=
    coordDot_targetFrameReparamSwap (x := x) (y := y) (z := y) hx hρ
  have hy' : coordDot y y = 1 := by
    simpa [coordDot, pow_two] using hy
  have htarget : coordDot (targetFrameReparamSwap x y) (targetFrameReparamSwap x y) = 1 := by
    rw [hdot, hy']
  simpa [coordDot, pow_two] using htarget

private lemma targetFrameReparamSwap_vCoord (x : ℝ × ℝ × ℝ) :
    targetFrameReparamSwap x vCoord = targetPoleCoord x := by
  ext <;> simp [targetFrameReparamSwap, coordLinearCombo, vCoord]

private lemma targetFrameReparamSwap_poleCoord (x : ℝ × ℝ × ℝ) :
    targetFrameReparamSwap x poleCoord = targetBridgeCoord x := by
  ext <;> simp [targetFrameReparamSwap, coordLinearCombo, poleCoord]

private lemma coordDot_self_polarQuarterTurnCoord
    (x : ℝ × ℝ × ℝ) :
    coordDot x (polarQuarterTurnCoord x) = x.2.2 ^ 2 := by
  unfold coordDot polarQuarterTurnCoord
  ring

private lemma inner_spherePointOfCoord_eq_coordDot
    (x y : ℝ × ℝ × ℝ)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1) :
    inner (𝕜 := ℝ) (spherePointOfCoord x hx).1 (spherePointOfCoord y hy).1 =
      coordDot x y := by
  rw [← coordDot_spherePointCoord]
  simp [spherePointCoord_spherePointOfCoord]

private def s2QuarterTurn (x : spherePoint3) : spherePoint3 :=
  spherePointOfCoord (polarQuarterTurnCoord (spherePointCoord x))
    (polarQuarterTurnCoord_sq_sum (spherePointCoord_sq_sum x))

private lemma spherePointCoord_s2QuarterTurn (x : spherePoint3) :
    spherePointCoord (s2QuarterTurn x) =
      polarQuarterTurnCoord (spherePointCoord x) := by
  simp [s2QuarterTurn, spherePointCoord_spherePointOfCoord]

private lemma s2QuarterTurn_apply_val (x : spherePoint3) :
    (s2QuarterTurn x).1 =
      WithLp.toLp 2 (Complex.I * x.1.fst, x.1.snd) := by
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  change
    (((-(x.1.fst.im) : ℝ) : ℂ) +
        Complex.I * ((x.1.fst.re : ℝ) : ℂ), x.1.snd) =
      (Complex.I * x.1.fst, x.1.snd)
  congr 1
  apply Complex.ext <;> simp

private lemma s2QuarterTurn_sphereMap_northRotation
    (t : ℝ) (x : spherePoint3) :
  s2QuarterTurn (sphereMap (northRotation t) x) =
      sphereMap (northRotation t) (s2QuarterTurn x) := by
  apply Subtype.ext
  conv_lhs => rw [s2QuarterTurn_apply_val]
  change WithLp.toLp 2
      (Complex.I * (northRotation t x.1).fst, (northRotation t x.1).snd) =
    northRotation t (s2QuarterTurn x).1
  rw [s2QuarterTurn_apply_val, northRotation_apply, northRotation_apply]
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  let c : ℂ := ((Circle.exp t : Circle) : ℂ)
  change (Complex.I * (c * x.1.fst), x.1.snd) =
    (c * (Complex.I * x.1.fst), x.1.snd)
  congr 1
  ring

private lemma third_coord_lt_one_of_horizontalRadius_ne_zero
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hρ : horizontalRadius z ≠ 0) :
    z.2.2 < 1 := by
  by_contra hnot
  have hge : 1 ≤ z.2.2 := le_of_not_gt hnot
  have hsum : z.1 ^ 2 + z.2.1 ^ 2 = 0 := by
    nlinarith [hz, sq_nonneg z.1, sq_nonneg z.2.1]
  have hρsq : horizontalRadius z ^ 2 = 0 := by
    rw [horizontalRadius_sq]
    exact hsum
  exact hρ (sq_eq_zero_iff.mp hρsq)

private lemma northCanonical_spherePointOfCoord
    (z : ℝ × ℝ × ℝ)
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1) :
    northCanonical (spherePointOfCoord z hz) =
      spherePointOfCoord (horizontalRadius z, (0, z.2.2)) (by
        rw [horizontalRadius_sq]
        nlinarith [hz]) := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  change
    ((‖((z.1 : ℂ) + Complex.I * (z.2.1 : ℂ))‖ : ℂ), z.2.2) =
      (((horizontalRadius z : ℝ) : ℂ) + Complex.I * ((0 : ℝ) : ℂ), z.2.2)
  congr 1
  rw [Complex.norm_def]
  simp [Complex.normSq, horizontalRadius]
  congr 1
  ring

private lemma exists_northRotation_northMeridianCoord
    {z : ℝ × ℝ × ℝ}
    (hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1)
    (hzpos : 0 < z.2.2)
    (hρ : horizontalRadius z ≠ 0) :
    ∃ θ t : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧
      sphereMap (northRotation t)
          (spherePointOfCoord (northMeridianCoord θ) (northMeridianCoord_sq_sum θ)) =
        spherePointOfCoord z hz := by
  let zs : spherePoint3 := spherePointOfCoord z hz
  let θ : ℝ := Real.arcsin z.2.2
  have hzlt : z.2.2 < 1 := third_coord_lt_one_of_horizontalRadius_ne_zero hz hρ
  have hθ := arcsin_mem_open_quarter hzpos hzlt
  have hcoord : northMeridianCoord θ = (0, (horizontalRadius z, z.2.2)) := by
    exact northMeridianCoord_arcsin hz (le_of_lt hzpos)
  have hmeridian :
      spherePointOfCoord (northMeridianCoord θ) (northMeridianCoord_sq_sum θ) =
        sphereMap (northRotation (Real.pi / 2)) (northCanonical zs) := by
    rw [northCanonical_spherePointOfCoord z hz]
    apply Subtype.ext
    apply (WithLp.equiv 2 (ℂ × ℝ)).injective
    simp [hcoord, sphereMap, spherePointOfCoord, northRotation_apply, Circle.coe_exp,
      Complex.exp_mul_I]
  rcases exists_northRotation_northCanonical zs with ⟨t, ht⟩
  refine ⟨θ, t - Real.pi / 2, hθ.1, hθ.2, ?_⟩
  rw [hmeridian]
  rw [← sphereMap_northRotation_add]
  convert ht using 1 <;> ring_nf

private lemma inner_s2QuarterTurn (x y : spherePoint3) :
    inner (𝕜 := ℝ) (s2QuarterTurn x).1 (s2QuarterTurn y).1 =
      inner (𝕜 := ℝ) x.1 y.1 := by
  rw [← coordDot_spherePointCoord (s2QuarterTurn x) (s2QuarterTurn y),
    spherePointCoord_s2QuarterTurn, spherePointCoord_s2QuarterTurn,
    coordDot_polarQuarterTurnCoord, coordDot_spherePointCoord]

private lemma IsSphereFrameFunction_comp_s2QuarterTurn
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f) :
    IsSphereFrameFunction (fun x => f (s2QuarterTurn x)) := by
  intro x y z hxy hxz hyz
  have hxy' :
      inner (𝕜 := ℝ) (s2QuarterTurn x).1 (s2QuarterTurn y).1 = 0 := by
    rw [inner_s2QuarterTurn, hxy]
  have hxz' :
      inner (𝕜 := ℝ) (s2QuarterTurn x).1 (s2QuarterTurn z).1 = 0 := by
    rw [inner_s2QuarterTurn, hxz]
  have hyz' :
      inner (𝕜 := ℝ) (s2QuarterTurn y).1 (s2QuarterTurn z).1 = 0 := by
    rw [inner_s2QuarterTurn, hyz]
  have hE12 :
      inner (𝕜 := ℝ) (s2QuarterTurn sphereE1).1 (s2QuarterTurn sphereE2).1 = 0 := by
    rw [inner_s2QuarterTurn, sphereE1_inner_sphereE2]
  have hE13 :
      inner (𝕜 := ℝ) (s2QuarterTurn sphereE1).1 (s2QuarterTurn sphereE3).1 = 0 := by
    rw [inner_s2QuarterTurn, sphereE1_inner_sphereE3]
  have hE23 :
      inner (𝕜 := ℝ) (s2QuarterTurn sphereE2).1 (s2QuarterTurn sphereE3).1 = 0 := by
    rw [inner_s2QuarterTurn, sphereE2_inner_sphereE3]
  have hconst :=
    hf (s2QuarterTurn sphereE1) (s2QuarterTurn sphereE2) (s2QuarterTurn sphereE3)
      hE12 hE13 hE23
  calc
    f (s2QuarterTurn x) + f (s2QuarterTurn y) + f (s2QuarterTurn z)
        = f sphereE1 + f sphereE2 + f sphereE3 := by
            exact hf (s2QuarterTurn x) (s2QuarterTurn y) (s2QuarterTurn z)
              hxy' hxz' hyz'
    _ = f (s2QuarterTurn sphereE1) +
          f (s2QuarterTurn sphereE2) +
          f (s2QuarterTurn sphereE3) := by
            exact hconst.symm

private def s2QuarterTurnAverage (f : spherePoint3 → ℝ) : spherePoint3 → ℝ :=
  fun x => (f x + f (s2QuarterTurn x)) / 2

private lemma IsSphereFrameFunction_s2QuarterTurnAverage
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f) :
    IsSphereFrameFunction (s2QuarterTurnAverage f) := by
  intro x y z hxy hxz hyz
  have hmain := hf x y z hxy hxz hyz
  have hturn :=
    IsSphereFrameFunction_comp_s2QuarterTurn hf x y z hxy hxz hyz
  unfold s2QuarterTurnAverage
  linarith

private lemma s2QuarterTurnAverage_nonneg
    {f : spherePoint3 → ℝ} (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) :
    ∀ x : spherePoint3, 0 ≤ s2QuarterTurnAverage f x := by
  intro x
  unfold s2QuarterTurnAverage
  linarith [hnonneg x, hnonneg (s2QuarterTurn x)]

private def sphereLinearComboPoint
    (x y : spherePoint3) (a b : ℝ)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hab : a ^ 2 + b ^ 2 = 1) : spherePoint3 :=
  ⟨a • x.1 + b • y.1, by
    have horth : inner (𝕜 := ℝ) (a • x.1) (b • y.1) = 0 := by
      rw [inner_smul_left, inner_smul_right, hxy]
      simp
    have hsq :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
        (x := a • x.1) (y := b • y.1) horth
    have hx : ‖x.1‖ = 1 := x.2
    have hy : ‖y.1‖ = 1 := y.2
    have hsq' : ‖a • x.1 + b • y.1‖ ^ 2 = 1 := by
      rw [show ‖a • x.1 + b • y.1‖ ^ 2 =
          ‖a • x.1 + b • y.1‖ * ‖a • x.1 + b • y.1‖ by ring]
      rw [hsq]
      simp [norm_smul, hx, hy, Real.norm_eq_abs]
      nlinarith [sq_abs a, sq_abs b, hab]
    exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).1
      (by simpa using hsq')⟩

private lemma IsSphereFrameFunction_pair_sum_coeff
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {x y : spherePoint3}
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    f (sphereLinearComboPoint x y a b hxy hab) +
      f (sphereLinearComboPoint x y b (-a) hxy (by nlinarith [hab])) =
    f x + f y := by
  rcases exists_common_orthogonal_spherePoint x y with ⟨z, hxz, hyz⟩
  let A : spherePoint3 := sphereLinearComboPoint x y a b hxy hab
  let B : spherePoint3 := sphereLinearComboPoint x y b (-a) hxy (by nlinarith [hab])
  have hyx : inner (𝕜 := ℝ) y.1 x.1 = 0 := by
    exact (inner_eq_zero_symm).mp hxy
  have hAz : inner (𝕜 := ℝ) A.1 z.1 = 0 := by
    change inner (𝕜 := ℝ) (a • x.1 + b • y.1) z.1 = 0
    rw [inner_add_left, inner_smul_left, inner_smul_left, hxz, hyz]
    simp
  have hBz : inner (𝕜 := ℝ) B.1 z.1 = 0 := by
    change inner (𝕜 := ℝ) (b • x.1 + (-a) • y.1) z.1 = 0
    rw [inner_add_left, inner_smul_left, inner_smul_left, hxz, hyz]
    simp
  have hAB : inner (𝕜 := ℝ) A.1 B.1 = 0 := by
    change inner (𝕜 := ℝ) (a • x.1 + b • y.1) (b • x.1 + (-a) • y.1) = 0
    simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      hxy, hyx, inner_self_eq_norm_sq_to_K, x.2, y.2]
    ring
  have h₁ := hf A B z hAB hAz hBz
  have h₂ := hf x y z hxy hxz hyz
  simpa [A, B] using (by linarith : f A + f B = f x + f y)

private lemma southCoord_sq_sum (α : ℝ) :
    (southCoord α).1 ^ 2 + (southCoord α).2.1 ^ 2 + (southCoord α).2.2 ^ 2 = 1 := by
  simp [southCoord]

private lemma coordDot_southCoord_ambientRCoord
    {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    coordDot (southCoord α) (ambientRCoord α x) = 0 := by
  unfold coordDot southCoord ambientRCoord southInnerCoord
  field_simp [hden]
  ring_nf
  have hcos2 : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq α]
  have hcos3 : Real.cos α ^ 3 = Real.cos α * (1 - Real.sin α ^ 2) := by
    calc
      Real.cos α ^ 3 = Real.cos α * Real.cos α ^ 2 := by ring
      _ = Real.cos α * (1 - Real.sin α ^ 2) := by rw [hcos2]
  rw [hcos3, hcos2]
  ring

private lemma ambientRCoord_sq_sum_coord
    {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    (ambientRCoord α x).1 ^ 2 + (ambientRCoord α x).2.1 ^ 2 +
        (ambientRCoord α x).2.2 ^ 2 = 1 := by
  let s : ℝ := southInnerCoord α x
  have hsd : southDenCoord α x ^ 2 = 1 - s ^ 2 := by
    simpa [s] using southDenCoord_sq (α := α) (x := x) hx
  unfold ambientRCoord
  field_simp [hden]
  change (x.1 - s * Real.cos α) ^ 2 + x.2.1 ^ 2 +
      (x.2.2 + s * Real.sin α) ^ 2 = southDenCoord α x ^ 2
  rw [hsd]
  dsimp [s, southInnerCoord]
  nlinarith [Real.sin_sq_add_cos_sq α, hx]

private lemma ambientQCoord_sq_sum_coord
    {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    (ambientQCoord α x).1 ^ 2 + (ambientQCoord α x).2.1 ^ 2 +
        (ambientQCoord α x).2.2 ^ 2 = 1 := by
  let s : ℝ := southInnerCoord α x
  have hsd : southDenCoord α x ^ 2 = 1 - s ^ 2 := by
    simpa [s] using southDenCoord_sq (α := α) (x := x) hx
  unfold ambientQCoord
  field_simp [hden]
  rw [hsd]
  dsimp [s, southInnerCoord]
  nlinarith [Real.sin_sq_add_cos_sq α, hx]

private lemma spherePointCoord_injective :
    Function.Injective spherePointCoord := by
  intro x y hxy
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  change (x.1.fst, x.1.snd) = (y.1.fst, y.1.snd)
  have hx1 : (spherePointCoord x).1 = (spherePointCoord y).1 := by
    simpa using congrArg Prod.fst hxy
  have hx2 : (spherePointCoord x).2.1 = (spherePointCoord y).2.1 := by
    simpa using congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) hxy
  have hx3 : (spherePointCoord x).2.2 = (spherePointCoord y).2.2 := by
    simpa using congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) hxy
  ext
  · apply Complex.ext
    · simpa [spherePointCoord] using hx1
    · simpa [spherePointCoord] using hx2
  · simpa [spherePointCoord] using hx3

private lemma sphereLinearComboPoint_south_ambientRCoord
    {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    sphereLinearComboPoint
        (spherePointOfCoord (southCoord α) (southCoord_sq_sum α))
        (spherePointOfCoord (ambientRCoord α x)
          (ambientRCoord_sq_sum_coord hx hden))
        (southInnerCoord α x) (southDenCoord α x)
        (by
          rw [inner_spherePointOfCoord_eq_coordDot]
          exact coordDot_southCoord_ambientRCoord hx hden)
        (southInnerCoord_sq_add_southDenCoord_sq hx) =
      spherePointOfCoord x hx := by
  apply spherePointCoord_injective
  ext
  · simp [spherePointCoord, sphereLinearComboPoint, spherePointOfCoord,
      southCoord, ambientRCoord]
    field_simp [hden]
    simp [Complex.cos_ofReal_re]
  · simp [spherePointCoord, sphereLinearComboPoint, spherePointOfCoord,
      southCoord, ambientRCoord]
    field_simp [hden]
  · simp [spherePointCoord, sphereLinearComboPoint, spherePointOfCoord,
      southCoord, ambientRCoord]
    field_simp [hden]
    ring

private lemma sphereLinearComboPoint_south_ambientRCoord_perp
    {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    sphereLinearComboPoint
        (spherePointOfCoord (southCoord α) (southCoord_sq_sum α))
        (spherePointOfCoord (ambientRCoord α x)
          (ambientRCoord_sq_sum_coord hx hden))
        (southDenCoord α x) (-(southInnerCoord α x))
        (by
          rw [inner_spherePointOfCoord_eq_coordDot]
          exact coordDot_southCoord_ambientRCoord hx hden)
        (by
          have h := southInnerCoord_sq_add_southDenCoord_sq (α := α) (x := x) hx
          nlinarith) =
      sphereAntipode
        (spherePointOfCoord (ambientQCoord α x)
          (ambientQCoord_sq_sum_coord hx hden)) := by
  apply spherePointCoord_injective
  ext
  · simp [spherePointCoord, sphereLinearComboPoint, spherePointOfCoord,
      sphereAntipode, sphereMap, southCoord, ambientRCoord, ambientQCoord]
    field_simp [hden]
    simp [Complex.cos_ofReal_re]
    ring_nf
    have hsum := southInnerCoord_sq_add_southDenCoord_sq (α := α) (x := x) hx
    ring_nf at hsum ⊢
    have hcosSum :
        southInnerCoord α x ^ 2 * Real.cos α +
            southDenCoord α x ^ 2 * Real.cos α = Real.cos α := by
      calc
        southInnerCoord α x ^ 2 * Real.cos α +
            southDenCoord α x ^ 2 * Real.cos α =
          (southInnerCoord α x ^ 2 + southDenCoord α x ^ 2) * Real.cos α := by ring
        _ = 1 * Real.cos α := by rw [hsum]
        _ = Real.cos α := by ring
    nlinarith [hcosSum]
  · simp [spherePointCoord, sphereLinearComboPoint, spherePointOfCoord,
      sphereAntipode, sphereMap, southCoord, ambientRCoord, ambientQCoord]
    field_simp [hden]
  · simp [spherePointCoord, sphereLinearComboPoint, spherePointOfCoord,
      sphereAntipode, sphereMap, southCoord, ambientRCoord, ambientQCoord]
    field_simp [hden]
    ring_nf
    have hsum := southInnerCoord_sq_add_southDenCoord_sq (α := α) (x := x) hx
    ring_nf at hsum ⊢
    have hsinSum :
        -(southInnerCoord α x ^ 2 * Real.sin α) -
            southDenCoord α x ^ 2 * Real.sin α = -Real.sin α := by
      calc
        -(southInnerCoord α x ^ 2 * Real.sin α) -
            southDenCoord α x ^ 2 * Real.sin α =
          -(southInnerCoord α x ^ 2 + southDenCoord α x ^ 2) * Real.sin α := by ring
        _ = -1 * Real.sin α := by rw [hsum]
        _ = -Real.sin α := by ring
    nlinarith [hsinSum]

private lemma IsSphereFrameFunction_south_ambientR_sum
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {α : ℝ} {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hden : southDenCoord α x ≠ 0) :
    f (spherePointOfCoord (southCoord α) (southCoord_sq_sum α)) +
        f (spherePointOfCoord (ambientRCoord α x)
          (ambientRCoord_sq_sum_coord hx hden)) =
      f (spherePointOfCoord x hx) +
        f (spherePointOfCoord (ambientQCoord α x)
          (ambientQCoord_sq_sum_coord hx hden)) := by
  let S : spherePoint3 := spherePointOfCoord (southCoord α) (southCoord_sq_sum α)
  let R : spherePoint3 :=
    spherePointOfCoord (ambientRCoord α x) (ambientRCoord_sq_sum_coord hx hden)
  have hSR : inner (𝕜 := ℝ) S.1 R.1 = 0 := by
    change inner (𝕜 := ℝ)
        (spherePointOfCoord (southCoord α) (southCoord_sq_sum α)).1
        (spherePointOfCoord (ambientRCoord α x)
          (ambientRCoord_sq_sum_coord hx hden)).1 = 0
    rw [inner_spherePointOfCoord_eq_coordDot]
    exact coordDot_southCoord_ambientRCoord hx hden
  have hpair :=
    IsSphereFrameFunction_pair_sum_coeff (f := f) hf hSR
      (a := southInnerCoord α x) (b := southDenCoord α x)
      (southInnerCoord_sq_add_southDenCoord_sq (α := α) (x := x) hx)
  have hX :
      sphereLinearComboPoint S R (southInnerCoord α x) (southDenCoord α x) hSR
          (southInnerCoord_sq_add_southDenCoord_sq hx) =
        spherePointOfCoord x hx := by
    simpa [S, R] using sphereLinearComboPoint_south_ambientRCoord hx hden
  have hQ :
      sphereLinearComboPoint S R (southDenCoord α x) (-(southInnerCoord α x)) hSR
          (by
            have h := southInnerCoord_sq_add_southDenCoord_sq (α := α) (x := x) hx
            nlinarith) =
        sphereAntipode
          (spherePointOfCoord (ambientQCoord α x)
            (ambientQCoord_sq_sum_coord hx hden)) := by
    simpa [S, R] using sphereLinearComboPoint_south_ambientRCoord_perp hx hden
  rw [hX, hQ, IsSphereFrameFunction_even hf] at hpair
  simpa [S, R, add_comm] using hpair.symm

private lemma exists_small_ambient_companion_cap_coords
    {ε : ℝ} (hε : 0 < ε) :
    ∃ α δ : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < δ ∧
      ∀ {x : ℝ × ℝ × ℝ}, dist x coordBase < δ →
        0 < southDenCoord α x ∧
        dist (ambientQCoord α x) poleCoord < ε ∧
        dist (ambientRCoord α x) poleCoord < ε := by
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
  intro x hx
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
  have hqcoord_pole : dist (ambientQCoord α x) poleCoord < ε := by
    have hqcoord_pole' : dist (ambientQCoord α x) poleCoord < ε / 3 := by
      simpa [ambientQCoord_base hα0 hαpi] using hqcoord
    nlinarith
  have hrcoord_base :
      dist (ambientRCoord α x) (northCoord α) < ε / 6 := by
    simpa [northCoord, ambientRCoord_base hα0 hαpi] using hrcoord
  have hrcoord_pole : dist (ambientRCoord α x) poleCoord < ε := by
    have htri := dist_triangle (ambientRCoord α x) (northCoord α) poleCoord
    exact lt_of_le_of_lt htri (by nlinarith)
  exact ⟨hden_pos, hqcoord_pole, hrcoord_pole⟩

private lemma s2_ambient_oscillation_bound_of_cap_coords
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {a ε : ℝ} (hε : 0 < ε)
    (hosc :
      ∀ {x y : ℝ × ℝ × ℝ},
        ∀ (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1),
        ∀ (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1),
        dist x poleCoord < ε →
        dist y poleCoord < ε →
        |f (spherePointOfCoord x hx) - f (spherePointOfCoord y hy)| ≤ a) :
    ∃ α δ : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        ∀ (hx₁ : x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1),
        ∀ (hx₂ : x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1),
        dist x₁ coordBase < δ →
        dist x₂ coordBase < δ →
        |f (spherePointOfCoord x₁ hx₁) - f (spherePointOfCoord x₂ hx₂)| ≤
          2 * a := by
  rcases exists_small_ambient_companion_cap_coords hε with
    ⟨α, δ, hα0, hαpi, hδ, hcap⟩
  refine ⟨α, δ, hα0, hαpi, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdist₁ hdist₂
  rcases hcap hdist₁ with ⟨hden₁pos, hq₁p, hr₁p⟩
  rcases hcap hdist₂ with ⟨hden₂pos, hq₂p, hr₂p⟩
  have hden₁ : southDenCoord α x₁ ≠ 0 := ne_of_gt hden₁pos
  have hden₂ : southDenCoord α x₂ ≠ 0 := ne_of_gt hden₂pos
  have hqbound :
      |f (spherePointOfCoord (ambientQCoord α x₂)
            (ambientQCoord_sq_sum_coord hx₂ hden₂)) -
        f (spherePointOfCoord (ambientQCoord α x₁)
            (ambientQCoord_sq_sum_coord hx₁ hden₁))| ≤ a := by
    exact hosc (ambientQCoord_sq_sum_coord hx₂ hden₂)
      (ambientQCoord_sq_sum_coord hx₁ hden₁) hq₂p hq₁p
  have hrbound :
      |f (spherePointOfCoord (ambientRCoord α x₁)
            (ambientRCoord_sq_sum_coord hx₁ hden₁)) -
        f (spherePointOfCoord (ambientRCoord α x₂)
            (ambientRCoord_sq_sum_coord hx₂ hden₂))| ≤ a := by
    exact hosc (ambientRCoord_sq_sum_coord hx₁ hden₁)
      (ambientRCoord_sq_sum_coord hx₂ hden₂) hr₁p hr₂p
  have hsum₁ :=
    IsSphereFrameFunction_south_ambientR_sum (f := f) hf hx₁ hden₁
  have hsum₂ :=
    IsSphereFrameFunction_south_ambientR_sum (f := f) hf hx₂ hden₂
  have hEq :
      f (spherePointOfCoord x₁ hx₁) - f (spherePointOfCoord x₂ hx₂) =
        (f (spherePointOfCoord (ambientRCoord α x₁)
              (ambientRCoord_sq_sum_coord hx₁ hden₁)) -
          f (spherePointOfCoord (ambientRCoord α x₂)
              (ambientRCoord_sq_sum_coord hx₂ hden₂))) +
        (f (spherePointOfCoord (ambientQCoord α x₂)
              (ambientQCoord_sq_sum_coord hx₂ hden₂)) -
          f (spherePointOfCoord (ambientQCoord α x₁)
              (ambientQCoord_sq_sum_coord hx₁ hden₁))) := by
    linarith
  calc
    |f (spherePointOfCoord x₁ hx₁) - f (spherePointOfCoord x₂ hx₂)|
        =
      |(f (spherePointOfCoord (ambientRCoord α x₁)
            (ambientRCoord_sq_sum_coord hx₁ hden₁)) -
        f (spherePointOfCoord (ambientRCoord α x₂)
            (ambientRCoord_sq_sum_coord hx₂ hden₂))) +
       (f (spherePointOfCoord (ambientQCoord α x₂)
            (ambientQCoord_sq_sum_coord hx₂ hden₂)) -
        f (spherePointOfCoord (ambientQCoord α x₁)
            (ambientQCoord_sq_sum_coord hx₁ hden₁)))| := by
          rw [hEq]
    _ ≤
      |f (spherePointOfCoord (ambientRCoord α x₁)
            (ambientRCoord_sq_sum_coord hx₁ hden₁)) -
        f (spherePointOfCoord (ambientRCoord α x₂)
            (ambientRCoord_sq_sum_coord hx₂ hden₂))| +
      |f (spherePointOfCoord (ambientQCoord α x₂)
            (ambientQCoord_sq_sum_coord hx₂ hden₂)) -
        f (spherePointOfCoord (ambientQCoord α x₁)
            (ambientQCoord_sq_sum_coord hx₁ hden₁))| := by
          exact abs_add_le _ _
    _ ≤ a + a := add_le_add hrbound hqbound
    _ = 2 * a := by ring

private lemma s2_base_oscillation_bound_of_cap_coords
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {a ε : ℝ} (hε : 0 < ε)
    (hosc :
      ∀ {x y : ℝ × ℝ × ℝ},
        ∀ (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1),
        ∀ (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1),
        dist x poleCoord < ε →
        dist y poleCoord < ε →
        |f (spherePointOfCoord x hx) - f (spherePointOfCoord y hy)| ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        ∀ (hx₁ : x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1),
        ∀ (hx₂ : x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1),
        dist x₁ coordBase < δ →
        dist x₂ coordBase < δ →
        |f (spherePointOfCoord x₁ hx₁) - f (spherePointOfCoord x₂ hx₂)| ≤
          2 * a := by
  rcases s2_ambient_oscillation_bound_of_cap_coords
      (f := f) hf hε hosc with
    ⟨_α, δ, _hα0, _hαpi, hδ, hlocal⟩
  exact ⟨δ, hδ, hlocal⟩

private lemma s2_base_oscillation_bound_of_cap
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {a ε : ℝ} (hε : 0 < ε)
    (hosc :
      ∀ {x y : spherePoint3},
        dist x sphereE3 < ε →
        dist y sphereE3 < ε →
        |f x - f y| ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : spherePoint3},
        dist x sphereE1 < δ →
        dist y sphereE1 < δ →
        |f x - f y| ≤ 2 * a := by
  let pole : coordSpherePoint3 := ⟨poleCoord, by norm_num [poleCoord]⟩
  have hpole : coordSphereToSphere pole = sphereE3 := by
    apply Subtype.ext
    simp [coordSphereToSphere, pole, spherePointOfCoord, poleCoord, sphereE3]
  rcases (Metric.continuousAt_iff.mp continuous_coordSphereToSphere.continuousAt)
      ε hε with ⟨εc, hεc, htoSphere⟩
  have hoscCoords :
      ∀ {x y : ℝ × ℝ × ℝ},
        ∀ (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1),
        ∀ (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1),
        dist x poleCoord < εc →
        dist y poleCoord < εc →
        |f (spherePointOfCoord x hx) - f (spherePointOfCoord y hy)| ≤ a := by
    intro x y hx hy hdx hdy
    let xs : coordSpherePoint3 := ⟨x, hx⟩
    let ys : coordSpherePoint3 := ⟨y, hy⟩
    have hdx' : dist xs pole < εc := by
      simpa [xs, pole] using hdx
    have hdy' : dist ys pole < εc := by
      simpa [ys, pole] using hdy
    have hdxSphere : dist (coordSphereToSphere xs) sphereE3 < ε := by
      simpa [hpole] using htoSphere hdx'
    have hdySphere : dist (coordSphereToSphere ys) sphereE3 < ε := by
      simpa [hpole] using htoSphere hdy'
    exact hosc hdxSphere hdySphere
  rcases s2_base_oscillation_bound_of_cap_coords
      (f := f) hf hεc hoscCoords with ⟨δc, hδc, hbase⟩
  rcases (Metric.continuousAt_iff.mp continuous_sphereToCoordSphere.continuousAt)
      δc hδc with ⟨δ, hδ, htoCoords⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hdx hdy
  have hbaseCoord : sphereToCoordSphere sphereE1 =
      (⟨coordBase, by norm_num [coordBase]⟩ : coordSpherePoint3) := by
    apply Subtype.ext
    exact spherePointCoord_sphereE1
  have hdxCoords : dist (spherePointCoord x) coordBase < δc := by
    have := htoCoords hdx
    simpa [sphereToCoordSphere, hbaseCoord] using this
  have hdyCoords : dist (spherePointCoord y) coordBase < δc := by
    have := htoCoords hdy
    simpa [sphereToCoordSphere, hbaseCoord] using this
  have hbound := hbase (spherePointCoord_sq_sum x) (spherePointCoord_sq_sum y)
      hdxCoords hdyCoords
  simpa [spherePointOfCoord_spherePointCoord] using hbound

private lemma s2_orthogonal_oscillation_bound_of_cap
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {a ε : ℝ} (hε : 0 < ε)
    {p x : spherePoint3}
    (hxp : inner (𝕜 := ℝ) x.1 p.1 = 0)
    (hosc :
      ∀ {y z : spherePoint3},
        dist y p < ε →
        dist z p < ε →
        |f y - f z| ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {y z : spherePoint3},
        dist y x < δ →
        dist z x < δ →
        |f y - f z| ≤ 2 * a := by
  rcases exists_sphere_isometry_map_standard_pair hxp with ⟨e, he1, he3⟩
  let g : spherePoint3 → ℝ := fun y => f (sphereMap e y)
  have hg : IsSphereFrameFunction g :=
    isSphereFrameFunction_comp_sphereMap e hf
  have hgCap :
      ∀ {y z : spherePoint3},
        dist y sphereE3 < ε →
        dist z sphereE3 < ε →
        |g y - g z| ≤ a := by
    intro y z hdy hdz
    apply hosc
    · rw [← he3, sphereMap_dist]
      exact hdy
    · rw [← he3, sphereMap_dist]
      exact hdz
  rcases s2_base_oscillation_bound_of_cap (f := g) hg hε hgCap with
    ⟨δ, hδ, hbase⟩
  refine ⟨δ, hδ, ?_⟩
  intro y z hdy hdz
  let y' := sphereMap e.symm y
  let z' := sphereMap e.symm z
  have he1' : sphereMap e.symm x = sphereE1 := by
    calc
      sphereMap e.symm x = sphereMap e.symm (sphereMap e sphereE1) := by rw [he1]
      _ = sphereE1 := sphereMap_symm_apply_osc e sphereE1
  have hdy' : dist y' sphereE1 < δ := by
    calc
      dist y' sphereE1 = dist (sphereMap e.symm y) (sphereMap e.symm x) := by
        rw [he1']
      _ = dist y x := sphereMap_dist e.symm y x
      _ < δ := hdy
  have hdz' : dist z' sphereE1 < δ := by
    calc
      dist z' sphereE1 = dist (sphereMap e.symm z) (sphereMap e.symm x) := by
        rw [he1']
      _ = dist z x := sphereMap_dist e.symm z x
      _ < δ := hdz
  have hbound := hbase hdy' hdz'
  simpa [g, y', z', sphereMap_apply_symm_osc] using hbound

private lemma s2_global_oscillation_bound_of_cap
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {a ε : ℝ} (hε : 0 < ε)
    {p : spherePoint3}
    (hosc :
      ∀ {x y : spherePoint3},
        dist x p < ε →
        dist y p < ε →
        |f x - f y| ≤ a) :
    ∀ z : spherePoint3,
      ∃ δ : ℝ, 0 < δ ∧
        ∀ {x y : spherePoint3},
          dist x z < δ →
          dist y z < δ →
          |f x - f y| ≤ 4 * a := by
  intro z
  rcases exists_common_orthogonal_spherePoint p z with ⟨q, hpq, hzq⟩
  have hqp : inner (𝕜 := ℝ) q.1 p.1 = 0 := (inner_eq_zero_symm).2 hpq
  rcases s2_orthogonal_oscillation_bound_of_cap
      (f := f) hf hε hqp hosc with ⟨εq, hεq, hqCap⟩
  rcases s2_orthogonal_oscillation_bound_of_cap
      (f := f) hf hεq hzq hqCap with ⟨δ, hδ, hzCap⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hdx hdy
  have hbound := hzCap hdx hdy
  convert hbound using 1 <;> ring

private lemma coordSphereFrameFun_base_oscillation_bound_of_coord_cap
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (hε : 0 < ε)
    (hcap :
      ∀ {x y : ℝ × ℝ × ℝ},
        ∀ (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1),
        ∀ (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1),
        dist x poleCoord < ε →
        dist y poleCoord < ε →
        |frame_quadratic (H := H) μ (coordPoint u v p x) -
          frame_quadratic (H := H) μ (coordPoint u v p y)| ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        ∀ (hx₁ : x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1),
        ∀ (hx₂ : x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1),
        dist x₁ coordBase < δ →
        dist x₂ coordBase < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p x₁) -
          frame_quadratic (H := H) μ (coordPoint u v p x₂)| ≤
          2 * a := by
  let f : spherePoint3 → ℝ := coordSphereFrameFun μ u v p
  have hf : IsSphereFrameFunction f := by
    show f ∈ sphereFrameSubmodule
    exact coordSphereFrameFun_mem_sphereFrameSubmodule_osc μ hu hv hp huv hup hvp
  have hcap' :
      ∀ {x y : ℝ × ℝ × ℝ},
        ∀ (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1),
        ∀ (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1),
        dist x poleCoord < ε →
        dist y poleCoord < ε →
        |f (spherePointOfCoord x hx) - f (spherePointOfCoord y hy)| ≤ a := by
    intro x y hx hy hdx hdy
    simpa [f, coordSphereFrameFun, spherePointCoord_spherePointOfCoord] using
      hcap hx hy hdx hdy
  rcases s2_base_oscillation_bound_of_cap_coords
      (f := f) hf hε hcap' with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro x₁ x₂ hx₁ hx₂ hdx₁ hdx₂
  simpa [f, coordSphereFrameFun, spherePointCoord_spherePointOfCoord] using
    hlocal hx₁ hx₂ hdx₁ hdx₂

private lemma coordSphereFrameFun_base_oscillation_bound_of_H_pole_cap
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {a ε : ℝ} (hε : 0 < ε)
    (hcap :
      ∀ {x y : ℝ × ℝ × ℝ},
        ∀ (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1),
        ∀ (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1),
        dist (coordPoint u v p x) p < ε →
        dist (coordPoint u v p y) p < ε →
        |frame_quadratic (H := H) μ (coordPoint u v p x) -
          frame_quadratic (H := H) μ (coordPoint u v p y)| ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x₁ x₂ : ℝ × ℝ × ℝ},
        ∀ (hx₁ : x₁.1 ^ 2 + x₁.2.1 ^ 2 + x₁.2.2 ^ 2 = 1),
        ∀ (hx₂ : x₂.1 ^ 2 + x₂.2.1 ^ 2 + x₂.2.2 ^ 2 = 1),
        dist x₁ coordBase < δ →
        dist x₂ coordBase < δ →
        |frame_quadratic (H := H) μ (coordPoint u v p x₁) -
          frame_quadratic (H := H) μ (coordPoint u v p x₂)| ≤
          2 * a := by
  have hε3 : 0 < ε / 3 := by positivity
  refine coordSphereFrameFun_base_oscillation_bound_of_coord_cap
    (μ := μ) hu hv hp huv hup hvp hε3 ?_
  intro x y hx hy hdx hdy
  have hdxH : dist (coordPoint u v p x) p < ε := by
    have hle := dist_coordPoint_le_three_mul_dist_coords hu hv hp x poleCoord
    have hlt : 3 * dist x poleCoord < ε := by nlinarith
    calc
      dist (coordPoint u v p x) p =
          dist (coordPoint u v p x) (coordPoint u v p poleCoord) := by
            rw [coordPoint_poleCoord]
      _ ≤ 3 * dist x poleCoord := hle
      _ < ε := hlt
  have hdyH : dist (coordPoint u v p y) p < ε := by
    have hle := dist_coordPoint_le_three_mul_dist_coords hu hv hp y poleCoord
    have hlt : 3 * dist y poleCoord < ε := by nlinarith
    calc
      dist (coordPoint u v p y) p =
          dist (coordPoint u v p y) (coordPoint u v p poleCoord) := by
            rw [coordPoint_poleCoord]
      _ ≤ 3 * dist y poleCoord := hle
      _ < ε := hlt
  exact hcap hx hy hdxH hdyH

private lemma IsSphereFrameFunction_pair_sum_eq_of_same_pole
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {x y x' y' z : spherePoint3}
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (hxy' : inner (𝕜 := ℝ) x'.1 y'.1 = 0)
    (hxz' : inner (𝕜 := ℝ) x'.1 z.1 = 0)
    (hyz' : inner (𝕜 := ℝ) y'.1 z.1 = 0) :
    f x + f y = f x' + f y' := by
  have h₁ := hf x y z hxy hxz hyz
  have h₂ := hf x' y' z hxy' hxz' hyz'
  linarith

private lemma IsSphereFrameFunction_greatCircle_pair_sum
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {x y z : spherePoint3}
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (θ : ℝ) :
    f (greatCircleParamPoint x y hxy θ) +
        f (greatCircleParamPoint x y hxy (θ + Real.pi / 2)) =
      f x + f y := by
  have hyx : inner (𝕜 := ℝ) y.1 x.1 = 0 := (inner_eq_zero_symm).2 hxy
  have hpair :
      inner (𝕜 := ℝ) (greatCircleParamPoint x y hxy θ).1
        (greatCircleParamPoint x y hxy (θ + Real.pi / 2)).1 = 0 := by
    rw [greatCircleParamPoint_val, greatCircleParamPoint_val]
    have hxnorm : ‖x.1‖ = 1 := x.2
    have hynorm : ‖y.1‖ = 1 := y.2
    simp [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      hxy, hyx, inner_self_eq_norm_sq_to_K, hxnorm, hynorm]
    rw [Real.cos_add, Real.sin_add]
    simp
    ring_nf
  have hxzθ :
      inner (𝕜 := ℝ) (greatCircleParamPoint x y hxy θ).1 z.1 = 0 := by
    rw [greatCircleParamPoint_val]
    simp [inner_add_left, inner_smul_left, hxz, hyz]
  have hyzθ :
      inner (𝕜 := ℝ) (greatCircleParamPoint x y hxy (θ + Real.pi / 2)).1 z.1 = 0 := by
    rw [greatCircleParamPoint_val]
    simp [inner_add_left, inner_smul_left, hxz, hyz]
  exact IsSphereFrameFunction_pair_sum_eq_of_same_pole hf hpair hxzθ hyzθ hxy hxz hyz

private lemma IsSphereFrameFunction_greatCircleRestriction_circleFrameFunction
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {x y : spherePoint3}
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0) :
    circleFrameFunction (fun θ : ℝ => f (greatCircleParamPoint x y hxy θ)) := by
  rcases exists_common_orthogonal_spherePoint x y with ⟨z, hxz, hyz⟩
  refine ⟨f x + f y, ?_⟩
  intro θ
  exact IsSphereFrameFunction_greatCircle_pair_sum hf hxy hxz hyz θ

private lemma s2TargetFrameReparamSwap_pair_sum_eq_base_targetPole
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0) :
    f (spherePointOfCoord (targetFrameReparamSwap x y)
        (targetFrameReparamSwap_sq_sum_coord hx hy hρ)) +
      f (spherePointOfCoord (targetFrameReparamSwap x (polarQuarterTurnCoord y))
        (targetFrameReparamSwap_sq_sum_coord hx (polarQuarterTurnCoord_sq_sum hy) hρ)) =
    f (spherePointOfCoord x hx) +
      f (spherePointOfCoord (targetPoleCoord x) (targetPoleCoord_sq_sum hρ)) := by
  let A : spherePoint3 :=
    spherePointOfCoord (targetFrameReparamSwap x y)
      (targetFrameReparamSwap_sq_sum_coord hx hy hρ)
  let B : spherePoint3 :=
    spherePointOfCoord (targetFrameReparamSwap x (polarQuarterTurnCoord y))
      (targetFrameReparamSwap_sq_sum_coord hx (polarQuarterTurnCoord_sq_sum hy) hρ)
  let C : spherePoint3 :=
    spherePointOfCoord (targetBridgeCoord x) (targetBridgeCoord_sq_sum hx hρ)
  let X : spherePoint3 := spherePointOfCoord x hx
  let P : spherePoint3 :=
    spherePointOfCoord (targetPoleCoord x) (targetPoleCoord_sq_sum hρ)
  have hAB_dot :
      coordDot (targetFrameReparamSwap x y)
          (targetFrameReparamSwap x (polarQuarterTurnCoord y)) = 0 := by
    rw [coordDot_targetFrameReparamSwap (x := x) (y := y)
      (z := polarQuarterTurnCoord y) hx hρ]
    rw [coordDot_self_polarQuarterTurnCoord, hy0]
    ring
  have hAC_dot :
      coordDot (targetFrameReparamSwap x y) (targetBridgeCoord x) = 0 := by
    rw [← targetFrameReparamSwap_poleCoord x]
    rw [coordDot_targetFrameReparamSwap (x := x) (y := y) (z := poleCoord) hx hρ]
    simp [coordDot, poleCoord, hy0]
  have hBC_dot :
      coordDot (targetFrameReparamSwap x (polarQuarterTurnCoord y))
          (targetBridgeCoord x) = 0 := by
    rw [← targetFrameReparamSwap_poleCoord x]
    rw [coordDot_targetFrameReparamSwap (x := x) (y := polarQuarterTurnCoord y)
      (z := poleCoord) hx hρ]
    simp [coordDot, poleCoord, polarQuarterTurnCoord, hy0]
  have hXP_dot : coordDot x (targetPoleCoord x) = 0 :=
    coordDot_target_targetPoleCoord hρ
  have hXC_dot : coordDot x (targetBridgeCoord x) = 0 :=
    coordDot_target_targetBridgeCoord hρ
  have hPC_dot : coordDot (targetPoleCoord x) (targetBridgeCoord x) = 0 :=
    coordDot_targetPole_targetBridgeCoord hρ
  have hAB : inner (𝕜 := ℝ) A.1 B.1 = 0 := by
    change inner (𝕜 := ℝ)
        (spherePointOfCoord (targetFrameReparamSwap x y)
          (targetFrameReparamSwap_sq_sum_coord hx hy hρ)).1
        (spherePointOfCoord (targetFrameReparamSwap x (polarQuarterTurnCoord y))
          (targetFrameReparamSwap_sq_sum_coord hx (polarQuarterTurnCoord_sq_sum hy) hρ)).1 = 0
    rw [inner_spherePointOfCoord_eq_coordDot]
    exact hAB_dot
  have hAC : inner (𝕜 := ℝ) A.1 C.1 = 0 := by
    change inner (𝕜 := ℝ)
        (spherePointOfCoord (targetFrameReparamSwap x y)
          (targetFrameReparamSwap_sq_sum_coord hx hy hρ)).1
        (spherePointOfCoord (targetBridgeCoord x) (targetBridgeCoord_sq_sum hx hρ)).1 = 0
    rw [inner_spherePointOfCoord_eq_coordDot]
    exact hAC_dot
  have hBC : inner (𝕜 := ℝ) B.1 C.1 = 0 := by
    change inner (𝕜 := ℝ)
        (spherePointOfCoord (targetFrameReparamSwap x (polarQuarterTurnCoord y))
          (targetFrameReparamSwap_sq_sum_coord hx (polarQuarterTurnCoord_sq_sum hy) hρ)).1
        (spherePointOfCoord (targetBridgeCoord x) (targetBridgeCoord_sq_sum hx hρ)).1 = 0
    rw [inner_spherePointOfCoord_eq_coordDot]
    exact hBC_dot
  have hXP : inner (𝕜 := ℝ) X.1 P.1 = 0 := by
    change inner (𝕜 := ℝ) (spherePointOfCoord x hx).1
        (spherePointOfCoord (targetPoleCoord x) (targetPoleCoord_sq_sum hρ)).1 = 0
    rw [inner_spherePointOfCoord_eq_coordDot]
    exact hXP_dot
  have hXC : inner (𝕜 := ℝ) X.1 C.1 = 0 := by
    change inner (𝕜 := ℝ) (spherePointOfCoord x hx).1
        (spherePointOfCoord (targetBridgeCoord x) (targetBridgeCoord_sq_sum hx hρ)).1 = 0
    rw [inner_spherePointOfCoord_eq_coordDot]
    exact hXC_dot
  have hPC : inner (𝕜 := ℝ) P.1 C.1 = 0 := by
    change inner (𝕜 := ℝ)
        (spherePointOfCoord (targetPoleCoord x) (targetPoleCoord_sq_sum hρ)).1
        (spherePointOfCoord (targetBridgeCoord x) (targetBridgeCoord_sq_sum hx hρ)).1 = 0
    rw [inner_spherePointOfCoord_eq_coordDot]
    exact hPC_dot
  change f A + f B = f X + f P
  exact IsSphereFrameFunction_pair_sum_eq_of_same_pole hf hAB hAC hBC hXP hXC hPC

private def s2PolarSumValue (f : spherePoint3 → ℝ)
    (x : ℝ × ℝ × ℝ)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) : ℝ :=
  f (spherePointOfCoord x hx) +
    f (spherePointOfCoord (polarQuarterTurnCoord x)
      (polarQuarterTurnCoord_sq_sum hx))

private lemma s2PolarSumValue_spherePointCoord
    (f : spherePoint3 → ℝ) (x : spherePoint3) :
    s2PolarSumValue f (spherePointCoord x) (spherePointCoord_sq_sum x) =
      f x + f (s2QuarterTurn x) := by
  simp [s2PolarSumValue, s2QuarterTurn, spherePointOfCoord_spherePointCoord]

private lemma s2PolarSumValue_comp_northRotation_spherePointCoord
    (f : spherePoint3 → ℝ) (t : ℝ) (x : spherePoint3) :
    s2PolarSumValue (fun y => f (sphereMap (northRotation t) y))
        (spherePointCoord x) (spherePointCoord_sq_sum x) =
      s2PolarSumValue f
        (spherePointCoord (sphereMap (northRotation t) x))
        (spherePointCoord_sq_sum (sphereMap (northRotation t) x)) := by
  rw [s2PolarSumValue_spherePointCoord, s2PolarSumValue_spherePointCoord]
  rw [s2QuarterTurn_sphereMap_northRotation]

private lemma s2PolarSumValue_eq_apply_add_quarterTurn
    (f : spherePoint3 → ℝ) (x : ℝ × ℝ × ℝ)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    s2PolarSumValue f x hx =
      f (spherePointOfCoord x hx) + f (s2QuarterTurn (spherePointOfCoord x hx)) := by
  simp [s2PolarSumValue, s2QuarterTurn, spherePointCoord_spherePointOfCoord]

private lemma s2PolarSumValue_eq_two_quarterTurnAverage
    (f : spherePoint3 → ℝ) (x : ℝ × ℝ × ℝ)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    s2PolarSumValue f x hx =
      2 * s2QuarterTurnAverage f (spherePointOfCoord x hx) := by
  rw [s2PolarSumValue_eq_apply_add_quarterTurn]
  unfold s2QuarterTurnAverage
  ring

private lemma spherePointOfCoord_poleCoord :
    spherePointOfCoord poleCoord (by norm_num [poleCoord]) = sphereE3 := by
  apply Subtype.ext
  simp [spherePointOfCoord, poleCoord, sphereE3]

private lemma spherePointOfCoord_negPoleCoord :
    spherePointOfCoord negPoleCoord (by norm_num [negPoleCoord]) =
      sphereAntipode sphereE3 := by
  apply Subtype.ext
  simp only [spherePointOfCoord, negPoleCoord, sphereAntipode, sphereMap, sphereE3,
    LinearIsometryEquiv.coe_neg]
  change WithLp.toLp 2 (((0 : ℝ) : ℂ) + Complex.I * ((0 : ℝ) : ℂ),
      (-(1 : ℝ))) =
    -WithLp.toLp 2 ((0 : ℂ), (1 : ℝ))
  rw [← WithLp.toLp_neg]
  congr <;> norm_num

private def s2FrameSum (f : spherePoint3 → ℝ) : ℝ :=
  f sphereE1 + f sphereE2 + f sphereE3

private lemma s2PolarSumValue_eq_frameSum_sub_north_on_equator
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hx3 : x.2.2 = 0) :
    s2PolarSumValue f x hx = s2FrameSum f - f sphereE3 := by
  let A : spherePoint3 := spherePointOfCoord x hx
  let B : spherePoint3 :=
    spherePointOfCoord (polarQuarterTurnCoord x) (polarQuarterTurnCoord_sq_sum hx)
  have hAB_dot : coordDot x (polarQuarterTurnCoord x) = 0 := by
    rw [coordDot_self_polarQuarterTurnCoord, hx3]
    ring
  have hA3_dot : coordDot x poleCoord = 0 := by
    simp [coordDot, poleCoord, hx3]
  have hB3_dot : coordDot (polarQuarterTurnCoord x) poleCoord = 0 := by
    simp [coordDot, poleCoord, polarQuarterTurnCoord, hx3]
  have hAB : inner (𝕜 := ℝ) A.1 B.1 = 0 := by
    change inner (𝕜 := ℝ) (spherePointOfCoord x hx).1
        (spherePointOfCoord (polarQuarterTurnCoord x) (polarQuarterTurnCoord_sq_sum hx)).1 = 0
    rw [inner_spherePointOfCoord_eq_coordDot]
    exact hAB_dot
  have hA3 : inner (𝕜 := ℝ) A.1 sphereE3.1 = 0 := by
    rw [← spherePointOfCoord_poleCoord]
    change inner (𝕜 := ℝ) (spherePointOfCoord x hx).1
        (spherePointOfCoord poleCoord (by norm_num [poleCoord])).1 = 0
    rw [inner_spherePointOfCoord_eq_coordDot]
    exact hA3_dot
  have hB3 : inner (𝕜 := ℝ) B.1 sphereE3.1 = 0 := by
    rw [← spherePointOfCoord_poleCoord]
    change inner (𝕜 := ℝ)
        (spherePointOfCoord (polarQuarterTurnCoord x) (polarQuarterTurnCoord_sq_sum hx)).1
        (spherePointOfCoord poleCoord (by norm_num [poleCoord])).1 = 0
    rw [inner_spherePointOfCoord_eq_coordDot]
    exact hB3_dot
  have hsum := hf A B sphereE3 hAB hA3 hB3
  dsimp [A, B, s2PolarSumValue, s2FrameSum] at hsum ⊢
  linarith

private lemma s2PolarSumValue_pair_sum_eq_base_targetPole
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0) :
    s2PolarSumValue f (targetFrameReparamSwap x y)
        (targetFrameReparamSwap_sq_sum_coord hx hy hρ) +
      s2PolarSumValue f (targetFrameReparamSwap x (polarQuarterTurnCoord y))
        (targetFrameReparamSwap_sq_sum_coord hx (polarQuarterTurnCoord_sq_sum hy) hρ) =
    s2PolarSumValue f x hx +
      s2PolarSumValue f (targetPoleCoord x) (targetPoleCoord_sq_sum hρ) := by
  have hfirst :=
    s2TargetFrameReparamSwap_pair_sum_eq_base_targetPole
      (f := f) hf hx hρ hy hy0
  have hxq : (polarQuarterTurnCoord x).1 ^ 2 +
      (polarQuarterTurnCoord x).2.1 ^ 2 +
      (polarQuarterTurnCoord x).2.2 ^ 2 = 1 :=
    polarQuarterTurnCoord_sq_sum hx
  have hρq : horizontalRadius (polarQuarterTurnCoord x) ≠ 0 := by
    simpa [horizontalRadius_polarQuarterTurnCoord x] using hρ
  have hsecond₀ :=
    s2TargetFrameReparamSwap_pair_sum_eq_base_targetPole
      (f := f) hf hxq hρq hy hy0
      (x := polarQuarterTurnCoord x) (y := y)
  have hcomm₁ :
      polarQuarterTurnCoord (targetFrameReparamSwap x y) =
        targetFrameReparamSwap (polarQuarterTurnCoord x) y :=
    targetFrameReparamSwap_polarQuarterTurn (x := x) (y := y) hρ
  have hcomm₂ :
      polarQuarterTurnCoord (targetFrameReparamSwap x (polarQuarterTurnCoord y)) =
        targetFrameReparamSwap (polarQuarterTurnCoord x) (polarQuarterTurnCoord y) :=
    targetFrameReparamSwap_polarQuarterTurn
      (x := x) (y := polarQuarterTurnCoord y) hρ
  have hpole_comm :
      targetPoleCoord (polarQuarterTurnCoord x) =
        polarQuarterTurnCoord (targetPoleCoord x) :=
    targetPoleCoord_polarQuarterTurnCoord (x := x) hρ
  unfold s2PolarSumValue
  simpa [hcomm₁, hcomm₂, hpole_comm, add_assoc, add_left_comm, add_comm] using
    congrArg₂ (fun a b : ℝ => a + b) hfirst hsecond₀

private lemma s2PolarSumValue_nonneg
    {f : spherePoint3 → ℝ} (hnonneg : ∀ x : spherePoint3, 0 ≤ f x)
    (x : ℝ × ℝ × ℝ)
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    0 ≤ s2PolarSumValue f x hx := by
  unfold s2PolarSumValue
  linarith [hnonneg (spherePointOfCoord x hx),
    hnonneg (spherePointOfCoord (polarQuarterTurnCoord x)
      (polarQuarterTurnCoord_sq_sum hx))]

private lemma s2PolarSumValue_le_frameSum_add_north
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x)
    {x : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1) :
    s2PolarSumValue f x hx ≤ s2FrameSum f + f sphereE3 := by
  have hnorth_le_frame : f sphereE3 ≤ s2FrameSum f := by
    unfold s2FrameSum
    linarith [hnonneg sphereE1, hnonneg sphereE2]
  by_cases hρ : horizontalRadius x = 0
  · rcases eq_pole_or_negPole_of_horizontalRadius_eq_zero hx hρ with rfl | rfl
    · have hpole :
          s2PolarSumValue f poleCoord (by norm_num [poleCoord]) =
            2 * f sphereE3 := by
        unfold s2PolarSumValue
        have hq : polarQuarterTurnCoord poleCoord = poleCoord := by
          ext <;> simp [polarQuarterTurnCoord, poleCoord]
        have hturn :
            spherePointOfCoord (polarQuarterTurnCoord poleCoord)
              (polarQuarterTurnCoord_sq_sum (by norm_num [poleCoord])) =
              sphereE3 := by
          exact (spherePointOfCoord_congr hq).trans spherePointOfCoord_poleCoord
        rw [spherePointOfCoord_poleCoord, hturn]
        ring
      rw [hpole]
      linarith
    · have hneg :
          s2PolarSumValue f negPoleCoord (by norm_num [negPoleCoord]) =
            2 * f sphereE3 := by
        unfold s2PolarSumValue
        have hq : polarQuarterTurnCoord negPoleCoord = negPoleCoord := by
          ext <;> simp [polarQuarterTurnCoord, negPoleCoord]
        have hturn :
            spherePointOfCoord (polarQuarterTurnCoord negPoleCoord)
              (polarQuarterTurnCoord_sq_sum (by norm_num [negPoleCoord])) =
              sphereAntipode sphereE3 := by
          exact (spherePointOfCoord_congr hq).trans spherePointOfCoord_negPoleCoord
        rw [spherePointOfCoord_negPoleCoord, hturn, IsSphereFrameFunction_even hf sphereE3]
        ring
      rw [hneg]
      linarith
  · let A : spherePoint3 := spherePointOfCoord x hx
    let P : spherePoint3 :=
      spherePointOfCoord (targetPoleCoord x) (targetPoleCoord_sq_sum hρ)
    let B : spherePoint3 :=
      spherePointOfCoord (targetBridgeCoord x) (targetBridgeCoord_sq_sum hx hρ)
    have hAP_dot : coordDot x (targetPoleCoord x) = 0 :=
      coordDot_target_targetPoleCoord hρ
    have hAB_dot : coordDot x (targetBridgeCoord x) = 0 :=
      coordDot_target_targetBridgeCoord hρ
    have hPB_dot : coordDot (targetPoleCoord x) (targetBridgeCoord x) = 0 :=
      coordDot_targetPole_targetBridgeCoord hρ
    have hAP : inner (𝕜 := ℝ) A.1 P.1 = 0 := by
      change inner (𝕜 := ℝ) (spherePointOfCoord x hx).1
          (spherePointOfCoord (targetPoleCoord x) (targetPoleCoord_sq_sum hρ)).1 = 0
      rw [inner_spherePointOfCoord_eq_coordDot]
      exact hAP_dot
    have hAB : inner (𝕜 := ℝ) A.1 B.1 = 0 := by
      change inner (𝕜 := ℝ) (spherePointOfCoord x hx).1
          (spherePointOfCoord (targetBridgeCoord x) (targetBridgeCoord_sq_sum hx hρ)).1 = 0
      rw [inner_spherePointOfCoord_eq_coordDot]
      exact hAB_dot
    have hPB : inner (𝕜 := ℝ) P.1 B.1 = 0 := by
      change inner (𝕜 := ℝ)
          (spherePointOfCoord (targetPoleCoord x) (targetPoleCoord_sq_sum hρ)).1
          (spherePointOfCoord (targetBridgeCoord x) (targetBridgeCoord_sq_sum hx hρ)).1 = 0
      rw [inner_spherePointOfCoord_eq_coordDot]
      exact hPB_dot
    have hsum₁ : f A + f P + f B = s2FrameSum f := by
      simpa [s2FrameSum] using hf A P B hAP hAB hPB
    have hsum₂ :
        f (s2QuarterTurn A) + f (s2QuarterTurn P) + f (s2QuarterTurn B) =
          s2FrameSum f := by
      have hAPq :
          inner (𝕜 := ℝ) (s2QuarterTurn A).1 (s2QuarterTurn P).1 = 0 := by
        rw [inner_s2QuarterTurn, hAP]
      have hABq :
          inner (𝕜 := ℝ) (s2QuarterTurn A).1 (s2QuarterTurn B).1 = 0 := by
        rw [inner_s2QuarterTurn, hAB]
      have hPBq :
          inner (𝕜 := ℝ) (s2QuarterTurn P).1 (s2QuarterTurn B).1 = 0 := by
        rw [inner_s2QuarterTurn, hPB]
      simpa [s2FrameSum] using
        hf (s2QuarterTurn A) (s2QuarterTurn P) (s2QuarterTurn B) hAPq hABq hPBq
    have hxPS :
        s2PolarSumValue f x hx = f A + f (s2QuarterTurn A) := by
      simpa [A] using s2PolarSumValue_eq_apply_add_quarterTurn f x hx
    have hpPS :
        s2PolarSumValue f (targetPoleCoord x) (targetPoleCoord_sq_sum hρ) =
          f P + f (s2QuarterTurn P) := by
      simpa [P] using
        s2PolarSumValue_eq_apply_add_quarterTurn f (targetPoleCoord x)
          (targetPoleCoord_sq_sum hρ)
    have hpair_total :
        s2PolarSumValue f x hx +
            s2PolarSumValue f (targetPoleCoord x) (targetPoleCoord_sq_sum hρ) +
            f B + f (s2QuarterTurn B) =
          2 * s2FrameSum f := by
      rw [hxPS, hpPS]
      linarith
    have hpair_le :
        s2PolarSumValue f x hx +
            s2PolarSumValue f (targetPoleCoord x) (targetPoleCoord_sq_sum hρ) ≤
          2 * s2FrameSum f := by
      linarith [hpair_total, hnonneg B, hnonneg (s2QuarterTurn B)]
    have hpole_eq :
        s2PolarSumValue f (targetPoleCoord x) (targetPoleCoord_sq_sum hρ) =
          s2FrameSum f - f sphereE3 := by
      exact s2PolarSumValue_eq_frameSum_sub_north_on_equator
        (f := f) hf (targetPoleCoord_sq_sum hρ) (by simp [targetPoleCoord])
    linarith

private lemma s2PolarSumValue_le_targetFrameReparamSwap_add_two_north
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x)
    {η : ℝ} (hnorth : f sphereE3 ≤ η)
    {x y : ℝ × ℝ × ℝ}
    (hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1)
    (hρ : horizontalRadius x ≠ 0)
    (hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1)
    (hy0 : y.2.2 = 0) :
    s2PolarSumValue f x hx ≤
      s2PolarSumValue f (targetFrameReparamSwap x y)
        (targetFrameReparamSwap_sq_sum_coord hx hy hρ) + 2 * η := by
  let t : ℝ × ℝ × ℝ := targetFrameReparamSwap x (polarQuarterTurnCoord y)
  have hconst :=
    s2PolarSumValue_pair_sum_eq_base_targetPole
      (f := f) hf hx hρ hy hy0
  have ht :
      t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 1 := by
    simpa [t] using
      targetFrameReparamSwap_sq_sum_coord hx (polarQuarterTurnCoord_sq_sum hy) hρ
  have ht_bound :
      s2PolarSumValue f t ht ≤ s2FrameSum f + f sphereE3 := by
    exact s2PolarSumValue_le_frameSum_add_north (f := f) hf hnonneg ht
  have hpole_eq :
      s2PolarSumValue f (targetPoleCoord x) (targetPoleCoord_sq_sum hρ) =
        s2FrameSum f - f sphereE3 := by
    exact s2PolarSumValue_eq_frameSum_sub_north_on_equator
      (f := f) hf (targetPoleCoord_sq_sum hρ) (by simp [targetPoleCoord])
  simpa [t] using (by linarith [hconst, ht_bound, hpole_eq, hnorth] :
    s2PolarSumValue f x hx ≤
      s2PolarSumValue f (targetFrameReparamSwap x y)
        (targetFrameReparamSwap_sq_sum_coord hx hy hρ) + 2 * η)

private lemma s2PolarSumValue_le_two_step_targetFrame_add_four_north
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x)
    {η : ℝ} (hnorth : f sphereE3 ≤ η)
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
    s2PolarSumValue f x hx ≤ s2PolarSumValue f z
      (by
        rw [hz_def]
        exact targetFrameReparamSwap_sq_sum_coord
          (by
            rw [hy_def]
            exact targetFrameReparamSwap_sq_sum_coord hx hs hρx)
          ht hρy) + 4 * η := by
  have hy :
      y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1 := by
    rw [hy_def]
    exact targetFrameReparamSwap_sq_sum_coord hx hs hρx
  have hz :
      z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1 := by
    rw [hz_def]
    exact targetFrameReparamSwap_sq_sum_coord hy ht hρy
  have hxy :
      s2PolarSumValue f x hx ≤ s2PolarSumValue f y hy + 2 * η := by
    simpa [hy_def] using
      s2PolarSumValue_le_targetFrameReparamSwap_add_two_north
        (f := f) hf hnonneg hnorth hx hρx hs hs0
  have hyz :
      s2PolarSumValue f y hy ≤ s2PolarSumValue f z hz + 2 * η := by
    simpa [hz_def] using
      s2PolarSumValue_le_targetFrameReparamSwap_add_two_north
        (f := f) hf hnonneg hnorth hy hρy ht ht0
  convert (by linarith : s2PolarSumValue f x hx ≤ s2PolarSumValue f z hz + 4 * η) using 1

private lemma s2PolarSumValue_band_of_two_step_near_infimum
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x)
    {β η : ℝ}
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        ∀ hw : w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1,
        β ≤ s2PolarSumValue f w hw)
    (hnorth : f sphereE3 ≤ η)
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
    (hzβ : s2PolarSumValue f z
        (by
          rw [hz_def]
          exact targetFrameReparamSwap_sq_sum_coord
            (by
              rw [hy_def]
              exact targetFrameReparamSwap_sq_sum_coord hx hs hρx)
            ht hρy) ≤ β + η) :
    β ≤ s2PolarSumValue f x hx ∧
      s2PolarSumValue f x hx ≤ β + 5 * η := by
  have hlow : β ≤ s2PolarSumValue f x hx := hβ hx
  have hstep :
      s2PolarSumValue f x hx ≤ s2PolarSumValue f z
        (by
          rw [hz_def]
          exact targetFrameReparamSwap_sq_sum_coord
            (by
              rw [hy_def]
              exact targetFrameReparamSwap_sq_sum_coord hx hs hρx)
            ht hρy) + 4 * η := by
    exact s2PolarSumValue_le_two_step_targetFrame_add_four_north
      (f := f) hf hnonneg hnorth hx hρx hs hs0 hy_def hρy ht ht0 hz_def
  constructor
  · exact hlow
  · linarith

private def s2NorthOpenNonpolePolarSumSet
    (f : spherePoint3 → ℝ) : Set ℝ :=
  {r : ℝ | ∃ x : ℝ × ℝ × ℝ,
      ∃ hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1,
      0 < x.2.2 ∧ horizontalRadius x ≠ 0 ∧ s2PolarSumValue f x hx = r}

private lemma s2NorthOpenNonpolePolarSumSet_nonempty
    (f : spherePoint3 → ℝ) :
    (s2NorthOpenNonpolePolarSumSet f).Nonempty := by
  let x : ℝ × ℝ × ℝ := northMeridianCoord (Real.pi / 4)
  have hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1 := by
    exact northMeridianCoord_sq_sum (Real.pi / 4)
  refine ⟨s2PolarSumValue f x hx, ?_⟩
  refine ⟨x, hx, ?_, ?_, rfl⟩
  · have hquarter : 0 < Real.pi / 4 := by
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith
    have hquarter_lt_pi : Real.pi / 4 < Real.pi := by
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith
    simpa [x, northMeridianCoord] using
      Real.sin_pos_of_pos_of_lt_pi hquarter hquarter_lt_pi
  · have hquarter : 0 < Real.pi / 4 := by
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith
    have hquarter_lt : Real.pi / 4 < Real.pi / 2 := by
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith
    simpa [x] using
      northMeridianCoord_horizontalRadius_ne_zero hquarter hquarter_lt

private lemma s2NorthOpenNonpolePolarSumSet_bddBelow
    {f : spherePoint3 → ℝ} (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) :
    BddBelow (s2NorthOpenNonpolePolarSumSet f) := by
  refine ⟨0, ?_⟩
  intro r hr
  rcases hr with ⟨x, hx, _, _, rfl⟩
  exact s2PolarSumValue_nonneg hnonneg x hx

private lemma exists_s2NorthOpenNonpolePolarSum_near_infimum
    {f : spherePoint3 → ℝ}
    {η : ℝ} (hη : 0 < η) :
    ∃ z : ℝ × ℝ × ℝ,
      ∃ hz : z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2 = 1,
      0 < z.2.2 ∧ horizontalRadius z ≠ 0 ∧
      s2PolarSumValue f z hz <
        sInf (s2NorthOpenNonpolePolarSumSet f) + η := by
  have hne := s2NorthOpenNonpolePolarSumSet_nonempty f
  obtain ⟨r, hr_mem, hr_lt⟩ := exists_lt_of_csInf_lt hne
    (by linarith :
      sInf (s2NorthOpenNonpolePolarSumSet f) <
        sInf (s2NorthOpenNonpolePolarSumSet f) + η)
  rcases hr_mem with ⟨z, hz, hzpos, hρz, rfl⟩
  exact ⟨z, hz, hzpos, hρz, hr_lt⟩

private lemma exists_s2_local_band_neighborhood_of_meridian_near_infimum
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        ∀ hw : w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1,
        β ≤ s2PolarSumValue f w hw)
    (hnorth : f sphereE3 ≤ η)
    (hzβ :
      s2PolarSumValue f (northMeridianCoord θ) (northMeridianCoord_sq_sum θ) ≤
        β + η) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      ∀ {x : ℝ × ℝ × ℝ},
        ∀ hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1,
        dist x x0 < δ →
        β ≤ s2PolarSumValue f x hx ∧
          s2PolarSumValue f x hx ≤ β + 5 * η := by
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
  have hρx : horizontalRadius x ≠ 0 :=
    horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hneg
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hx hneg with
    ⟨y, s, t, hy, hρy, hs, hs0, ht, ht0, hy_def, hz_def⟩
  have hzβ' :
      s2PolarSumValue f (northMeridianCoord θ) (by
        rw [hz_def]
        exact targetFrameReparamSwap_sq_sum_coord hy ht hρy) ≤ β + η := by
    convert hzβ
  exact s2PolarSumValue_band_of_two_step_near_infimum
    (f := f) hf hnonneg hβ hnorth hx hρx hs hs0 hy_def hρy ht ht0 hz_def hzβ'

private lemma exists_s2_local_band_neighborhood_of_meridian_near_infimum_on_north
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        ∀ hw : w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1,
        0 < w.2.2 → horizontalRadius w ≠ 0 →
        β ≤ s2PolarSumValue f w hw)
    (hnorth : f sphereE3 ≤ η)
    (hzβ :
      s2PolarSumValue f (northMeridianCoord θ) (northMeridianCoord_sq_sum θ) ≤
        β + η) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      0 < x0.2.2 ∧
      ∀ {x : ℝ × ℝ × ℝ},
        ∀ hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1,
        dist x x0 < δ →
        0 < x.2.2 ∧
        β ≤ s2PolarSumValue f x hx ∧
          s2PolarSumValue f x hx ≤ β + 5 * η := by
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
  have hnhds : {x : ℝ × ℝ × ℝ | ψ x < 0 ∧ 0 < x.2.2} ∈ nhds x0 :=
    Filter.inter_mem (hopenψ.mem_nhds hx0memψ) (hopenr.mem_nhds hx0memr)
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨δ, hδ, hball⟩
  refine ⟨x0, δ, hδ, by simpa [x0] using hx0, by simpa [x0] using hx0pos, ?_⟩
  intro x hx hdist
  have hxball : x ∈ {x : ℝ × ℝ × ℝ | ψ x < 0 ∧ 0 < x.2.2} := hball hdist
  have hneg : Thm25.gleasonPsiSwap θ x.1 x.2.1 x.2.2 < 0 := hxball.1
  have hxpos : 0 < x.2.2 := hxball.2
  have hρx : horizontalRadius x ≠ 0 :=
    horizontalRadius_ne_zero_of_gleasonPsiSwap_neg hneg
  rcases exists_two_step_targetFrameSwap_of_gleasonPsiSwap_neg
      hu hv hp huv hup hvp hθ0 hθpi hx hneg with
    ⟨y, s, t, hy, hρy, hs, hs0, ht, ht0, hy_def, hz_def⟩
  have hstep :
      s2PolarSumValue f x hx ≤
        s2PolarSumValue f (northMeridianCoord θ) (northMeridianCoord_sq_sum θ) +
          4 * η := by
    exact s2PolarSumValue_le_two_step_targetFrame_add_four_north
      (f := f) hf hnonneg hnorth hx hρx hs hs0 hy_def hρy ht ht0 hz_def
  have hlow : β ≤ s2PolarSumValue f x hx := hβ hx hxpos hρx
  have hhigh : s2PolarSumValue f x hx ≤ β + 5 * η := by
    linarith
  exact ⟨hxpos, hlow, hhigh⟩

private lemma exists_s2_local_polar_sum_oscillation_of_meridian_near_infimum
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    {β η θ : ℝ}
    (hθ0 : 0 < θ) (hθpi : θ < Real.pi / 2)
    (hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        ∀ hw : w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1,
        0 < w.2.2 → horizontalRadius w ≠ 0 →
        β ≤ s2PolarSumValue f w hw)
    (hnorth : f sphereE3 ≤ η)
    (hzβ :
      s2PolarSumValue f (northMeridianCoord θ) (northMeridianCoord_sq_sum θ) ≤
        β + η) :
    ∃ x0 : ℝ × ℝ × ℝ, ∃ δ : ℝ, 0 < δ ∧
      x0.1 ^ 2 + x0.2.1 ^ 2 + x0.2.2 ^ 2 = 1 ∧
      ∀ {x y : ℝ × ℝ × ℝ},
        ∀ hx : x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 = 1,
        ∀ hy : y.1 ^ 2 + y.2.1 ^ 2 + y.2.2 ^ 2 = 1,
        dist x x0 < δ → dist y x0 < δ →
        |s2PolarSumValue f x hx - s2PolarSumValue f y hy| ≤ 5 * η := by
  rcases exists_s2_local_band_neighborhood_of_meridian_near_infimum_on_north
      (f := f) hf hnonneg hu hv hp huv hup hvp hθ0 hθpi hβ hnorth hzβ with
    ⟨x0, δ, hδ, hx0, _hx0pos, hlocal⟩
  refine ⟨x0, δ, hδ, hx0, ?_⟩
  intro x y hx hy hdx hdy
  rcases hlocal hx hdx with ⟨_hxpos, hxlo, hxhi⟩
  rcases hlocal hy hdy with ⟨_hypos, hylo, hyhi⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma exists_s2_local_oscillation_of_small_north
    (hdim : 3 ≤ Module.finrank ℂ H)
    {f : spherePoint3 → ℝ} (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x)
    {η : ℝ} (hηpos : 0 < η) (hnorth : f sphereE3 ≤ η)
    (target : spherePoint3) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {x y : spherePoint3},
        dist x target < δ → dist y target < δ →
        |f x - f y| ≤ 88 * η := by
  let β : ℝ := sInf (s2NorthOpenNonpolePolarSumSet f)
  rcases exists_s2NorthOpenNonpolePolarSum_near_infimum (f := f) hηpos with
    ⟨z, hz, hzpos, hρz, hzβ⟩
  rcases exists_northRotation_northMeridianCoord hz hzpos hρz with
    ⟨θ, t, hθ0, hθpi, hmeridian⟩
  let frot : spherePoint3 → ℝ := fun x => f (sphereMap (northRotation t) x)
  have hfrot : IsSphereFrameFunction frot :=
    isSphereFrameFunction_comp_sphereMap (northRotation t) hf
  have hfrotNonneg : ∀ x : spherePoint3, 0 ≤ frot x := by
    intro x
    exact hnonneg (sphereMap (northRotation t) x)
  have hfrotNorth : frot sphereE3 ≤ η := by
    simpa [frot] using hnorth
  have hβ :
      ∀ {w : ℝ × ℝ × ℝ},
        ∀ hw : w.1 ^ 2 + w.2.1 ^ 2 + w.2.2 ^ 2 = 1,
        0 < w.2.2 → horizontalRadius w ≠ 0 →
        β ≤ s2PolarSumValue frot w hw := by
    intro w hw hwpos hρw
    let ws : spherePoint3 := spherePointOfCoord w hw
    let rwcoord : ℝ × ℝ × ℝ :=
      spherePointCoord (sphereMap (northRotation t) ws)
    have hrw :
        rwcoord.1 ^ 2 + rwcoord.2.1 ^ 2 + rwcoord.2.2 ^ 2 = 1 := by
      exact spherePointCoord_sq_sum (sphereMap (northRotation t) ws)
    have hthird : rwcoord.2.2 = w.2.2 := by
      simp [rwcoord, ws, spherePointCoord, sphereMap, northRotation_apply,
        spherePointOfCoord]
    have hrwpos : 0 < rwcoord.2.2 := by
      rw [hthird]
      exact hwpos
    have hρsq : horizontalRadius rwcoord ^ 2 = horizontalRadius w ^ 2 := by
      rw [horizontalRadius_sq, horizontalRadius_sq]
      nlinarith [hrw, hw, hthird]
    have hρrw : horizontalRadius rwcoord ≠ 0 := by
      intro hzero
      apply hρw
      have : horizontalRadius w ^ 2 = 0 := by
        rw [← hρsq, hzero]
        ring
      exact sq_eq_zero_iff.mp this
    have hlow : β ≤ s2PolarSumValue f rwcoord hrw := by
      exact csInf_le (s2NorthOpenNonpolePolarSumSet_bddBelow hnonneg)
        ⟨rwcoord, hrw, hrwpos, hρrw, rfl⟩
    have hrotate :=
      s2PolarSumValue_comp_northRotation_spherePointCoord f t ws
    have heq : s2PolarSumValue frot w hw = s2PolarSumValue f rwcoord hrw := by
      simpa [frot, ws, rwcoord, spherePointCoord_spherePointOfCoord] using hrotate
    rw [heq]
    exact hlow
  have hzβrot :
      s2PolarSumValue frot (northMeridianCoord θ) (northMeridianCoord_sq_sum θ) ≤
        β + η := by
    let m : spherePoint3 :=
      spherePointOfCoord (northMeridianCoord θ) (northMeridianCoord_sq_sum θ)
    have hrotate := s2PolarSumValue_comp_northRotation_spherePointCoord f t m
    have hcoords : spherePointCoord (sphereMap (northRotation t) m) = z := by
      rw [hmeridian]
      exact spherePointCoord_spherePointOfCoord z hz
    have heq :
        s2PolarSumValue frot (northMeridianCoord θ) (northMeridianCoord_sq_sum θ) =
          s2PolarSumValue f z hz := by
      simpa [frot, m, hcoords, spherePointCoord_spherePointOfCoord] using hrotate
    rw [heq]
    exact le_of_lt hzβ
  rcases exists_unit_orthogonal_to_pair (H := H) hdim (0 : H) (0 : H) with
    ⟨p, hp, _h0p, _h0p'⟩
  rcases exists_unit_orthogonal_to_pair (H := H) hdim p p with
    ⟨u, hu, hpu, _hpu'⟩
  rcases exists_unit_orthogonal_to_pair (H := H) hdim u p with
    ⟨v, hv, huv, hpv⟩
  have hup : inner (𝕜 := ℂ) u p = 0 := (inner_eq_zero_symm).2 hpu
  have hvp : inner (𝕜 := ℂ) v p = 0 := (inner_eq_zero_symm).2 hpv
  rcases exists_s2_local_polar_sum_oscillation_of_meridian_near_infimum
      (f := frot) hfrot hfrotNonneg hu hv hp huv hup hvp
      hθ0 hθpi hβ hfrotNorth hzβrot with
    ⟨x0, δc, hδc, hx0, hlocalPolar⟩
  let x0s : spherePoint3 := spherePointOfCoord x0 hx0
  have hcoordCont : ContinuousAt sphereToCoordSphere x0s :=
    continuous_sphereToCoordSphere.continuousAt
  rcases (Metric.continuousAt_iff.mp hcoordCont)
      δc hδc with ⟨δs, hδs, htoCoords⟩
  have hx0coords : sphereToCoordSphere x0s = (⟨x0, hx0⟩ : coordSpherePoint3) := by
    apply Subtype.ext
    exact spherePointCoord_spherePointOfCoord x0 hx0
  have hx0coordval : spherePointCoord x0s = x0 := by
    exact spherePointCoord_spherePointOfCoord x0 hx0
  have hlocalAverage :
      ∀ {x y : spherePoint3},
        dist x x0s < δs → dist y x0s < δs →
        |s2QuarterTurnAverage frot x - s2QuarterTurnAverage frot y| ≤ 5 * η / 2 := by
    intro x y hdx hdy
    have hdxCoord : dist (spherePointCoord x) x0 < δc := by
      have hmain := htoCoords hdx
      simpa [Subtype.dist_eq, sphereToCoordSphere, hx0coordval] using hmain
    have hdyCoord : dist (spherePointCoord y) x0 < δc := by
      have hmain := htoCoords hdy
      simpa [Subtype.dist_eq, sphereToCoordSphere, hx0coordval] using hmain
    have hpolar := hlocalPolar (spherePointCoord_sq_sum x) (spherePointCoord_sq_sum y)
      hdxCoord hdyCoord
    rw [s2PolarSumValue_eq_two_quarterTurnAverage,
      s2PolarSumValue_eq_two_quarterTurnAverage] at hpolar
    have hpolar' :
        |2 * s2QuarterTurnAverage frot x - 2 * s2QuarterTurnAverage frot y| ≤
          5 * η := by
      simpa [spherePointOfCoord_spherePointCoord] using hpolar
    have hfactor :
        |2 * s2QuarterTurnAverage frot x - 2 * s2QuarterTurnAverage frot y| =
          2 * |s2QuarterTurnAverage frot x - s2QuarterTurnAverage frot y| := by
      rw [show 2 * s2QuarterTurnAverage frot x - 2 * s2QuarterTurnAverage frot y =
        2 * (s2QuarterTurnAverage frot x - s2QuarterTurnAverage frot y) by ring]
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hfactor] at hpolar'
    nlinarith [abs_nonneg (s2QuarterTurnAverage frot x - s2QuarterTurnAverage frot y)]
  have hfrotAverage : IsSphereFrameFunction (s2QuarterTurnAverage frot) :=
    IsSphereFrameFunction_s2QuarterTurnAverage hfrot
  rcases s2_global_oscillation_bound_of_cap
      (f := s2QuarterTurnAverage frot) hfrotAverage hδs hlocalAverage sphereE3 with
    ⟨δn, hδn, hnorthAverage⟩
  have hturnNorth : s2QuarterTurn sphereE3 = sphereE3 := by
    apply Subtype.ext
    rw [s2QuarterTurn_apply_val]
    simp [sphereE3]
  have haverageNorth : s2QuarterTurnAverage frot sphereE3 = frot sphereE3 := by
    simp [s2QuarterTurnAverage, hturnNorth]
  have hfrotNorthCap :
      ∀ {x y : spherePoint3},
        dist x sphereE3 < δn → dist y sphereE3 < δn →
        |frot x - frot y| ≤ 22 * η := by
    intro x y hdx hdy
    have hd0 : dist sphereE3 sphereE3 < δn := by simpa using hδn
    have hxavg := hnorthAverage hdx hd0
    have hyavg := hnorthAverage hdy hd0
    have hxavgBound :
        |s2QuarterTurnAverage frot x - s2QuarterTurnAverage frot sphereE3| ≤
          10 * η := by
      have h := hxavg
      nlinarith
    have hyavgBound :
        |s2QuarterTurnAverage frot y - s2QuarterTurnAverage frot sphereE3| ≤
          10 * η := by
      have h := hyavg
      nlinarith
    have hxavgLe : s2QuarterTurnAverage frot x ≤ 11 * η := by
      have hu := (abs_le.mp hxavgBound).2
      rw [haverageNorth] at hu
      linarith
    have hyavgLe : s2QuarterTurnAverage frot y ≤ 11 * η := by
      have hu := (abs_le.mp hyavgBound).2
      rw [haverageNorth] at hu
      linarith
    have hxLe : frot x ≤ 22 * η := by
      have hq := hfrotNonneg (s2QuarterTurn x)
      unfold s2QuarterTurnAverage at hxavgLe
      linarith
    have hyLe : frot y ≤ 22 * η := by
      have hq := hfrotNonneg (s2QuarterTurn y)
      unfold s2QuarterTurnAverage at hyavgLe
      linarith
    exact abs_le.mpr ⟨by linarith [hfrotNonneg x], by linarith [hfrotNonneg y]⟩
  let target' := sphereMap (northRotation t).symm target
  rcases s2_global_oscillation_bound_of_cap
      (f := frot) hfrot hδn hfrotNorthCap target' with
    ⟨δ, hδ, htarget⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hdx hdy
  let x' := sphereMap (northRotation t).symm x
  let y' := sphereMap (northRotation t).symm y
  have hdx' : dist x' target' < δ := by
    simpa [x', target', sphereMap_dist] using hdx
  have hdy' : dist y' target' < δ := by
    simpa [y', target', sphereMap_dist] using hdy
  have hbound := htarget hdx' hdy'
  have hfx : frot x' = f x := by
    simp [frot, x']
  have hfy : frot y' = f y := by
    simp [frot, y']
  rw [hfx, hfy] at hbound
  calc
    |f x - f y| ≤ 4 * (22 * η) := hbound
    _ = 88 * η := by ring

private theorem s2_nonnegative_frame_continuous_osc
    (hdim : 3 ≤ Module.finrank ℂ H) :
    ∀ f : spherePoint3 → ℝ,
      IsSphereFrameFunction f →
      (∀ x : spherePoint3, 0 ≤ f x) →
      Continuous f := by
  intro f hf hnonneg
  apply continuous_s2_of_pointwise_abs_oscillation
  intro target ε hε
  let η : ℝ := ε / 176
  have hηpos : 0 < η := by positivity
  let m : ℝ := sInf (Set.range f)
  let g : spherePoint3 → ℝ := fun x => f x - m
  have hg : IsSphereFrameFunction g := IsSphereFrameFunction_sub_const hf m
  have hgNonneg : ∀ x : spherePoint3, 0 ≤ g x := by
    intro x
    exact IsSphereFrameFunction_sub_sInf_nonneg hnonneg x
  rcases exists_s2Frame_near_sInf (f := f) hηpos with ⟨p, hp⟩
  have hgp : g p ≤ η := by
    dsimp [g, m]
    linarith
  rcases exists_common_orthogonal_spherePoint p p with ⟨q, hpq, _hpq'⟩
  have hqp : inner (𝕜 := ℝ) q.1 p.1 = 0 := (inner_eq_zero_symm).2 hpq
  rcases exists_sphere_isometry_map_standard_pair hqp with ⟨e, _he1, he3⟩
  let h : spherePoint3 → ℝ := fun x => g (sphereMap e x)
  have hh : IsSphereFrameFunction h := isSphereFrameFunction_comp_sphereMap e hg
  have hhNonneg : ∀ x : spherePoint3, 0 ≤ h x := by
    intro x
    exact hgNonneg (sphereMap e x)
  have hhNorth : h sphereE3 ≤ η := by
    simpa [h, he3] using hgp
  let target' := sphereMap e.symm target
  rcases exists_s2_local_oscillation_of_small_north
      (H := H) hdim hh hhNonneg hηpos hhNorth target' with
    ⟨δ, hδ, hlocal⟩
  refine ⟨δ, hδ, ?_⟩
  intro y hdy
  let y' := sphereMap e.symm y
  have hdy' : dist y' target' < δ := by
    simpa [y', target', sphereMap_dist] using hdy
  have htarget' : dist target' target' < δ := by simpa using hδ
  have hbound := hlocal hdy' htarget'
  have hhy : h y' = g y := by
    simp [h, y']
  have hhtarget : h target' = g target := by
    simp [h, target']
  rw [hhy, hhtarget] at hbound
  have hfg : g y - g target = f y - f target := by
    simp [g]
  rw [hfg] at hbound
  have hηbound : 88 * η ≤ ε := by
    dsimp [η]
    linarith
  exact le_trans hbound hηbound

private lemma local_defect_g_zero_of_s2_frame_continuity_principle_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hS2cont :
      ∀ f : spherePoint3 → ℝ,
        IsSphereFrameFunction f →
        (∀ x : spherePoint3, 0 ≤ f x) →
        Continuous f)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  rcases exists_unit_orthogonal_to_pair (H := H) hdim u v with ⟨p, hp, hup, hvp⟩
  let f : spherePoint3 → ℝ := coordSphereFrameFun μ u v p
  have hfFrame : IsSphereFrameFunction f := by
    show f ∈ sphereFrameSubmodule
    exact coordSphereFrameFun_mem_sphereFrameSubmodule_osc μ hu hv hp huv hup hvp
  let g : C(spherePoint3, ℝ) :=
    ⟨f, hS2cont f hfFrame (coordSphereFrameFun_nonneg μ u v p)⟩
  have hgFrame : g ∈ continuousSphereFrameSubmodule := by
    show f ∈ sphereFrameSubmodule
    exact hfFrame
  have hgQuad : g ∈ continuousSphereQuadraticSubmodule :=
    continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_s2_low_osc
      s2_frame_eq_low_theorem hgFrame
  rcases hgQuad with ⟨Q, hQ⟩
  exact
    local_defect_g_eq_zero_of_coordSphere_quadraticMap
      (μ := μ) (u := u) (v := v) (p := p) (Q := Q)
      (by
        intro x
        simpa [g, f] using hQ x)
      t

private lemma local_defect_g_zero_of_s2_uniform_oscillation_principle_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hS2osc :
      ∀ f : spherePoint3 → ℝ,
        IsSphereFrameFunction f →
        (∀ x : spherePoint3, 0 ≤ f x) →
        ∀ {ε : ℝ}, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ x y : spherePoint3, dist x y < δ → |f x - f y| ≤ ε)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  exact
    local_defect_g_zero_of_s2_frame_continuity_principle_osc hdim μ
      (fun f hf hnonneg =>
        continuous_s2_of_uniform_abs_oscillation (hS2osc f hf hnonneg))
      u v hu hv huv t

private theorem local_quad2DDefect_eq_zero_of_s2_frame_continuity_principle_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hS2cont :
      ∀ f : spherePoint3 → ℝ,
        IsSphereFrameFunction f →
        (∀ x : spherePoint3, 0 ≤ f x) →
        Continuous f)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    local_quad2DDefect μ u v a b = 0 := by
  have hg0 : ∀ t : ℝ, local_defect_g μ u v t = 0 :=
    fun t =>
      local_defect_g_zero_of_s2_frame_continuity_principle_osc
        hdim μ hS2cont u v hu hv huv t
  exact defect_zero_of_g_zero μ u v hg0 a b

private theorem hasQuad2D_of_s2_frame_continuity_principle_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hS2cont :
      ∀ f : spherePoint3 → ℝ,
        IsSphereFrameFunction f →
        (∀ x : spherePoint3, 0 ≤ f x) →
        Continuous f) :
    μ.HasQuad2D := by
  intro u v hu hv huv
  refine ⟨2 * frame_quadratic (H := H) μ u, 0, 2 * frame_quadratic (H := H) μ v, ?_⟩
  intro a b
  have hD : local_quad2DDefect μ u v a b = 0 :=
    local_quad2DDefect_eq_zero_of_s2_frame_continuity_principle_osc
      hdim μ hS2cont u v hu hv huv a b
  have hD' : local_quad2DExpr μ u v a b
      = 2 * a ^ 2 * frame_quadratic (H := H) μ u
        + 2 * b ^ 2 * frame_quadratic (H := H) μ v := by
    have : local_quad2DExpr μ u v a b -
        (2 * a ^ 2 * frame_quadratic (H := H) μ u +
          2 * b ^ 2 * frame_quadratic (H := H) μ v) = 0 := by
      simpa [local_quad2DDefect] using hD
    linarith
  have hpoly : local_quad2DExpr μ u v a b
      = (2 * frame_quadratic (H := H) μ u) * a ^ 2 + 0 * a * b +
          (2 * frame_quadratic (H := H) μ v) * b ^ 2 := by
    linarith [hD']
  simpa [local_quad2DExpr] using hpoly

private theorem hasQuad2D_of_s2_uniform_oscillation_principle_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hS2osc :
      ∀ f : spherePoint3 → ℝ,
        IsSphereFrameFunction f →
        (∀ x : spherePoint3, 0 ≤ f x) →
        ∀ {ε : ℝ}, 0 < ε →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ x y : spherePoint3, dist x y < δ → |f x - f y| ≤ ε) :
    μ.HasQuad2D := by
  exact hasQuad2D_of_s2_frame_continuity_principle_osc hdim μ
    (fun f hf hnonneg =>
      continuous_s2_of_uniform_abs_oscillation (hS2osc f hf hnonneg))

private theorem frame_quadratic_continuous_on_sphere_of_s2_frame_continuity_principle_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hS2cont :
      ∀ f : spherePoint3 → ℝ,
        IsSphereFrameFunction f →
        (∀ x : spherePoint3, 0 ≤ f x) →
        Continuous f) :
    ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1) := by
  have hquad := hasQuad2D_of_s2_frame_continuity_principle_osc hdim μ hS2cont
  rcases frame_quadratic_lipschitz (H := H) hdim μ hquad with ⟨C, hC⟩
  set L := |C| + 1 with hL_def
  have hLpos : 0 < L := by positivity
  have hCL : C ≤ L := le_of_lt (lt_of_le_of_lt (le_abs_self C) (lt_add_one |C|))
  intro x hx
  have hx_norm : ‖x‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hx
  apply Metric.continuousWithinAt_iff.mpr
  intro ε εpos
  refine ⟨ε / L, by positivity, ?_⟩
  intro y hy_mem hy_dist
  have hy_norm : ‖y‖ = 1 := by
    rw [Metric.mem_sphere, dist_zero_right] at hy_mem
    exact hy_mem
  rw [Real.dist_eq]
  calc
    |frame_quadratic (H := H) μ y - frame_quadratic (H := H) μ x|
        ≤ C * ‖y - x‖ := hC y x hy_norm hx_norm
    _ ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_right hCL (norm_nonneg _)
    _ = L * dist y x := by rw [dist_eq_norm]
    _ < L * (ε / L) := mul_lt_mul_of_pos_left hy_dist hLpos
    _ = ε := by field_simp [ne_of_gt hLpos]

private lemma local_defect_g_zero_of_s2_bounded_frame_continuity_principle_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hS2boundedCont :
      ∀ f : spherePoint3 → ℝ,
        IsSphereFrameFunction f →
        (∃ M : ℝ, ∀ x : spherePoint3, |f x| ≤ M) →
        Continuous f)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  exact
    local_defect_g_zero_of_s2_frame_continuity_principle_osc hdim μ
      (s2_frame_continuity_principle_of_bounded_frame_continuity hS2boundedCont)
      u v hu hv huv t

private theorem hasQuad2D_of_s2_bounded_frame_continuity_principle_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hS2boundedCont :
      ∀ f : spherePoint3 → ℝ,
        IsSphereFrameFunction f →
        (∃ M : ℝ, ∀ x : spherePoint3, |f x| ≤ M) →
        Continuous f) :
    μ.HasQuad2D := by
  exact hasQuad2D_of_s2_frame_continuity_principle_osc hdim μ
    (s2_frame_continuity_principle_of_bounded_frame_continuity hS2boundedCont)

private lemma local_defect_g_zero_of_sphere_continuity_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1))
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  rcases exists_unit_orthogonal_to_pair (H := H) hdim u v with ⟨p, hp, hup, hvp⟩
  exact
    local_defect_g_eq_zero_of_s2_frame_eq_low_of_sphere_continuous_osc
      (H := H) hdim μ hcont s2_frame_eq_low_theorem
      hu hv hp huv hup hvp t

private lemma exists_zero_pole_of_sInf_zero_of_sphere_continuity_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hInf : sInf (Q_sphere_set μ) = 0)
    (hcont : ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1)) :
    ∃ p₀ : H, ‖p₀‖ = 1 ∧ frame_quadratic (H := H) μ p₀ = 0 := by
  haveI : ProperSpace H := FiniteDimensional.proper_rclike ℂ H
  have hsphere_cpt : IsCompact (Metric.sphere (0 : H) 1) := isCompact_sphere 0 1
  have hsphere_nonempty : (Metric.sphere (0 : H) 1).Nonempty := by
    have hdim_pos : 0 < Module.finrank ℂ H := by omega
    haveI : Nontrivial H := Module.nontrivial_of_finrank_pos hdim_pos
    obtain ⟨w, hw⟩ := exists_ne (0 : H)
    refine ⟨(‖w‖⁻¹ : ℝ) • w, ?_⟩
    simp [Metric.mem_sphere, norm_smul,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
  obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
    hsphere_cpt.exists_isMinOn hsphere_nonempty hcont
  have hp₀ : ‖p₀‖ = 1 := by
    rwa [Metric.mem_sphere, dist_zero_right] at hp₀_mem
  refine ⟨p₀, hp₀, ?_⟩
  have hp₀_val :
      frame_quadratic (H := H) μ p₀ = sInf (Q_sphere_set μ) := by
    apply le_antisymm
    · exact le_csInf (Q_sphere_set_nonempty hdim μ) (fun y hy => by
        rcases hy with ⟨x, hx_mem, rfl⟩
        exact hp₀_min hx_mem)
    · exact csInf_le (Q_sphere_set_bddBelow μ) ⟨p₀, by simp [Metric.mem_sphere, hp₀], rfl⟩
  rw [hp₀_val, hInf]

private lemma local_defect_g_zero_of_shiftedNormalized_sphere_continuity_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (hden0 : 1 - sInf (Q_sphere_set μ) * (Module.finrank ℂ H : ℝ) ≠ 0)
    (hcont :
      ContinuousOn
        (fun x => frame_quadratic (H := H)
          (shiftedNormalizedFrameFunction (H := H) hdim μ hden0) x)
        (Metric.sphere (0 : H) 1))
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) :
    local_defect_g μ u v t = 0 := by
  let ν := shiftedNormalizedFrameFunction (H := H) hdim μ hden0
  have hν : local_defect_g ν u v t = 0 :=
    local_defect_g_zero_of_sphere_continuity_osc hdim ν hcont u v hu hv huv t
  exact
    local_defect_g_eq_zero_of_shiftedNormalized_zero_osc
      (H := H) hdim μ hden0 u v hu hv huv t hν

/-- High even harmonic sectors have trivial intersection with continuous frame functions. -/
private theorem spectral_closure_theorem :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
      continuousSphereFrameSubmodule = ⊥ := by
  exact spectral_closure_theorem_of_s2_frame_eq_low_osc s2_frame_eq_low_theorem

/-- The centered north-zonal square quotient is continuous at the north pole. -/
private theorem sqquotientRaw_continuousAt_zero_theorem :
    ∀ {g : C(spherePoint3, ℝ)},
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule →
      IsNorthZonal g →
      ContinuousAt (sqCenteredNorthZonalQuotientRaw g) zeroUnitIcc := by
  intro g hg _hgz
  have hg0 : g = 0 := by
    have hgBot : g ∈ (⊥ : Submodule ℝ C(spherePoint3, ℝ)) := by
      simpa [spectral_closure_theorem] using hg
    simpa using hgBot
  subst g
  have hzeroFun :
      sqCenteredNorthZonalQuotientRaw (0 : C(spherePoint3, ℝ)) = fun _ : unitIcc => (0 : ℝ) := by
    funext u
    by_cases hu0 : u.1 = 0
    · simp [sqCenteredNorthZonalQuotientRaw, hu0]
    · simp [sqCenteredNorthZonalQuotientRaw, hu0]
  rw [hzeroFun]
  simpa using (continuousAt_const : ContinuousAt (fun _ : unitIcc => (0 : ℝ)) zeroUnitIcc)

set_option maxHeartbeats 1200000 in
private lemma local_defect_g_zero_of_continuity_osc
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (t : ℝ) : local_defect_g μ u v t = 0 := by
  exact
    local_defect_g_zero_of_s2_frame_continuity_principle_osc hdim μ
      (s2_nonnegative_frame_continuous_osc (H := H) hdim)
      u v hu hv huv t

theorem local_quad2DDefect_eq_zero_from_oscillation
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (u v : H) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner (𝕜 := ℂ) u v = 0)
    (a b : ℝ) :
    local_quad2DDefect μ u v a b = 0 := by
  exact
    local_quad2DDefect_eq_zero_of_s2_frame_continuity_principle_osc
      hdim μ (s2_nonnegative_frame_continuous_osc (H := H) hdim)
      u v hu hv huv a b

theorem hasQuad2D_of_finrank_ge_three_from_oscillation
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H) : μ.HasQuad2D := by
  classical
  intro u v hu hv huv
  refine ⟨2 * frame_quadratic (H := H) μ u, 0, 2 * frame_quadratic (H := H) μ v, ?_⟩
  intro a b
  have hD : local_quad2DDefect μ u v a b = 0 :=
    local_quad2DDefect_eq_zero_from_oscillation hdim μ u v hu hv huv a b
  have hD' : local_quad2DExpr μ u v a b
      = 2 * a ^ 2 * frame_quadratic (H := H) μ u
        + 2 * b ^ 2 * frame_quadratic (H := H) μ v := by
    have : local_quad2DExpr μ u v a b -
        (2 * a ^ 2 * frame_quadratic (H := H) μ u +
          2 * b ^ 2 * frame_quadratic (H := H) μ v) = 0 := by
      simpa [local_quad2DDefect] using hD
    linarith
  have hpoly : local_quad2DExpr μ u v a b
      = (2 * frame_quadratic (H := H) μ u) * a ^ 2 + 0 * a * b +
          (2 * frame_quadratic (H := H) μ v) * b ^ 2 := by
    linarith [hD']
  simpa [local_quad2DExpr] using hpoly

theorem frame_quadratic_full_parallelogram_from_oscillation
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H)
    (x y : H) :
    frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
      2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y :=
  frame_quadratic_parallelogram hdim μ
    (hasQuad2D_of_finrank_ge_three_from_oscillation hdim μ) x y

theorem frame_quadratic_continuous_on_sphere_from_oscillation
    (hdim : 3 ≤ Module.finrank ℂ H) (μ : FrameFunction H) :
    ContinuousOn (fun x => frame_quadratic (H := H) μ x) (Metric.sphere (0 : H) 1) := by
  have hquad := hasQuad2D_of_finrank_ge_three_from_oscillation hdim μ
  rcases frame_quadratic_lipschitz (H := H) hdim μ hquad with ⟨C, hC⟩
  set L := |C| + 1 with hL_def
  have hLpos : 0 < L := by positivity
  have hCL : C ≤ L := le_of_lt (lt_of_le_of_lt (le_abs_self C) (lt_add_one |C|))
  intro x hx
  have hx_norm : ‖x‖ = 1 := by rwa [Metric.mem_sphere, dist_zero_right] at hx
  apply Metric.continuousWithinAt_iff.mpr
  intro ε εpos
  refine ⟨ε / L, by positivity, ?_⟩
  intro y hy_mem hy_dist
  have hy_norm : ‖y‖ = 1 := by
    rw [Metric.mem_sphere, dist_zero_right] at hy_mem; exact hy_mem
  rw [Real.dist_eq]
  calc
    |frame_quadratic (H := H) μ y - frame_quadratic (H := H) μ x|
        ≤ C * ‖y - x‖ := hC y x hy_norm hx_norm
    _ ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_right hCL (norm_nonneg _)
    _ = L * dist y x := by congr 1; exact (dist_eq_norm y x).symm
    _ < L * (ε / L) := mul_lt_mul_of_pos_left hy_dist hLpos
    _ = ε := by field_simp

/-- Every nonnegative frame function on the real two-sphere is continuous. -/
theorem s2_nonnegative_frame_continuous
    (f : spherePoint3 → ℝ)
    (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) :
    Continuous f := by
  have hdim : 3 ≤ Module.finrank ℂ (EuclideanSpace ℂ (Fin 3)) := by simp
  exact
    s2_nonnegative_frame_continuous_osc
      (H := EuclideanSpace ℂ (Fin 3)) hdim f hf hnonneg

/-- Every nonnegative frame function on the real two-sphere is the restriction
of a quadratic map on the ambient real three-dimensional Hilbert space. -/
theorem s2_nonnegative_frame_is_quadratic
    (f : spherePoint3 → ℝ)
    (hf : IsSphereFrameFunction f)
    (hnonneg : ∀ x : spherePoint3, 0 ≤ f x) :
    ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ,
      ∀ x : spherePoint3, f x = Q x.1 := by
  let fC : C(spherePoint3, ℝ) :=
    ⟨f, s2_nonnegative_frame_continuous f hf hnonneg⟩
  have hfC : fC ∈ continuousSphereFrameSubmodule := by
    exact hf
  have hquadratic : fC ∈ continuousSphereQuadraticSubmodule :=
    continuousSphereFrameSubmodule_le_continuousSphereQuadraticSubmodule_of_s2_low_osc
      s2_frame_eq_low_theorem hfC
  exact hquadratic
