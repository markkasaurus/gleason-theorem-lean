import Gleason.Separable.ComplexTrace
import Gleason.Separable.RankOneTrace

/-!
# Uniqueness over the Complex Field

Rank-one trace values determine the diagonal quadratic form. Complex
polarization then determines the representing operator.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem represents_unique_complex (m : ProjectionMeasure ℂ H)
    {T S : H →L[ℂ] H} (hT : Represents m T) (hS : Represents m S) :
    T = S := by
  have hunit : ∀ u : H, ‖u‖ = 1 →
      (inner ℂ u (T u)).re = (inner ℂ u (S u)).re := by
    intro u hu
    let P := OrthogonalProjection.rankOne (𝕜 := ℂ) u
    have hTu := hasProjectionTrace_rankOne_eq_inner T u hu (m.μ P) (hT.2.2 P)
    have hSu := hasProjectionTrace_rankOne_eq_inner S u hu (m.μ P) (hS.2.2 P)
    exact hTu.symm.trans hSu

  have hdiag : ∀ x : H,
      (inner ℂ x (T x)).re = (inner ℂ x (S x)).re := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp
    let u : H := ((‖x‖⁻¹ : ℂ)) • x
    have hu : ‖u‖ = 1 := by
      simpa [u] using norm_smul_inv_norm (𝕜 := ℂ) hx
    have hxu : ((‖x‖ : ℂ) • u) = x := by
      simp [u, smul_smul, hx]
    rw [← hxu]
    simp only [map_smul, inner_smul_left, inner_smul_right]
    simp [Complex.mul_re, hunit u hu]

  have hTself : IsSelfAdjoint T :=
    (ContinuousLinearMap.isPositive_def'.mp hT.1).1
  have hSself : IsSelfAdjoint S :=
    (ContinuousLinearMap.isPositive_def'.mp hS.1).1
  have hTsym : T.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hTself
  have hSsym : S.toLinearMap.IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSself
  have hlin : T.toLinearMap = S.toLinearMap := by
    apply (ext_inner_map T.toLinearMap S.toLinearMap).mp
    intro x
    calc
      inner ℂ (T x) x = inner ℂ x (T x) := hTsym x x
      _ = (RCLike.re (inner ℂ x (T x)) : ℂ) :=
        (hTsym.coe_re_inner_self_apply x).symm
      _ = (RCLike.re (inner ℂ x (S x)) : ℂ) := by
        simpa only [RCLike.re_eq_complex_re] using
          congrArg (fun r : ℝ => (r : ℂ)) (hdiag x)
      _ = inner ℂ x (S x) := hSsym.coe_re_inner_self_apply x
      _ = inner ℂ (S x) x := (hSsym x x).symm
  ext x
  exact LinearMap.congr_fun hlin x

end ClassicalGleason.Separable
