import Gleason.Separable.RealTrace
import Gleason.Separable.RankOneTrace

/-!
# Uniqueness over the Real Field

Rank-one trace values determine the diagonal quadratic form. Real
polarization then determines the representing operator.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem represents_unique_real (m : ProjectionMeasure ℝ H)
    {T S : H →L[ℝ] H} (hT : Represents m T) (hS : Represents m S) :
    T = S := by
  have hunit : ∀ u : H, ‖u‖ = 1 →
      inner ℝ u (T u) = inner ℝ u (S u) := by
    intro u hu
    let P := OrthogonalProjection.rankOne (𝕜 := ℝ) u
    have hTu := hasProjectionTrace_rankOne_eq_inner
      T u hu (m.μ P) (hT.2.2 P)
    have hSu := hasProjectionTrace_rankOne_eq_inner
      S u hu (m.μ P) (hS.2.2 P)
    simpa using hTu.symm.trans hSu
  have hdiag : ∀ x : H,
      inner ℝ x (T x) = inner ℝ x (S x) := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp
    let u : H := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, norm_ne_zero_iff.mpr hx]
    have hxu : ‖x‖ • u = x := by
      simp [u, smul_smul, norm_ne_zero_iff.mpr hx]
    calc
      inner ℝ x (T x) =
          inner ℝ (‖x‖ • u) (T (‖x‖ • u)) := by rw [hxu]
      _ = ‖x‖ ^ 2 * inner ℝ u (T u) := by
        simp [inner_smul_left, inner_smul_right, pow_two, mul_assoc]
      _ = ‖x‖ ^ 2 * inner ℝ u (S u) := by rw [hunit u hu]
      _ = inner ℝ (‖x‖ • u) (S (‖x‖ • u)) := by
        simp [inner_smul_left, inner_smul_right, pow_two, mul_assoc]
      _ = inner ℝ x (S x) := by rw [hxu]
  have hT_sym : T.toLinearMap.IsSymmetric := hT.1.isSymmetric
  have hS_sym : S.toLinearMap.IsSymmetric := hS.1.isSymmetric
  let D : H →ₗ[ℝ] H := T.toLinearMap - S.toLinearMap
  have hD_sym : D.IsSymmetric := hT_sym.sub hS_sym
  have hD_diag : ∀ x : H, inner ℝ (D x) x = 0 := by
    intro x
    simp only [D, LinearMap.sub_apply, inner_sub_left]
    rw [hT_sym x x, hS_sym x x]
    change inner ℝ x (T x) - inner ℝ x (S x) = 0
    rw [hdiag x]
    exact sub_self _
  have hD_zero : D = 0 := hD_sym.inner_map_self_eq_zero.mp hD_diag
  apply ContinuousLinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hD_zero x
  have hx' : T x - S x = 0 := by
    simpa [D] using hx
  exact sub_eq_zero.mp hx'

end ClassicalGleason.Separable
