import Mathlib
import Gleason.Finite.FrameFunction
import Gleason.Finite.Quadratic.Basic
import Gleason.Finite.Quadratic.Homogeneity
import Gleason.Finite.Quadratic.Orthonormal

noncomputable section

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

theorem parallelogram_orthogonal (μ : FrameFunction H) (hquad : μ.HasQuad2D)
    (x y : H) (hxy : inner (𝕜 := ℂ) x y = 0) :
    frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
      2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by
  classical
  by_cases hx0 : x = 0
  · subst hx0
    -- Q(y) + Q(-y) = 2 Q(y)
    simp [sub_eq_add_neg, frame_quadratic_zero (H := H), frame_quadratic_neg (H := H)]
    ring
  by_cases hy0 : y = 0
  · subst hy0
    simp [sub_eq_add_neg, frame_quadratic_zero (H := H)]
    ring

  have hx : x ≠ 0 := hx0
  have hy : y ≠ 0 := hy0
  have hnx : ‖x‖ ≠ 0 := by simpa [norm_eq_zero] using hx
  have hny : ‖y‖ ≠ 0 := by simpa [norm_eq_zero] using hy
  have hcx : ((‖x‖ : ℂ)) ≠ 0 := by exact_mod_cast hnx
  have hcy : ((‖y‖ : ℂ)) ≠ 0 := by exact_mod_cast hny

  let u : H := ((‖x‖ : ℂ)⁻¹) • x
  let v : H := ((‖y‖ : ℂ)⁻¹) • y

  have hu : ‖u‖ = (1 : ℝ) := by
    calc
      ‖u‖ = ‖((‖x‖ : ℂ)⁻¹)‖ * ‖x‖ := by simp [u, norm_smul]
      _ = (‖(‖x‖ : ℂ)‖)⁻¹ * ‖x‖ := by simp
      _ = (‖x‖)⁻¹ * ‖x‖ := by simp [Complex.norm_real]
      _ = 1 := by simpa using inv_mul_cancel₀ hnx

  have hv : ‖v‖ = (1 : ℝ) := by
    calc
      ‖v‖ = ‖((‖y‖ : ℂ)⁻¹)‖ * ‖y‖ := by simp [v, norm_smul]
      _ = (‖(‖y‖ : ℂ)‖)⁻¹ * ‖y‖ := by simp
      _ = (‖y‖)⁻¹ * ‖y‖ := by simp [Complex.norm_real]
      _ = 1 := by simpa using inv_mul_cancel₀ hny

  have huv : inner (𝕜 := ℂ) u v = 0 := by
    simp [u, v, hxy]

  -- First prove the complex rescaling equalities, then convert to real-smul.
  have hxC : ((‖x‖ : ℂ) • u) = x := by
    simp [u, smul_smul, hcx]
  have hyC : ((‖y‖ : ℂ) • v) = y := by
    simp [v, smul_smul, hcy]

  have hxsmul : (‖x‖ : ℝ) • u = x := by
    simpa [Algebra.smul_def] using hxC
  have hysmul : (‖y‖ : ℝ) • v = y := by
    simpa [Algebra.smul_def] using hyC

  have hlin :=
    frame_quadratic_linear_combination (H := H) μ hquad u v hu hv huv ‖x‖ ‖y‖

  have hlin' :
      frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y) =
        2 * ‖x‖ ^ 2 * frame_quadratic (H := H) μ u +
          2 * ‖y‖ ^ 2 * frame_quadratic (H := H) μ v := by
    simpa [hxsmul, hysmul] using hlin

  have hxQ : frame_quadratic (H := H) μ x = ‖x‖ ^ 2 * frame_quadratic (H := H) μ u := by
    have hhom := frame_quadratic_sq_hom (H := H) μ (‖x‖ : ℂ) u
    simpa [hxC, Complex.norm_real, mul_assoc] using hhom
  have hyQ : frame_quadratic (H := H) μ y = ‖y‖ ^ 2 * frame_quadratic (H := H) μ v := by
    have hhom := frame_quadratic_sq_hom (H := H) μ (‖y‖ : ℂ) v
    simpa [hyC, Complex.norm_real, mul_assoc] using hhom

  calc
    frame_quadratic (H := H) μ (x + y) + frame_quadratic (H := H) μ (x - y)
        = 2 * ‖x‖ ^ 2 * frame_quadratic (H := H) μ u +
            2 * ‖y‖ ^ 2 * frame_quadratic (H := H) μ v := hlin'
    _ = 2 * frame_quadratic (H := H) μ x + 2 * frame_quadratic (H := H) μ y := by
      have hxQ' : ‖x‖ ^ 2 * frame_quadratic (H := H) μ u = frame_quadratic (H := H) μ x := hxQ.symm
      have hyQ' : ‖y‖ ^ 2 * frame_quadratic (H := H) μ v = frame_quadratic (H := H) μ y := hyQ.symm
      simp [mul_assoc, hxQ', hyQ']

