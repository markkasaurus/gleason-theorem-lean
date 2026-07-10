import Gleason.Harmonic.Zonal.NorthZonalSubmodule
import Gleason.Harmonic.Sphere.SphereCoordsAlgebra
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

lemma fst_norm_sq_add_snd_sq (x : spherePoint3) :
    ‖x.1.fst‖ ^ 2 + x.1.snd ^ 2 = 1 := by
  have hinner := (WithLp.prod_inner_apply (𝕜 := ℝ) x.1 x.1)
  have hnormsq : ‖x.1‖ ^ 2 = ‖x.1.fst‖ ^ 2 + x.1.snd ^ 2 := by
    simpa [inner_self_eq_norm_sq_to_K, pow_two] using hinner
  have hx2 : ‖x.1‖ ^ 2 = 1 := by
    nlinarith [x.2]
  nlinarith

def northCanonical (x : spherePoint3) : spherePoint3 :=
  ⟨WithLp.toLp 2 (((‖x.1.fst‖ : ℂ)), x.1.snd), by
    have hsq :
        ‖WithLp.toLp 2 (((‖x.1.fst‖ : ℂ)), x.1.snd)‖ ^ 2 = 1 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      have hx := fst_norm_sq_add_snd_sq x
      simpa [pow_two, sq_abs, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] using hx
    have hnonneg : 0 ≤ ‖WithLp.toLp 2 (((‖x.1.fst‖ : ℂ)), x.1.snd)‖ := norm_nonneg _
    nlinarith⟩

@[simp] lemma northCanonical_snd (x : spherePoint3) :
    (northCanonical x).1.snd = x.1.snd := by
  simp [northCanonical]

lemma snd_mem_Icc (x : spherePoint3) :
    x.1.snd ∈ Set.Icc (-1 : ℝ) 1 := by
  have hx : ‖x.1.fst‖ ^ 2 + x.1.snd ^ 2 = 1 := fst_norm_sq_add_snd_sq x
  have hxle : x.1.snd ^ 2 ≤ 1 := by
    nlinarith [hx, sq_nonneg ‖x.1.fst‖]
  have hupper : x.1.snd ≤ 1 := by
    nlinarith
  have hlower : -1 ≤ x.1.snd := by
    nlinarith
  exact ⟨hlower, hupper⟩

def northSection (z : Set.Icc (-1 : ℝ) 1) : spherePoint3 :=
  ⟨WithLp.toLp 2 (((Real.sqrt (1 - z.1 ^ 2) : ℝ) : ℂ), z.1), by
    have hzsq : z.1 ^ 2 ≤ 1 := by
      nlinarith [z.2.1, z.2.2]
    have hsq :
        ‖WithLp.toLp 2 ((((Real.sqrt (1 - z.1 ^ 2) : ℝ) : ℂ)), z.1)‖ ^ 2 = 1 := by
      rw [WithLp.prod_norm_sq_eq_of_L2]
      have hsqrt : (Real.sqrt (1 - z.1 ^ 2)) ^ 2 = 1 - z.1 ^ 2 := by
        rw [Real.sq_sqrt]
        linarith
      have hreal :
          ‖(((Real.sqrt (1 - z.1 ^ 2) : ℝ) : ℂ))‖ ^ 2 =
            (Real.sqrt (1 - z.1 ^ 2)) ^ 2 := by
        simpa [Complex.normSq_eq_norm_sq] using
          (Complex.normSq_ofReal (Real.sqrt (1 - z.1 ^ 2)))
      have hmain :
          ‖(((Real.sqrt (1 - z.1 ^ 2) : ℝ) : ℂ))‖ ^ 2 + z.1 ^ 2 = 1 := by
        rw [hreal, hsqrt]
        ring
      simpa [pow_two] using hmain
    have hnonneg : 0 ≤ ‖WithLp.toLp 2 ((((Real.sqrt (1 - z.1 ^ 2) : ℝ) : ℂ)), z.1)‖ :=
      norm_nonneg _
    nlinarith
  ⟩

@[simp] lemma northSection_snd (z : Set.Icc (-1 : ℝ) 1) :
    (northSection z).1.snd = z.1 := by
  simp [northSection]

lemma northCanonical_eq_of_snd_eq {x y : spherePoint3}
    (hxy : x.1.snd = y.1.snd) :
    northCanonical x = northCanonical y := by
  have hx : ‖x.1.fst‖ ^ 2 + x.1.snd ^ 2 = 1 := fst_norm_sq_add_snd_sq x
  have hy : ‖y.1.fst‖ ^ 2 + y.1.snd ^ 2 = 1 := fst_norm_sq_add_snd_sq y
  rw [← hxy] at hy
  have hsq : ‖x.1.fst‖ ^ 2 = ‖y.1.fst‖ ^ 2 := by
    nlinarith [hx, hy]
  have hnorm : ‖x.1.fst‖ = ‖y.1.fst‖ := by
    nlinarith [norm_nonneg x.1.fst, norm_nonneg y.1.fst, hsq]
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  simp [northCanonical, hnorm, hxy]

lemma northSection_eq_northCanonical_snd (x : spherePoint3) :
    northSection ⟨x.1.snd, snd_mem_Icc x⟩ = northCanonical x := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  have hx : ‖x.1.fst‖ ^ 2 + x.1.snd ^ 2 = 1 := fst_norm_sq_add_snd_sq x
  have hnonneg : 0 ≤ 1 - x.1.snd ^ 2 := by
    nlinarith [hx, sq_nonneg ‖x.1.fst‖]
  have hsq : ‖x.1.fst‖ ^ 2 = 1 - x.1.snd ^ 2 := by
    nlinarith [hx]
  have hnorm :
      ‖x.1.fst‖ = Real.sqrt (1 - x.1.snd ^ 2) := by
    have hsqrt := congrArg Real.sqrt hsq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hsqrt
    exact hsqrt
  simp [northSection, northCanonical, hnorm]

lemma exists_northRotation_northCanonical (x : spherePoint3) :
    ∃ t : ℝ, sphereMap (northRotation t) (northCanonical x) = x := by
  refine ⟨Complex.arg x.1.fst, ?_⟩
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  refine Prod.ext ?_ rfl
  calc
    (((Circle.exp (Complex.arg x.1.fst) : Circle) : ℂ) * (‖x.1.fst‖ : ℂ))
        = Complex.exp (Complex.arg x.1.fst * Complex.I) * (‖x.1.fst‖ : ℂ) := by
            simp [Circle.coe_exp]
    _ = x.1.fst := by
          simpa [mul_comm] using Complex.norm_mul_exp_arg_mul_I x.1.fst

lemma eq_of_isNorthZonal_of_snd_eq
    {f : C(spherePoint3, ℝ)} (hf : IsNorthZonal f)
    {x y : spherePoint3} (hxy : x.1.snd = y.1.snd) :
    f x = f y := by
  rcases exists_northRotation_northCanonical x with ⟨tx, htx⟩
  rcases exists_northRotation_northCanonical y with ⟨ty, hty⟩
  have hfx :=
    congrArg (fun g : C(spherePoint3, ℝ) => g (northCanonical x)) (hf tx)
  have hfy :=
    congrArg (fun g : C(spherePoint3, ℝ) => g (northCanonical y)) (hf ty)
  have hcan : northCanonical x = northCanonical y :=
    northCanonical_eq_of_snd_eq hxy
  calc
    f x = f (northCanonical x) := by
      simpa [spherePrecomp_apply, htx] using hfx
    _ = f (northCanonical y) := by rw [hcan]
    _ = f y := by
      symm
      simpa [spherePrecomp_apply, hty] using hfy

lemma eq_of_isNorthZonal_of_sphereCoordZ_eq
    {f : C(spherePoint3, ℝ)} (hf : IsNorthZonal f)
    {x y : spherePoint3} (hxy : sphereCoordZ x = sphereCoordZ y) :
    f x = f y := by
  exact eq_of_isNorthZonal_of_snd_eq hf (by simpa [sphereCoordZ] using hxy)

def northZonalProfile (f : C(spherePoint3, ℝ)) :
    Set.Icc (-1 : ℝ) 1 → ℝ :=
  fun z => f (northSection z)

@[simp] lemma northZonalProfile_apply
    (f : C(spherePoint3, ℝ)) (z : Set.Icc (-1 : ℝ) 1) :
    northZonalProfile f z = f (northSection z) := by
  rfl

lemma northZonalProfile_eq_of_isNorthZonal
    {f : C(spherePoint3, ℝ)} (hf : IsNorthZonal f) (x : spherePoint3) :
    northZonalProfile f ⟨x.1.snd, snd_mem_Icc x⟩ = f x := by
  rw [northZonalProfile_apply, northSection_eq_northCanonical_snd]
  exact eq_of_isNorthZonal_of_snd_eq hf (x := northCanonical x) (y := x) (by simp [northCanonical_snd])
