import Gleason.Harmonic.Auxiliary.PoleAverage
import Gleason.Harmonic.Sphere.SphericalBridge
import Gleason.Harmonic.Sphere.S2PoleAverageEquivariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

def greatCircleParamPoint
    (x y : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (θ : ℝ) : spherePoint3 :=
  ⟨Real.cos θ • x.1 + Real.sin θ • y.1, by
    have hx : ‖x.1‖ = 1 := x.2
    have hy : ‖y.1‖ = 1 := y.2
    have horth :
        inner (𝕜 := ℝ) (Real.cos θ • x.1) (Real.sin θ • y.1) = 0 := by
      simp [inner_smul_left, inner_smul_right, hxy]
    have hsq :
        ‖Real.cos θ • x.1 + Real.sin θ • y.1‖ ^ 2 =
          Real.cos θ ^ 2 + Real.sin θ ^ 2 := by
      rw [pow_two]
      rw [norm_add_sq_eq_norm_sq_add_norm_sq_real horth]
      simp [norm_smul, hx, hy]
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hnorm :
        ‖Real.cos θ • x.1 + Real.sin θ • y.1‖ = 1 := by
      have hnonneg : 0 ≤ ‖Real.cos θ • x.1 + Real.sin θ • y.1‖ := norm_nonneg _
      nlinarith [Real.sin_sq_add_cos_sq θ]
    exact hnorm⟩

@[simp] theorem greatCircleParamPoint_val
    (x y : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (θ : ℝ) :
    (greatCircleParamPoint x y hxy θ).1 =
      Real.cos θ • x.1 + Real.sin θ • y.1 := rfl

theorem continuous_greatCircleParamPoint
    {X : Type*} [TopologicalSpace X]
    {x y : X → spherePoint3}
    (hx : Continuous x) (hy : Continuous y)
    (hxy : ∀ a : X, inner (𝕜 := ℝ) (x a).1 (y a).1 = 0) :
    Continuous fun p : X × ℝ =>
      greatCircleParamPoint (x p.1) (y p.1) (hxy p.1) p.2 := by
  refine Continuous.subtype_mk ?_ (fun p => (greatCircleParamPoint (x p.1) (y p.1) (hxy p.1) p.2).2)
  have hxval : Continuous fun p : X × ℝ => (x p.1).1 :=
    continuous_subtype_val.comp (hx.comp continuous_fst)
  have hyval : Continuous fun p : X × ℝ => (y p.1).1 :=
    continuous_subtype_val.comp (hy.comp continuous_fst)
  have hcos : Continuous fun p : X × ℝ => Real.cos p.2 := Real.continuous_cos.comp continuous_snd
  have hsin : Continuous fun p : X × ℝ => Real.sin p.2 := Real.continuous_sin.comp continuous_snd
  simpa [greatCircleParamPoint] using (hcos.smul hxval).add (hsin.smul hyval)

theorem sphereMap_sphereTripleIsometryEquiv_equatorSpherePoint
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (θ : ℝ) :
    sphereMap (sphereTripleIsometryEquiv x y z hxy hxz hyz) (equatorSpherePoint θ) =
      greatCircleParamPoint x y hxy θ := by
  apply Subtype.ext
  change
    sphereTripleIsometryEquiv x y z hxy hxz hyz (equatorSpherePoint θ).1 =
      (greatCircleParamPoint x y hxy θ).1
  have hcombo :
      (equatorSpherePoint θ).1 =
        Real.cos θ • sphereE1.1 + Real.sin θ • sphereE2.1 := by
    apply (WithLp.equiv 2 (ℂ × ℝ)).injective
    simp [equatorSpherePoint, sphereE1, sphereE2]
    ring
  rw [hcombo]
  simp [map_add]

theorem greatCircleAverageLinear_eq_paramIntegral
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    greatCircleAverageLinear x y z hxy hxz hyz f =
      (2 * Real.pi)⁻¹ *
        ∫ θ in 0..2 * Real.pi, f (greatCircleParamPoint x y hxy θ) := by
  rw [greatCircleAverageLinear_apply, northEquatorAverageLinear_apply]
  congr 1
  congr 1
  funext θ
  simp [spherePrecomp_apply, sphereMap_sphereTripleIsometryEquiv_equatorSpherePoint]

theorem continuous_parametric_greatCircleAverage
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {x y : X → spherePoint3}
    (hx : Continuous x) (hy : Continuous y)
    (hxy : ∀ a : X, inner (𝕜 := ℝ) (x a).1 (y a).1 = 0)
    (f : C(spherePoint3, ℝ)) :
    Continuous fun a : X =>
      (2 * Real.pi)⁻¹ *
        ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
          f (greatCircleParamPoint (x a) (y a) (hxy a) θ) := by
  have huncurry :
      Continuous fun p : X × ℝ =>
        f (greatCircleParamPoint (x p.1) (y p.1) (hxy p.1) p.2) :=
    f.continuous.comp (continuous_greatCircleParamPoint hx hy hxy)
  exact continuous_const.mul
    (continuous_parametric_integral_of_continuous huncurry isCompact_Icc)

theorem continuous_parametric_greatCircleAverageLinear
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {x y z : X → spherePoint3}
    (hx : Continuous x) (hy : Continuous y)
    (hxy : ∀ a : X, inner (𝕜 := ℝ) (x a).1 (y a).1 = 0)
    (hxz : ∀ a : X, inner (𝕜 := ℝ) (x a).1 (z a).1 = 0)
    (hyz : ∀ a : X, inner (𝕜 := ℝ) (y a).1 (z a).1 = 0)
    (f : C(spherePoint3, ℝ)) :
    Continuous fun a : X =>
      greatCircleAverageLinear (x a) (y a) (z a)
        (hxy a) (hxz a) (hyz a) f := by
  have hcont :=
    continuous_parametric_greatCircleAverage hx hy hxy f
  have hEq :
      (fun a : X =>
        greatCircleAverageLinear (x a) (y a) (z a)
          (hxy a) (hxz a) (hyz a) f) =
      fun a : X =>
        (2 * Real.pi)⁻¹ *
          ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
            f (greatCircleParamPoint (x a) (y a) (hxy a) θ) := by
    funext a
    rw [greatCircleAverageLinear_eq_paramIntegral]
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    rw [← integral_Icc_eq_integral_Ioc]
  rw [hEq]
  exact hcont

theorem continuousOn_poleAverageLinear_of_local_frame
    {s : Set spherePoint3} [LocallyCompactSpace s]
    {x y : s → spherePoint3}
    (hx : Continuous x) (hy : Continuous y)
    (hxy : ∀ a : s, inner (𝕜 := ℝ) (x a).1 (y a).1 = 0)
    (hxz : ∀ a : s, inner (𝕜 := ℝ) (x a).1 a.1.1 = 0)
    (hyz : ∀ a : s, inner (𝕜 := ℝ) (y a).1 a.1.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    ContinuousOn (fun z : spherePoint3 => poleAverageLinear f z) s := by
  rw [continuousOn_iff_continuous_restrict]
  let z : s → spherePoint3 := fun a => a.1
  have hcont :
      Continuous fun a : s =>
        greatCircleAverageLinear (x a) (y a) (z a)
          (hxy a) (hxz a) (hyz a) f :=
    continuous_parametric_greatCircleAverageLinear hx hy hxy hxz hyz f
  have hEq :
      s.restrict (fun z : spherePoint3 => poleAverageLinear f z) =
        fun a : s =>
          greatCircleAverageLinear (x a) (y a) (z a)
            (hxy a) (hxz a) (hyz a) f := by
    funext a
    exact
      poleAverageLinear_eq_greatCircleAverageLinear
        f (x a) (y a) (z a) (hxy a) (hxz a) (hyz a)
  rw [hEq]
  exact hcont

theorem continuousAt_poleAverageLinear_of_local_frame
    {s : Set spherePoint3} (hs : IsOpen s) {z0 : spherePoint3} (hz0 : z0 ∈ s)
    {x y : s → spherePoint3}
    (hx : Continuous x) (hy : Continuous y)
    (hxy : ∀ a : s, inner (𝕜 := ℝ) (x a).1 (y a).1 = 0)
    (hxz : ∀ a : s, inner (𝕜 := ℝ) (x a).1 a.1.1 = 0)
    (hyz : ∀ a : s, inner (𝕜 := ℝ) (y a).1 a.1.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    ContinuousAt (fun z : spherePoint3 => poleAverageLinear f z) z0 := by
  letI : LocallyCompactSpace s := hs.locallyCompactSpace
  exact
    (continuousOn_poleAverageLinear_of_local_frame hx hy hxy hxz hyz f).continuousAt
      (hs.mem_nhds hz0)

def ambientCross (u v : sphereAmbient3) : sphereAmbient3 :=
  ambientPointOfCoords fun i =>
    match i with
    | 0 => ambientCoordFun 1 u * ambientCoordFun 2 v -
        ambientCoordFun 2 u * ambientCoordFun 1 v
    | 1 => ambientCoordFun 2 u * ambientCoordFun 0 v -
        ambientCoordFun 0 u * ambientCoordFun 2 v
    | 2 => ambientCoordFun 0 u * ambientCoordFun 1 v -
        ambientCoordFun 1 u * ambientCoordFun 0 v

@[simp] theorem ambientCoordFun_ambientCross_zero (u v : sphereAmbient3) :
    ambientCoordFun 0 (ambientCross u v) =
      ambientCoordFun 1 u * ambientCoordFun 2 v -
        ambientCoordFun 2 u * ambientCoordFun 1 v := by
  simp [ambientCross]

@[simp] theorem ambientCoordFun_ambientCross_one (u v : sphereAmbient3) :
    ambientCoordFun 1 (ambientCross u v) =
      ambientCoordFun 2 u * ambientCoordFun 0 v -
        ambientCoordFun 0 u * ambientCoordFun 2 v := by
  simp [ambientCross]

@[simp] theorem ambientCoordFun_ambientCross_two (u v : sphereAmbient3) :
    ambientCoordFun 2 (ambientCross u v) =
      ambientCoordFun 0 u * ambientCoordFun 1 v -
        ambientCoordFun 1 u * ambientCoordFun 0 v := by
  simp [ambientCross]

theorem ambientCross_inner_left (u v : sphereAmbient3) :
    inner (𝕜 := ℝ) (ambientCross u v) u = 0 := by
  rw [WithLp.prod_inner_apply]
  simp [ambientCross, ambientPointOfCoords, ambientCoordFun, complexProjL, realProjL,
    Complex.mul_re, sub_eq_add_neg]
  ring

theorem ambientCross_inner_right (u v : sphereAmbient3) :
    inner (𝕜 := ℝ) (ambientCross u v) v = 0 := by
  rw [WithLp.prod_inner_apply]
  simp [ambientCross, ambientPointOfCoords, ambientCoordFun, complexProjL, realProjL,
    Complex.mul_re, sub_eq_add_neg]
  ring

theorem ambientCross_norm_sq (u v : sphereAmbient3) :
    ‖ambientCross u v‖ ^ 2 =
      (ambientCoordFun 1 u * ambientCoordFun 2 v -
          ambientCoordFun 2 u * ambientCoordFun 1 v) ^ 2 +
        (ambientCoordFun 2 u * ambientCoordFun 0 v -
          ambientCoordFun 0 u * ambientCoordFun 2 v) ^ 2 +
        (ambientCoordFun 0 u * ambientCoordFun 1 v -
          ambientCoordFun 1 u * ambientCoordFun 0 v) ^ 2 := by
  simpa [ambientCross] using
    GleasonS2Bridge.ambientPointOfCoords_norm_sq
      (fun i : Fin 3 =>
        match i with
        | 0 => ambientCoordFun 1 u * ambientCoordFun 2 v -
            ambientCoordFun 2 u * ambientCoordFun 1 v
        | 1 => ambientCoordFun 2 u * ambientCoordFun 0 v -
            ambientCoordFun 0 u * ambientCoordFun 2 v
        | 2 => ambientCoordFun 0 u * ambientCoordFun 1 v -
            ambientCoordFun 1 u * ambientCoordFun 0 v)

theorem ambient_norm_sq_eq_coord (u : sphereAmbient3) :
    ‖u‖ ^ 2 =
      ambientCoordFun 0 u ^ 2 + ambientCoordFun 1 u ^ 2 + ambientCoordFun 2 u ^ 2 := by
  have hinner := (WithLp.prod_inner_apply (𝕜 := ℝ) u u)
  have hnormsq :
      ‖u‖ ^ 2 = ‖u.fst‖ ^ 2 + u.snd ^ 2 := by
    simpa [inner_self_eq_norm_sq_to_K, pow_two] using hinner
  have hcomplex : ‖u.fst‖ ^ 2 = u.fst.re ^ 2 + u.fst.im ^ 2 := by
    simpa [pow_two] using Complex.sq_norm u.fst
  calc
    ‖u‖ ^ 2 = ‖u.fst‖ ^ 2 + u.snd ^ 2 := hnormsq
    _ = u.fst.re ^ 2 + u.fst.im ^ 2 + u.snd ^ 2 := by rw [hcomplex]
    _ = ambientCoordFun 0 u ^ 2 + ambientCoordFun 1 u ^ 2 + ambientCoordFun 2 u ^ 2 := by
          simp [ambientCoordFun, complexProjL, realProjL]

theorem ambient_inner_eq_coord (u v : sphereAmbient3) :
    inner (𝕜 := ℝ) u v =
      ambientCoordFun 0 u * ambientCoordFun 0 v +
        ambientCoordFun 1 u * ambientCoordFun 1 v +
        ambientCoordFun 2 u * ambientCoordFun 2 v := by
  rw [WithLp.prod_inner_apply]
  simp [ambientCoordFun, complexProjL, realProjL, Complex.mul_re, add_assoc, mul_comm]

theorem ambientCross_norm_eq_one_of_orthonormal
    {u v : sphereAmbient3}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner (𝕜 := ℝ) u v = 0) :
    ‖ambientCross u v‖ = 1 := by
  have hucoord := ambient_norm_sq_eq_coord u
  have hvcoord := ambient_norm_sq_eq_coord v
  have huvcoord := ambient_inner_eq_coord u v
  rw [hu] at hucoord
  rw [hv] at hvcoord
  rw [huv] at huvcoord
  have hcross := ambientCross_norm_sq u v
  have hlagrange :
      (ambientCoordFun 1 u * ambientCoordFun 2 v -
          ambientCoordFun 2 u * ambientCoordFun 1 v) ^ 2 +
        (ambientCoordFun 2 u * ambientCoordFun 0 v -
          ambientCoordFun 0 u * ambientCoordFun 2 v) ^ 2 +
        (ambientCoordFun 0 u * ambientCoordFun 1 v -
          ambientCoordFun 1 u * ambientCoordFun 0 v) ^ 2 =
        (ambientCoordFun 0 u ^ 2 + ambientCoordFun 1 u ^ 2 + ambientCoordFun 2 u ^ 2) *
          (ambientCoordFun 0 v ^ 2 + ambientCoordFun 1 v ^ 2 + ambientCoordFun 2 v ^ 2) -
        (ambientCoordFun 0 u * ambientCoordFun 0 v +
          ambientCoordFun 1 u * ambientCoordFun 1 v +
          ambientCoordFun 2 u * ambientCoordFun 2 v) ^ 2 := by
    ring
  have hsq : ‖ambientCross u v‖ ^ 2 = 1 := by
    rw [hcross, hlagrange]
    nlinarith
  have hnonneg : 0 ≤ ‖ambientCross u v‖ := norm_nonneg _
  nlinarith

def sphereAxisAmbient (i : Fin 3) : sphereAmbient3 :=
  ambientPointOfCoords fun j : Fin 3 => if j = i then 1 else 0

theorem sphereAxisAmbient_norm (i : Fin 3) :
    ‖sphereAxisAmbient i‖ = 1 := by
  have hsq : ‖sphereAxisAmbient i‖ ^ 2 = 1 := by
    fin_cases i <;>
      simp [sphereAxisAmbient, GleasonS2Bridge.ambientPointOfCoords_norm_sq]
  have hnonneg : 0 ≤ ‖sphereAxisAmbient i‖ := norm_nonneg _
  nlinarith

def sphereAxisPoint (i : Fin 3) : spherePoint3 :=
  ⟨sphereAxisAmbient i, sphereAxisAmbient_norm i⟩

theorem continuous_ambientCoordFun (i : Fin 3) :
    Continuous (ambientCoordFun i) := by
  fin_cases i
  · simpa [ambientCoordFun, complexProjL] using
      Complex.continuous_re.comp (WithLp.continuous_fst 2 ℂ ℝ)
  · simpa [ambientCoordFun, complexProjL] using
      Complex.continuous_im.comp (WithLp.continuous_fst 2 ℂ ℝ)
  · simpa [ambientCoordFun, realProjL] using
      (WithLp.continuous_snd 2 ℂ ℝ)

theorem sphereAxisAmbient_inner (i : Fin 3) (u : sphereAmbient3) :
    inner (𝕜 := ℝ) (sphereAxisAmbient i) u = ambientCoordFun i u := by
  fin_cases i <;>
    rw [WithLp.prod_inner_apply] <;>
    simp [sphereAxisAmbient, ambientPointOfCoords, ambientCoordFun, complexProjL, realProjL,
      Complex.mul_re]

def axisPatch (i : Fin 3) : Set spherePoint3 :=
  {z | ambientCoordFun i z.1 ^ 2 < 1}

theorem isOpen_axisPatch (i : Fin 3) : IsOpen (axisPatch i) := by
  have hcoord : Continuous fun z : spherePoint3 => ambientCoordFun i z.1 :=
    (continuous_ambientCoordFun i).comp continuous_subtype_val
  change IsOpen {z : spherePoint3 | (fun z : spherePoint3 => ambientCoordFun i z.1) z ^ 2 < 1}
  exact isOpen_lt (hcoord.pow 2) continuous_const

def tangentSeed (i : Fin 3) (z : spherePoint3) : sphereAmbient3 :=
  sphereAxisAmbient i - ambientCoordFun i z.1 • z.1

theorem tangentSeed_inner_pole (i : Fin 3) (z : spherePoint3) :
    inner (𝕜 := ℝ) (tangentSeed i z) z.1 = 0 := by
  rw [tangentSeed, inner_sub_left, sphereAxisAmbient_inner, inner_smul_left]
  have hself : inner (𝕜 := ℝ) z.1 z.1 = (1 : ℝ) := by
    have hnormsq : ‖z.1‖ ^ 2 = (1 : ℝ) := by rw [z.2]; norm_num
    simpa [inner_self_eq_norm_sq_to_K] using hnormsq
  rw [hself]
  simp

theorem tangentSeed_ne_zero_of_mem_axisPatch
    {i : Fin 3} {z : spherePoint3}
    (hz : z ∈ axisPatch i) :
    tangentSeed i z ≠ 0 := by
  intro hzero
  have hEq : sphereAxisAmbient i = ambientCoordFun i z.1 • z.1 := by
    exact sub_eq_zero.mp hzero
  have hnorm := congrArg norm hEq
  have hcoord_abs : |ambientCoordFun i z.1| = 1 := by
    rw [sphereAxisAmbient_norm, norm_smul, z.2, mul_one, Real.norm_eq_abs] at hnorm
    exact hnorm.symm
  have hcoord_sq : ambientCoordFun i z.1 ^ 2 = 1 := by
    nlinarith [sq_abs (ambientCoordFun i z.1)]
  exact (ne_of_lt hz) hcoord_sq

def localFrameX (i : Fin 3) (z : axisPatch i) : spherePoint3 :=
  ⟨(‖tangentSeed i z.1‖)⁻¹ • tangentSeed i z.1, by
    have hne : tangentSeed i z.1 ≠ 0 := tangentSeed_ne_zero_of_mem_axisPatch z.2
    have hnorm_pos : 0 < ‖tangentSeed i z.1‖ := norm_pos_iff.mpr hne
    rw [norm_smul]
    simp [hnorm_pos.ne']⟩

theorem localFrameX_inner_pole (i : Fin 3) (z : axisPatch i) :
    inner (𝕜 := ℝ) (localFrameX i z).1 z.1.1 = 0 := by
  change inner (𝕜 := ℝ) ((‖tangentSeed i z.1‖)⁻¹ • tangentSeed i z.1) z.1.1 = 0
  rw [inner_smul_left, tangentSeed_inner_pole]
  simp

theorem localFrameX_norm (i : Fin 3) (z : axisPatch i) :
    ‖(localFrameX i z).1‖ = 1 :=
  (localFrameX i z).2

def localFrameY (i : Fin 3) (z : axisPatch i) : spherePoint3 :=
  ⟨ambientCross z.1.1 (localFrameX i z).1, by
    have hz : ‖z.1.1‖ = 1 := z.1.2
    have hx : ‖(localFrameX i z).1‖ = 1 := localFrameX_norm i z
    have horth : inner (𝕜 := ℝ) z.1.1 (localFrameX i z).1 = 0 := by
      rw [real_inner_comm]
      exact localFrameX_inner_pole i z
    exact ambientCross_norm_eq_one_of_orthonormal hz hx horth⟩

theorem localFrameY_inner_pole (i : Fin 3) (z : axisPatch i) :
    inner (𝕜 := ℝ) (localFrameY i z).1 z.1.1 = 0 := by
  change inner (𝕜 := ℝ) (ambientCross z.1.1 (localFrameX i z).1) z.1.1 = 0
  exact ambientCross_inner_left z.1.1 (localFrameX i z).1

theorem localFrameX_inner_localFrameY (i : Fin 3) (z : axisPatch i) :
    inner (𝕜 := ℝ) (localFrameX i z).1 (localFrameY i z).1 = 0 := by
  rw [real_inner_comm]
  change inner (𝕜 := ℝ) (ambientCross z.1.1 (localFrameX i z).1) (localFrameX i z).1 = 0
  exact ambientCross_inner_right z.1.1 (localFrameX i z).1

theorem continuous_ambientCross :
    Continuous fun p : sphereAmbient3 × sphereAmbient3 => ambientCross p.1 p.2 := by
  let c0 : sphereAmbient3 × sphereAmbient3 → ℝ := fun p =>
    ambientCoordFun 1 p.1 * ambientCoordFun 2 p.2 -
      ambientCoordFun 2 p.1 * ambientCoordFun 1 p.2
  let c1 : sphereAmbient3 × sphereAmbient3 → ℝ := fun p =>
    ambientCoordFun 2 p.1 * ambientCoordFun 0 p.2 -
      ambientCoordFun 0 p.1 * ambientCoordFun 2 p.2
  let c2 : sphereAmbient3 × sphereAmbient3 → ℝ := fun p =>
    ambientCoordFun 0 p.1 * ambientCoordFun 1 p.2 -
      ambientCoordFun 1 p.1 * ambientCoordFun 0 p.2
  have hc0 : Continuous c0 := by
    dsimp [c0]
    exact (((continuous_ambientCoordFun 1).comp continuous_fst).mul
      ((continuous_ambientCoordFun 2).comp continuous_snd)).sub
      (((continuous_ambientCoordFun 2).comp continuous_fst).mul
        ((continuous_ambientCoordFun 1).comp continuous_snd))
  have hc1 : Continuous c1 := by
    dsimp [c1]
    exact (((continuous_ambientCoordFun 2).comp continuous_fst).mul
      ((continuous_ambientCoordFun 0).comp continuous_snd)).sub
      (((continuous_ambientCoordFun 0).comp continuous_fst).mul
        ((continuous_ambientCoordFun 2).comp continuous_snd))
  have hc2 : Continuous c2 := by
    dsimp [c2]
    exact (((continuous_ambientCoordFun 0).comp continuous_fst).mul
      ((continuous_ambientCoordFun 1).comp continuous_snd)).sub
      (((continuous_ambientCoordFun 1).comp continuous_fst).mul
        ((continuous_ambientCoordFun 0).comp continuous_snd))
  have hpair : Continuous fun p : sphereAmbient3 × sphereAmbient3 =>
      (((c0 p : ℂ) + Complex.I * (c1 p : ℂ)), c2 p) := by
    have hc0c : Continuous fun p : sphereAmbient3 × sphereAmbient3 => (c0 p : ℂ) :=
      Complex.continuous_ofReal.comp hc0
    have hc1c : Continuous fun p : sphereAmbient3 × sphereAmbient3 => (c1 p : ℂ) :=
      Complex.continuous_ofReal.comp hc1
    exact (hc0c.add (continuous_const.mul hc1c)).prodMk hc2
  simpa [ambientCross, ambientPointOfCoords, c0, c1, c2] using
    (WithLp.prod_continuous_toLp 2 ℂ ℝ).comp hpair

theorem continuous_localFrameX (i : Fin 3) :
    Continuous (localFrameX i) := by
  refine Continuous.subtype_mk ?_ (fun z => (localFrameX i z).2)
  have hseed : Continuous fun z : axisPatch i => tangentSeed i z.1 := by
    have hcoord : Continuous fun z : axisPatch i => ambientCoordFun i z.1.1 :=
      (continuous_ambientCoordFun i).comp (continuous_subtype_val.comp continuous_subtype_val)
    have hzval : Continuous fun z : axisPatch i => z.1.1 := continuous_subtype_val.comp continuous_subtype_val
    simpa [tangentSeed] using continuous_const.sub (hcoord.smul hzval)
  have hnorm : Continuous fun z : axisPatch i => (‖tangentSeed i z.1‖)⁻¹ :=
    (continuous_norm.comp hseed).inv₀ fun z =>
      norm_ne_zero_iff.mpr (tangentSeed_ne_zero_of_mem_axisPatch z.2)
  simpa [localFrameX] using hnorm.smul hseed

theorem continuous_localFrameY (i : Fin 3) :
    Continuous (localFrameY i) := by
  refine Continuous.subtype_mk ?_ (fun z => (localFrameY i z).2)
  have hz : Continuous fun z : axisPatch i => z.1.1 :=
    continuous_subtype_val.comp continuous_subtype_val
  have hx : Continuous fun z : axisPatch i => (localFrameX i z).1 :=
    continuous_subtype_val.comp (continuous_localFrameX i)
  have hpair : Continuous fun z : axisPatch i => (z.1.1, (localFrameX i z).1) :=
    hz.prodMk hx
  simpa [localFrameY] using continuous_ambientCross.comp hpair

theorem continuousAt_poleAverageLinear_of_axisPatch
    (i : Fin 3) {z0 : spherePoint3} (hz0 : z0 ∈ axisPatch i)
    (f : C(spherePoint3, ℝ)) :
    ContinuousAt (fun z : spherePoint3 => poleAverageLinear f z) z0 := by
  exact
    continuousAt_poleAverageLinear_of_local_frame
      (isOpen_axisPatch i) hz0
      (continuous_localFrameX i) (continuous_localFrameY i)
      (localFrameX_inner_localFrameY i)
      (localFrameX_inner_pole i)
      (localFrameY_inner_pole i)
      f

theorem exists_mem_axisPatch (z : spherePoint3) :
    ∃ i : Fin 3, z ∈ axisPatch i := by
  by_cases h0 : ambientCoordFun 0 z.1 ^ 2 < 1
  · exact ⟨0, h0⟩
  · by_cases h1 : ambientCoordFun 1 z.1 ^ 2 < 1
    · exact ⟨1, h1⟩
    · have hsum := ambient_norm_sq_eq_coord z.1
      rw [z.2] at hsum
      norm_num at hsum
      have h0ge : 1 ≤ ambientCoordFun 0 z.1 ^ 2 := le_of_not_gt h0
      have h1ge : 1 ≤ ambientCoordFun 1 z.1 ^ 2 := le_of_not_gt h1
      have h2nonneg : 0 ≤ ambientCoordFun 2 z.1 ^ 2 := sq_nonneg _
      nlinarith

theorem continuous_poleAverageLinear (f : C(spherePoint3, ℝ)) :
    Continuous fun z : spherePoint3 => poleAverageLinear f z := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases exists_mem_axisPatch z with ⟨i, hz⟩
  exact continuousAt_poleAverageLinear_of_axisPatch i hz f

def poleAverageContinuousLinear : C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ) where
  toFun f := ⟨poleAverageLinear f, continuous_poleAverageLinear f⟩
  map_add' := by
    intro f g
    ext z
    simp
  map_smul' := by
    intro c f
    ext z
    simp

@[simp] theorem poleAverageContinuousLinear_apply
    (f : C(spherePoint3, ℝ)) (z : spherePoint3) :
    poleAverageContinuousLinear f z = poleAverageLinear f z := rfl

theorem norm_northEquatorAverageLinear_le (f : C(spherePoint3, ℝ)) :
    ‖northEquatorAverageLinear f‖ ≤ ‖f‖ := by
  rw [northEquatorAverageLinear_apply]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hInt :
      ‖∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ)‖ ≤
        ‖f‖ * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro θ hθ
    exact f.norm_coe_le_norm (equatorSpherePoint θ)
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpi)]
  calc
    (2 * Real.pi)⁻¹ * ‖∫ θ in 0..2 * Real.pi, f (equatorSpherePoint θ)‖
        ≤ (2 * Real.pi)⁻¹ * (‖f‖ * |2 * Real.pi - 0|) := by
          gcongr
    _ = ‖f‖ := by
          rw [sub_zero, abs_of_pos hpi]
          field_simp [hpi.ne']

theorem norm_spherePrecomp_le
    (e : sphereAmbient3 ≃ₗᵢ[ℝ] sphereAmbient3)
    (f : C(spherePoint3, ℝ)) :
    ‖spherePrecomp e f‖ ≤ ‖f‖ := by
  haveI : Nonempty spherePoint3 := ⟨sphereE1⟩
  refine (ContinuousMap.norm_le_of_nonempty (f := spherePrecomp e f) (M := ‖f‖)).2 ?_
  intro z
  exact f.norm_coe_le_norm (sphereMap e z)

theorem norm_greatCircleAverageLinear_le
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    ‖greatCircleAverageLinear x y z hxy hxz hyz f‖ ≤ ‖f‖ := by
  rw [greatCircleAverageLinear_apply]
  exact (norm_northEquatorAverageLinear_le _).trans
    (norm_spherePrecomp_le (sphereTripleIsometryEquiv x y z hxy hxz hyz) f)

theorem norm_poleAverageLinear_apply_le
    (f : C(spherePoint3, ℝ)) (z : spherePoint3) :
    ‖poleAverageLinear f z‖ ≤ ‖f‖ := by
  rw [poleAverageLinear_apply]
  exact
    norm_greatCircleAverageLinear_le
      (poleChoiceX z) (poleChoiceY z) z
      (poleChoice_spec z).1 (poleChoice_spec z).2.1 (poleChoice_spec z).2.2 f

theorem norm_poleAverageContinuousLinear_le (f : C(spherePoint3, ℝ)) :
    ‖poleAverageContinuousLinear f‖ ≤ ‖f‖ := by
  haveI : Nonempty spherePoint3 := ⟨sphereE1⟩
  refine (ContinuousMap.norm_le_of_nonempty (f := poleAverageContinuousLinear f) (M := ‖f‖)).2 ?_
  intro z
  exact norm_poleAverageLinear_apply_le f z

def poleAverageCLM : C(spherePoint3, ℝ) →L[ℝ] C(spherePoint3, ℝ) :=
  poleAverageContinuousLinear.mkContinuous 1 <| by
    intro f
    simpa using norm_poleAverageContinuousLinear_le f

@[simp] theorem poleAverageCLM_apply
    (f : C(spherePoint3, ℝ)) :
    poleAverageCLM f = poleAverageContinuousLinear f := by
  simp [poleAverageCLM, LinearMap.mkContinuous_apply]

namespace GleasonS2Bridge

open SphericalHarmonics

def s2PoleAverageContinuousLinear : C(S2, ℝ) →ₗ[ℝ] C(S2, ℝ) :=
  s2Pullback.symm.toLinearMap.comp
    (poleAverageContinuousLinear.comp s2Pullback.toLinearMap)

@[simp] theorem s2PoleAverageContinuousLinear_apply
    (f : C(S2, ℝ)) (z : S2) :
    s2PoleAverageContinuousLinear f z = s2PoleAverageLinear f z := by
  rfl

theorem s2Pullback_s2PoleAverageContinuousLinear_eq_poleAverageLinear
    (f : C(S2, ℝ)) :
    s2Pullback (s2PoleAverageContinuousLinear f) =
      poleAverageLinear (s2Pullback f) := by
  have hC :
      s2Pullback (s2PoleAverageContinuousLinear f) =
        poleAverageContinuousLinear (s2Pullback f) := by
    change
      s2Pullback (s2Pullback.symm (poleAverageContinuousLinear (s2Pullback f))) =
        poleAverageContinuousLinear (s2Pullback f)
    exact s2Pullback.apply_symm_apply (poleAverageContinuousLinear (s2Pullback f))
  exact congrArg (fun g : C(spherePoint3, ℝ) => (g : spherePoint3 → ℝ)) hC

theorem s2PoleAverageContinuousLinear_compContinuous
    (ρ : Rotation) (f : C(S2, ℝ)) :
    s2PoleAverageContinuousLinear (Rotation.compContinuous ρ f) =
      Rotation.compContinuous ρ (s2PoleAverageContinuousLinear f) := by
  ext z
  rw [s2PoleAverageContinuousLinear_apply, s2PoleAverageLinear_compContinuous_apply]
  rfl

end GleasonS2Bridge
