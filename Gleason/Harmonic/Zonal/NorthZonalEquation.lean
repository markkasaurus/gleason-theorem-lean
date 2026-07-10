import Gleason.Harmonic.Zonal.NorthZonalFactor
import Gleason.Harmonic.Auxiliary.GlobalOscillationBridge
import Gleason.Harmonic.GreatCircle.GreatCirclePointStandard

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

def specialZPoint (r : Set.Icc (0 : ℝ) 1) : spherePoint3 :=
  northSection
    ⟨Real.sqrt (1 - r.1 ^ 2), by
      have hr2 : r.1 ^ 2 ≤ 1 := by
        nlinarith [r.2.1, r.2.2]
      have hnonneg : 0 ≤ 1 - r.1 ^ 2 := by
        nlinarith
      have hsqrt_sq : (Real.sqrt (1 - r.1 ^ 2)) ^ 2 = 1 - r.1 ^ 2 := by
        exact Real.sq_sqrt hnonneg
      constructor
      · linarith [Real.sqrt_nonneg (1 - r.1 ^ 2)]
      · have hsqrt_le1 : Real.sqrt (1 - r.1 ^ 2) ≤ 1 := by
          nlinarith [Real.sqrt_nonneg (1 - r.1 ^ 2), hsqrt_sq]
        simpa using hsqrt_le1⟩

def specialXPoint (r : Set.Icc (0 : ℝ) 1) : spherePoint3 :=
  sphereMap (northRotation Real.pi) (northSection ⟨r.1, by
    constructor
    · linarith [r.2.1]
    · exact r.2.2⟩)

@[simp] lemma spherePointCoord_specialZPoint (r : Set.Icc (0 : ℝ) 1) :
    spherePointCoord (specialZPoint r) =
      (r.1, (0, Real.sqrt (1 - r.1 ^ 2))) := by
  ext
  · have hnonneg : 0 ≤ 1 - r.1 ^ 2 := by
      nlinarith [r.2.1, r.2.2]
    have hsqrt : (Real.sqrt (1 - r.1 ^ 2)) ^ 2 = 1 - r.1 ^ 2 := by
      exact Real.sq_sqrt hnonneg
    have hroot : Real.sqrt (1 - (Real.sqrt (1 - r.1 ^ 2)) ^ 2) = r.1 := by
      rw [hsqrt]
      ring_nf
      exact Real.sqrt_sq r.2.1
    simpa [spherePointCoord, specialZPoint, northSection] using hroot
  · simp [spherePointCoord, specialZPoint, northSection]
  · simp [spherePointCoord, specialZPoint, northSection]

@[simp] lemma spherePointCoord_specialXPoint (r : Set.Icc (0 : ℝ) 1) :
    spherePointCoord (specialXPoint r) =
      (-Real.sqrt (1 - r.1 ^ 2), (0, r.1)) := by
  ext <;> simp [specialXPoint, northSection, sphereMap, northRotation_apply, spherePointCoord]

@[simp] lemma specialXPoint_inner_sphereE2 (r : Set.Icc (0 : ℝ) 1) :
    inner (𝕜 := ℝ) (specialXPoint r).1 sphereE2.1 = 0 := by
  have hcoord := coordDot_spherePointCoord (specialXPoint r) sphereE2
  rw [spherePointCoord_specialXPoint, spherePointCoord_sphereE2, coordDot, vCoord] at hcoord
  simpa using hcoord.symm

@[simp] lemma specialZPoint_inner_sphereE2 (r : Set.Icc (0 : ℝ) 1) :
    inner (𝕜 := ℝ) (specialZPoint r).1 sphereE2.1 = 0 := by
  have hcoord := coordDot_spherePointCoord (specialZPoint r) sphereE2
  rw [spherePointCoord_specialZPoint, spherePointCoord_sphereE2, coordDot, vCoord] at hcoord
  simpa using hcoord.symm

@[simp] lemma sphereE2_inner_specialZPoint (r : Set.Icc (0 : ℝ) 1) :
    inner (𝕜 := ℝ) sphereE2.1 (specialZPoint r).1 = 0 := by
  simpa [real_inner_comm, mul_comm] using specialZPoint_inner_sphereE2 r

@[simp] lemma specialXPoint_inner_specialZPoint (r : Set.Icc (0 : ℝ) 1) :
    inner (𝕜 := ℝ) (specialXPoint r).1 (specialZPoint r).1 = 0 := by
  have hcoord := coordDot_spherePointCoord (specialXPoint r) (specialZPoint r)
  rw [spherePointCoord_specialXPoint, spherePointCoord_specialZPoint, coordDot] at hcoord
  have hsqrt : (Real.sqrt (1 - r.1 ^ 2)) ^ 2 = 1 - r.1 ^ 2 := by
    apply Real.sq_sqrt
    nlinarith [r.2.1, r.2.2]
  nlinarith

@[simp] lemma sphereCoordZ_specialXPoint (r : Set.Icc (0 : ℝ) 1) :
    sphereCoordZ (specialXPoint r) = r.1 := by
  simp [sphereCoordZ, specialXPoint]

@[simp] lemma sphereCoordZ_specialZPoint (r : Set.Icc (0 : ℝ) 1) :
    sphereCoordZ (specialZPoint r) = Real.sqrt (1 - r.1 ^ 2) := by
  simp [sphereCoordZ, specialZPoint]

lemma equatorSpherePoint_val_eq_combo (θ : ℝ) :
    (equatorSpherePoint θ).1 =
      Real.cos θ • sphereE1.1 + Real.sin θ • sphereE2.1 := by
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  simp [equatorSpherePoint, sphereE1, sphereE2]
  ring

lemma mul_cos_mem_Icc (r : Set.Icc (0 : ℝ) 1) (θ : ℝ) :
    r.1 * Real.cos θ ∈ Set.Icc (-1 : ℝ) 1 := by
  refine ⟨?_, ?_⟩ <;> nlinarith [r.2.1, r.2.2, Real.neg_one_le_cos θ, Real.cos_le_one θ]

lemma sphereCoordZ_specialTriple_equator
    (r : Set.Icc (0 : ℝ) 1) (θ : ℝ) :
    sphereCoordZ
      (sphereMap
        (sphereTripleIsometryEquiv
        (specialXPoint r) sphereE2 (specialZPoint r)
        (specialXPoint_inner_sphereE2 r)
        (specialXPoint_inner_specialZPoint r)
        (sphereE2_inner_specialZPoint r))
        (equatorSpherePoint θ)) =
      r.1 * Real.cos θ := by
  have hmap :
      (sphereMap
        (sphereTripleIsometryEquiv
        (specialXPoint r) sphereE2 (specialZPoint r)
        (specialXPoint_inner_sphereE2 r)
        (specialXPoint_inner_specialZPoint r)
        (sphereE2_inner_specialZPoint r))
        (equatorSpherePoint θ)).1 =
      Real.cos θ • (specialXPoint r).1 + Real.sin θ • sphereE2.1 := by
    change
      sphereTripleIsometryEquiv
        (specialXPoint r) sphereE2 (specialZPoint r)
        (specialXPoint_inner_sphereE2 r)
        (specialXPoint_inner_specialZPoint r)
        (sphereE2_inner_specialZPoint r)
        ((equatorSpherePoint θ).1)
      =
      Real.cos θ • (specialXPoint r).1 + Real.sin θ • sphereE2.1
    rw [equatorSpherePoint_val_eq_combo]
    simp [map_add]
  have hsnd := congrArg (fun w : WithLp 2 (ℂ × ℝ) => w.snd) hmap
  simpa [sphereCoordZ, sphereCoordZ_specialXPoint, sphereE2, specialXPoint, mul_comm] using hsnd

lemma northZonal_specialTriple_equator_eval
    {f : C(spherePoint3, ℝ)} (hf : IsNorthZonal f)
    (r : Set.Icc (0 : ℝ) 1) (θ : ℝ) :
    (spherePrecomp
      (sphereTripleIsometryEquiv
        (specialXPoint r) sphereE2 (specialZPoint r)
        (specialXPoint_inner_sphereE2 r)
        (specialXPoint_inner_specialZPoint r)
        (sphereE2_inner_specialZPoint r))
      f) (equatorSpherePoint θ) =
      northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ := by
  let p :=
    sphereMap
      (sphereTripleIsometryEquiv
        (specialXPoint r) sphereE2 (specialZPoint r)
        (specialXPoint_inner_sphereE2 r)
        (specialXPoint_inner_specialZPoint r)
        (sphereE2_inner_specialZPoint r))
      (equatorSpherePoint θ)
  have hprof := northZonalProfile_eq_of_isNorthZonal hf
    p
  have hsub :
      (⟨p.1.snd, snd_mem_Icc p⟩ : Set.Icc (-1 : ℝ) 1) =
        ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ := by
    apply Subtype.ext
    simpa [sphereCoordZ, p] using sphereCoordZ_specialTriple_equator r θ
  calc
    (spherePrecomp
      (sphereTripleIsometryEquiv
        (specialXPoint r) sphereE2 (specialZPoint r)
        (specialXPoint_inner_sphereE2 r)
        (specialXPoint_inner_specialZPoint r)
        (sphereE2_inner_specialZPoint r))
      f) (equatorSpherePoint θ)
        = f p := by
            simp [p, spherePrecomp_apply]
    _ = northZonalProfile f ⟨p.1.snd, snd_mem_Icc p⟩ := by
          simpa using hprof.symm
    _ = northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ := by
          rw [hsub]

lemma greatCircleAverageLinear_special_of_isNorthZonal
    {f : C(spherePoint3, ℝ)} (hf : IsNorthZonal f)
    (r : Set.Icc (0 : ℝ) 1) :
    greatCircleAverageLinear
      (specialXPoint r) sphereE2 (specialZPoint r)
      (specialXPoint_inner_sphereE2 r)
      (specialXPoint_inner_specialZPoint r)
      (sphereE2_inner_specialZPoint r)
      f =
      ((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ := by
  rw [greatCircleAverageLinear_apply, northEquatorAverageLinear_apply]
  have hfun :
      (fun θ : ℝ =>
        ((spherePrecomp
          (sphereTripleIsometryEquiv
            (specialXPoint r) sphereE2 (specialZPoint r)
            (specialXPoint_inner_sphereE2 r)
            (specialXPoint_inner_specialZPoint r)
            (sphereE2_inner_specialZPoint r))
          f) (equatorSpherePoint θ))) =
      (fun θ : ℝ => northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) := by
    funext θ
    exact northZonal_specialTriple_equator_eval hf r θ
  rw [hfun]
