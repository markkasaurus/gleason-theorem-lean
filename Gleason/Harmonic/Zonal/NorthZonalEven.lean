import Gleason.Harmonic.Zonal.NorthZonalConstraint
import Gleason.Harmonic.GreatCircle.GreatCirclePointRotation

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

def negIcc (z : Set.Icc (-1 : ℝ) 1) : Set.Icc (-1 : ℝ) 1 :=
  ⟨-z.1, by
    constructor <;> nlinarith [z.2.1, z.2.2]⟩

@[simp] lemma negIcc_val (z : Set.Icc (-1 : ℝ) 1) :
    (negIcc z : ℝ) = -z.1 := by
  rfl

@[simp] lemma negIcc_zeroIcc :
    negIcc zeroIcc = zeroIcc := by
  ext
  simp [zeroIcc, negIcc]

def southFlipLinearEquiv :
    WithLp 2 (ℂ × ℝ) ≃ₗ[ℝ] WithLp 2 (ℂ × ℝ) :=
  (WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).trans
      (((LinearEquiv.refl ℝ ℂ).prodCongr (LinearEquiv.neg ℝ)))
    |>.trans (WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).symm

@[simp] lemma southFlipLinearEquiv_apply
    (x : WithLp 2 (ℂ × ℝ)) :
    southFlipLinearEquiv x = WithLp.toLp 2 (x.fst, -x.snd) := by
  simp [southFlipLinearEquiv]

def southFlip : WithLp 2 (ℂ × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℝ) :=
  ⟨southFlipLinearEquiv, by
    intro x
    rw [southFlipLinearEquiv_apply, WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
    simp⟩

@[simp] lemma southFlip_apply
    (x : WithLp 2 (ℂ × ℝ)) :
    southFlip x = WithLp.toLp 2 (x.fst, -x.snd) := by
  simp [southFlip]

@[simp] lemma southFlip_symm_apply
    (x : WithLp 2 (ℂ × ℝ)) :
    southFlip.symm x = southFlip x := by
  cases x
  apply southFlip.injective
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  simp [southFlip_apply]

@[simp] lemma southFlip_symm :
    southFlip.symm = southFlip := by
  ext x
  exact southFlip_symm_apply x

@[simp] lemma southFlip_trans_northRotation
    (t : ℝ) :
    southFlip.trans (northRotation t) =
      (northRotation t).trans southFlip := by
  ext x
  simp [southFlip_apply, northRotation_apply, mul_comm]

@[simp] lemma sphereMap_southFlip_northSection
    (z : Set.Icc (-1 : ℝ) 1) :
    sphereMap southFlip (northSection z) = northSection (negIcc z) := by
  apply Subtype.ext
  simp [sphereMap, southFlip_apply, northSection, negIcc]

lemma IsNorthZonal.spherePrecomp_southFlip
    {f : C(spherePoint3, ℝ)} (hf : IsNorthZonal f) :
    IsNorthZonal (spherePrecomp southFlip f) := by
  intro t
  calc
    spherePrecomp (northRotation t) (spherePrecomp southFlip f)
        = spherePrecomp ((northRotation t).trans southFlip) f := by
            rw [spherePrecomp_trans]
    _ = spherePrecomp (southFlip.trans (northRotation t)) f := by
          rw [southFlip_trans_northRotation]
    _ = spherePrecomp southFlip (spherePrecomp (northRotation t) f) := by
          rw [spherePrecomp_trans]
    _ = spherePrecomp southFlip f := by rw [hf t]

@[simp] lemma northZonalProfile_spherePrecomp_southFlip
    (f : C(spherePoint3, ℝ)) (z : Set.Icc (-1 : ℝ) 1) :
    northZonalProfile (spherePrecomp southFlip f) z =
      northZonalProfile f (negIcc z) := by
  simp [northZonalProfile, spherePrecomp_apply]

@[simp] lemma centeredNorthZonalProfile_spherePrecomp_southFlip
    (f : C(spherePoint3, ℝ)) (z : Set.Icc (-1 : ℝ) 1) :
    centeredNorthZonalProfile (spherePrecomp southFlip f) z =
      centeredNorthZonalProfile f (negIcc z) := by
  simp [centeredNorthZonalProfile, negIcc_zeroIcc]

theorem centeredNorthZonalProfile_special_equation_of_mem_pointConstraint_neg
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (r : Set.Icc (0 : ℝ) 1) :
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
      ∫ θ in 0..2 * Real.pi,
        centeredNorthZonalProfile f
          (negIcc ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)) =
      centeredNorthZonalProfile f (negIcc (nonnegIccToIcc r)) := by
  have hmem' :
      spherePrecomp southFlip f ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
    exact continuousSphereGreatCirclePointConstraintSubmodule_invariant_under_spherePrecomp
      southFlip hfmem
  have hfz' : IsNorthZonal (spherePrecomp southFlip f) :=
    hfz.spherePrecomp_southFlip
  simpa using
    centeredNorthZonalProfile_special_equation_of_mem_pointConstraint hmem' hfz' r

lemma centeredNorthZonalProfile_neg_integral_eq
    (f : C(spherePoint3, ℝ)) (r : Set.Icc (0 : ℝ) 1) :
    (∫ θ in 0..2 * Real.pi,
      centeredNorthZonalProfile f
        (negIcc ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)) =
      ∫ θ in 0..2 * Real.pi,
        centeredNorthZonalProfile f
          ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ := by
  let G : ℝ → ℝ :=
    fun θ =>
      centeredNorthZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩
  have hshift :
      (∫ θ in 0..2 * Real.pi, G (θ + Real.pi)) =
        ∫ u in Real.pi..2 * Real.pi + Real.pi, G u := by
    simpa [G] using
      (intervalIntegral.integral_comp_add_right (f := G) (a := 0) (b := 2 * Real.pi) Real.pi)
  have hperiodic : Function.Periodic G (2 * Real.pi) := by
    intro θ
    simp [G, Real.cos_add_two_pi]
  have hperiod :
      ∫ u in Real.pi..2 * Real.pi + Real.pi, G u =
        ∫ u in 0..2 * Real.pi, G u := by
    simpa [add_assoc, add_left_comm, add_comm] using hperiodic.intervalIntegral_add_eq Real.pi 0
  have hEq :
      (fun θ : ℝ =>
        centeredNorthZonalProfile f
          (negIcc ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)) =
      fun θ : ℝ => G (θ + Real.pi) := by
    funext θ
    change
      centeredNorthZonalProfile f (negIcc ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) =
        centeredNorthZonalProfile f ⟨r.1 * Real.cos (θ + Real.pi),
          mul_cos_mem_Icc r (θ + Real.pi)⟩
    congr 1
    ext
    simp [negIcc, Real.cos_add_pi]
  calc
    (∫ θ in 0..2 * Real.pi,
      centeredNorthZonalProfile f
        (negIcc ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩))
      = ∫ θ in 0..2 * Real.pi, G (θ + Real.pi) := by rw [hEq]
    _ = ∫ u in Real.pi..2 * Real.pi + Real.pi, G u := by rw [hshift]
    _ = ∫ u in 0..2 * Real.pi, G u := by rw [hperiod]
    _ = ∫ θ in 0..2 * Real.pi,
          centeredNorthZonalProfile f
            ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ := by rfl

theorem centeredNorthZonalProfile_even_of_mem_pointConstraint_nonneg
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (r : Set.Icc (0 : ℝ) 1) :
    centeredNorthZonalProfile f (negIcc (nonnegIccToIcc r)) =
      centeredNorthZonalProfile f (nonnegIccToIcc r) := by
  have hpos :=
    centeredNorthZonalProfile_special_equation_of_mem_pointConstraint hfmem hfz r
  have hneg :=
    centeredNorthZonalProfile_special_equation_of_mem_pointConstraint_neg hfmem hfz r
  rw [centeredNorthZonalProfile_neg_integral_eq f r] at hneg
  exact hneg.symm.trans hpos

theorem centeredNorthZonalProfile_even_of_mem_pointConstraint
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (z : Set.Icc (-1 : ℝ) 1) :
    centeredNorthZonalProfile f (negIcc z) =
      centeredNorthZonalProfile f z := by
  by_cases hz : 0 ≤ z.1
  · let r : Set.Icc (0 : ℝ) 1 := ⟨z.1, ⟨hz, z.2.2⟩⟩
    have hzEq : z = nonnegIccToIcc r := by
      ext
      simp [r, nonnegIccToIcc]
    rw [hzEq]
    exact centeredNorthZonalProfile_even_of_mem_pointConstraint_nonneg hfmem hfz r
  · have hnegz : 0 ≤ (-z.1 : ℝ) := by linarith
    let r : Set.Icc (0 : ℝ) 1 := ⟨-z.1, ⟨hnegz, by nlinarith [z.2.1, z.2.2]⟩⟩
    have hzEq : negIcc z = nonnegIccToIcc r := by
      ext
      simp [r, negIcc, nonnegIccToIcc]
    have hrEq : negIcc (nonnegIccToIcc r) = z := by
      ext
      simp [r, negIcc, nonnegIccToIcc]
    rw [hzEq, ← hrEq]
    exact (centeredNorthZonalProfile_even_of_mem_pointConstraint_nonneg hfmem hfz r).symm

theorem northZonalProfile_even_of_mem_pointConstraint
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (z : Set.Icc (-1 : ℝ) 1) :
    northZonalProfile f (negIcc z) = northZonalProfile f z := by
  have hcent :=
    centeredNorthZonalProfile_even_of_mem_pointConstraint hfmem hfz z
  simp [centeredNorthZonalProfile] at hcent ⊢
  linarith
