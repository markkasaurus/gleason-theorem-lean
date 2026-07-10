import Gleason.Harmonic.Zonal.NorthZonalEquation

noncomputable section

open Complex InnerProductSpace MeasureTheory intervalIntegral

def zeroIcc : Set.Icc (-1 : ℝ) 1 := ⟨0, by constructor <;> norm_num⟩

def nonnegIccToIcc (r : Set.Icc (0 : ℝ) 1) : Set.Icc (-1 : ℝ) 1 :=
  ⟨r.1, by
    constructor
    · nlinarith [r.2.1]
    · exact r.2.2⟩

@[simp] lemma nonnegIccToIcc_val (r : Set.Icc (0 : ℝ) 1) :
    (nonnegIccToIcc r : ℝ) = r.1 := by
  rfl

@[simp] lemma northZonalProfile_zero_of_isNorthZonal
    {f : C(spherePoint3, ℝ)} (hf : IsNorthZonal f) :
    northZonalProfile f zeroIcc = f sphereE2 := by
  have hprof := northZonalProfile_eq_of_isNorthZonal hf sphereE2
  simpa [zeroIcc, sphereCoordZ, sphereE2] using hprof

@[simp] lemma northZonalProfile_nonneg_of_isNorthZonal
    {f : C(spherePoint3, ℝ)} (hf : IsNorthZonal f)
    (r : Set.Icc (0 : ℝ) 1) :
    northZonalProfile f (nonnegIccToIcc r) = f (specialXPoint r) := by
  have hprof := northZonalProfile_eq_of_isNorthZonal hf (specialXPoint r)
  simpa [nonnegIccToIcc, sphereCoordZ_specialXPoint] using hprof

theorem northZonalProfile_special_equation_of_mem_pointConstraint
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (r : Set.Icc (0 : ℝ) 1) :
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
      ∫ θ in 0..2 * Real.pi, northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) =
      northZonalProfile f (nonnegIccToIcc r) + northZonalProfile f zeroIcc := by
  have hpt :=
    (mem_continuousSphereGreatCirclePointConstraintSubmodule_iff f).1 hfmem
      (specialXPoint r) sphereE2 (specialZPoint r)
      (specialXPoint_inner_sphereE2 r)
      (specialXPoint_inner_specialZPoint r)
      (sphereE2_inner_specialZPoint r)
  rw [greatCircleAverageLinear_special_of_isNorthZonal hfz r] at hpt
  rw [← northZonalProfile_nonneg_of_isNorthZonal hfz r,
    ← northZonalProfile_zero_of_isNorthZonal hfz] at hpt
  exact hpt

def centeredNorthZonalProfile (f : C(spherePoint3, ℝ)) :
    Set.Icc (-1 : ℝ) 1 → ℝ :=
  fun z => northZonalProfile f z - northZonalProfile f zeroIcc

@[simp] lemma centeredNorthZonalProfile_apply
    (f : C(spherePoint3, ℝ)) (z : Set.Icc (-1 : ℝ) 1) :
    centeredNorthZonalProfile f z =
      northZonalProfile f z - northZonalProfile f zeroIcc := by
  rfl

@[simp] lemma centeredNorthZonalProfile_zero
    (f : C(spherePoint3, ℝ)) :
    centeredNorthZonalProfile f zeroIcc = 0 := by
  simp [centeredNorthZonalProfile]

theorem centeredNorthZonalProfile_special_equation_of_mem_pointConstraint
    {f : C(spherePoint3, ℝ)}
    (hfmem : f ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hfz : IsNorthZonal f)
    (r : Set.Icc (0 : ℝ) 1) :
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
      ∫ θ in 0..2 * Real.pi, centeredNorthZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) =
      centeredNorthZonalProfile f (nonnegIccToIcc r) := by
  have hbase :=
    northZonalProfile_special_equation_of_mem_pointConstraint hfmem hfz r
  have hconst :
      (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, northZonalProfile f zeroIcc) =
        northZonalProfile f zeroIcc := by
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hconstInt :
        (∫ θ in 0..2 * Real.pi, northZonalProfile f zeroIcc) =
          (2 * Real.pi) * northZonalProfile f zeroIcc := by
      simp
    rw [hconstInt]
    field_simp [hpi]
  have havg_centered :
      (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, centeredNorthZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) =
      (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
        northZonalProfile f zeroIcc := by
    have hfun :
        (fun θ : ℝ => centeredNorthZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) =
        (fun θ : ℝ =>
          northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩ -
            northZonalProfile f zeroIcc) := by
      funext θ
      simp [centeredNorthZonalProfile]
    have hInt1 :
        IntervalIntegrable
          (fun θ : ℝ => northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
          volume 0 (2 * Real.pi) := by
      have heq :
          (fun θ : ℝ => northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) =
          (fun θ : ℝ =>
            (spherePrecomp
              (sphereTripleIsometryEquiv
                (specialXPoint r) sphereE2 (specialZPoint r)
                (specialXPoint_inner_sphereE2 r)
                (specialXPoint_inner_specialZPoint r)
                (sphereE2_inner_specialZPoint r))
              f) (equatorSpherePoint θ)) := by
        funext θ
        exact (northZonal_specialTriple_equator_eval hfz r θ).symm
      have hcont :
          Continuous
            (fun θ : ℝ => northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) := by
        have hbasecont :
            Continuous
              (fun θ : ℝ =>
                (spherePrecomp
                  (sphereTripleIsometryEquiv
                    (specialXPoint r) sphereE2 (specialZPoint r)
                    (specialXPoint_inner_sphereE2 r)
                    (specialXPoint_inner_specialZPoint r)
                    (sphereE2_inner_specialZPoint r))
                  f) (equatorSpherePoint θ)) := by
          exact
            (ContinuousMap.continuous _
              : Continuous
                  ((spherePrecomp
                    (sphereTripleIsometryEquiv
                      (specialXPoint r) sphereE2 (specialZPoint r)
                      (specialXPoint_inner_sphereE2 r)
                      (specialXPoint_inner_specialZPoint r)
                    (sphereE2_inner_specialZPoint r))
                    f) : spherePoint3 → ℝ)).comp continuous_equatorSpherePoint
        rw [heq]
        exact hbasecont
      exact hcont.intervalIntegrable _ _
    have hInt2 :
        IntervalIntegrable (fun θ : ℝ => northZonalProfile f zeroIcc)
          volume 0 (2 * Real.pi) := by
      simpa using (continuous_const : Continuous fun _ : ℝ => northZonalProfile f zeroIcc).intervalIntegrable
        0 (2 * Real.pi)
    rw [hfun, intervalIntegral.integral_sub hInt1 hInt2]
    calc
      ((2 * Real.pi)⁻¹ : ℝ) *
          ((∫ θ in 0..2 * Real.pi, northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
            ∫ θ in 0..2 * Real.pi, northZonalProfile f zeroIcc)
        =
          (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi, northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
          (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi, northZonalProfile f zeroIcc) := by
              ring
      _ = (((2 * Real.pi)⁻¹ : ℝ) *
            ∫ θ in 0..2 * Real.pi, northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩) -
            northZonalProfile f zeroIcc := by
              rw [hconst]
  calc
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
        ∫ θ in 0..2 * Real.pi, centeredNorthZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
      = 2 * ((((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi, northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)
          - northZonalProfile f zeroIcc) := by
            rw [havg_centered]
    _ = (2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi, northZonalProfile f ⟨r.1 * Real.cos θ, mul_cos_mem_Icc r θ⟩)) -
          2 * northZonalProfile f zeroIcc := by ring
    _ = (northZonalProfile f (nonnegIccToIcc r) + northZonalProfile f zeroIcc) -
          2 * northZonalProfile f zeroIcc := by rw [hbase]
    _ = centeredNorthZonalProfile f (nonnegIccToIcc r) := by
          simp [centeredNorthZonalProfile]
          ring
