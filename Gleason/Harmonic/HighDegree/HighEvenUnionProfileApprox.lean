import Gleason.Harmonic.HighDegree.HighEvenUnionFixedApprox
import Gleason.Harmonic.Zonal.NorthZonalSquaredFactorBridge

noncomputable section

open Complex InnerProductSpace

abbrev unitIccLocal := Set.Icc (0 : ℝ) 1

def sqCenteredNorthZonalContinuousMap (f : C(spherePoint3, ℝ)) : C(unitIccLocal, ℝ) :=
  ⟨sqCenteredNorthZonalProfile f, continuous_sqCenteredNorthZonalProfile f⟩

lemma northSection_zeroIcc_eq_sphereE1 :
    northSection zeroIcc = sphereE1 := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  simp [northSection, zeroIcc, sphereE1]

theorem norm_sqCenteredNorthZonalContinuousMap_le_two_mul
    (f : C(spherePoint3, ℝ)) :
    ‖sqCenteredNorthZonalContinuousMap f‖ ≤ 2 * ‖f‖ := by
  haveI : Nonempty unitIccLocal := ⟨⟨0, by constructor <;> norm_num⟩⟩
  refine (ContinuousMap.norm_le_of_nonempty
    (f := sqCenteredNorthZonalContinuousMap f) (M := 2 * ‖f‖)).2 ?_
  intro u
  have hsq :
      sqCenteredNorthZonalContinuousMap f u =
        f (northSection
          ⟨Real.sqrt u.1, by
            constructor
            · nlinarith [Real.sqrt_nonneg u.1]
            · have hpow : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
              nlinarith [u.2.2, Real.sqrt_nonneg u.1, hpow]⟩) - f sphereE1 := by
    simp [sqCenteredNorthZonalContinuousMap, sqCenteredNorthZonalProfile,
      centeredNorthZonalProfile, northZonalProfile, northSection_zeroIcc_eq_sphereE1]
  rw [hsq]
  calc
    ‖f (northSection
        ⟨Real.sqrt u.1, by
          constructor
          · nlinarith [Real.sqrt_nonneg u.1]
          · have hpow : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
            nlinarith [u.2.2, Real.sqrt_nonneg u.1, hpow]⟩) - f sphereE1‖
      ≤ ‖f (northSection
          ⟨Real.sqrt u.1, by
            constructor
            · nlinarith [Real.sqrt_nonneg u.1]
            · have hpow : (Real.sqrt u.1) ^ 2 = u.1 := Real.sq_sqrt u.2.1
              nlinarith [u.2.2, Real.sqrt_nonneg u.1, hpow]⟩)‖ + ‖f sphereE1‖ := norm_sub_le _ _
    _ ≤ ‖f‖ + ‖f‖ := by
          gcongr
          · exact f.norm_coe_le_norm _
          · exact f.norm_coe_le_norm sphereE1
    _ = 2 * ‖f‖ := by ring

theorem norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul
    (f g : C(spherePoint3, ℝ)) :
    ‖sqCenteredNorthZonalContinuousMap f - sqCenteredNorthZonalContinuousMap g‖ ≤
      2 * ‖f - g‖ := by
  have hsub :
      sqCenteredNorthZonalContinuousMap f - sqCenteredNorthZonalContinuousMap g =
        sqCenteredNorthZonalContinuousMap (f - g) := by
    ext u
    simp [sqCenteredNorthZonalContinuousMap, sqCenteredNorthZonalProfile,
      centeredNorthZonalProfile, northZonalProfile, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc]
  rw [hsub]
  exact norm_sqCenteredNorthZonalContinuousMap_le_two_mul (f - g)

theorem exists_fixed_northZonal_profile_approx_of_nontrivial_tail
    (hne :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
        continuousSphereFrameSubmodule ≠ ⊥) :
    ∃ g : C(spherePoint3, ℝ),
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule ∧
      g ≠ 0 ∧
      IsNorthZonal g ∧
      northOrbitAverage g = g ∧
      ∀ {ε : ℝ}, 0 < ε →
        ∃ h : C(spherePoint3, ℝ),
          h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
          IsNorthZonal h ∧
          ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < ε := by
  rcases exists_fixed_northZonal_with_highEvenUnion_approx_of_nontrivial_tail hne with
    ⟨g, hg, hgne, hgz, hfix, happ⟩
  refine ⟨g, hg, hgne, hgz, hfix, ?_⟩
  intro ε hε
  rcases happ (show 0 < ε / 2 by positivity) with ⟨h, hh, hhz, hdist⟩
  refine ⟨h, hh, hhz, ?_⟩
  calc
    ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖
      ≤ 2 * ‖h - g‖ := norm_sqCenteredNorthZonalContinuousMap_sub_le_two_mul h g
    _ < 2 * (ε / 2) := by gcongr
    _ = ε := by ring
