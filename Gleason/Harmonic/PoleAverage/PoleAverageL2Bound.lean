import Gleason.Harmonic.PoleAverage.PoleAverageL2Lift
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.IntervalAverage

noncomputable section

open scoped ENNReal MeasureTheory Interval
open MeasureTheory

namespace GleasonS2Bridge

open SphericalHarmonics

theorem sq_intervalAverage_le_intervalAverage_sq
    {h : ℝ → ℝ}
    (hh : Continuous h) :
    (⨍ θ in (0 : ℝ)..2 * Real.pi, h θ) ^ 2 ≤
      ⨍ θ in (0 : ℝ)..2 * Real.pi, (h θ) ^ 2 := by
  have hconv : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ 2) :=
    (even_two).convexOn_pow
  have hcont : ContinuousOn (fun x : ℝ => x ^ 2) (Set.univ : Set ℝ) :=
    continuous_pow 2 |>.continuousOn
  have hclosed : IsClosed (Set.univ : Set ℝ) := isClosed_univ
  have hmem : ∀ᵐ θ ∂(volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))),
      h θ ∈ (Set.univ : Set ℝ) :=
    Filter.Eventually.of_forall fun _ => Set.mem_univ _
  have hint : IntegrableOn h (Set.uIoc (0 : ℝ) (2 * Real.pi)) volume :=
    hh.integrableOn_uIoc
  have hint_sq : IntegrableOn (fun θ => (h θ) ^ 2)
      (Set.uIoc (0 : ℝ) (2 * Real.pi)) volume :=
    (hh.pow 2).integrableOn_uIoc
  simpa using
    hconv.map_set_average_le
      (μ := volume)
      (t := Set.uIoc (0 : ℝ) (2 * Real.pi))
      hcont hclosed
      (by
        rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Real.volume_Ioc]
        simp [Real.pi_pos])
      (by
        rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top)
      hmem hint hint_sq

theorem greatCircleAverageLinear_eq_paramIntervalAverage
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    greatCircleAverageLinear x y z hxy hxz hyz f =
      ⨍ θ in (0 : ℝ)..2 * Real.pi, f (greatCircleParamPoint x y hxy θ) := by
  rw [greatCircleAverageLinear_eq_paramIntegral]
  rw [interval_average_eq]
  simp [smul_eq_mul]

theorem continuous_greatCircleParamPoint_const
    (x y : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0) :
    Continuous fun θ : ℝ => greatCircleParamPoint x y hxy θ := by
  refine Continuous.subtype_mk ?_ (fun θ => (greatCircleParamPoint x y hxy θ).2)
  have hcos : Continuous fun θ : ℝ => Real.cos θ := Real.continuous_cos
  have hsin : Continuous fun θ : ℝ => Real.sin θ := Real.continuous_sin
  simpa [greatCircleParamPoint] using
    (hcos.smul (continuous_const : Continuous fun _ : ℝ => x.1)).add
      (hsin.smul (continuous_const : Continuous fun _ : ℝ => y.1))

theorem greatCircleAverageLinear_sq_le
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0)
    (f : C(spherePoint3, ℝ)) :
    (greatCircleAverageLinear x y z hxy hxz hyz f) ^ 2 ≤
      greatCircleAverageLinear x y z hxy hxz hyz (f * f) := by
  have hcont :
      Continuous fun θ : ℝ => f (greatCircleParamPoint x y hxy θ) :=
    f.continuous.comp (continuous_greatCircleParamPoint_const x y hxy)
  have hJ := sq_intervalAverage_le_intervalAverage_sq hcont
  rw [greatCircleAverageLinear_eq_paramIntervalAverage x y z hxy hxz hyz f]
  rw [greatCircleAverageLinear_eq_paramIntervalAverage x y z hxy hxz hyz (f * f)]
  simpa [pow_two] using hJ

theorem poleAverageLinear_sq_le
    (f : C(spherePoint3, ℝ)) (z : spherePoint3) :
    (poleAverageLinear f z) ^ 2 ≤ poleAverageLinear (f * f) z := by
  rw [poleAverageLinear_apply, poleAverageLinear_apply]
  exact
    greatCircleAverageLinear_sq_le
      (poleChoiceX z) (poleChoiceY z) z
      (poleChoice_spec z).1 (poleChoice_spec z).2.1 (poleChoice_spec z).2.2 f

theorem norm_s2Pullback_le (f : C(S2, ℝ)) :
    ‖s2Pullback f‖ ≤ ‖f‖ := by
  haveI : Nonempty spherePoint3 := ⟨sphereE1⟩
  refine (ContinuousMap.norm_le_of_nonempty (f := s2Pullback f) (M := ‖f‖)).2 ?_
  intro x
  exact ContinuousMap.norm_coe_le_norm f (spherePoint3ToS2 x)

theorem norm_s2PoleAverageContinuousLinear_le (f : C(S2, ℝ)) :
    ‖s2PoleAverageContinuousLinear f‖ ≤ ‖f‖ := by
  haveI : Nonempty S2 := ⟨northPole⟩
  refine
    (ContinuousMap.norm_le_of_nonempty
      (f := s2PoleAverageContinuousLinear f) (M := ‖f‖)).2 ?_
  intro z
  calc
    ‖s2PoleAverageContinuousLinear f z‖
        = ‖poleAverageLinear (s2Pullback f) (s2ToSpherePoint3 z)‖ := by
            rfl
    _ ≤ ‖s2Pullback f‖ :=
        norm_poleAverageLinear_apply_le (s2Pullback f) (s2ToSpherePoint3 z)
    _ ≤ ‖f‖ := norm_s2Pullback_le f

def s2PoleAverageCLM : C(S2, ℝ) →L[ℝ] C(S2, ℝ) :=
  s2PoleAverageContinuousLinear.mkContinuous 1 <| by
    intro f
    simpa using norm_s2PoleAverageContinuousLinear_le f

@[simp] theorem s2PoleAverageCLM_apply (f : C(S2, ℝ)) :
    s2PoleAverageCLM f = s2PoleAverageContinuousLinear f := by
  simp [s2PoleAverageCLM, LinearMap.mkContinuous_apply]

def s2IntegralCLM : C(S2, ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (continuousToLp (1 : C(S2, ℝ)))).comp continuousToLp

@[simp] theorem s2IntegralCLM_apply (f : C(S2, ℝ)) :
    s2IntegralCLM f = ∫ x, f x ∂rotationMeasure := by
  rw [s2IntegralCLM]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [innerSL_apply_apply]
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (1 : C(S2, ℝ)) f]
  simp

theorem s2IntegralCLM_compContinuous (ρ : Rotation) (f : C(S2, ℝ)) :
    s2IntegralCLM (Rotation.compContinuous ρ f) = s2IntegralCLM f := by
  simp only [s2IntegralCLM_apply]
  let e : S2 ≃ᵐ S2 :=
    (Rotation.toSphereEquiv ρ.symm).toHomeomorph.toMeasurableEquiv
  have hpres : MeasurePreserving e rotationMeasure rotationMeasure :=
    ⟨e.measurable, by simp [e, Rotation.map_rotationMeasure ρ.symm]⟩
  calc
    ∫ x, Rotation.compContinuous ρ f x ∂rotationMeasure
        = ∫ x, f (e x) ∂rotationMeasure := by rfl
    _ = ∫ y, f y ∂rotationMeasure := hpres.integral_comp' f

theorem s2IntegralCLM_s2PoleAverageCLM_compContinuous
    (ρ : Rotation) (f : C(S2, ℝ)) :
    (ContinuousLinearMap.comp
        (R₁ := ℝ) (R₂ := ℝ) (R₃ := ℝ)
        (σ₁₂ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ) (σ₁₃ := RingHom.id ℝ)
        s2IntegralCLM s2PoleAverageCLM) (Rotation.compContinuous ρ f) =
      (ContinuousLinearMap.comp
        (R₁ := ℝ) (R₂ := ℝ) (R₃ := ℝ)
        (σ₁₂ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ) (σ₁₃ := RingHom.id ℝ)
        s2IntegralCLM s2PoleAverageCLM) f := by
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [s2PoleAverageCLM_apply, s2PoleAverageCLM_apply]
  rw [s2PoleAverageContinuousLinear_compContinuous]
  exact s2IntegralCLM_compContinuous ρ (s2PoleAverageContinuousLinear f)

def s2PoleAverageIntegralCLM : C(S2, ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.comp
    (R₁ := ℝ) (R₂ := ℝ) (R₃ := ℝ)
    (σ₁₂ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ) (σ₁₃ := RingHom.id ℝ)
    s2IntegralCLM s2PoleAverageCLM

theorem s2PoleAverageIntegralCLM_compContinuous
    (ρ : Rotation) (f : C(S2, ℝ)) :
    s2PoleAverageIntegralCLM (Rotation.compContinuous ρ f) =
      s2PoleAverageIntegralCLM f := by
  exact s2IntegralCLM_s2PoleAverageCLM_compContinuous ρ f

theorem integral_eq_zero_of_mem_sector_ne_zero
    {n : ℕ} (hn0 : n ≠ 0) {f : C(S2, ℝ)} (hf : f ∈ sector n) :
    ∫ x, f x ∂rotationMeasure = 0 := by
  have hone : (1 : C(S2, ℝ)) ∈ sector 0 := by
    have hz0 : zonal0 = (1 : C(S2, ℝ)) := by
      ext x
      simp [zonal0, zonalFromPolynomial]
    rw [← hz0]
    exact zonal0_mem_sector
  have horth := sectorL2_isOrtho_of_ne (n := 0) (m := n) (Ne.symm hn0)
  rw [Submodule.isOrtho_iff_inner_eq] at horth
  have hinner :
      inner ℝ (continuousToLp (1 : C(S2, ℝ))) (continuousToLp f) = 0 := by
    exact
      horth
        (continuousToLp (1 : C(S2, ℝ))) (continuousToLp_mem_sectorL2 hone)
        (continuousToLp f) (continuousToLp_mem_sectorL2 hf)
  rw [MeasureTheory.ContinuousMap.inner_toLp rotationMeasure (1 : C(S2, ℝ)) f] at hinner
  simpa using hinner

theorem invariant_continuousLinearMap_eq_zero_of_mem_sector_ne_zero
    (ℓ : C(S2, ℝ) →L[ℝ] ℝ)
    (hℓrot : ∀ (ρ : Rotation) (f : C(S2, ℝ)),
      ℓ (Rotation.compContinuous ρ f) = ℓ f)
    {n : ℕ} (hn0 : n ≠ 0) {f : C(S2, ℝ)} (hf : f ∈ sector n) :
    ℓ f = 0 := by
  let e : sector n ≃ₗ[ℝ] sectorL2 n :=
    LinearEquiv.ofBijective (sectorToSectorL2 n)
      ⟨by
        intro f g hfg
        apply Subtype.ext
        exact ContinuousMap.toLp_injective rotationMeasure <| by
          simpa [sectorToSectorL2] using congrArg Subtype.val hfg,
        sectorToSectorL2_surjective n⟩
  have hone_mem : (1 : C(S2, ℝ)) ∈ sector 0 := by
    have hz0 : zonal0 = (1 : C(S2, ℝ)) := by
      ext x
      simp [zonal0, zonalFromPolynomial]
    rw [← hz0]
    exact zonal0_mem_sector
  let one0 : sectorL2 0 :=
    ⟨continuousToLp (1 : C(S2, ℝ)), continuousToLp_mem_sectorL2 hone_mem⟩
  have hone0 : one0 ≠ 0 := by
    intro hzero
    have hfun : (1 : C(S2, ℝ)) = 0 := by
      exact ContinuousMap.toLp_injective rotationMeasure (by
        simpa [one0] using congrArg Subtype.val hzero)
    have hval := congrArg (fun g : C(S2, ℝ) => g northPole) hfun
    norm_num at hval
  have hone0_fixed : ∀ ρ : Rotation, sectorCompL2Rotation ρ 0 one0 = one0 := by
    intro ρ
    apply Subtype.ext
    change Rotation.compL2Rotation ρ (continuousToLp (1 : C(S2, ℝ))) =
      continuousToLp (1 : C(S2, ℝ))
    rw [continuousToLp_compContinuous_symm]
    rfl
  let Bₗ : sectorL2 n →ₗ[ℝ] sectorL2 0 :=
    { toFun := fun u => ℓ ((e.symm u : sector n).1) • one0
      map_add' := by
        intro u v
        simp [map_add, add_smul]
      map_smul' := by
        intro a u
        simp [smul_smul] }
  let B : sectorL2 n →L[ℝ] sectorL2 0 := LinearMap.toContinuousLinearMap Bₗ
  have hBrot : SectorHom.IsRotationEquivariant B := by
    intro ρ u
    have hpre :
        e.symm (sectorCompL2Rotation ρ n u) =
          ⟨Rotation.compContinuous ρ.symm (e.symm u : sector n).1,
            compContinuous_mem_sector ρ.symm n (e.symm u : sector n).2⟩ := by
      apply e.injective
      simp [e]
    apply Subtype.ext
    simp [B, Bₗ, hpre, hℓrot, hone0_fixed]
  have hBzero : B = 0 := by
    apply SectorHom.eq_zero_of_finrank_ne B hBrot
    rw [finrank_sectorL2, finrank_sectorL2]
    omega
  have hBu : B (sectorToSectorL2 n ⟨f, hf⟩) = 0 := by
    rw [hBzero]
    simp
  have hsmul : ℓ f • one0 = 0 := by
    simpa [B, Bₗ, e] using hBu
  rcases smul_eq_zero.mp hsmul with hzero | hzero
  · exact hzero
  · exact False.elim (hone0 hzero)

theorem exists_smul_one_of_mem_sector_zero
    {f : C(S2, ℝ)} (hf : f ∈ sector 0) :
    ∃ c : ℝ, c • (1 : C(S2, ℝ)) = f := by
  have hone_mem : (1 : C(S2, ℝ)) ∈ sector 0 := by
    have hz0 : zonal0 = (1 : C(S2, ℝ)) := by
      ext x
      simp [zonal0, zonalFromPolynomial]
    rw [← hz0]
    exact zonal0_mem_sector
  let one0 : sector 0 := ⟨(1 : C(S2, ℝ)), hone_mem⟩
  have hone0 : one0 ≠ 0 := by
    intro hzero
    have hfun : (1 : C(S2, ℝ)) = 0 := congrArg Subtype.val hzero
    have hval := congrArg (fun g : C(S2, ℝ) => g northPole) hfun
    norm_num at hval
  have hfin : Module.finrank ℝ (sector 0) = 1 := by
    simpa using finrank_sector 0
  rcases exists_smul_eq_of_finrank_eq_one hfin hone0 ⟨f, hf⟩ with ⟨c, hc⟩
  exact ⟨c, congrArg Subtype.val hc⟩

theorem continuousPolynomialSpan_le_iSup_sector :
    continuousPolynomialSpan ≤ ⨆ n : ℕ, sector n := by
  rw [continuousPolynomialSpan]
  exact Submodule.span_le.mpr <| by
    intro f hf
    rcases hf with ⟨p, rfl⟩
    exact restrict_mem_iSup_sector p

theorem invariant_continuousLinearMap_eq_zero_of_one_eq_zero_of_mem_iSup_sector
    (ℓ : C(S2, ℝ) →L[ℝ] ℝ)
    (hℓrot : ∀ (ρ : Rotation) (f : C(S2, ℝ)),
      ℓ (Rotation.compContinuous ρ f) = ℓ f)
    (hone : ℓ (1 : C(S2, ℝ)) = 0)
    {f : C(S2, ℝ)} (hf : f ∈ ⨆ n : ℕ, sector n) :
    ℓ f = 0 := by
  refine Submodule.iSup_induction (p := sector) (motive := fun g => ℓ g = 0) hf ?mem ?zero ?add
  · intro n g hg
    by_cases hn : n = 0
    · subst n
      rcases exists_smul_one_of_mem_sector_zero hg with ⟨c, rfl⟩
      rw [map_smul, hone, smul_zero]
    · exact invariant_continuousLinearMap_eq_zero_of_mem_sector_ne_zero ℓ hℓrot hn hg
  · exact map_zero ℓ
  · intro f g hf hg
    rw [map_add, hf, hg, add_zero]

theorem invariant_continuousLinearMap_eq_zero_of_one_eq_zero
    (ℓ : C(S2, ℝ) →L[ℝ] ℝ)
    (hℓrot : ∀ (ρ : Rotation) (f : C(S2, ℝ)),
      ℓ (Rotation.compContinuous ρ f) = ℓ f)
    (hone : ℓ (1 : C(S2, ℝ)) = 0)
    (f : C(S2, ℝ)) :
    ℓ f = 0 := by
  have hspan_le : continuousPolynomialSpan ≤ LinearMap.ker ℓ.toLinearMap := by
    intro g hg
    rw [LinearMap.mem_ker]
    exact invariant_continuousLinearMap_eq_zero_of_one_eq_zero_of_mem_iSup_sector
      ℓ hℓrot hone (continuousPolynomialSpan_le_iSup_sector hg)
  have hclosure_le :
      continuousPolynomialSpan.topologicalClosure ≤ LinearMap.ker ℓ.toLinearMap :=
    Submodule.topologicalClosure_minimal continuousPolynomialSpan hspan_le
      (ContinuousLinearMap.isClosed_ker ℓ)
  have htop_le : (⊤ : Submodule ℝ C(S2, ℝ)) ≤ LinearMap.ker ℓ.toLinearMap := by
    simpa [continuousPolynomialSpan_topologicalClosure_eq_top] using hclosure_le
  have hfker : f ∈ LinearMap.ker ℓ.toLinearMap := htop_le trivial
  simpa [LinearMap.mem_ker] using hfker

theorem s2PoleAverageIntegral_eq_integral (f : C(S2, ℝ)) :
    ∫ x, s2PoleAverageContinuousLinear f x ∂rotationMeasure =
      ∫ x, f x ∂rotationMeasure := by
  let D : C(S2, ℝ) →L[ℝ] ℝ := s2PoleAverageIntegralCLM - s2IntegralCLM
  have hDrot : ∀ (ρ : Rotation) (g : C(S2, ℝ)),
      D (Rotation.compContinuous ρ g) = D g := by
    intro ρ g
    change
      s2PoleAverageIntegralCLM (Rotation.compContinuous ρ g) -
          s2IntegralCLM (Rotation.compContinuous ρ g) =
        s2PoleAverageIntegralCLM g - s2IntegralCLM g
    rw [s2PoleAverageIntegralCLM_compContinuous, s2IntegralCLM_compContinuous]
  have hone : D (1 : C(S2, ℝ)) = 0 := by
    change s2PoleAverageIntegralCLM (1 : C(S2, ℝ)) - s2IntegralCLM (1 : C(S2, ℝ)) = 0
    rw [sub_eq_zero]
    have hconst : s2PoleAverageCLM (1 : C(S2, ℝ)) = 1 := by
      rw [s2PoleAverageCLM_apply]
      ext x
      simpa using congrFun (s2PoleAverageLinear_const 1) x
    change s2IntegralCLM (s2PoleAverageCLM (1 : C(S2, ℝ))) =
      s2IntegralCLM (1 : C(S2, ℝ))
    rw [hconst]
  have hDzero := invariant_continuousLinearMap_eq_zero_of_one_eq_zero D hDrot hone f
  have hEq : s2PoleAverageIntegralCLM f = s2IntegralCLM f := sub_eq_zero.mp hDzero
  simpa [s2PoleAverageIntegralCLM, s2PoleAverageCLM_apply] using hEq

theorem s2PoleAverageContinuousLinear_sq_le
    (f : C(S2, ℝ)) (z : S2) :
    (s2PoleAverageContinuousLinear f z) ^ 2 ≤
      s2PoleAverageContinuousLinear (f * f) z := by
  have h := poleAverageLinear_sq_le (s2Pullback f) (s2ToSpherePoint3 z)
  simpa [s2PoleAverageContinuousLinear_apply, s2PoleAverageLinear_apply,
    s2Pullback_apply, pow_two] using h

theorem continuous_integrable_rotationMeasure (f : C(S2, ℝ)) :
    Integrable (fun x => f x) rotationMeasure :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuousToLp_norm_sq_eq_integral_sq (f : C(S2, ℝ)) :
    ‖continuousToLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂rotationMeasure := by
  have hinner := MeasureTheory.ContinuousMap.inner_toLp rotationMeasure f f
  rw [← real_inner_self_eq_norm_sq (continuousToLp f)]
  simpa [pow_two] using hinner

theorem s2PoleAverageContinuousLinear_l2_norm_le (f : C(S2, ℝ)) :
    ‖continuousToLp (s2PoleAverageContinuousLinear f)‖ ≤ ‖continuousToLp f‖ := by
  have hint_left :
      Integrable (fun x : S2 => (s2PoleAverageContinuousLinear f x) ^ 2) rotationMeasure :=
    ((s2PoleAverageContinuousLinear f).continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint_right :
      Integrable (fun x : S2 => s2PoleAverageContinuousLinear (f * f) x) rotationMeasure :=
    continuous_integrable_rotationMeasure (s2PoleAverageContinuousLinear (f * f))
  have hIntLe :
      ∫ x, (s2PoleAverageContinuousLinear f x) ^ 2 ∂rotationMeasure ≤
        ∫ x, s2PoleAverageContinuousLinear (f * f) x ∂rotationMeasure :=
    integral_mono hint_left hint_right (s2PoleAverageContinuousLinear_sq_le f)
  have hsq :
      ‖continuousToLp (s2PoleAverageContinuousLinear f)‖ ^ 2 ≤
        ‖continuousToLp f‖ ^ 2 := by
    rw [continuousToLp_norm_sq_eq_integral_sq,
      continuousToLp_norm_sq_eq_integral_sq]
    calc
      ∫ x, (s2PoleAverageContinuousLinear f x) ^ 2 ∂rotationMeasure
          ≤ ∫ x, s2PoleAverageContinuousLinear (f * f) x ∂rotationMeasure := hIntLe
      _ = ∫ x, (f * f) x ∂rotationMeasure := s2PoleAverageIntegral_eq_integral (f * f)
      _ = ∫ x, f x ^ 2 ∂rotationMeasure := by
          simp [pow_two]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

theorem s2PoleAverage_l2_bound :
    ∀ f : C(S2, ℝ),
      ‖continuousToLp (s2PoleAverageContinuousLinear f)‖ ≤
        (1 : ℝ) * ‖continuousToLp f‖ := by
  intro f
  simpa using s2PoleAverageContinuousLinear_l2_norm_le f

theorem projected_poleAverage_commutation_unconditional
    (n : ℕ) (g : C(S2, ℝ)) :
    poleAverageLinear
        (harmonicDegreeProjectionContinuous n (s2Pullback g)) sphereE3 =
      harmonicDegreeProjectionContinuous n
        (s2Pullback (s2PoleAverageContinuousLinear g)) sphereE3 :=
  projected_poleAverage_commutation_of_l2_bound 1 s2PoleAverage_l2_bound n g

theorem projected_poleAverage_commutation_unconditional_pointConstraint
    {n : ℕ} {g : C(S2, ℝ)}
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmoduleS2) :
    poleAverageLinear
        (harmonicDegreeProjectionContinuous n (s2Pullback g)) sphereE3 =
      harmonicDegreeProjectionContinuous n
        (s2Pullback
          (s2PoleAverageContinuousOfGreatCircleConstraint g
            (by
              have hframe : g ∈ continuousSphereFrameSubmoduleS2 := by
                simpa [continuousSphereGreatCirclePointConstraintSubmoduleS2_eq_continuousSphereFrameSubmoduleS2]
                  using hgpc
              exact continuousSphereFrameSubmoduleS2_le_continuousSphereGreatCircleConstraintSubmoduleS2
                hframe)))
        sphereE3 :=
  projected_poleAverage_commutation_of_l2_bound_pointConstraint 1 s2PoleAverage_l2_bound hgpc

end GleasonS2Bridge
