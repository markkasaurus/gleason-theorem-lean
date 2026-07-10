import Gleason.Harmonic.Sphere.SphereDegreeProjection
import Gleason.Harmonic.HighDegree.EvenUnionSplit
import Gleason.Harmonic.HighDegree.HighEvenBoundedClosure
import Mathlib.Topology.Algebra.Module.LinearMap

noncomputable section

open Complex InnerProductSpace
open SphericalHarmonics

namespace GleasonS2Bridge

def s2PullbackCLM : C(S2, ℝ) →L[ℝ] C(spherePoint3, ℝ) :=
  s2Pullback.toLinearMap.mkContinuous 1 <| by
    intro f
    haveI : Nonempty spherePoint3 := ⟨sphereE1⟩
    rw [one_mul]
    refine (ContinuousMap.norm_le_of_nonempty (f := s2Pullback f) (M := ‖f‖)).2 ?_
    intro x
    simpa [s2Pullback_apply] using f.norm_coe_le_norm (spherePoint3ToS2 x)

@[simp] theorem s2PullbackCLM_apply (f : C(S2, ℝ)) :
    s2PullbackCLM f = s2Pullback f := by
  simp [s2PullbackCLM, LinearMap.mkContinuous_apply]

def s2PushforwardCLM : C(spherePoint3, ℝ) →L[ℝ] C(S2, ℝ) :=
  s2Pullback.symm.toLinearMap.mkContinuous 1 <| by
    intro f
    haveI : Nonempty S2 := ⟨spherePoint3ToS2 sphereE1⟩
    rw [one_mul]
    refine (ContinuousMap.norm_le_of_nonempty (f := s2Pullback.symm f) (M := ‖f‖)).2 ?_
    intro x
    simpa [s2Pullback, spherePoint3EquivS2] using f.norm_coe_le_norm (s2ToSpherePoint3 x)

@[simp] theorem s2PushforwardCLM_apply (f : C(spherePoint3, ℝ)) :
    s2PushforwardCLM f = s2Pullback.symm f := by
  simp [s2PushforwardCLM, LinearMap.mkContinuous_apply]

@[simp] theorem s2PullbackCLM_comp_s2PushforwardCLM :
    s2PullbackCLM.comp s2PushforwardCLM = ContinuousLinearMap.id ℝ C(spherePoint3, ℝ) := by
  ext f x
  simp [s2PullbackCLM, s2PushforwardCLM]

@[simp] theorem s2PushforwardCLM_comp_s2PullbackCLM :
    s2PushforwardCLM.comp s2PullbackCLM = ContinuousLinearMap.id ℝ C(S2, ℝ) := by
  ext f x
  simp [s2PullbackCLM, s2PushforwardCLM]

/-- Continuous degree-`n` harmonic projector on `spherePoint3`, transported from `S²`. -/
def harmonicDegreeProjectionContinuousCLM (n : ℕ) :
    C(spherePoint3, ℝ) →L[ℝ] C(spherePoint3, ℝ) :=
  s2PullbackCLM.comp ((ambientSectorProjectionContinuous n).comp s2PushforwardCLM)

@[simp] theorem harmonicDegreeProjectionContinuousCLM_apply
    (n : ℕ) (f : C(spherePoint3, ℝ)) :
    harmonicDegreeProjectionContinuousCLM n f = harmonicDegreeProjectionContinuous n f := by
  rfl

/-- The ambient low-degree projector selecting degrees `0` and `2`. -/
def ambientLowHarmonicProjectionContinuous :
    C(spherePoint3, ℝ) →L[ℝ] C(spherePoint3, ℝ) :=
  harmonicDegreeProjectionContinuousCLM 0 + harmonicDegreeProjectionContinuousCLM 2

@[simp] theorem ambientLowHarmonicProjectionContinuous_apply
    (f : C(spherePoint3, ℝ)) :
    ambientLowHarmonicProjectionContinuous f =
      harmonicDegreeProjectionContinuous 0 f +
        harmonicDegreeProjectionContinuous 2 f := by
  rfl

theorem harmonicDegreeProjectionContinuous_eq_self_of_mem_harmonicPolyHomogeneousImageSubmodule
    {n : ℕ} {f : C(spherePoint3, ℝ)}
    (hf : f ∈ harmonicPolyHomogeneousImageSubmodule n) :
    harmonicDegreeProjectionContinuous n f = f := by
  rcases hf with ⟨p, hp, rfl⟩
  have hpS2 : restrictToSphere p ∈ sector n := by
    refine ⟨p, ?_, rfl⟩
    simpa [harmonicHomogeneousSubmodule_eq_harmonicPolyHomogeneousSubmodule n] using hp
  have hs :
      s2Pullback.symm (sphereCoordMvEval p) = restrictToSphere p := by
    apply s2Pullback.injective
    simp [s2Pullback_restrictToSphere]
  calc
    harmonicDegreeProjectionContinuous n (sphereCoordMvEval p)
        = s2Pullback (ambientSectorProjectionContinuous n (restrictToSphere p)) := by
            simp [harmonicDegreeProjectionContinuous, hs]
    _ = s2Pullback (restrictToSphere p) := by rw [ambientSectorProjectionContinuous_eq_self hpS2]
    _ = sphereCoordMvEval p := by simpa using (s2Pullback_restrictToSphere p)

theorem harmonicDegreeProjectionContinuous_eq_zero_of_mem_harmonicPolyHomogeneousImageSubmodule
    {m n : ℕ} (hmn : m ≠ n)
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ harmonicPolyHomogeneousImageSubmodule m) :
    harmonicDegreeProjectionContinuous n f = 0 := by
  rcases hf with ⟨p, hp, rfl⟩
  have hpS2 : restrictToSphere p ∈ sector m := by
    refine ⟨p, ?_, rfl⟩
    simpa [harmonicHomogeneousSubmodule_eq_harmonicPolyHomogeneousSubmodule m] using hp
  have hs :
      s2Pullback.symm (sphereCoordMvEval p) = restrictToSphere p := by
    apply s2Pullback.injective
    simp [s2Pullback_restrictToSphere]
  calc
    harmonicDegreeProjectionContinuous n (sphereCoordMvEval p)
        = s2Pullback (ambientSectorProjectionContinuous n (restrictToSphere p)) := by
            simp [harmonicDegreeProjectionContinuous, hs]
    _ = 0 := by rw [ambientSectorProjectionContinuous_eq_zero_of_orthogonal hmn hpS2, map_zero]

theorem ambientLowHarmonicProjectionContinuous_eq_self_of_mem_lowHarmonicPolyHomogeneousImageSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ lowHarmonicPolyHomogeneousImageSubmodule) :
    ambientLowHarmonicProjectionContinuous f = f := by
  rcases Submodule.mem_sup.mp (by simpa [lowHarmonicPolyHomogeneousImageSubmodule] using hf) with
    ⟨f0, hf0, f2, hf2, rfl⟩
  have h00 :
      harmonicDegreeProjectionContinuous 0 f0 = f0 :=
    harmonicDegreeProjectionContinuous_eq_self_of_mem_harmonicPolyHomogeneousImageSubmodule hf0
  have h02 :
      harmonicDegreeProjectionContinuous 0 f2 = 0 :=
    harmonicDegreeProjectionContinuous_eq_zero_of_mem_harmonicPolyHomogeneousImageSubmodule
      (show 2 ≠ 0 by norm_num) hf2
  have h20 :
      harmonicDegreeProjectionContinuous 2 f0 = 0 :=
    harmonicDegreeProjectionContinuous_eq_zero_of_mem_harmonicPolyHomogeneousImageSubmodule
      (show 0 ≠ 2 by norm_num) hf0
  have h22 :
      harmonicDegreeProjectionContinuous 2 f2 = f2 :=
    harmonicDegreeProjectionContinuous_eq_self_of_mem_harmonicPolyHomogeneousImageSubmodule hf2
  simp [ambientLowHarmonicProjectionContinuous_apply, map_add, h00, h02, h20, h22]

theorem highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_ker_ambientLowHarmonicProjectionContinuous
    (N : ℕ) :
    highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ≤
      LinearMap.ker
        (ambientLowHarmonicProjectionContinuous : C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ)) := by
  unfold highEvenBoundedHarmonicPolyHomogeneousImageSubmodule
  simp_rw [Finset.sup_eq_iSup]
  refine iSup_le ?_
  intro k
  refine iSup_le ?_
  intro hk f hf
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  show ambientLowHarmonicProjectionContinuous f = 0
  calc
    ambientLowHarmonicProjectionContinuous f
        = harmonicDegreeProjectionContinuous 0 f + harmonicDegreeProjectionContinuous 2 f := by
            rfl
    _ = 0 + 0 := by
          rw [harmonicDegreeProjectionContinuous_eq_zero_of_mem_harmonicPolyHomogeneousImageSubmodule
                (show 2 * k ≠ 0 by omega) hf]
          rw [harmonicDegreeProjectionContinuous_eq_zero_of_mem_harmonicPolyHomogeneousImageSubmodule
                (show 2 * k ≠ 2 by omega) hf]
    _ = 0 := by simp

theorem highEvenUnionHarmonicPolyHomogeneousImageSubmodule_le_ker_ambientLowHarmonicProjectionContinuous :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule ≤
      LinearMap.ker
        (ambientLowHarmonicProjectionContinuous : C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ)) := by
  unfold highEvenUnionHarmonicPolyHomogeneousImageSubmodule
  refine iSup_le ?_
  intro N
  exact highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_ker_ambientLowHarmonicProjectionContinuous N

theorem ambientLowHarmonicProjectionContinuous_eq_zero_of_mem_highEvenUnion
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule) :
    ambientLowHarmonicProjectionContinuous f = 0 := by
  exact highEvenUnionHarmonicPolyHomogeneousImageSubmodule_le_ker_ambientLowHarmonicProjectionContinuous hf

theorem topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule_le_ker_ambientLowHarmonicProjectionContinuous :
    highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ≤
      LinearMap.ker
        (ambientLowHarmonicProjectionContinuous : C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ)) := by
  intro f hf
  have hmap :
      ambientLowHarmonicProjectionContinuous f ∈
        (highEvenUnionHarmonicPolyHomogeneousImageSubmodule.map
          (ambientLowHarmonicProjectionContinuous : C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ))).topologicalClosure := by
    have hmem :
        ambientLowHarmonicProjectionContinuous f ∈
          highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure.map
            (ambientLowHarmonicProjectionContinuous : C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ)) := by
      exact ⟨f, hf, rfl⟩
    exact
      Submodule.topologicalClosure_map
        (ambientLowHarmonicProjectionContinuous : C(spherePoint3, ℝ) →L[ℝ] C(spherePoint3, ℝ))
        highEvenUnionHarmonicPolyHomogeneousImageSubmodule hmem
  have hzeroMap :
      highEvenUnionHarmonicPolyHomogeneousImageSubmodule.map
        (ambientLowHarmonicProjectionContinuous : C(spherePoint3, ℝ) →ₗ[ℝ] C(spherePoint3, ℝ)) = ⊥ := by
    apply le_antisymm
    · intro g hg
      rcases hg with ⟨x, hx, rfl⟩
      simp [ambientLowHarmonicProjectionContinuous_eq_zero_of_mem_highEvenUnion hx]
    · exact bot_le
  have hzero :
      ambientLowHarmonicProjectionContinuous f ∈
        (⊥ : Submodule ℝ C(spherePoint3, ℝ)) := by
    have hbotclosed :
        IsClosed (((⊥ : Submodule ℝ C(spherePoint3, ℝ)) : Set C(spherePoint3, ℝ))) := by
      simpa using (isClosed_singleton : IsClosed ({(0 : C(spherePoint3, ℝ))} : Set C(spherePoint3, ℝ)))
    have hbotle :
        (⊥ : Submodule ℝ C(spherePoint3, ℝ)).topologicalClosure ≤
          (⊥ : Submodule ℝ C(spherePoint3, ℝ)) :=
      Submodule.topologicalClosure_minimal (⊥ : Submodule ℝ C(spherePoint3, ℝ)) bot_le hbotclosed
    exact hbotle <| by simpa [hzeroMap] using hmap
  show ambientLowHarmonicProjectionContinuous f = 0
  simpa using hzero

theorem ambientLowHarmonicProjectionContinuous_eq_zero_of_mem_topologicalClosure_highEvenUnion
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure) :
    ambientLowHarmonicProjectionContinuous f = 0 := by
  exact topologicalClosure_highEvenUnionHarmonicPolyHomogeneousImageSubmodule_le_ker_ambientLowHarmonicProjectionContinuous hf

theorem norm_low_le_global_const_mul_norm_sub_of_mem_low_of_mem_topologicalClosure_highEvenUnion
    {h l : C(spherePoint3, ℝ)}
    (hl : l ∈ lowHarmonicPolyHomogeneousImageSubmodule)
    (hh : h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure) :
    ‖l‖ ≤ ‖ambientLowHarmonicProjectionContinuous‖ * ‖h - l‖ := by
  have hlow : ambientLowHarmonicProjectionContinuous l = l :=
    ambientLowHarmonicProjectionContinuous_eq_self_of_mem_lowHarmonicPolyHomogeneousImageSubmodule hl
  have hhigh : ambientLowHarmonicProjectionContinuous h = 0 :=
    ambientLowHarmonicProjectionContinuous_eq_zero_of_mem_topologicalClosure_highEvenUnion hh
  have hcalc :
      ambientLowHarmonicProjectionContinuous (h - l) = -l := by
    rw [map_sub, hhigh, hlow]
    simp
  calc
    ‖l‖ = ‖ambientLowHarmonicProjectionContinuous (h - l)‖ := by
          rw [hcalc]
          simp
    _ ≤ ‖ambientLowHarmonicProjectionContinuous‖ * ‖h - l‖ :=
          ambientLowHarmonicProjectionContinuous.le_opNorm (h - l)

theorem norm_sphereE3_le_one_add_global_const_mul_norm_sub_of_mem_low_of_mem_topologicalClosure_highEvenUnion
    {h l : C(spherePoint3, ℝ)}
    (hl : l ∈ lowHarmonicPolyHomogeneousImageSubmodule)
    (hh : h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure) :
    ‖h sphereE3‖ ≤ (1 + ‖ambientLowHarmonicProjectionContinuous‖) * ‖h - l‖ := by
  calc
    ‖h sphereE3‖ ≤ ‖(h - l) sphereE3‖ + ‖l sphereE3‖ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            norm_add_le ((h - l) sphereE3) (l sphereE3)
    _ ≤ ‖h - l‖ + ‖l‖ := by
          gcongr
          · exact (h - l).norm_coe_le_norm sphereE3
          · exact l.norm_coe_le_norm sphereE3
    _ ≤ ‖h - l‖ + ‖ambientLowHarmonicProjectionContinuous‖ * ‖h - l‖ := by
          gcongr
          exact norm_low_le_global_const_mul_norm_sub_of_mem_low_of_mem_topologicalClosure_highEvenUnion hl hh
    _ = (1 + ‖ambientLowHarmonicProjectionContinuous‖) * ‖h - l‖ := by ring

end GleasonS2Bridge
