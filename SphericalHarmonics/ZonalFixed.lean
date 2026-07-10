import SphericalHarmonics.FiniteDimensional
import SphericalHarmonics.SectorProjectionInvariant
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

open MeasureTheory intervalIntegral

namespace SphericalHarmonics

/-- The continuous functions on `S²` fixed by all north-axis rotations. -/
def northFixedSubmodule : Submodule ℝ C(S2, ℝ) where
  carrier := {f | ∀ t : ℝ, Rotation.compContinuous (rotation01 t) f = f}
  zero_mem' := by
    intro t
    ext x
    simp [Rotation.compContinuous_apply]
  add_mem' hf hg := by
    intro t
    ext x
    simp [hf t, hg t]
  smul_mem' c f hf := by
    intro t
    simpa using congrArg (fun g : C(S2, ℝ) => c • g) (hf t)

@[simp] theorem mem_northFixedSubmodule_iff (f : C(S2, ℝ)) :
    f ∈ northFixedSubmodule ↔ ∀ t : ℝ, Rotation.compContinuous (rotation01 t) f = f := by
  rfl

@[simp] theorem rotation01_add (s t : ℝ) :
    rotation01 (s + t) = (rotation01 s).trans (rotation01 t) := by
  ext x i
  simp [rotation01_apply, rot01Point_add, neg_add, add_assoc]

@[simp] theorem rotation01_two_pi :
    rotation01 (2 * Real.pi) = LinearIsometryEquiv.refl ℝ E3 := by
  ext x i
  fin_cases i <;> simp [rotation01_apply, rot01Point, Real.cos_two_pi, Real.sin_two_pi]

@[simp] theorem rotation01_add_two_pi (t : ℝ) :
    rotation01 (t + 2 * Real.pi) = rotation01 t := by
  calc
    rotation01 (t + 2 * Real.pi)
        = (rotation01 t).trans (rotation01 (2 * Real.pi)) := by
            simpa [add_assoc, add_comm, add_left_comm] using rotation01_add t (2 * Real.pi)
    _ = rotation01 t := by simp

@[simp] theorem norm_coe_S2 (x : S2) : ‖(x : E3)‖ = 1 := by
  simpa [Metric.mem_sphere, dist_eq_norm] using x.2

@[simp] theorem rotation01_symm_symm_apply (t : ℝ) (x : S2) :
    (rotation01 t).toSphereEquiv.symm x =
      ⟨rot01Point t (x : E3), by
        have hsq : ‖rot01Point t (x : E3)‖ ^ 2 = (1 : ℝ) := by
          simpa [norm_coe_S2 x] using (rot01Point_norm_sq t (x : E3))
        have hnn : 0 ≤ ‖rot01Point t (x : E3)‖ := norm_nonneg _
        have hnorm : ‖rot01Point t (x : E3)‖ = 1 := by
          nlinarith
        simpa [Metric.mem_sphere, dist_eq_norm] using hnorm⟩ := by
  rfl

@[simp] theorem rotation01_toSphereEquiv_symm_comp (s t : ℝ) (x : S2) :
    (rotation01 s).toSphereEquiv.symm ((rotation01 t).toSphereEquiv.symm x) =
      (rotation01 (t + s)).toSphereEquiv.symm x := by
  apply Subtype.ext
  ext i
  change rot01Point s (rot01Point t (x : E3)) i = rot01Point (t + s) (x : E3) i
  simpa [add_comm] using congrArg (fun z : E3 => z i) (rot01Point_add s t (x : E3))

lemma northRotationOrbitContinuousS2 (f : C(S2, ℝ)) :
    Continuous (fun t : ℝ => Rotation.compContinuous (rotation01 t) f) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have hpair : Continuous fun p : ℝ × S2 => (p.1, (p.2 : E3)) := by
    continuity
  have hrot : Continuous fun p : ℝ × S2 => rot01Point p.1 (p.2 : E3) := by
    simpa using continuous_rot01Point_uncurry.comp hpair
  have hnorm : ∀ p : ℝ × S2, ‖rot01Point p.1 (p.2 : E3)‖ = 1 := by
    intro p
    have hsq : ‖rot01Point p.1 (p.2 : E3)‖ ^ 2 = (1 : ℝ) := by
      simpa [norm_coe_S2 p.2] using (rot01Point_norm_sq p.1 (p.2 : E3))
    have hnn : 0 ≤ ‖rot01Point p.1 (p.2 : E3)‖ := norm_nonneg _
    nlinarith
  have hsphere : Continuous fun p : ℝ × S2 =>
      (⟨rot01Point p.1 (p.2 : E3), by
        simpa [Metric.mem_sphere, dist_eq_norm] using hnorm p⟩ : S2) := by
    exact Continuous.subtype_mk hrot fun p => by
      simpa [Metric.mem_sphere, dist_eq_norm] using hnorm p
  simpa [Rotation.compContinuous_apply] using f.continuous.comp hsphere

lemma northRotationOrbit_intervalIntegrableS2 (f : C(S2, ℝ)) :
    IntervalIntegrable (fun t : ℝ => Rotation.compContinuous (rotation01 t) f)
      volume 0 (2 * Real.pi) := by
  exact (northRotationOrbitContinuousS2 f).intervalIntegrable 0 (2 * Real.pi)

/-- Averaging a continuous function over the north-axis rotations on `S²`. -/
def northAxisAverage (f : C(S2, ℝ)) : C(S2, ℝ) :=
  ((2 * Real.pi)⁻¹ : ℝ) • ∫ t in 0..2 * Real.pi, Rotation.compContinuous (rotation01 t) f

@[simp] theorem northAxisAverage_apply (f : C(S2, ℝ)) (x : S2) :
    northAxisAverage f x =
      ((2 * Real.pi)⁻¹ : ℝ) *
        ∫ t in 0..2 * Real.pi, f ((rotation01 t).toSphereEquiv.symm x) := by
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hInt :
      Integrable (fun t : ℝ => Rotation.compContinuous (rotation01 t) f)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    exact (northRotationOrbitContinuousS2 f).integrableOn_Ioc
  rw [northAxisAverage, ContinuousMap.smul_apply, smul_eq_mul, intervalIntegral_eq_integral_uIoc]
  simp [hpi]
  rw [ContinuousMap.integral_apply hInt x, intervalIntegral_eq_integral_uIoc]
  simp [hpi, Rotation.compContinuous_apply]

@[simp] theorem rotation01_symm_northPole (t : ℝ) :
    (rotation01 t).toSphereEquiv.symm northPole = northPole := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [northPole, rot01Point]

theorem northAxisAverage_northPole (f : C(S2, ℝ)) :
    northAxisAverage f northPole = f northPole := by
  rw [northAxisAverage_apply]
  have hconst :
      (∫ t in 0..2 * Real.pi, f ((rotation01 t).toSphereEquiv.symm northPole))
        = (2 * Real.pi) * f northPole := by
    simp only [rotation01_symm_northPole]
    simp
  rw [hconst]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  field_simp [hpi]

theorem northAxisAverage_ne_zero_of_northPole_ne_zero
    {f : C(S2, ℝ)} (hf : f northPole ≠ 0) :
    northAxisAverage f ≠ 0 := by
  intro hzero
  apply hf
  rw [← northAxisAverage_northPole f]
  simpa [hzero]

theorem northAxisAverage_eq_of_compContinuous_rotation01
    (f : C(S2, ℝ)) (s : ℝ) :
    northAxisAverage (Rotation.compContinuous (rotation01 s) f) = northAxisAverage f := by
  ext x
  rw [northAxisAverage_apply, northAxisAverage_apply]
  let F : ℝ → ℝ := fun t => f ((rotation01 t).toSphereEquiv.symm x)
  have hshift :
      (∫ t in 0..2 * Real.pi, F (t + s)) = ∫ u in s..2 * Real.pi + s, F u := by
    simpa [F] using
      (intervalIntegral.integral_comp_add_right (f := F) (a := 0) (b := 2 * Real.pi) s)
  have hperiodic : Function.Periodic F (2 * Real.pi) := by
    intro t
    simp [F, rotation01_add_two_pi, add_assoc, add_left_comm, add_comm]
  have hperiod :
      ∫ u in s..2 * Real.pi + s, F u = ∫ u in 0..2 * Real.pi, F u := by
    simpa [add_assoc, add_left_comm, add_comm] using hperiodic.intervalIntegral_add_eq s 0
  have hEq1 :
      (fun t : ℝ =>
        Rotation.compContinuous (rotation01 s) f ((rotation01 t).toSphereEquiv.symm x)) =
      fun t : ℝ => F (t + s) := by
    funext t
    rw [Rotation.compContinuous_apply, rotation01_toSphereEquiv_symm_comp]
  calc
    ((2 * Real.pi)⁻¹ : ℝ) *
        ∫ t in 0..2 * Real.pi,
          Rotation.compContinuous (rotation01 s) f ((rotation01 t).toSphereEquiv.symm x)
      = ((2 * Real.pi)⁻¹ : ℝ) * ∫ t in 0..2 * Real.pi, F (t + s) := by
          rw [hEq1]
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ u in s..2 * Real.pi + s, F u := by
          rw [hshift]
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ u in 0..2 * Real.pi, F u := by
          rw [hperiod]
    _ = ((2 * Real.pi)⁻¹ : ℝ) *
          ∫ t in 0..2 * Real.pi, f ((rotation01 t).toSphereEquiv.symm x) := by
            simp [F]

theorem northAxisAverage_mem_northFixedSubmodule (f : C(S2, ℝ)) :
    northAxisAverage f ∈ northFixedSubmodule := by
  intro t
  ext x
  rw [Rotation.compContinuous_apply, northAxisAverage_apply, northAxisAverage_apply]
  let F : ℝ → ℝ := fun s => f ((rotation01 s).toSphereEquiv.symm x)
  have hshift :
      (∫ s in 0..2 * Real.pi, F (t + s)) = ∫ u in t..t + 2 * Real.pi, F u := by
    simpa [F] using
      (intervalIntegral.integral_comp_add_left (f := F) (a := 0) (b := 2 * Real.pi) t)
  have hperiodic : Function.Periodic F (2 * Real.pi) := by
    intro s
    simp [F, rotation01_add_two_pi, add_assoc, add_left_comm, add_comm]
  have hperiod :
      ∫ u in t..t + 2 * Real.pi, F u = ∫ u in 0..2 * Real.pi, F u := by
    simpa [add_assoc, add_left_comm, add_comm] using hperiodic.intervalIntegral_add_eq t 0
  have hEq1 :
      (fun s : ℝ => f ((rotation01 s).toSphereEquiv.symm ((rotation01 t).toSphereEquiv.symm x))) =
      fun s : ℝ => F (t + s) := by
    funext s
    rw [rotation01_toSphereEquiv_symm_comp]
  calc
    ((2 * Real.pi)⁻¹ : ℝ) *
        ∫ s in 0..2 * Real.pi,
          f ((rotation01 s).toSphereEquiv.symm ((rotation01 t).toSphereEquiv.symm x))
      = ((2 * Real.pi)⁻¹ : ℝ) * ∫ s in 0..2 * Real.pi, F (t + s) := by
          rw [hEq1]
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ u in t..t + 2 * Real.pi, F u := by
          rw [hshift]
    _ = ((2 * Real.pi)⁻¹ : ℝ) * ∫ u in 0..2 * Real.pi, F u := by
          rw [hperiod]
    _ = ((2 * Real.pi)⁻¹ : ℝ) *
          ∫ s in 0..2 * Real.pi, f ((rotation01 s).toSphereEquiv.symm x) := by
          simp [F]

lemma exists_point_ne_zero_of_ne_zero {f : C(S2, ℝ)} (hf : f ≠ 0) :
    ∃ x : S2, f x ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hf
  ext x
  exact h x

theorem exists_rotation_toSphereEquiv_eq_northPole (x : S2) :
    ∃ ρ : Rotation, ρ.toSphereEquiv x = northPole := by
  let seed : Fin 3 → E3 := fun i => if i = (2 : Fin 3) then (x : E3) else 0
  let s : Set (Fin 3) := {(2 : Fin 3)}
  have hseed_orth : Orthonormal ℝ (s.restrict seed) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    have hi' : i = (2 : Fin 3) := by simpa [s] using hi
    have hj' : j = (2 : Fin 3) := by simpa [s] using hj
    subst hi'; subst hj'
    simp [seed, x.2]
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (ι := Fin 3) (𝕜 := ℝ) (E := E3)
      (card_ι := by
        simpa [E3] using (Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin 3)))
      hseed_orth
  refine ⟨b.repr, ?_⟩
  apply Subtype.ext
  have hb2 : b (2 : Fin 3) = x := hb (2 : Fin 3) (by simp [s])
  calc
    b.repr (x : E3) = b.repr (b (2 : Fin 3)) := by simpa [hb2]
    _ = EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
          simpa using OrthonormalBasis.repr_self b (2 : Fin 3)
    _ = (northPole : E3) := by rfl

/-- Rotation-invariant submodules of a fixed continuous sector. -/
def SectorContinuousSubmodule.IsRotationInvariant (n : ℕ) (W : Submodule ℝ (sector n)) : Prop :=
  ∀ (ρ : Rotation) (x : sector n), x ∈ W →
    ⟨Rotation.compContinuous ρ x.1, compContinuous_mem_sector ρ n x.2⟩ ∈ W

theorem exists_nonzero_mem_inf_northFixed_of_isRotationInvariant_of_ne_bot
    {n : ℕ} {W : Submodule ℝ (sector n)}
    (hWrot : SectorContinuousSubmodule.IsRotationInvariant n W)
    (hWne : W ≠ ⊥) :
    ∃ f : sector n, f ∈ W ∧ f ≠ 0 ∧ ((f : C(S2, ℝ)) ∈ northFixedSubmodule) := by
  letI : FiniteDimensional ℝ W := by infer_instance
  haveI : CompleteSpace W := by infer_instance
  have hWnonzero : ∃ f : W, f ≠ 0 := by
    by_contra h
    apply hWne
    rw [Submodule.eq_bot_iff]
    intro f hf
    by_contra hf0
    exact h ⟨⟨f, hf⟩, fun hsub => hf0 (Subtype.ext_iff.mp hsub)⟩
  rcases hWnonzero with ⟨fW, hf0⟩
  let f : sector n := fW.1
  have hfW : f ∈ W := fW.2
  have hfcne : ((f : sector n) : C(S2, ℝ)) ≠ 0 := by
    intro h
    apply hf0
    ext x
    exact congrArg (fun g : C(S2, ℝ) => g x) h
  rcases exists_point_ne_zero_of_ne_zero hfcne with ⟨x, hfx⟩
  rcases exists_rotation_toSphereEquiv_eq_northPole x with ⟨ρ, hρx⟩
  let g : sector n := ⟨Rotation.compContinuous ρ f.1, compContinuous_mem_sector ρ n f.2⟩
  have hgW : g ∈ W := hWrot ρ f hfW
  have hρx' : ρ.toSphereEquiv.symm northPole = x := by
    simpa [hρx] using (ρ.toSphereEquiv.left_inv x)
  have hgnorth_eval : (g : C(S2, ℝ)) northPole = (f : C(S2, ℝ)) x := by
    change Rotation.compContinuous ρ f.1 northPole = (f : C(S2, ℝ)) x
    rw [Rotation.compContinuous_apply]
    simpa [f] using congrArg (fun z : S2 => (f : C(S2, ℝ)) z) hρx'
  have hgnorth : (g : C(S2, ℝ)) northPole ≠ 0 := by
    simpa [hgnorth_eval] using hfx
  let G : ℝ → sector n := fun t =>
    ⟨Rotation.compContinuous (rotation01 t) g.1,
      compContinuous_mem_sector (rotation01 t) n g.2⟩
  have hGcont0 : Continuous fun t : ℝ => Rotation.compContinuous (rotation01 t) (g : C(S2, ℝ)) := by
    simpa using northRotationOrbitContinuousS2 (g : C(S2, ℝ))
  have hGcont : Continuous G := by
    exact Continuous.subtype_mk hGcont0 fun t =>
      compContinuous_mem_sector (rotation01 t) n g.2
  have hGInt : IntervalIntegrable G volume 0 (2 * Real.pi) := hGcont.intervalIntegrable 0 (2 * Real.pi)
  have hWclosed : IsClosed (W : Set (sector n)) := Submodule.closed_of_finiteDimensional W
  have h0 : volume (Set.Ioc 0 (2 * Real.pi)) ≠ 0 := by
    rw [Real.volume_Ioc]
    rw [ENNReal.ofReal_ne_zero_iff]
    nlinarith [Real.pi_pos]
  have ht : volume (Set.Ioc 0 (2 * Real.pi)) ≠ ⊤ := by
    simpa using (measure_Ioc_lt_top (μ := volume) (a := 0) (b := 2 * Real.pi)).ne
  have hfs : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 (2 * Real.pi)), G t ∈ (W : Set (sector n)) := by
    exact Filter.Eventually.of_forall fun t => hWrot (rotation01 t) g hgW
  have hfi : IntegrableOn G (Set.Ioc 0 (2 * Real.pi)) volume := by
    exact hGcont.integrableOn_Ioc
  let avg : sector n := ((2 * Real.pi)⁻¹ : ℝ) • ∫ t in 0..2 * Real.pi, G t
  have havgW : avg ∈ W := by
    have hEq :
        avg = ⨍ t in Set.Ioc 0 (2 * Real.pi), G t ∂volume := by
      change ((2 * Real.pi)⁻¹ : ℝ) • ∫ t in 0..2 * Real.pi, G t =
        ⨍ t in Set.Ioc 0 (2 * Real.pi), G t ∂volume
      rw [MeasureTheory.setAverage_eq]
      have hpi : 0 ≤ 2 * Real.pi := by positivity
      rw [intervalIntegral_eq_integral_uIoc]
      simp [hpi]
    rw [hEq]
    exact W.convex.set_average_mem hWclosed h0 ht hfs hfi
  have havg_eq' : ((avg : sector n) : C(S2, ℝ)) = northAxisAverage (g : C(S2, ℝ)) := by
    change (sector n).subtypeL (((2 * Real.pi)⁻¹ : ℝ) • ∫ t in 0..2 * Real.pi, G t) =
      northAxisAverage (g : C(S2, ℝ))
    unfold northAxisAverage
    rw [ContinuousLinearMap.map_smul, ← ContinuousLinearMap.intervalIntegral_comp_comm
      (sector n).subtypeL hGInt]
    rfl
  refine ⟨avg, havgW, ?_, ?_⟩
  · intro havg0
    apply northAxisAverage_ne_zero_of_northPole_ne_zero hgnorth
    rw [← havg_eq']
    ext y
    exact congrArg (fun z : sector n => ((z : C(S2, ℝ)) y)) havg0
  · rw [havg_eq']
    exact northAxisAverage_mem_northFixedSubmodule (g : C(S2, ℝ))

end SphericalHarmonics
