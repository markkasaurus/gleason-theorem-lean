import SphericalHarmonics.ZonalHit
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open scoped BigOperators

noncomputable section

namespace SphericalHarmonics

theorem eval_smul_of_isHomogeneous {n : ℕ} {p : Poly3}
    (hp : p.IsHomogeneous n) (c : ℝ) (x : E3) :
    MvPolynomial.eval (fun i => c * x i) p = c ^ n * MvPolynomial.eval x p := by
  rw [p.as_sum, MvPolynomial.eval_sum, MvPolynomial.eval_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hdeg : d.sum (fun _ m => m) = n := by
    simpa [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one, Finsupp.sum] using
      hp (by simpa [MvPolynomial.mem_support_iff] using hd)
  have hsum : ∑ i ∈ d.support, d i = n := by
    simpa [Finsupp.sum] using hdeg
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  simp_rw [mul_pow]
  rw [Finsupp.prod, Finsupp.prod]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hsum]
  ring

theorem restrictToSphere_injective_on_homogeneousSubmodule (n : ℕ) :
    Function.Injective fun p : homogeneousSubmodule n => restrictToSphere p.1 := by
  intro p q hpq
  apply Subtype.ext
  let r : Poly3 := p.1 - q.1
  have hrhom : r.IsHomogeneous n := by
    exact ((MvPolynomial.mem_homogeneousSubmodule n p.1).mp p.2).sub
      ((MvPolynomial.mem_homogeneousSubmodule n q.1).mp q.2)
  have hsphere : ∀ y : S2, MvPolynomial.eval y.1.ofLp r = 0 := by
    intro y
    have hy : restrictToSphere p.1 y = restrictToSphere q.1 y := by
      simpa using congrArg (fun f : C(S2, ℝ) => f y) hpq
    simpa [r, restrictToSphere_apply] using sub_eq_zero.mpr hy
  have hall : ∀ x : E3, MvPolynomial.eval x.ofLp r = 0 := by
    intro x
    by_cases hx : x = 0
    · subst x
      calc
        MvPolynomial.eval (0 : E3) r
            = MvPolynomial.eval (fun i => (0 : ℝ) * (northPole : E3) i) r := by simp
        _ = (0 : ℝ) ^ n * MvPolynomial.eval (northPole : E3) r :=
              eval_smul_of_isHomogeneous hrhom 0 (northPole : E3)
        _ = 0 := by simp [hsphere northPole]
    · let y : S2 := ⟨‖x‖⁻¹ • x, by
        have hnx : ‖x‖ ≠ 0 := by
          exact norm_ne_zero_iff.mpr hx
        have hy : ‖‖x‖⁻¹ • x‖ = 1 := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
          exact inv_mul_cancel₀ hnx
        simpa [Metric.mem_sphere, dist_eq_norm] using hy⟩
      have hnx : ‖x‖ ≠ 0 := by
        exact norm_ne_zero_iff.mpr hx
      have hyx : ‖x‖ • (y : E3) = x := by
        change ‖x‖ • (‖x‖⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ hnx, one_smul]
      have hyxfun : x.ofLp = fun i => ‖x‖ * (y : E3) i := by
        funext i
        exact congrArg (fun z : E3 => z i) hyx.symm
      calc
        MvPolynomial.eval x.ofLp r
            = MvPolynomial.eval (fun i => ‖x‖ * (y : E3) i) r := by rw [hyxfun]
        _ = ‖x‖ ^ n * MvPolynomial.eval (y : E3) r :=
              eval_smul_of_isHomogeneous hrhom ‖x‖ (y : E3)
        _ = 0 := by simp [hsphere y]
  have hall' : ∀ x : Fin 3 → ℝ, MvPolynomial.eval x r = 0 := by
    intro x
    simpa using hall ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 3)).symm x)
  have hrzero : r = 0 :=
    MvPolynomial.IsHomogeneous.eq_zero_of_forall_eval_eq_zero hrhom hall'
  exact sub_eq_zero.mp hrzero

theorem restrictToSphere_injective_on_harmonicHomogeneousSubmodule (n : ℕ) :
    Function.Injective fun p : harmonicHomogeneousSubmodule n => restrictToSphere p.1 := by
  intro p q hpq
  let p' : homogeneousSubmodule n := ⟨p.1, p.2.1⟩
  let q' : homogeneousSubmodule n := ⟨q.1, q.2.1⟩
  have h' : p' = q' :=
    restrictToSphere_injective_on_homogeneousSubmodule n <| by
      simpa [p', q'] using hpq
  apply Subtype.ext
  exact congrArg (fun z : homogeneousSubmodule n => z.1) h'

theorem compPolynomial_eq_self_of_mem_northFixedSector
    {n : ℕ} {p : harmonicHomogeneousSubmodule n}
    (hfix : restrictToSphere p.1 ∈ northFixedSubmodule) (t : ℝ) :
    (rotation01 t).compPolynomial p.1 = p.1 := by
  let pt : harmonicHomogeneousSubmodule n := ⟨(rotation01 t).compPolynomial p.1,
    Rotation.compPolynomial_mem_harmonicHomogeneousSubmodule (rotation01 t) n p.2⟩
  have hres :
      restrictToSphere pt.1 = restrictToSphere p.1 := by
    calc
      restrictToSphere pt.1
          = Rotation.compContinuous (rotation01 t) (restrictToSphere p.1) := by
              simpa [pt] using Rotation.restrictToSphere_compPolynomial (rotation01 t) p.1
      _ = restrictToSphere p.1 := (mem_northFixedSubmodule_iff _).1 hfix t
  exact congrArg Subtype.val <|
    restrictToSphere_injective_on_harmonicHomogeneousSubmodule n hres

theorem exists_fixed_ambientRepresentative_of_mem_northFixedSector
    {n : ℕ} {f : sector n} (hf : f ∈ northFixedSector n) :
    ∃ p : harmonicHomogeneousSubmodule n,
      restrictToSphere p.1 = (f : C(S2, ℝ)) ∧
      ∀ t : ℝ, (rotation01 t).compPolynomial p.1 = p.1 := by
  rcases f.2 with ⟨p, hp, hpf⟩
  refine ⟨⟨p, hp⟩, hpf, ?_⟩
  intro t
  have hfix : restrictToSphere p ∈ northFixedSubmodule := by
    simpa [northFixedSector, hpf] using hf
  simpa using compPolynomial_eq_self_of_mem_northFixedSector (p := ⟨p, hp⟩) hfix t

theorem exists_fixed_ambientRepresentative_of_mem_northFixedSectorL2
    {n : ℕ} {u : sectorL2 n} (hu : u ∈ northFixedSectorL2 n) :
    ∃ p : harmonicHomogeneousSubmodule n,
      sectorToSectorL2 n ⟨restrictToSphere p.1, ⟨p.1, p.2, rfl⟩⟩ = u ∧
      ∀ t : ℝ, (rotation01 t).compPolynomial p.1 = p.1 := by
  rcases hu with ⟨f, hf, rfl⟩
  rcases exists_fixed_ambientRepresentative_of_mem_northFixedSector hf with
    ⟨p, hp, hprot⟩
  refine ⟨p, ?_, hprot⟩
  apply Subtype.ext
  simpa [sectorToSectorL2, hp]

theorem exists_nonzero_fixed_ambientRepresentative_of_isRotationInvariant_of_ne_bot
    {n : ℕ} {W : Submodule ℝ (sectorL2 n)}
    (hWrot : SectorSubmodule.IsRotationInvariant n W)
    (hWne : W ≠ ⊥) :
    ∃ p : harmonicHomogeneousSubmodule n,
      let u : sectorL2 n := sectorToSectorL2 n ⟨restrictToSphere p.1, ⟨p.1, p.2, rfl⟩⟩
      u ∈ W ∧ u ≠ 0 ∧
      ∀ t : ℝ, (rotation01 t).compPolynomial p.1 = p.1 := by
  rcases exists_nonzero_mem_inf_northFixedSectorL2_of_isRotationInvariant_of_ne_bot hWrot hWne with
    ⟨u, hu, hu0⟩
  rcases exists_fixed_ambientRepresentative_of_mem_northFixedSectorL2 hu.2 with
    ⟨p, hp, hprot⟩
  refine ⟨p, ?_⟩
  dsimp
  refine ⟨?_, ?_, hprot⟩
  · simpa [hp] using hu.1
  · simpa [hp] using hu0

end SphericalHarmonics
