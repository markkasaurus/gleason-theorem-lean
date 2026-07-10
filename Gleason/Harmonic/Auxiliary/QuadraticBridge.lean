import Gleason.Harmonic.Auxiliary.SingleWitness
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.LinearAlgebra.QuadraticForm.Basic

noncomputable section

open scoped Topology

lemma iteratedDeriv_two_sq_mul_const (a : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => t ^ 2 * a) 0 = 2 * a := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (fun t : ℝ => t ^ 2 * a) = fun t : ℝ => (2 * t) * a := by
    funext t
    rw [deriv_mul_const]
    · simpa using
        deriv_pow (f := fun t : ℝ => t) (x := t) differentiableAt_fun_id 2
    · simpa using (differentiableAt_fun_id.pow 2).mul_const a
  rw [h1]
  have hfun : (fun t : ℝ => (2 * t) * a) = fun t : ℝ => (2 * a) * t := by
    funext t
    ring
  rw [hfun, deriv_const_mul]
  · simp
  · exact differentiableAt_fun_id

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def quadraticMapOfTwoHomogeneous (f : E → ℝ) : QuadraticMap ℝ E ℝ :=
  LinearMap.BilinMap.toQuadraticMap ((1 / 2 : ℝ) • bilinearIteratedFDerivTwo ℝ f 0)

lemma bilinearIteratedFDerivTwo_eq_two_mul_of_two_homogeneous
    {f : E → ℝ} (hcont : ContDiffAt ℝ 2 f 0)
    (hhom : ∀ (t : ℝ) (x : E), f (t • x) = t ^ 2 * f x) (x : E) :
    ((bilinearIteratedFDerivTwo ℝ f 0) x) x = 2 * f x := by
  have hcomp := iteratedDeriv_two_comp_add_smul (x := (0 : E)) (v := x) hcont
  have hpath : (fun t : ℝ => f ((0 : E) + t • x)) = fun t : ℝ => t ^ 2 * f x := by
    funext t
    simp [hhom t x]
  rw [hpath] at hcomp
  calc
    ((bilinearIteratedFDerivTwo ℝ f 0) x) x = iteratedFDeriv ℝ 2 f 0 ![x, x] := by
      rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
    _ = iteratedDeriv 2 (fun t : ℝ => t ^ 2 * f x) 0 := by
      simpa using hcomp.symm
    _ = 2 * f x := iteratedDeriv_two_sq_mul_const (f x)

theorem quadraticMapOfTwoHomogeneous_apply
    {f : E → ℝ} (hcont : ContDiffAt ℝ 2 f 0)
    (hhom : ∀ (t : ℝ) (x : E), f (t • x) = t ^ 2 * f x) (x : E) :
    quadraticMapOfTwoHomogeneous f x = f x := by
  have hhess :
      ((bilinearIteratedFDerivTwo ℝ f 0) x) x = 2 * f x :=
    bilinearIteratedFDerivTwo_eq_two_mul_of_two_homogeneous hcont hhom x
  calc
    quadraticMapOfTwoHomogeneous f x
      = (((1 / 2 : ℝ) • bilinearIteratedFDerivTwo ℝ f 0) x) x := by
          simp [quadraticMapOfTwoHomogeneous, LinearMap.BilinMap.toQuadraticMap_apply]
    _ = (1 / 2 : ℝ) * (((bilinearIteratedFDerivTwo ℝ f 0) x) x) := by
          simp
    _ = (1 / 2 : ℝ) * (2 * f x) := by rw [hhess]
    _ = f x := by ring

theorem exists_quadraticMap_of_contDiffAt_two_homogeneous
    {f : E → ℝ} (hcont : ContDiffAt ℝ 2 f 0)
    (hhom : ∀ (t : ℝ) (x : E), f (t • x) = t ^ 2 * f x) :
    ∃ Q : QuadraticMap ℝ E ℝ, ∀ x : E, f x = Q x := by
  refine ⟨quadraticMapOfTwoHomogeneous f, ?_⟩
  intro x
  symm
  exact quadraticMapOfTwoHomogeneous_apply hcont hhom x

end

theorem exists_quadraticMap_of_harmonicHomogeneousDegree_two
    {f : WithLp 2 (ℂ × ℝ) → ℝ} (hf : HarmonicHomogeneousDegree 2 f) :
    ∃ Q : QuadraticMap ℝ (WithLp 2 (ℂ × ℝ)) ℝ, ∀ x : WithLp 2 (ℂ × ℝ), f x = Q x := by
  refine exists_quadraticMap_of_contDiffAt_two_homogeneous ?_ hf.2
  exact (hf.1 0).1
