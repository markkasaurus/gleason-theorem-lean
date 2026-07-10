import SphericalHarmonics.Geometry

open scoped BigOperators

namespace SphericalHarmonics

/-- Ambient polynomial ring on `ℝ^3`. -/
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- The algebraic Laplacian `∂₀² + ∂₁² + ∂₂²` on ambient polynomials. -/
noncomputable def laplacian : Poly3 →ₗ[ℝ] Poly3 where
  toFun p := ∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)
  map_add' p q := by
    simp [Finset.sum_add_distrib]
  map_smul' c p := by
    simp [Finset.smul_sum]

/-- Harmonic ambient polynomials on `ℝ^3`. -/
noncomputable def harmonicSubmodule : Submodule ℝ Poly3 := LinearMap.ker laplacian

/-- Homogeneous ambient polynomials of degree `n`. -/
abbrev homogeneousSubmodule (n : ℕ) : Submodule ℝ Poly3 :=
  MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n

/-- Harmonic homogeneous ambient polynomials of degree `n`. -/
noncomputable def harmonicHomogeneousSubmodule (n : ℕ) : Submodule ℝ Poly3 :=
  homogeneousSubmodule n ⊓ harmonicSubmodule

theorem laplacian_isHomogeneous {p : Poly3} {n : ℕ} (hp : p.IsHomogeneous n) :
    (laplacian p).IsHomogeneous (n - 2) := by
  classical
  unfold laplacian
  refine MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun i => MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) (n - 2) ?_
  intro i hi
  simpa using (hp.pderiv.pderiv (i := i))

/-- Restriction of an ambient polynomial to the sphere. -/
noncomputable def restrictToSphere : Poly3 →ₗ[ℝ] C(S2, ℝ) where
  toFun p :=
    { toFun := fun x => MvPolynomial.eval x.1.ofLp p
      continuous_toFun := by
        simpa using
          ((MvPolynomial.continuous_eval p).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))).comp
            continuous_subtype_val }
  map_add' p q := by
    ext x
    simp
  map_smul' c p := by
    ext x
    simp

@[simp] theorem restrictToSphere_apply (p : Poly3) (x : S2) :
    restrictToSphere p x = MvPolynomial.eval x.1.ofLp p := rfl

/-- The degree-`n` polynomial spherical sector, defined as the image of harmonic homogeneous
polynomials under restriction to the sphere. -/
noncomputable def sector (n : ℕ) : Submodule ℝ C(S2, ℝ) :=
  (harmonicHomogeneousSubmodule n).map restrictToSphere

theorem restrict_mem_sector {n : ℕ} {p : Poly3} (hp : p ∈ harmonicHomogeneousSubmodule n) :
    restrictToSphere p ∈ sector n :=
  ⟨p, hp, rfl⟩

/-- The ambient squared-radius polynomial `x₀² + x₁² + x₂²`. -/
noncomputable def radiusSq : Poly3 :=
  ∑ i : Fin 3, (MvPolynomial.X i) ^ 2

theorem radiusSq_isHomogeneous : radiusSq.IsHomogeneous 2 := by
  classical
  unfold radiusSq
  refine MvPolynomial.IsHomogeneous.sum Finset.univ (fun i => (MvPolynomial.X i : Poly3) ^ 2) 2 ?_
  intro i hi
  simpa using (MvPolynomial.isHomogeneous_X_pow (R := ℝ) i 2)

@[simp] theorem laplacian_radiusSq : laplacian radiusSq = 6 := by
  have h0 : (MvPolynomial.pderiv 0) (2 : Poly3) = 0 := by
    simpa using (MvPolynomial.pderiv 0).map_natCast 2
  have h1 : (MvPolynomial.pderiv 1) (2 : Poly3) = 0 := by
    simpa using (MvPolynomial.pderiv 1).map_natCast 2
  have h2 : (MvPolynomial.pderiv 2) (2 : Poly3) = 0 := by
    simpa using (MvPolynomial.pderiv 2).map_natCast 2
  simp [laplacian, radiusSq, Fin.sum_univ_three, h0, h1, h2]
  ring

@[simp] theorem radiusSq_eval (x : S2) : MvPolynomial.eval x.1.ofLp radiusSq = 1 := by
  have hxnorm : ‖x.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using x.2
  rw [EuclideanSpace.norm_eq] at hxnorm
  have hsum : ∑ i : Fin 3, ‖x.1 i‖ ^ 2 = 1 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ ∑ i : Fin 3, ‖x.1 i‖ ^ 2 by positivity), hxnorm]
  simpa [radiusSq, pow_two] using hsum

@[simp] theorem restrictToSphere_radiusSq : restrictToSphere radiusSq = 1 := by
  ext x
  simp [radiusSq_eval]

@[simp] theorem restrictToSphere_radiusSq_mul (p : Poly3) :
    restrictToSphere (radiusSq * p) = restrictToSphere p := by
  ext x
  simp [radiusSq_eval]

@[simp] theorem restrictToSphere_mul_radiusSq (p : Poly3) :
    restrictToSphere (p * radiusSq) = restrictToSphere p := by
  ext x
  simp [radiusSq_eval]

@[simp] theorem restrictToSphere_radiusSq_pow (n : ℕ) :
    restrictToSphere (radiusSq ^ n) = 1 := by
  ext x
  simp [radiusSq_eval]

@[simp] theorem restrictToSphere_radiusSq_pow_mul (n : ℕ) (p : Poly3) :
    restrictToSphere (radiusSq ^ n * p) = restrictToSphere p := by
  ext x
  simp [radiusSq_eval]

@[simp] theorem restrictToSphere_radiusSq_sub_one : restrictToSphere (radiusSq - 1) = 0 := by
  ext x
  simp

@[simp] theorem restrictToSphere_radiusSq_sub_one_mul (p : Poly3) :
    restrictToSphere ((radiusSq - 1) * p) = 0 := by
  ext x
  simp [radiusSq_eval]

theorem restrictToSphere_eq_of_mul_radiusSq_sub_one {p q r : Poly3}
    (h : p - q = (radiusSq - 1) * r) : restrictToSphere p = restrictToSphere q := by
  have hzero : restrictToSphere (p - q) = 0 := by
    rw [h]
    exact restrictToSphere_radiusSq_sub_one_mul r
  ext x
  have hx : restrictToSphere (p - q) x = 0 := by
    exact congrArg (fun f : C(S2, ℝ) => f x) hzero
  exact sub_eq_zero.mp <| by simpa using hx

namespace Rotation

/-- The `j,i` coefficient of the orthogonal matrix of `ρ`, viewed in the standard Euclidean basis. -/
noncomputable def coeff (ρ : Rotation) (j i : Fin 3) : ℝ :=
  (ρ (EuclideanSpace.single j (1 : ℝ))) i

/-- The `j`-th rotated coordinate polynomial, representing `x ↦ (ρ.symm x)_j`. -/
noncomputable def coordPoly (ρ : Rotation) (j : Fin 3) : Poly3 :=
  ∑ i : Fin 3, MvPolynomial.C (coeff ρ j i) * MvPolynomial.X i

theorem coordPoly_isHomogeneous (ρ : Rotation) (j : Fin 3) :
    (coordPoly ρ j).IsHomogeneous 1 := by
  unfold coordPoly
  refine MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun i => MvPolynomial.C (coeff ρ j i) * MvPolynomial.X i) 1 ?_
  intro i hi
  simpa using (MvPolynomial.isHomogeneous_C_mul_X (r := coeff ρ j i) (i := i))

theorem eval_coordPoly (ρ : Rotation) (x : E3) (j : Fin 3) :
    MvPolynomial.eval x.ofLp (coordPoly ρ j) = (ρ.symm x) j := by
  calc
    MvPolynomial.eval x.ofLp (coordPoly ρ j)
        = ∑ i : Fin 3, coeff ρ j i * x i := by
            simp [coordPoly, coeff, Fin.sum_univ_three, mul_comm]
    _ = inner ℝ (ρ (EuclideanSpace.single j (1 : ℝ))) x := by
          simp [coeff, PiLp.inner_apply, Fin.sum_univ_three]
          ring
    _ = inner ℝ (EuclideanSpace.single j (1 : ℝ)) (ρ.symm x) := by
          rw [← ρ.inner_map_map (EuclideanSpace.single j (1 : ℝ)) (ρ.symm x), ρ.apply_symm_apply]
    _ = (ρ.symm x) j := by
          simp [EuclideanSpace.inner_single_left]

/-- Pullback of ambient polynomials by the orthogonal map `ρ`. -/
noncomputable def compPolynomial (ρ : Rotation) : Poly3 →ₐ[ℝ] Poly3 :=
  MvPolynomial.aeval (coordPoly ρ)

theorem eval_compPolynomial (ρ : Rotation) (p : Poly3) (x : E3) :
    MvPolynomial.eval x.ofLp (compPolynomial ρ p) = MvPolynomial.eval (ρ.symm x).ofLp p := by
  refine MvPolynomial.induction_on (motive := fun p : Poly3 =>
    MvPolynomial.eval x.ofLp (compPolynomial ρ p) = MvPolynomial.eval (ρ.symm x).ofLp p) p ?_ ?_ ?_
  · intro a
    simp [compPolynomial]
  · intro p q hp hq
    rw [show compPolynomial ρ (p + q) = compPolynomial ρ p + compPolynomial ρ q by
          exact (compPolynomial ρ).map_add p q]
    rw [MvPolynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  · intro p i hp
    calc
      MvPolynomial.eval x.ofLp (compPolynomial ρ (p * MvPolynomial.X i))
          = MvPolynomial.eval x.ofLp (compPolynomial ρ p * compPolynomial ρ (MvPolynomial.X i)) := by
              simpa using congrArg (MvPolynomial.eval x.ofLp)
                ((compPolynomial ρ).map_mul p (MvPolynomial.X i))
      _ = MvPolynomial.eval (ρ.symm x).ofLp p * (ρ.symm x) i := by
              rw [MvPolynomial.eval_mul, hp]
              simp [compPolynomial, eval_coordPoly]
      _ = MvPolynomial.eval (ρ.symm x).ofLp (p * MvPolynomial.X i) := by
              simp

theorem pderiv_coordPoly (ρ : Rotation) (i j : Fin 3) :
    MvPolynomial.pderiv i (coordPoly ρ j) = MvPolynomial.C (coeff ρ j i) := by
  fin_cases i <;> fin_cases j <;> simp [coordPoly, coeff, Fin.sum_univ_three]

theorem compPolynomial_isHomogeneous (ρ : Rotation) {p : Poly3} {n : ℕ}
    (hp : p.IsHomogeneous n) : (compPolynomial ρ p).IsHomogeneous n := by
  simpa [compPolynomial, one_mul] using
    hp.eval₂ (MvPolynomial.C) (coordPoly ρ)
      (fun r => by
        show (MvPolynomial.C r : Poly3).IsHomogeneous 0
        exact MvPolynomial.isHomogeneous_C (σ := Fin 3) (R := ℝ) r)
      (coordPoly_isHomogeneous ρ)

@[simp] theorem restrictToSphere_compPolynomial (ρ : Rotation) (p : Poly3) :
    restrictToSphere (ρ.compPolynomial p) = Rotation.compContinuous ρ (restrictToSphere p) := by
  ext x
  simpa [Rotation.compContinuous_apply] using eval_compPolynomial ρ p (x : E3)

end Rotation

end SphericalHarmonics
