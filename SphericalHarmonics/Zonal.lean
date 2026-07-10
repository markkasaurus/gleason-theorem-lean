import SphericalHarmonics.Polynomial

namespace SphericalHarmonics

/-- Zonal continuous functions obtained by evaluating a univariate polynomial on the height
coordinate. -/
noncomputable def zonalFromPolynomial (q : Polynomial ℝ) : C(S2, ℝ) where
  toFun x := Polynomial.eval (x.1 (2 : Fin 3)) q
  continuous_toFun := by
    simpa [height] using
      ((Polynomial.continuous_eval₂ q (RingHom.id ℝ)).comp
        ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (2 : Fin 3)).comp continuous_subtype_val))

@[simp] theorem zonalFromPolynomial_apply (q : Polynomial ℝ) (x : S2) :
    zonalFromPolynomial q x = Polynomial.eval (x.1 (2 : Fin 3)) q := rfl

theorem zonalFromPolynomial_isZonal (q : Polynomial ℝ) :
    IsZonal northPole (zonalFromPolynomial q) := by
  unfold IsZonal
  intro x y hxy
  have hh : x.1 (2 : Fin 3) = y.1 (2 : Fin 3) := by
    simpa [inner_northPole] using hxy
  simp [zonalFromPolynomial, hh]

/-- The algebra map sending a univariate polynomial `q(t)` to the ambient polynomial `q(z)`,
where `z = x₃`. -/
noncomputable def northPolynomialEmbedding : Polynomial ℝ →ₐ[ℝ] Poly3 :=
  Polynomial.aeval (MvPolynomial.X (2 : Fin 3))

@[simp] theorem northPolynomialEmbedding_X :
    northPolynomialEmbedding Polynomial.X = (MvPolynomial.X (2 : Fin 3) : Poly3) := by
  simp [northPolynomialEmbedding]

@[simp] theorem restrict_northPolynomialEmbedding (q : Polynomial ℝ) :
    restrictToSphere (northPolynomialEmbedding q) = zonalFromPolynomial q := by
  ext x
  simpa [northPolynomialEmbedding, zonalFromPolynomial] using
    (congrArg (fun g : Polynomial ℝ →ₐ[ℝ] ℝ => g q)
      (Polynomial.aeval_algHom (MvPolynomial.aeval x.1.ofLp) (MvPolynomial.X (2 : Fin 3)))).symm

/-- The degree-`0` zonal mode. -/
noncomputable def zonal0 : C(S2, ℝ) := zonalFromPolynomial 1

/-- The degree-`1` zonal mode. -/
noncomputable def zonal1 : C(S2, ℝ) := zonalFromPolynomial Polynomial.X

/-- The scaled degree-`2` Legendre mode `3 z^2 - 1`. -/
noncomputable def zonal2 : C(S2, ℝ) :=
  zonalFromPolynomial (3 * Polynomial.X ^ 2 - 1)

@[simp] theorem zonal0_apply (x : S2) : zonal0 x = 1 := by
  simp [zonal0, zonalFromPolynomial]

@[simp] theorem zonal1_apply (x : S2) : zonal1 x = x.1 (2 : Fin 3) := by
  simp [zonal1, zonalFromPolynomial]

@[simp] theorem zonal2_apply (x : S2) : zonal2 x = 3 * x.1 (2 : Fin 3) ^ 2 - 1 := by
  simp [zonal2, zonalFromPolynomial]

@[simp] theorem zonal0_isZonal : IsZonal northPole zonal0 :=
  zonalFromPolynomial_isZonal 1

@[simp] theorem zonal1_isZonal : IsZonal northPole zonal1 :=
  zonalFromPolynomial_isZonal Polynomial.X

@[simp] theorem zonal2_isZonal : IsZonal northPole zonal2 :=
  zonalFromPolynomial_isZonal (3 * Polynomial.X ^ 2 - 1)

/-- Constant ambient polynomial representative of the degree-`0` mode. -/
noncomputable abbrev northConstantAmbient : Poly3 := 1

/-- Ambient linear polynomial representative of the degree-`1` north-zonal mode. -/
noncomputable abbrev northLinearAmbient : Poly3 := MvPolynomial.X (2 : Fin 3)

/-- Ambient harmonic quadratic representative of the scaled degree-`2` Legendre mode. -/
noncomputable def northQuadraticAmbient : Poly3 :=
  (3 : ℝ) • ((MvPolynomial.X (2 : Fin 3) : Poly3) ^ 2) - radiusSq

@[simp] theorem restrict_northConstantAmbient :
    restrictToSphere northConstantAmbient = zonal0 := by
  ext x
  simp [northConstantAmbient, zonal0, zonalFromPolynomial]

@[simp] theorem restrict_northLinearAmbient :
    restrictToSphere northLinearAmbient = zonal1 := by
  simpa [northLinearAmbient, zonal1] using restrict_northPolynomialEmbedding Polynomial.X

@[simp] theorem restrict_northQuadraticAmbient :
    restrictToSphere northQuadraticAmbient = zonal2 := by
  ext x
  simp [northQuadraticAmbient, zonal2, zonalFromPolynomial]

theorem northConstantAmbient_mem_harmonicHomogeneous :
    northConstantAmbient ∈ harmonicHomogeneousSubmodule 0 := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · change northConstantAmbient.IsHomogeneous 0
    simpa [northConstantAmbient] using (MvPolynomial.isHomogeneous_one (σ := Fin 3) (R := ℝ))
  · show laplacian northConstantAmbient = 0
    simp [northConstantAmbient, laplacian, Fin.sum_univ_three]

theorem northLinearAmbient_mem_harmonicHomogeneous :
    northLinearAmbient ∈ harmonicHomogeneousSubmodule 1 := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · change northLinearAmbient.IsHomogeneous 1
    simpa [northLinearAmbient] using
      (MvPolynomial.isHomogeneous_X (R := ℝ) (2 : Fin 3))
  · show laplacian northLinearAmbient = 0
    simp [northLinearAmbient, laplacian, Fin.sum_univ_three]

@[simp] theorem laplacian_northLinearSquare :
    laplacian ((northLinearAmbient : Poly3) ^ 2) = 2 := by
  have h2 : (MvPolynomial.pderiv 2) (2 : Poly3) = 0 := by
    simpa using (MvPolynomial.pderiv 2).map_natCast 2
  simp [northLinearAmbient, laplacian, Fin.sum_univ_three, h2]

theorem northQuadraticAmbient_mem_harmonicHomogeneous :
    northQuadraticAmbient ∈ harmonicHomogeneousSubmodule 2 := by
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · change northQuadraticAmbient.IsHomogeneous 2
    have hsq : (((3 : ℝ) • ((MvPolynomial.X (2 : Fin 3) : Poly3) ^ 2)) : Poly3).IsHomogeneous 2 := by
      simpa [Algebra.smul_def] using
        (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (2 : Fin 3) 2).C_mul (3 : ℝ)
    exact hsq.sub radiusSq_isHomogeneous
  · show laplacian northQuadraticAmbient = 0
    simp [northQuadraticAmbient, laplacian_northLinearSquare, laplacian_radiusSq]
    simpa [Algebra.smul_def] using
      congrArg (MvPolynomial.C (σ := Fin 3)) (show (3 : ℝ) * 2 - 6 = 0 by norm_num)

theorem zonal0_mem_sector : zonal0 ∈ sector 0 := by
  refine ⟨northConstantAmbient, northConstantAmbient_mem_harmonicHomogeneous, ?_⟩
  simpa using restrict_northConstantAmbient

theorem zonal1_mem_sector : zonal1 ∈ sector 1 := by
  refine ⟨northLinearAmbient, northLinearAmbient_mem_harmonicHomogeneous, ?_⟩
  simpa using restrict_northLinearAmbient

theorem zonal2_mem_sector : zonal2 ∈ sector 2 := by
  refine ⟨northQuadraticAmbient, northQuadraticAmbient_mem_harmonicHomogeneous, ?_⟩
  simpa using restrict_northQuadraticAmbient

/-- The standard degree-`0` Legendre polynomial. -/
noncomputable def legendre0 : Polynomial ℝ := 1

/-- The standard degree-`1` Legendre polynomial. -/
noncomputable def legendre1 : Polynomial ℝ := Polynomial.X

/-- The standard degree-`2` Legendre polynomial. -/
noncomputable def legendre2 : Polynomial ℝ :=
  Polynomial.C (3 / 2 : ℝ) * Polynomial.X ^ 2 - Polynomial.C (1 / 2 : ℝ)

@[simp] theorem zonalFromPolynomial_legendre0 :
    zonalFromPolynomial legendre0 = zonal0 := by
  rfl

@[simp] theorem zonalFromPolynomial_legendre1 :
    zonalFromPolynomial legendre1 = zonal1 := by
  rfl

@[simp] theorem two_smul_zonalFromPolynomial_legendre2 :
    (2 : ℝ) • zonalFromPolynomial legendre2 = zonal2 := by
  ext x
  simp [legendre2, zonal2, zonalFromPolynomial]
  ring

theorem zonalFromPolynomial_legendre2_mem_sector :
    zonalFromPolynomial legendre2 ∈ sector 2 := by
  have h := zonal2_mem_sector
  have hscale : zonalFromPolynomial legendre2 = (1 / 2 : ℝ) • zonal2 := by
    ext x
    simp [legendre2, zonal2, zonalFromPolynomial]
    ring
  rw [hscale]
  exact (sector 2).smul_mem _ h

end SphericalHarmonics
