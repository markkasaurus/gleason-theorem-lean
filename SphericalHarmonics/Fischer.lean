import SphericalHarmonics.LowDegree

open scoped BigOperators

namespace SphericalHarmonics

/-- The multi-indices in `ℝ^3` of total degree `n`. -/
abbrev DegreeExponents (n : ℕ) := {d : Fin 3 →₀ ℕ // d.degree = n}

instance (n : ℕ) : Finite (DegreeExponents n) := by
  classical
  let f : DegreeExponents n → Fin 3 → Fin (n + 1) := fun d i =>
    ⟨d.1 i, Nat.lt_succ_of_le <| by
      have hsingle : d.1 i ≤ d.1.degree := by
        by_cases hi : d.1 i = 0
        · simp [Finsupp.degree, hi]
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finsupp.mem_support_iff.mpr hi)
      exact hsingle.trans_eq d.2⟩
  refine Finite.of_injective f ?_
  intro a b hab
  apply Subtype.ext
  ext i
  exact congrArg Fin.val <| congrArg (fun g => g i) hab

noncomputable instance (n : ℕ) : Fintype (DegreeExponents n) := Fintype.ofFinite _

/-- The factorial weight `d! = ∏ᵢ dᵢ!` used in Fischer's inner product. -/
noncomputable def multiFactorial (d : Fin 3 →₀ ℕ) : ℝ :=
  ∏ i : Fin 3, (Nat.factorial (d i) : ℝ)

theorem multiFactorial_pos (d : Fin 3 →₀ ℕ) : 0 < multiFactorial d := by
  classical
  unfold multiFactorial
  positivity

theorem multiFactorial_ne_zero (d : Fin 3 →₀ ℕ) : multiFactorial d ≠ 0 :=
  (multiFactorial_pos d).ne'

theorem multiFactorial_add_single (d : Fin 3 →₀ ℕ) (i : Fin 3) :
    multiFactorial (d + Finsupp.single i 1) = (d i + 1 : ℝ) * multiFactorial d := by
  fin_cases i <;>
    simp [multiFactorial, Fin.prod_univ_three, Nat.factorial_succ, Nat.cast_add, Nat.cast_mul,
      Nat.cast_one, mul_assoc, mul_left_comm, mul_comm]

/-- The coefficient formula for partial derivatives. -/
theorem coeff_pderiv (i : Fin 3) (d : Fin 3 →₀ ℕ) (p : Poly3) :
    MvPolynomial.coeff d (MvPolynomial.pderiv i p) =
      (d i + 1 : ℝ) * MvPolynomial.coeff (d + Finsupp.single i 1) p := by
  classical
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro s a
    by_cases hs : s = d + Finsupp.single i 1
    · subst hs
      rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
      have hle : Finsupp.single i 1 ≤ d + Finsupp.single i 1 := by
        intro j
        by_cases hji : j = i
        · subst hji
          simp
        · simp [Finsupp.single_apply, hji]
      simp [tsub_add_cancel_of_le hle]
      ring
    · rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
      by_cases hsi : s i = 0
      · simp [hs, hsi]
      · have hsub : s - Finsupp.single i 1 ≠ d := by
          intro hsd
          apply hs
          calc
            s = (s - Finsupp.single i 1) + Finsupp.single i 1 := by
              simpa using (Finsupp.sub_add_single_one_cancel hsi).symm
            _ = d + Finsupp.single i 1 := by simp [hsd]
        simp [hs, hsi, hsub]
  · intro p q hp hq
    rw [map_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add, add_mul]
    ring

/-- The Fischer functional in the left variable. -/
noncomputable def fischerLinear (q : Poly3) : Poly3 →ₗ[ℝ] ℝ :=
  (MvPolynomial.basisMonomials (Fin 3) ℝ).constr ℝ
    (fun d => multiFactorial d * MvPolynomial.coeff d q)

/-- Fischer's bilinear form. -/
noncomputable def fischer (p q : Poly3) : ℝ :=
  fischerLinear q p

theorem fischer_eq_sum (p q : Poly3) :
    fischer p q =
      Finset.sum p.support
        (fun d => multiFactorial d * MvPolynomial.coeff d p * MvPolynomial.coeff d q) := by
  classical
  unfold fischer fischerLinear
  rw [Module.Basis.constr_apply, MvPolynomial.basisMonomials, Finsupp.basisSingleOne_repr,
    MvPolynomial.sum_def]
  change
    ∑ x ∈ MvPolynomial.support p,
      MvPolynomial.coeff x p * (multiFactorial x * MvPolynomial.coeff x q) =
        ∑ x ∈ MvPolynomial.support p,
          multiFactorial x * MvPolynomial.coeff x p * MvPolynomial.coeff x q
  refine Finset.sum_congr rfl ?_
  intro d hd
  ring

theorem fischer_add_left (p q r : Poly3) :
    fischer (p + q) r = fischer p r + fischer q r := by
  simp [fischer]

theorem fischer_smul_left (a : ℝ) (p q : Poly3) :
    fischer (a • p) q = a * fischer p q := by
  simp [fischer]

theorem fischer_sum_left {ι : Type*} (s : Finset ι) (f : ι → Poly3) (q : Poly3) :
    fischer (∑ i ∈ s, f i) q = ∑ i ∈ s, fischer (f i) q := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [fischer]
  · intro i s hi hs
    simp [hi, fischer_add_left, hs]

theorem fischer_add_right (p q r : Poly3) :
    fischer p (q + r) = fischer p q + fischer p r := by
  rw [fischer_eq_sum, fischer_eq_sum, fischer_eq_sum]
  simp [Finset.sum_add_distrib, mul_add, add_mul]

theorem fischer_smul_right (a : ℝ) (p q : Poly3) :
    fischer p (a • q) = a * fischer p q := by
  rw [fischer_eq_sum, fischer_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  simp [mul_assoc, mul_left_comm, mul_comm]

theorem fischer_sum_right {ι : Type*} (s : Finset ι) (p : Poly3) (f : ι → Poly3) :
    fischer p (∑ i ∈ s, f i) = ∑ i ∈ s, fischer p (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [fischer_eq_sum]
  · intro i s hi hs
    simp [hi, fischer_add_right, hs]

theorem fischer_zero_left (q : Poly3) : fischer 0 q = 0 := by
  simp [fischer]

theorem fischer_zero_right (p : Poly3) : fischer p 0 = 0 := by
  rw [fischer_eq_sum]
  simp

theorem fischer_monomial_one_left (d : Fin 3 →₀ ℕ) (q : Poly3) :
    fischer (MvPolynomial.monomial d 1) q = multiFactorial d * MvPolynomial.coeff d q := by
  rw [fischer_eq_sum]
  simp

theorem fischer_monomial_left (d : Fin 3 →₀ ℕ) (a : ℝ) (q : Poly3) :
    fischer (MvPolynomial.monomial d a) q = a * multiFactorial d * MvPolynomial.coeff d q := by
  rw [show MvPolynomial.monomial d a = a • MvPolynomial.monomial d (1 : ℝ) by
      simpa using (MvPolynomial.smul_monomial (s := d) (a := (1 : ℝ)) a).symm]
  rw [fischer_smul_left, fischer_monomial_one_left]
  ring

/-- Multiplication by a coordinate is adjoint to the corresponding partial derivative for Fischer's
pairing. -/
theorem fischer_X_mul (i : Fin 3) (p q : Poly3) :
    fischer (MvPolynomial.X i * p) q = fischer p (MvPolynomial.pderiv i q) := by
  classical
  rw [p.as_sum, Finset.mul_sum, fischer_sum_left, fischer_sum_left]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hX :
      MvPolynomial.X i * MvPolynomial.monomial d (MvPolynomial.coeff d p) =
        MvPolynomial.monomial (d + Finsupp.single i 1) (MvPolynomial.coeff d p) := by
    simpa [MvPolynomial.X, add_comm, add_left_comm, add_assoc] using
      (MvPolynomial.monomial_mul :
        MvPolynomial.monomial d (MvPolynomial.coeff d p) *
          MvPolynomial.monomial (Finsupp.single i 1) (1 : ℝ) =
            MvPolynomial.monomial (d + Finsupp.single i 1) (MvPolynomial.coeff d p * 1))
  rw [hX, fischer_monomial_left, fischer_monomial_left, coeff_pderiv, multiFactorial_add_single]
  ring

theorem fischer_radiusSq_mul (p q : Poly3) :
    fischer (radiusSq * p) q = fischer p (laplacian q) := by
  classical
  unfold radiusSq laplacian
  rw [Finset.sum_mul, fischer_sum_left]
  simp_rw [pow_two, mul_assoc, fischer_X_mul]
  simpa using
    (fischer_sum_right (s := Finset.univ) p
      (fun i => MvPolynomial.pderiv i (MvPolynomial.pderiv i q))).symm

theorem fischer_self_pos {p : Poly3} (hp : p ≠ 0) : 0 < fischer p p := by
  classical
  rcases (MvPolynomial.ne_zero_iff).mp hp with ⟨d, hd⟩
  have hd' : d ∈ p.support := MvPolynomial.mem_support_iff.mpr hd
  have hterm : 0 < multiFactorial d * MvPolynomial.coeff d p * MvPolynomial.coeff d p := by
    have hmf : 0 < multiFactorial d := multiFactorial_pos d
    have hsq : 0 < MvPolynomial.coeff d p * MvPolynomial.coeff d p := by
      nlinarith [sq_pos_of_ne_zero hd]
    nlinarith
  have hnonneg :
      ∀ e ∈ p.support, 0 ≤ multiFactorial e * MvPolynomial.coeff e p * MvPolynomial.coeff e p := by
    intro e he
    have hmf : 0 ≤ multiFactorial e := (multiFactorial_pos e).le
    nlinarith [hmf, sq_nonneg (MvPolynomial.coeff e p)]
  calc
    0 < multiFactorial d * MvPolynomial.coeff d p * MvPolynomial.coeff d p := hterm
    _ ≤ fischer p p := by
      rw [fischer_eq_sum]
      exact Finset.single_le_sum hnonneg hd'

theorem fischer_self_eq_zero {p : Poly3} (h : fischer p p = 0) : p = 0 := by
  by_contra hp
  exact (fischer_self_pos hp).ne' h

theorem radiusSq_ne_zero : radiusSq ≠ 0 := by
  intro h
  have : laplacian radiusSq = 0 := by simpa [h] using LinearMap.map_zero laplacian
  norm_num at this

/-- Multiplication by `radiusSq` on homogeneous polynomials. -/
noncomputable def radiusSqMulHomogeneous (n : ℕ) :
    homogeneousSubmodule n →ₗ[ℝ] homogeneousSubmodule (n + 2) where
  toFun p :=
    ⟨radiusSq * p.1, by
      simpa [add_comm, add_left_comm, add_assoc] using radiusSq_isHomogeneous.mul p.2⟩
  map_add' p q := by
    ext
    simp [left_distrib]
  map_smul' a p := by
    ext
    simp [smul_mul_assoc]

/-- The Laplacian on homogeneous polynomials, lowering degree by `2`. -/
noncomputable def laplacianHomogeneous (n : ℕ) :
    homogeneousSubmodule (n + 2) →ₗ[ℝ] homogeneousSubmodule n where
  toFun p :=
    ⟨laplacian p.1, by
      simpa using laplacian_isHomogeneous p.2⟩
  map_add' p q := by
    ext
    simp
  map_smul' a p := by
    ext
    simp

instance homogeneousSubmodule_moduleFinite (n : ℕ) : Module.Finite ℝ (homogeneousSubmodule n) := by
  classical
  let s : Set (Fin 3 →₀ ℕ) := {d | d.degree = n}
  have hs : Finite s := by
    simpa [DegreeExponents, s] using (show Finite (DegreeExponents n) by infer_instance)
  let e :
      homogeneousSubmodule n ≃ₗ[ℝ] Finsupp.supported ℝ ℝ s :=
    LinearEquiv.ofEq _ _ <| by
      simpa [s] using
        (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (σ := Fin 3) (R := ℝ) n)
  exact Module.Finite.of_basis <| (MvPolynomial.basisRestrictSupport (R := ℝ) s).map e.symm

/-- The key endomorphism `Δ ∘ (radiusSq ·)` on homogeneous polynomials. -/
noncomputable def laplacianRadiusSqHomogeneous (n : ℕ) :
    homogeneousSubmodule n →ₗ[ℝ] homogeneousSubmodule n :=
  (laplacianHomogeneous n).comp (radiusSqMulHomogeneous n)

theorem laplacianRadiusSqHomogeneous_injective (n : ℕ) :
    Function.Injective (laplacianRadiusSqHomogeneous n) := by
  intro p q hpq
  have hzero : laplacianRadiusSqHomogeneous n (p - q) = 0 := by
    simpa [LinearMap.map_sub, hpq]
  let a : Poly3 := ((p - q : homogeneousSubmodule n) : Poly3)
  have hpair :
      fischer (radiusSq * a) (radiusSq * a)
        = 0 := by
    have hL :
        laplacian (radiusSq * a) = 0 := by
      exact congrArg Subtype.val hzero
    calc
      fischer (radiusSq * a) (radiusSq * a) = fischer a (laplacian (radiusSq * a)) := by
        simpa [a] using fischer_radiusSq_mul a (radiusSq * a)
      _ = 0 := by simp [hL, fischer_zero_right]
  have hr : radiusSq * a = 0 :=
    fischer_self_eq_zero hpair
  have hpq' : ((p - q : homogeneousSubmodule n) : Poly3) = 0 := by
    exact (mul_eq_zero.mp hr).resolve_left radiusSq_ne_zero
  exact Subtype.ext <| sub_eq_zero.mp hpq'

theorem laplacianRadiusSqHomogeneous_surjective (n : ℕ) :
    Function.Surjective (laplacianRadiusSqHomogeneous n) :=
  (LinearMap.injective_iff_surjective (f := laplacianRadiusSqHomogeneous n)).mp
    (laplacianRadiusSqHomogeneous_injective n)

/-- The one-step Fischer decomposition on homogeneous polynomials in `ℝ^3`. -/
theorem exists_harmonic_add_radiusSq_mul_of_mem_homogeneousSubmodule {n : ℕ} {p : Poly3}
    (hp : p ∈ homogeneousSubmodule (n + 2)) :
    ∃ h q : Poly3,
      h ∈ harmonicHomogeneousSubmodule (n + 2) ∧
      q ∈ homogeneousSubmodule n ∧
      p = h + radiusSq * q := by
  let dp : homogeneousSubmodule n := ⟨laplacian p, by
    simpa using laplacian_isHomogeneous ((MvPolynomial.mem_homogeneousSubmodule (n + 2) p).mp hp)⟩
  obtain ⟨q, hq⟩ := laplacianRadiusSqHomogeneous_surjective n dp
  let h : Poly3 := p - radiusSq * q
  refine ⟨h, q, ?_, q.2, ?_⟩
  · refine Submodule.mem_inf.mpr ?_
    constructor
    · have hp' : p.IsHomogeneous (n + 2) := (MvPolynomial.mem_homogeneousSubmodule (n + 2) p).mp hp
      have hq' : (radiusSq * (q : Poly3)).IsHomogeneous (n + 2) := by
        simpa [add_comm, add_left_comm, add_assoc] using radiusSq_isHomogeneous.mul q.2
      exact hp'.sub hq'
    · show laplacian h = 0
      have hq' : laplacian (radiusSq * (q : Poly3)) = laplacian p := by
        exact congrArg Subtype.val hq
      simp [h, hq']
  · simp [h, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

theorem restrict_mem_iSup_sector_of_mem_homogeneousSubmodule :
    ∀ {n : ℕ} {p : Poly3}, p ∈ homogeneousSubmodule n → restrictToSphere p ∈ ⨆ m : ℕ, sector m
  | 0, p, hp => by
      exact Submodule.mem_iSup_of_mem 0 <|
        restrict_mem_sector_zero_of_mem_homogeneousSubmodule hp
  | 1, p, hp => by
      exact Submodule.mem_iSup_of_mem 1 <|
        restrict_mem_sector_one_of_mem_homogeneousSubmodule hp
  | n + 2, p, hp => by
      rcases exists_harmonic_add_radiusSq_mul_of_mem_homogeneousSubmodule hp with
        ⟨h, q, hh, hq, rfl⟩
      have hh' : restrictToSphere h ∈ ⨆ m : ℕ, sector m :=
        Submodule.mem_iSup_of_mem (n + 2) <| restrict_mem_sector hh
      have hq' : restrictToSphere q ∈ ⨆ m : ℕ, sector m :=
        restrict_mem_iSup_sector_of_mem_homogeneousSubmodule hq
      have hq'' : restrictToSphere (radiusSq * q) ∈ ⨆ m : ℕ, sector m := by
        simpa using hq'
      have hadd : restrictToSphere h + restrictToSphere (radiusSq * q) ∈ ⨆ m : ℕ, sector m :=
        Submodule.add_mem (⨆ m : ℕ, sector m) hh' hq''
      simpa [restrictToSphere_radiusSq_mul] using hadd

/-- Every polynomial restriction on `S²` decomposes into harmonic degree sectors. -/
theorem restrict_mem_iSup_sector (p : Poly3) :
    restrictToSphere p ∈ ⨆ n : ℕ, sector n := by
  classical
  rw [← MvPolynomial.sum_homogeneousComponent (φ := p)]
  rw [map_sum]
  refine Submodule.sum_mem (⨆ n : ℕ, sector n) ?_
  intro n hn
  exact restrict_mem_iSup_sector_of_mem_homogeneousSubmodule
    ((MvPolynomial.mem_homogeneousSubmodule n _).mpr
      (MvPolynomial.homogeneousComponent_isHomogeneous (n := n) (φ := p)))

end SphericalHarmonics
