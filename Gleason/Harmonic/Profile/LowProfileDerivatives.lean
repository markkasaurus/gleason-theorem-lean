import Gleason.Harmonic.Zonal.NorthZonalSectorQ02
import Gleason.Harmonic.GreatCircle.GreatCirclePointEndpoint
import Gleason.Harmonic.Zonal.NorthZonalQuadraticRepresentation
import Gleason.Harmonic.Rotation.RotatedSector

noncomputable section

open Complex InnerProductSpace

lemma continuousHarmonicSphereDegreeSup_zero_two_le_continuousSphereGreatCirclePointConstraintSubmodule :
    continuousHarmonicSphereDegreeSubmodule 0 ⊔
        continuousHarmonicSphereDegreeSubmodule 2 ≤
      continuousSphereGreatCirclePointConstraintSubmodule := by
  rw [sup_le_iff]
  exact
    ⟨continuousHarmonicSphereDegreeSubmodule_zero_le_continuousSphereGreatCirclePointConstraintSubmodule,
      continuousHarmonicSphereDegreeSubmodule_two_le_continuousSphereGreatCirclePointConstraintSubmodule⟩

theorem harmonicAt_second_directional_sum_zero
    {f : WithLp 2 (ℂ × ℝ) → ℝ} {p : WithLp 2 (ℂ × ℝ)}
    (hf : HarmonicAt f p) :
    iteratedDeriv 2 (fun s : ℝ => f (p + s • complexOneVec)) 0 +
        iteratedDeriv 2 (fun s : ℝ => f (p + s • complexIVec)) 0 +
        iteratedDeriv 2 (fun s : ℝ => f (p + s • realUnitVec)) 0 = 0 := by
  let M := iteratedFDeriv ℝ 2 f p
  have hcont : ContDiffAt ℝ 2 f p := hf.1
  have hx :
      M ![complexOneVec, complexOneVec] =
        iteratedDeriv 2 (fun s : ℝ => f (p + s • complexOneVec)) 0 := by
    symm
    simpa [M] using (iteratedDeriv_two_comp_add_smul (x := p) (v := complexOneVec) hcont)
  have hy :
      M ![complexIVec, complexIVec] =
        iteratedDeriv 2 (fun s : ℝ => f (p + s • complexIVec)) 0 := by
    symm
    simpa [M] using (iteratedDeriv_two_comp_add_smul (x := p) (v := complexIVec) hcont)
  have hz :
      M ![realUnitVec, realUnitVec] =
        iteratedDeriv 2 (fun s : ℝ => f (p + s • realUnitVec)) 0 := by
    symm
    simpa [M] using (iteratedDeriv_two_comp_add_smul (x := p) (v := realUnitVec) hcont)
  have hΔ : Δ f p = 0 := by
    simpa using hf.2.eq_of_nhds
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := f) complexRealBasis] at hΔ
  simp [complexRealBasis, complexBasis, realBasis, OrthonormalBasis.prod_apply, Fin.sum_univ_two] at hΔ
  rw [hx, hy, hz] at hΔ
  simpa [add_assoc] using hΔ

lemma hasDerivAt_one_add_sq (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
  simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using
    (((hasDerivAt_id t).pow 2).const_add (1 : ℝ))

lemma iteratedDeriv_two_one_add_sq :
    iteratedDeriv 2 (fun s : ℝ => 1 + s ^ 2) 0 = 2 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ => 1 + s ^ 2) = fun s => 2 * s := by
    funext s
    exact (hasDerivAt_one_add_sq s).deriv
  rw [hderiv]
  simpa [two_mul] using ((hasDerivAt_id 0).const_mul (2 : ℝ)).deriv

lemma iteratedDeriv_two_one_add_sq_pow (k : ℕ) :
    iteratedDeriv 2 (fun s : ℝ => (1 + s ^ 2) ^ k) 0 = 2 * (k : ℝ) := by
  have hg : ContDiffAt ℝ 2 (fun u : ℝ => u ^ k) (1 : ℝ) := by
    simpa using ((contDiff_id.pow k).contDiffAt : ContDiffAt ℝ 2 (fun u : ℝ => u ^ k) 1)
  have hf : ContDiffAt ℝ 2 (fun s : ℝ => 1 + s ^ 2) (0 : ℝ) := by
    simpa using (((contDiff_const.add (contDiff_id.pow 2)).contDiffAt) :
      ContDiffAt ℝ 2 (fun s : ℝ => 1 + s ^ 2) 0)
  have hg' : ContDiffAt ℝ 2 (fun u : ℝ => u ^ k) ((fun s : ℝ => 1 + s ^ 2) 0) := by
    simpa using hg
  have hcomp :=
    iteratedDeriv_vcomp_two (g := fun u : ℝ => u ^ k) (f := fun s : ℝ => 1 + s ^ 2) (x := 0) hg' hf
  have hder0 : deriv (fun s : ℝ => 1 + s ^ 2) 0 = 0 := by
    simpa using (hasDerivAt_one_add_sq 0).deriv
  have hiter0 : iteratedDeriv 2 (fun s : ℝ => 1 + s ^ 2) 0 = 2 := iteratedDeriv_two_one_add_sq
  have hfirst :
      fderiv ℝ (fun u : ℝ => u ^ k) 1 (iteratedDeriv 2 (fun s : ℝ => 1 + s ^ 2) 0)
        = 2 * (k : ℝ) := by
    rw [hiter0, fderiv_eq_deriv_mul]
    have hpow :
        deriv (fun u : ℝ => u ^ k) 1 = (k : ℝ) * 1 ^ (k - 1) := by
      simpa using deriv_pow (differentiableAt_id : DifferentiableAt ℝ (fun u : ℝ => u) 1) k
    rw [hpow]
    ring
  have hzero :
      iteratedFDeriv ℝ 2 (fun u : ℝ => u ^ k) 1 (fun _ : Fin 2 => deriv (fun s : ℝ => 1 + s ^ 2) 0)
        = 0 := by
    rw [hder0]
    exact (iteratedFDeriv ℝ 2 (fun u : ℝ => u ^ k) (1 : ℝ)).map_coord_zero 0 rfl
  have hzero' :
      iteratedFDeriv ℝ 2 (fun u : ℝ => u ^ k) 1 (fun _ : Fin 2 => (0 : ℝ)) = 0 := by
    exact (iteratedFDeriv ℝ 2 (fun u : ℝ => u ^ k) (1 : ℝ)).map_coord_zero 0 rfl
  have hcomp' :
      iteratedDeriv 2 (fun s : ℝ => (1 + s ^ 2) ^ k) 0 =
        iteratedFDeriv ℝ 2 (fun u : ℝ => u ^ k) 1 (fun _ : Fin 2 => 0) + 2 * (k : ℝ) := by
    simpa [Function.comp, hder0, hiter0, hfirst] using hcomp
  rw [hzero'] at hcomp'
  simpa using hcomp'

  lemma iteratedDeriv_two_sq_mul_one_add_sq_pow (k : ℕ) :
    iteratedDeriv 2 (fun s : ℝ => s ^ 2 * (1 + s ^ 2) ^ k) 0 = 2 := by
  have hEq :
      (fun s : ℝ => s ^ 2 * (1 + s ^ 2) ^ k) =
        fun s : ℝ => (1 + s ^ 2) ^ (k + 1) - (1 + s ^ 2) ^ k := by
    funext s
    ring
  rw [hEq]
  have hsub :=
    iteratedDeriv_sub
      ((((contDiff_const.add (contDiff_id.pow 2)).pow (k + 1)).contDiffAt :
        ContDiffAt ℝ 2 (fun s : ℝ => (1 + s ^ 2) ^ (k + 1)) 0))
      ((((contDiff_const.add (contDiff_id.pow 2)).pow k).contDiffAt :
        ContDiffAt ℝ 2 (fun s : ℝ => (1 + s ^ 2) ^ k) 0))
  have hsub' :
      iteratedDeriv 2 (fun s : ℝ => (1 + s ^ 2) ^ (k + 1) - (1 + s ^ 2) ^ k) 0 =
        iteratedDeriv 2 (fun s : ℝ => (1 + s ^ 2) ^ (k + 1)) 0 -
          iteratedDeriv 2 (fun s : ℝ => (1 + s ^ 2) ^ k) 0 := by
    simpa using hsub
  have haux : 2 * ((k + 1 : ℕ) : ℝ) - 2 * (k : ℝ) = 2 := by
    calc
      2 * ((k + 1 : ℕ) : ℝ) - 2 * (k : ℝ)
        = 2 * ((k : ℝ) + 1) - 2 * (k : ℝ) := by norm_num [Nat.cast_add]
      _ = 2 := by ring
  rw [iteratedDeriv_two_one_add_sq_pow, iteratedDeriv_two_one_add_sq_pow] at hsub'
  calc
    iteratedDeriv 2 (fun s : ℝ => (1 + s ^ 2) ^ (k + 1) - (1 + s ^ 2) ^ k) 0
      = 2 * ((k + 1 : ℕ) : ℝ) - 2 * (k : ℝ) := hsub'
    _ = 2 := haux

lemma complexOne_add_smul_complexIVec_eq (t : ℝ) :
    complexOneVec + t • complexIVec =
      WithLp.toLp 2 (((1 : ℂ) + (t : ℂ) * Complex.I), (0 : ℝ)) := by
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  simp [complexOneVec, complexIVec, add_comm, add_left_comm, add_assoc, mul_comm]

lemma complexOne_add_smul_realUnitVec_eq (t : ℝ) :
    complexOneVec + t • realUnitVec =
      WithLp.toLp 2 (((1 : ℂ)), t) := by
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  simp [complexOneVec, realUnitVec, add_comm, add_left_comm, add_assoc]

lemma realUnit_add_smul_complexOneVec_eq (t : ℝ) :
    realUnitVec + t • complexOneVec =
      WithLp.toLp 2 (((t : ℂ)), (1 : ℝ)) := by
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  simp [complexOneVec, realUnitVec, add_comm, add_left_comm, add_assoc]

lemma norm_sq_complexOne_add_smul_complexIVec (t : ℝ) :
    ‖complexOneVec + t • complexIVec‖ ^ 2 = 1 + t ^ 2 := by
  rw [complexOne_add_smul_complexIVec_eq, WithLp.norm_toLp_fst]
  have hsq : ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [pow_two, mul_comm] using (Complex.normSq_add_mul_I (1 : ℝ) t)
  simpa using hsq

lemma norm_sq_complexOne_add_smul_realUnitVec (t : ℝ) :
    ‖complexOneVec + t • realUnitVec‖ ^ 2 = 1 + t ^ 2 := by
  let x : WithLp 2 (ℂ × ℝ) := WithLp.toLp 2 (((1 : ℂ)), t)
  have hp : 0 < ((2 : ENNReal).toReal) := by norm_num
  have hnorm :
      ‖x‖ =
        (‖(1 : ℂ)‖ ^ (2 : ℝ) + ‖t‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [x] using (WithLp.prod_norm_eq_add (p := (2 : ENNReal)) hp x)
  have hnorm' :
      ‖x‖ =
        Real.sqrt (‖(1 : ℂ)‖ ^ (2 : ℝ) + ‖t‖ ^ (2 : ℝ)) := by
    simpa [Real.sqrt_eq_rpow] using hnorm
  have hx : x = complexOneVec + t • realUnitVec := by
    symm
    exact complexOne_add_smul_realUnitVec_eq t
  have hnonneg : 0 ≤ ‖(1 : ℂ)‖ ^ (2 : ℝ) + ‖t‖ ^ (2 : ℝ) := by positivity
  have hnormsq :
      ‖complexOneVec + t • realUnitVec‖ * ‖complexOneVec + t • realUnitVec‖ =
        Real.sqrt (‖(1 : ℂ)‖ ^ (2 : ℝ) + ‖t‖ ^ (2 : ℝ)) *
          Real.sqrt (‖(1 : ℂ)‖ ^ (2 : ℝ) + ‖t‖ ^ (2 : ℝ)) := by
    simpa [hx] using congrArg (fun r : ℝ => r * r) hnorm'
  have hsqrt :
      Real.sqrt (‖(1 : ℂ)‖ ^ (2 : ℝ) + ‖t‖ ^ (2 : ℝ)) *
          Real.sqrt (‖(1 : ℂ)‖ ^ (2 : ℝ) + ‖t‖ ^ (2 : ℝ)) =
        1 + t * t := by
    rw [← pow_two, Real.sq_sqrt hnonneg]
    simp [sq_abs, pow_two]
  simpa [pow_two] using hnormsq.trans hsqrt

lemma norm_sq_realUnit_add_smul_complexOneVec (t : ℝ) :
    ‖realUnitVec + t • complexOneVec‖ ^ 2 = 1 + t ^ 2 := by
  let x : WithLp 2 (ℂ × ℝ) := WithLp.toLp 2 (((t : ℂ)), (1 : ℝ))
  have hp : 0 < ((2 : ENNReal).toReal) := by norm_num
  have hnorm :
      ‖x‖ =
        (‖(t : ℂ)‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [x] using (WithLp.prod_norm_eq_add (p := (2 : ENNReal)) hp x)
  have hnorm' :
      ‖x‖ =
        Real.sqrt (‖(t : ℂ)‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) := by
    simpa [Real.sqrt_eq_rpow] using hnorm
  have hx : x = realUnitVec + t • complexOneVec := by
    symm
    exact realUnit_add_smul_complexOneVec_eq t
  have hnonneg : 0 ≤ ‖(t : ℂ)‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ) := by positivity
  have hnormsq :
      ‖realUnitVec + t • complexOneVec‖ * ‖realUnitVec + t • complexOneVec‖ =
        Real.sqrt (‖(t : ℂ)‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) *
          Real.sqrt (‖(t : ℂ)‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) := by
    simpa [hx] using congrArg (fun r : ℝ => r * r) hnorm'
  have hsqrt :
      Real.sqrt (‖(t : ℂ)‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) *
          Real.sqrt (‖(t : ℂ)‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) =
        t * t + 1 := by
    rw [← pow_two, Real.sq_sqrt hnonneg]
    simp [sq_abs, pow_two, add_comm]
  have hfinal : ‖realUnitVec + t • complexOneVec‖ ^ 2 = t * t + 1 := by
    simpa [pow_two] using hnormsq.trans hsqrt
  nlinarith

lemma norm_inv_smul_mem_sphere {p : WithLp 2 (ℂ × ℝ)} (hp : p ≠ 0) :
    ‖‖p‖⁻¹ • p‖ = 1 := by
  have hpnorm : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))]
  field_simp [hpnorm]

lemma sphereCoordZ_norm_inv_smul {p : WithLp 2 (ℂ × ℝ)} (hp : p ≠ 0) :
    sphereCoordZ ⟨‖p‖⁻¹ • p, norm_inv_smul_mem_sphere hp⟩ = realProjL p / ‖p‖ := by
  rw [show sphereCoordZ ⟨‖p‖⁻¹ • p, norm_inv_smul_mem_sphere hp⟩ = (‖p‖⁻¹ • p).snd by rfl]
  simp [realProjL, div_eq_mul_inv, mul_comm]

lemma even_degree_eval_of_sphere_low_profile
    {k : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree (2 * (k + 1)) f)
    (hfg : sphereRestrictionLinear f = g)
    {a b : ℝ}
    (hrep : ∀ x : spherePoint3, g x = a + b * sphereCoordZ x ^ 2)
    {p : WithLp 2 (ℂ × ℝ)} (hp : p ≠ 0) :
    f p = a * (‖p‖ ^ 2) ^ (k + 1) + b * (realProjL p) ^ 2 * (‖p‖ ^ 2) ^ k := by
  let x : spherePoint3 := ⟨‖p‖⁻¹ • p, norm_inv_smul_mem_sphere hp⟩
  have hpnorm : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have hxrep : f x.1 = a + b * (realProjL p / ‖p‖) ^ 2 := by
    calc
      f x.1 = g x := by simpa [x] using congrFun hfg x
      _ = a + b * sphereCoordZ x ^ 2 := hrep x
      _ = a + b * (realProjL p / ‖p‖) ^ 2 := by
            rw [sphereCoordZ_norm_inv_smul hp]
  have hp_eq : p = ‖p‖ • x.1 := by
    simp [x, hpnorm]
  have hscale : f (‖p‖ • x.1) = ‖p‖ ^ (2 * (k + 1)) * f x.1 := by
    simpa using hf.2 ‖p‖ x.1
  conv_lhs => rw [hp_eq]
  rw [hscale, hxrep]
  have hpow : ‖p‖ ^ (2 * (k + 1)) = (‖p‖ ^ 2) ^ (k + 1) := by
    rw [pow_mul]
  rw [hpow]
  field_simp [hpnorm]
  ring

lemma complexOne_add_smul_complexIVec_ne_zero (t : ℝ) :
    complexOneVec + t • complexIVec ≠ 0 := by
  intro h0
  have hnorm : ‖complexOneVec + t • complexIVec‖ ^ 2 = 0 := by simpa [h0]
  nlinarith [norm_sq_complexOne_add_smul_complexIVec t]

lemma complexOne_add_smul_realUnitVec_ne_zero (t : ℝ) :
    complexOneVec + t • realUnitVec ≠ 0 := by
  intro h0
  have hnorm : ‖complexOneVec + t • realUnitVec‖ ^ 2 = 0 := by simpa [h0]
  nlinarith [norm_sq_complexOne_add_smul_realUnitVec t]

lemma realUnit_add_smul_complexOneVec_ne_zero (t : ℝ) :
    realUnitVec + t • complexOneVec ≠ 0 := by
  intro h0
  have hnorm : ‖realUnitVec + t • complexOneVec‖ ^ 2 = 0 := by simpa [h0]
  nlinarith [norm_sq_realUnit_add_smul_complexOneVec t]

lemma realUnit_add_smul_complexIVec_eq (t : ℝ) :
    realUnitVec + t • complexIVec =
      WithLp.toLp 2 (((t : ℂ) * Complex.I), (1 : ℝ)) := by
  apply (WithLp.equiv 2 (ℂ × ℝ)).injective
  simp [complexIVec, realUnitVec, add_comm, mul_comm]

lemma norm_sq_realUnit_add_smul_complexIVec (t : ℝ) :
    ‖realUnitVec + t • complexIVec‖ ^ 2 = 1 + t ^ 2 := by
  let x : WithLp 2 (ℂ × ℝ) := WithLp.toLp 2 (((t : ℂ) * Complex.I), (1 : ℝ))
  have hp : 0 < ((2 : ENNReal).toReal) := by norm_num
  have hnorm :
      ‖x‖ =
        (‖(t : ℂ) * Complex.I‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    simpa [x] using (WithLp.prod_norm_eq_add (p := (2 : ENNReal)) hp x)
  have hnorm' :
      ‖x‖ =
        Real.sqrt (‖(t : ℂ) * Complex.I‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) := by
    simpa [Real.sqrt_eq_rpow] using hnorm
  have hx : x = realUnitVec + t • complexIVec := by
    symm
    exact realUnit_add_smul_complexIVec_eq t
  have hnonneg : 0 ≤ ‖(t : ℂ) * Complex.I‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ) := by positivity
  have hnormsq :
      ‖realUnitVec + t • complexIVec‖ * ‖realUnitVec + t • complexIVec‖ =
        Real.sqrt (‖(t : ℂ) * Complex.I‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) *
          Real.sqrt (‖(t : ℂ) * Complex.I‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) := by
    simpa [hx] using congrArg (fun r : ℝ => r * r) hnorm'
  have hsqrt :
      Real.sqrt (‖(t : ℂ) * Complex.I‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) *
          Real.sqrt (‖(t : ℂ) * Complex.I‖ ^ (2 : ℝ) + ‖(1 : ℝ)‖ ^ (2 : ℝ)) =
        t * t + 1 := by
    rw [← pow_two, Real.sq_sqrt hnonneg]
    have hnormI : ‖(t : ℂ) * Complex.I‖ ^ (2 : ℝ) = t * t := by
      calc
        ‖(t : ℂ) * Complex.I‖ ^ (2 : ℝ) = Complex.normSq ((t : ℂ) * Complex.I) := by
          simpa using (Complex.normSq_eq_norm_sq (z := ((t : ℂ) * Complex.I))).symm
        _ = Complex.normSq (t : ℂ) * Complex.normSq Complex.I := by rw [Complex.normSq_mul]
        _ = t * t := by simp [Complex.normSq, pow_two]
    rw [hnormI]
    norm_num
  have hfinal : ‖realUnitVec + t • complexIVec‖ ^ 2 = t * t + 1 := by
    simpa [pow_two] using hnormsq.trans hsqrt
  nlinarith

lemma realUnit_add_smul_complexIVec_ne_zero (t : ℝ) :
    realUnitVec + t • complexIVec ≠ 0 := by
  intro h0
  have hnorm : ‖realUnitVec + t • complexIVec‖ ^ 2 = 0 := by simpa [h0]
  nlinarith [norm_sq_realUnit_add_smul_complexIVec t]

lemma even_degree_eval_complexOne_add_smul_complexIVec
    {k : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree (2 * (k + 1)) f)
    (hfg : sphereRestrictionLinear f = g)
    {a b : ℝ}
    (hrep : ∀ x : spherePoint3, g x = a + b * sphereCoordZ x ^ 2)
    (t : ℝ) :
    f (complexOneVec + t • complexIVec) = a * (1 + t ^ 2) ^ (k + 1) := by
  have hmain :=
    even_degree_eval_of_sphere_low_profile hf hfg hrep (complexOne_add_smul_complexIVec_ne_zero t)
  have hz : realProjL (complexOneVec + t • complexIVec) = 0 := by
    simp [realProjL, complexOneVec, complexIVec]
  rw [hz, norm_sq_complexOne_add_smul_complexIVec t] at hmain
  simpa [mul_assoc] using hmain

lemma even_degree_eval_complexOne_add_smul_realUnitVec
    {k : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree (2 * (k + 1)) f)
    (hfg : sphereRestrictionLinear f = g)
    {a b : ℝ}
    (hrep : ∀ x : spherePoint3, g x = a + b * sphereCoordZ x ^ 2)
    (t : ℝ) :
    f (complexOneVec + t • realUnitVec) =
      a * (1 + t ^ 2) ^ (k + 1) + b * t ^ 2 * (1 + t ^ 2) ^ k := by
  have hmain :=
    even_degree_eval_of_sphere_low_profile hf hfg hrep (complexOne_add_smul_realUnitVec_ne_zero t)
  have hz : (realProjL (complexOneVec + t • realUnitVec)) ^ 2 = t ^ 2 := by
    simp [realProjL, complexOneVec, realUnitVec, pow_two]
  rw [hz, norm_sq_complexOne_add_smul_realUnitVec t] at hmain
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmain

lemma even_degree_eval_realUnit_add_smul_complexOneVec
    {k : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree (2 * (k + 1)) f)
    (hfg : sphereRestrictionLinear f = g)
    {a b : ℝ}
    (hrep : ∀ x : spherePoint3, g x = a + b * sphereCoordZ x ^ 2)
    (t : ℝ) :
    f (realUnitVec + t • complexOneVec) =
      a * (1 + t ^ 2) ^ (k + 1) + b * (1 + t ^ 2) ^ k := by
  have hmain :=
    even_degree_eval_of_sphere_low_profile hf hfg hrep (realUnit_add_smul_complexOneVec_ne_zero t)
  have hz : (realProjL (realUnitVec + t • complexOneVec)) ^ 2 = 1 := by
    simp [realProjL, realUnitVec, complexOneVec, pow_two]
  rw [hz, norm_sq_realUnit_add_smul_complexOneVec t] at hmain
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmain

lemma even_degree_eval_realUnit_add_smul_complexIVec
    {k : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree (2 * (k + 1)) f)
    (hfg : sphereRestrictionLinear f = g)
    {a b : ℝ}
    (hrep : ∀ x : spherePoint3, g x = a + b * sphereCoordZ x ^ 2)
    (t : ℝ) :
    f (realUnitVec + t • complexIVec) =
      a * (1 + t ^ 2) ^ (k + 1) + b * (1 + t ^ 2) ^ k := by
  have hmain :=
    even_degree_eval_of_sphere_low_profile hf hfg hrep (realUnit_add_smul_complexIVec_ne_zero t)
  have hz : (realProjL (realUnitVec + t • complexIVec)) ^ 2 = 1 := by
    simp [realProjL, realUnitVec, complexIVec, pow_two]
  rw [hz, norm_sq_realUnit_add_smul_complexIVec t] at hmain
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmain

lemma even_degree_eval_complexOne_add_smul_complexOneVec
    {k : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree (2 * (k + 1)) f)
    (hfg : sphereRestrictionLinear f = g)
    {a b : ℝ}
    (hrep : ∀ x : spherePoint3, g x = a + b * sphereCoordZ x ^ 2)
    (t : ℝ) :
    f (complexOneVec + t • complexOneVec) = a * (1 + t) ^ (2 * (k + 1)) := by
  have hvec : complexOneVec + t • complexOneVec = (1 + t) • complexOneVec := by
    calc
      complexOneVec + t • complexOneVec = (1 : ℝ) • complexOneVec + t • complexOneVec := by simp
      _ = (1 + t) • complexOneVec := by rw [← add_smul]
  have hbase : f complexOneVec = a := by
    calc
      f complexOneVec = g sphereE1 := by simpa [sphereE1] using congrFun hfg sphereE1
      _ = a + b * sphereCoordZ sphereE1 ^ 2 := hrep sphereE1
      _ = a := by simp [sphereCoordZ, sphereE1]
  rw [hvec, hf.2 (1 + t) complexOneVec, hbase]
  ring

lemma even_degree_eval_realUnit_add_smul_realUnitVec
    {k : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ} {g : C(spherePoint3, ℝ)}
    (hf : HarmonicHomogeneousDegree (2 * (k + 1)) f)
    (hfg : sphereRestrictionLinear f = g)
    {a b : ℝ}
    (hrep : ∀ x : spherePoint3, g x = a + b * sphereCoordZ x ^ 2)
    (t : ℝ) :
    f (realUnitVec + t • realUnitVec) = (a + b) * (1 + t) ^ (2 * (k + 1)) := by
  have hvec : realUnitVec + t • realUnitVec = (1 + t) • realUnitVec := by
    calc
      realUnitVec + t • realUnitVec = (1 : ℝ) • realUnitVec + t • realUnitVec := by simp
      _ = (1 + t) • realUnitVec := by rw [← add_smul]
  have hbase : f realUnitVec = a + b := by
    calc
      f realUnitVec = g sphereE3 := by simpa [sphereE3] using congrFun hfg sphereE3
      _ = a + b * sphereCoordZ sphereE3 ^ 2 := hrep sphereE3
      _ = a + b := by simp [sphereCoordZ, sphereE3]
  rw [hvec, hf.2 (1 + t) realUnitVec, hbase]
  ring

lemma iteratedDeriv_two_axis_even_degree (k : ℕ) (a : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => a * (1 + s) ^ (2 * (k + 1))) 0 =
      a * ((2 * (k + 1) : ℕ) : ℝ) * ((2 * (k + 1) - 1 : ℕ) : ℝ) := by
  have hcont :
      ContDiffAt ℝ 2 (fun s : ℝ => (1 + s) ^ (2 * (k + 1))) 0 := by
    simpa [add_comm] using
      ((((contDiff_const.add contDiff_id).pow (2 * (k + 1))).contDiffAt) :
        ContDiffAt ℝ 2 (fun s : ℝ => (1 + s) ^ (2 * (k + 1))) 0)
  rw [iteratedDeriv_const_mul hcont a, iteratedDeriv_two_add_const_pow (by omega) 1]
  ring

lemma iteratedDeriv_two_normsq_even_degree (k : ℕ) (a : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1)) 0 =
      2 * a * (k + 1) := by
  have hcont :
      ContDiffAt ℝ 2 (fun s : ℝ => (1 + s ^ 2) ^ (k + 1)) 0 := by
    simpa using
      ((((contDiff_const.add (contDiff_id.pow 2)).pow (k + 1)).contDiffAt) :
        ContDiffAt ℝ 2 (fun s : ℝ => (1 + s ^ 2) ^ (k + 1)) 0)
  rw [iteratedDeriv_const_mul hcont a, iteratedDeriv_two_one_add_sq_pow]
  norm_num [Nat.cast_add]
  ring

lemma iteratedDeriv_two_equator_low_profile (k : ℕ) (a b : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1) + b * s ^ 2 * (1 + s ^ 2) ^ k) 0 =
      2 * a * (k + 1) + 2 * b := by
  have hcont1 :
      ContDiffAt ℝ 2 (fun s : ℝ => (1 + s ^ 2) ^ (k + 1)) 0 := by
    simpa using
      ((((contDiff_const.add (contDiff_id.pow 2)).pow (k + 1)).contDiffAt) :
        ContDiffAt ℝ 2 (fun s : ℝ => (1 + s ^ 2) ^ (k + 1)) 0)
  have hcont2 :
      ContDiffAt ℝ 2 (fun s : ℝ => s ^ 2 * (1 + s ^ 2) ^ k) 0 := by
    simpa [pow_two] using
      (((contDiff_id.pow 2).mul ((contDiff_const.add (contDiff_id.pow 2)).pow k)).contDiffAt :
        ContDiffAt ℝ 2 (fun s : ℝ => s ^ 2 * (1 + s ^ 2) ^ k) 0)
  have hcont1a :
      ContDiffAt ℝ 2 (fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1)) 0 := by
    simpa [smul_eq_mul] using ContDiffAt.const_smul a hcont1
  have hcont2b :
      ContDiffAt ℝ 2 (fun s : ℝ => b * (s ^ 2 * (1 + s ^ 2) ^ k)) 0 := by
    simpa [smul_eq_mul] using ContDiffAt.const_smul b hcont2
  have hsplit :
      (fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1) + b * s ^ 2 * (1 + s ^ 2) ^ k) =
        (fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1)) +
          fun s : ℝ => b * (s ^ 2 * (1 + s ^ 2) ^ k) := by
    funext s
    simp [Pi.add_apply, mul_assoc]
  rw [hsplit, iteratedDeriv_add hcont1a hcont2b, iteratedDeriv_const_mul hcont1 a,
    iteratedDeriv_const_mul hcont2 b, iteratedDeriv_two_one_add_sq_pow,
    iteratedDeriv_two_sq_mul_one_add_sq_pow]
  norm_num [Nat.cast_add]
  ring

lemma iteratedDeriv_two_pole_low_profile (k : ℕ) (a b : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1) + b * (1 + s ^ 2) ^ k) 0 =
      2 * a * (k + 1) + 2 * b * k := by
  have hcont1 :
      ContDiffAt ℝ 2 (fun s : ℝ => (1 + s ^ 2) ^ (k + 1)) 0 := by
    simpa using
      ((((contDiff_const.add (contDiff_id.pow 2)).pow (k + 1)).contDiffAt) :
        ContDiffAt ℝ 2 (fun s : ℝ => (1 + s ^ 2) ^ (k + 1)) 0)
  have hcont2 :
      ContDiffAt ℝ 2 (fun s : ℝ => (1 + s ^ 2) ^ k) 0 := by
    simpa using
      ((((contDiff_const.add (contDiff_id.pow 2)).pow k).contDiffAt) :
        ContDiffAt ℝ 2 (fun s : ℝ => (1 + s ^ 2) ^ k) 0)
  have hcont1a :
      ContDiffAt ℝ 2 (fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1)) 0 := by
    simpa [smul_eq_mul] using ContDiffAt.const_smul a hcont1
  have hcont2b :
      ContDiffAt ℝ 2 (fun s : ℝ => b * (1 + s ^ 2) ^ k) 0 := by
    simpa [smul_eq_mul] using ContDiffAt.const_smul b hcont2
  have hsplit :
      (fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1) + b * (1 + s ^ 2) ^ k) =
        (fun s : ℝ => a * (1 + s ^ 2) ^ (k + 1)) + fun s : ℝ => b * (1 + s ^ 2) ^ k := by
    funext s
    simp [Pi.add_apply]
  rw [hsplit, iteratedDeriv_add hcont1a hcont2b, iteratedDeriv_const_mul hcont1 a,
    iteratedDeriv_const_mul hcont2 b, iteratedDeriv_two_one_add_sq_pow,
    iteratedDeriv_two_one_add_sq_pow]
  norm_num [Nat.cast_add]
  ring
