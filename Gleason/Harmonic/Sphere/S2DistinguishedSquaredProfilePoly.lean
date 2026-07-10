import Gleason.Harmonic.Sphere.S2DistinguishedNorthZonal
import Gleason.Harmonic.HighDegree.HighEvenUnionProfilePolyApprox
import Gleason.Harmonic.Fischer.FischerDirect
import Gleason.Harmonic.HighDegree.EvenBoundedPolyDegree

noncomputable section

open Complex InnerProductSpace Polynomial

namespace GleasonS2Bridge

open SphericalHarmonics

theorem sphereCoordPolyAntipode_eq_self_of_mem_homogeneousSubmodule_even
    {n : ℕ} {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 3) ℝ n)
    (hnEven : Even n) :
    sphereCoordPolyAntipode p = p := by
  apply (eq_of_sphereCoordMvEval_eq_of_mem_homogeneousSubmodule
    (p := sphereCoordPolyAntipode p) (q := p)
    (sphereCoordPolyAntipode_mem_homogeneousSubmodule hp) hp)
  · ext x
    have hanti :
        sphereAntipodeAlgHom (sphereCoordMvEval p) x = sphereCoordMvEval p x := by
      rw [sphereAntipodeAlgHom_apply, sphereCoordMvEval_apply, sphereCoordMvEval_apply]
      have hcoords :
          (fun i => sphereCoordVec i (sphereAntipode x)) =
            fun i => (-1 : ℝ) * sphereCoordVec i x := by
        funext i
        fin_cases i <;>
          simp [sphereAntipode_apply_val, sphereCoordVec, sphereCoordRe, sphereCoordIm,
            sphereCoordZ]
      rw [hcoords]
      rw [_root_.eval_smul_of_isHomogeneous ((MvPolynomial.mem_homogeneousSubmodule n p).mp hp)]
      simpa [hnEven.neg_one_pow]
    simpa [sphereCoordMvEval_polyAntipode] using hanti

theorem exists_sqCenteredNorthZonalPolynomial_of_even_distinguishedZonalSector
    {n : ℕ} (hnEven : Even n) :
    ∃ q : ℝ[X],
      ∀ u : Set.Icc (0 : ℝ) 1,
        sqCenteredNorthZonalProfile
            (s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
              C(S2, ℝ))))) u =
          q.eval u.1 := by
  rcases exists_fixed_ambientRepresentative_of_mem_northFixedSector
      ((distinguishedZonalSector n).property) with ⟨p, hpRes, hpFix⟩
  have hpEval :
      sphereCoordMvEval p.1 =
        s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
          C(S2, ℝ)))) := by
    rw [← s2Pullback_restrictToSphere p.1, hpRes]
  have hpEven : sphereCoordPolyAntipode p.1 = p.1 := by
    exact sphereCoordPolyAntipode_eq_self_of_mem_homogeneousSubmodule_even p.2.1 hnEven
  rcases exists_sqCenteredNorthZonalPolynomial_of_isNorthZonal_of_even_mvPolynomial
      (isNorthZonal_s2Pullback_distinguishedZonalSector n) hpEval hpEven with ⟨q, hq⟩
  exact ⟨q, hq⟩

theorem exists_sqCenteredNorthZonalQuotientPolynomial_of_even_distinguishedZonalSector
    {n : ℕ} (hnEven : Even n) :
    ∃ q : ℝ[X],
      ∀ u : Set.Icc (0 : ℝ) 1,
        sqCenteredNorthZonalProfile
            (s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
              C(S2, ℝ))))) u =
          u.1 * q.eval u.1 := by
  rcases exists_sqCenteredNorthZonalPolynomial_of_even_distinguishedZonalSector
      (n := n) hnEven with ⟨p0, hp0⟩
  have hp00eval : p0.eval 0 = 0 := by
    calc
      p0.eval 0 = p0.eval zeroUnitIcc.1 := by simp [zeroUnitIcc]
      _ =
          sqCenteredNorthZonalProfile
            (s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
              C(S2, ℝ))))) zeroUnitIcc := by
                symm
                simpa using hp0 zeroUnitIcc
      _ = 0 := by
            rw [sqCenteredNorthZonalProfile_apply]
            have hzero :
                (⟨Real.sqrt (↑zeroUnitIcc), by
                  constructor
                  · nlinarith [Real.sqrt_nonneg (↑zeroUnitIcc)]
                  · have hsq : (Real.sqrt (↑zeroUnitIcc)) ^ 2 = (↑zeroUnitIcc : ℝ) :=
                      Real.sq_sqrt zeroUnitIcc.2.1
                    nlinarith [zeroUnitIcc.2.2, Real.sqrt_nonneg (↑zeroUnitIcc), hsq]⟩
                  : Set.Icc (-1 : ℝ) 1) = zeroIcc := by
              apply Subtype.ext
              simp [zeroUnitIcc, zeroIcc]
            rw [hzero]
            exact centeredNorthZonalProfile_zero _
  have hp00 : p0.coeff 0 = 0 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hp00eval
  refine ⟨p0.divX, ?_⟩
  intro u
  have hdivxEval :
      (Polynomial.X * p0.divX + Polynomial.C (p0.coeff 0)).eval u.1 = p0.eval u.1 := by
    exact congrArg (fun r : ℝ[X] => r.eval u.1) (Polynomial.X_mul_divX_add p0)
  have hdivxEval' :
      p0.eval u.1 = u.1 * (p0.divX).eval u.1 + p0.coeff 0 := by
    have htmp :
        p0.eval u.1 = (Polynomial.X * p0.divX + Polynomial.C (p0.coeff 0)).eval u.1 :=
      hdivxEval.symm
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C] at htmp
    simpa using htmp
  calc
    sqCenteredNorthZonalProfile
        (s2Pullback (((((distinguishedZonalSector n : northFixedSector n) : sector n) :
          C(S2, ℝ))))) u = p0.eval u.1 := hp0 u
    _ = u.1 * (p0.divX).eval u.1 + p0.coeff 0 := hdivxEval'
    _ = u.1 * (p0.divX).eval u.1 := by simp [hp00]

end GleasonS2Bridge
