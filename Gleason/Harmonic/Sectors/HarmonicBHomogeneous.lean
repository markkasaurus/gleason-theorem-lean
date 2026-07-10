import Gleason.Harmonic.Sectors.HarmonicBWitness

noncomputable section

open Complex InnerProductSpace Real

lemma complexNormSqMulRePowLift_homogeneous
    (m : ℕ) (t : ℝ) (p : WithLp 2 (ℂ × ℝ)) :
    complexNormSqMulRePowLift m (t • p) =
      t ^ (m + 2) * complexNormSqMulRePowLift m p := by
  have hsq :
      Complex.normSq ((t : ℂ) * complexProjL p) =
        t ^ 2 * Complex.normSq (complexProjL p) := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have hre :
      (((t : ℂ) * complexProjL p) ^ m).re =
        t ^ m * ((complexProjL p) ^ m).re := by
    simpa using complexRePow_homogeneous m (complexProjL p) t
  calc
    complexNormSqMulRePowLift m (t • p)
      = Complex.normSq ((t : ℂ) * complexProjL p) *
          ((((t : ℂ) * complexProjL p) ^ m).re) := by
            simp [complexNormSqMulRePowLift, complexProjL, map_smul]
    _ = (t ^ 2 * Complex.normSq (complexProjL p)) *
          (t ^ m * ((complexProjL p) ^ m).re) := by
            rw [hsq, hre]
    _ = t ^ (m + 2) * complexNormSqMulRePowLift m p := by
            simp [complexNormSqMulRePowLift, pow_add]
            ring

lemma realSqMulRePowLift_homogeneous
    (m : ℕ) (t : ℝ) (p : WithLp 2 (ℂ × ℝ)) :
    realSqMulRePowLift m (t • p) =
      t ^ (m + 2) * realSqMulRePowLift m p := by
  have hreal : (t * realProjL p) ^ 2 = t ^ 2 * (realProjL p) ^ 2 := by
    ring
  have hre :
      (((t : ℂ) * complexProjL p) ^ m).re =
        t ^ m * ((complexProjL p) ^ m).re := by
    simpa using complexRePow_homogeneous m (complexProjL p) t
  calc
    realSqMulRePowLift m (t • p)
      = (t * realProjL p) ^ 2 * ((((t : ℂ) * complexProjL p) ^ m).re) := by
          simp [realSqMulRePowLift, realProjL, complexProjL, map_smul]
    _ = (t ^ 2 * (realProjL p) ^ 2) *
          (t ^ m * ((complexProjL p) ^ m).re) := by
            rw [hreal, hre]
    _ = t ^ (m + 2) * realSqMulRePowLift m p := by
            simp [realSqMulRePowLift, pow_add]
            ring

lemma surfaceModeBL2_homogeneous
    {n : ℕ} (hn : 2 ≤ n) (t : ℝ) (p : WithLp 2 (ℂ × ℝ)) :
    surfaceModeBL2 n (t • p) = t ^ n * surfaceModeBL2 n p := by
  rw [surfaceModeBL2_eq_split hn]
  simp [Pi.add_apply, Pi.smul_apply]
  rw [complexNormSqMulRePowLift_homogeneous (n - 2) t p]
  rw [realSqMulRePowLift_homogeneous (n - 2) t p]
  rw [Nat.sub_add_cancel hn]
  simp [mul_assoc, mul_left_comm, mul_comm, left_distrib]
