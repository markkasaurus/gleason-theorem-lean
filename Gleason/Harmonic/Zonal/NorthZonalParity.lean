import Gleason.Harmonic.Zonal.NorthZonalEven
import Gleason.Continuity.Auxiliary.ContinuousEndpoint

noncomputable section

open Complex InnerProductSpace

def sphereNeg (x : spherePoint3) : spherePoint3 :=
  ⟨-x.1, by simpa [norm_neg] using x.2⟩

@[simp] lemma sphereNeg_val (x : spherePoint3) : (sphereNeg x).1 = -x.1 := by
  rfl

@[simp] lemma sphereNeg_snd (x : spherePoint3) : (sphereNeg x).1.snd = -x.1.snd := by
  simp [sphereNeg]

lemma sphereRestrictionLinear_sphereNeg_of_harmonicHomogeneousDegree
    {n : ℕ} {f : WithLp 2 (ℂ × ℝ) → ℝ}
    (hf : HarmonicHomogeneousDegree n f) (x : spherePoint3) :
    sphereRestrictionLinear f (sphereNeg x) = (-1 : ℝ) ^ n * sphereRestrictionLinear f x := by
  simpa [sphereRestrictionLinear, sphereNeg] using hf.2 (-1) x.1

lemma sphereRestriction_sphereNeg_of_mem_continuousHarmonicSphereDegreeSubmodule
    {n : ℕ} {g : C(spherePoint3, ℝ)}
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n) (x : spherePoint3) :
    g (sphereNeg x) = (-1 : ℝ) ^ n * g x := by
  have hg' : (g : spherePoint3 → ℝ) ∈ harmonicSphereDegreeSubmodule n := hg
  rcases hg' with ⟨f, hf, hfg⟩
  calc
    g (sphereNeg x) = sphereRestrictionLinear f (sphereNeg x) := by
      exact (congrFun hfg (sphereNeg x)).symm
    _ = (-1 : ℝ) ^ n * sphereRestrictionLinear f x :=
      sphereRestrictionLinear_sphereNeg_of_harmonicHomogeneousDegree hf x
    _ = (-1 : ℝ) ^ n * g x := by
      rw [congrFun hfg x]

lemma northZonalProfile_parity_of_mem_continuousHarmonicSphereDegreeSubmodule
    {n : ℕ} {g : C(spherePoint3, ℝ)}
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hgz : IsNorthZonal g)
    (z : Set.Icc (-1 : ℝ) 1) :
    northZonalProfile g (negIcc z) = (-1 : ℝ) ^ n * northZonalProfile g z := by
  have hneg :
      northZonalProfile g ⟨(sphereNeg (northSection z)).1.snd,
        snd_mem_Icc (sphereNeg (northSection z))⟩ =
        g (sphereNeg (northSection z)) :=
    northZonalProfile_eq_of_isNorthZonal hgz (sphereNeg (northSection z))
  have hpos :
      northZonalProfile g ⟨(northSection z).1.snd, snd_mem_Icc (northSection z)⟩ =
        g (northSection z) :=
    northZonalProfile_eq_of_isNorthZonal hgz (northSection z)
  have hsndneg :
      (⟨(sphereNeg (northSection z)).1.snd,
        snd_mem_Icc (sphereNeg (northSection z))⟩ : Set.Icc (-1 : ℝ) 1) = negIcc z := by
    apply Subtype.ext
    simp [sphereNeg, northSection, negIcc]
  have hsndpos :
      (⟨(northSection z).1.snd, snd_mem_Icc (northSection z)⟩ : Set.Icc (-1 : ℝ) 1) = z := by
    apply Subtype.ext
    simp [northSection]
  calc
    northZonalProfile g (negIcc z)
      = g (sphereNeg (northSection z)) := by rw [← hsndneg]; exact hneg
    _ = (-1 : ℝ) ^ n * g (northSection z) :=
        sphereRestriction_sphereNeg_of_mem_continuousHarmonicSphereDegreeSubmodule hg (northSection z)
    _ = (-1 : ℝ) ^ n * northZonalProfile g z := by
          rw [← hpos, hsndpos]

lemma northZonalProfile_zero_of_odd_of_mem_pointConstraint
    {n : ℕ} {g : C(spherePoint3, ℝ)}
    (hnodd : Odd n)
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hgz : IsNorthZonal g)
    (z : Set.Icc (-1 : ℝ) 1) :
    northZonalProfile g z = 0 := by
  have hpar :=
    northZonalProfile_parity_of_mem_continuousHarmonicSphereDegreeSubmodule hg hgz z
  have heven :=
    northZonalProfile_even_of_mem_pointConstraint hgpc hgz z
  have hpow : (-1 : ℝ) ^ n = -1 := by
    rcases hnodd with ⟨k, hk⟩
    rw [hk]
    simp [pow_add, pow_mul]
  rw [hpow] at hpar
  rw [heven] at hpar
  linarith

theorem eq_zero_of_odd_of_mem_continuousHarmonicSphereDegreeSubmodule_of_northZonal_pointConstraint
    {n : ℕ} {g : C(spherePoint3, ℝ)}
    (hnodd : Odd n)
    (hg : g ∈ continuousHarmonicSphereDegreeSubmodule n)
    (hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule)
    (hgz : IsNorthZonal g) :
    g = 0 := by
  ext x
  have hprof :
      northZonalProfile g ⟨x.1.snd, snd_mem_Icc x⟩ = g x :=
    northZonalProfile_eq_of_isNorthZonal hgz x
  have hzero :
      northZonalProfile g ⟨x.1.snd, snd_mem_Icc x⟩ = 0 :=
    northZonalProfile_zero_of_odd_of_mem_pointConstraint hnodd hg hgpc hgz
      ⟨x.1.snd, snd_mem_Icc x⟩
  exact hprof.symm.trans hzero
