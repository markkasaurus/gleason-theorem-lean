import Gleason.Continuity.NearInfimumOscillation
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open GleasonBridge RankOne Set Complex Real InnerProductSpace
open scoped Topology

section

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

lemma exists_unit_orthogonal_to_unit
    (hdim : 2 ≤ Module.finrank ℂ H)
    {p : H} (hp : ‖p‖ = 1) :
    ∃ u : H, ‖u‖ = 1 ∧ inner (𝕜 := ℂ) u p = 0 := by
  let n : ℕ := Module.finrank ℂ H
  let i0 : Fin n := ⟨0, lt_of_lt_of_le (by omega) hdim⟩
  let i1 : Fin n := ⟨1, lt_of_lt_of_le (by omega) hdim⟩
  let seed : Fin n → H := fun i => if h0 : i = i0 then p else 0
  let s : Set (Fin n) := {i0}
  have hseed_orth : Orthonormal ℂ (s.restrict seed) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    have hi' : i = i0 := by simpa [s, Set.mem_singleton_iff] using hi
    have hj' : j = i0 := by simpa [s, Set.mem_singleton_iff] using hj
    subst hi'; subst hj'
    simp [seed, hp, i0]
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℂ) (E := H) (ι := Fin n) (by simp [n]) (v := seed) (s := s) hseed_orth
  have hb0 : b i0 = p := hb i0 (by simp [s, i0])
  have hortho := orthonormal_iff_ite.mp b.orthonormal
  have hi01 : i0 ≠ i1 := by
    intro h
    have : (0 : ℕ) = 1 := by simpa [i0, i1] using congrArg Fin.val h
    omega
  have hunorm : ‖b i1‖ = 1 := by
    have hnorm : inner (𝕜 := ℂ) (b i1) (b i1) = (1 : ℂ) := by simpa using hortho i1 i1
    simpa [inner_self_eq_norm_sq_to_K] using hnorm
  have hup : inner (𝕜 := ℂ) (b i1) p = 0 := by
    have htmp : inner (𝕜 := ℂ) (b i1) (b i0) = 0 := by simpa [hi01] using hortho i1 i0
    simpa [hb0] using htmp
  exact ⟨b i1, hunorm, hup⟩

lemma exists_orthonormal_completion_of_pair
    (hdim : 3 ≤ Module.finrank ℂ H)
    {u p : H} (hu : ‖u‖ = 1) (hp : ‖p‖ = 1)
    (hup : inner (𝕜 := ℂ) u p = 0) :
    ∃ v : H, ‖v‖ = 1 ∧ inner (𝕜 := ℂ) u v = 0 ∧ inner (𝕜 := ℂ) v p = 0 := by
  let n : ℕ := Module.finrank ℂ H
  let i0 : Fin n := ⟨0, lt_of_lt_of_le (by omega) hdim⟩
  let i1 : Fin n := ⟨1, lt_of_lt_of_le (by omega) hdim⟩
  let i2 : Fin n := ⟨2, lt_of_lt_of_le (by omega) hdim⟩
  let seed : Fin n → H := fun i =>
    if h0 : i = i0 then u else if h1 : i = i1 then p else 0
  let s : Set (Fin n) := {i0, i1}
  have hseed_orth : Orthonormal ℂ (s.restrict seed) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    have hi' : i = i0 ∨ i = i1 := by
      simpa [s, Set.mem_insert_iff, Set.mem_singleton_iff] using hi
    have hj' : j = i0 ∨ j = i1 := by
      simpa [s, Set.mem_insert_iff, Set.mem_singleton_iff] using hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
      simp [seed, hu, hp, hup, inner_eq_zero_symm, i0, i1]
  obtain ⟨b, hb⟩ :=
    Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      (𝕜 := ℂ) (E := H) (ι := Fin n) (by simp [n]) (v := seed) (s := s) hseed_orth
  have hb0 : b i0 = u := hb i0 (by simp [s, i0, i1])
  have hb1 : b i1 = p := hb i1 (by simp [s, i0, i1])
  have hortho := orthonormal_iff_ite.mp b.orthonormal
  have hi02 : i0 ≠ i2 := by
    intro h
    have : (0 : ℕ) = 2 := by simpa [i0, i2] using congrArg Fin.val h
    omega
  have hi12 : i1 ≠ i2 := by
    intro h
    have : (1 : ℕ) = 2 := by simpa [i1, i2] using congrArg Fin.val h
    omega
  have hvnorm : ‖b i2‖ = 1 := by
    have hnorm : inner (𝕜 := ℂ) (b i2) (b i2) = (1 : ℂ) := by simpa using hortho i2 i2
    simpa [inner_self_eq_norm_sq_to_K] using hnorm
  have huv' : inner (𝕜 := ℂ) u (b i2) = 0 := by
    have htmp : inner (𝕜 := ℂ) (b i0) (b i2) = 0 := by simpa [hi02] using hortho i0 i2
    simpa [hb0] using htmp
  have hvp' : inner (𝕜 := ℂ) (b i2) p = 0 := by
    have htmp : inner (𝕜 := ℂ) (b i2) (b i1) = 0 := by simpa [hi12] using hortho i2 i1
    simpa [hb1] using htmp
  exact ⟨b i2, hvnorm, huv', hvp'⟩

lemma frame_quadratic_unit_smul_eq (μ : FrameFunction H)
    {c : ℂ} (hc : ‖c‖ = 1) (x : H) :
    frame_quadratic μ (c • x) = frame_quadratic μ x := by
  rw [frame_quadratic_sq_hom (H := H) μ c x, hc]
  ring

lemma dist_unit_smul_eq {c : ℂ} (hc : ‖c‖ = 1) (x y : H) :
    dist (c • x) (c • y) = dist x y := by
  have hsub : c • x - c • y = c • (x - y) := by simp [smul_sub]
  rw [dist_eq_norm, dist_eq_norm, hsub, norm_smul, hc, one_mul]

lemma exists_phase_orthogonal_decomp_of_unit
    {p x : H} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) :
    ∃ c : ℂ, ∃ r : ℝ, ∃ y : H,
      ‖c‖ = 1 ∧
      0 ≤ r ∧
      c • x = y + (r : ℂ) • p ∧
      inner (𝕜 := ℂ) y p = 0 ∧
      ‖y‖ ^ 2 + r ^ 2 = 1 := by
  rcases exists_unit_phase_inner_eq_nonneg_real p x with ⟨c, hc, r, hr0, hr⟩
  let x' : H := c • x
  let y : H := x' - (r : ℂ) • p
  have hx' : ‖x'‖ = 1 := by
    dsimp [x']
    simpa [norm_smul, hc] using hx
  have hpy : inner (𝕜 := ℂ) p y = 0 := by
    dsimp [y, x']
    rw [inner_sub_right, inner_smul_right]
    have hpp : inner (𝕜 := ℂ) p p = (1 : ℂ) := by
      have hpp_real : ‖p‖ ^ 2 = 1 := by nlinarith [hp]
      calc
        inner (𝕜 := ℂ) p p = ((‖p‖ ^ 2 : ℝ) : ℂ) := by simp [inner_self_eq_norm_sq_to_K]
        _ = 1 := by norm_num [hpp_real]
    have hpp' : inner (𝕜 := ℂ) p ((r : ℂ) • p) = (r : ℂ) := by
      rw [inner_smul_right, hpp]
      simp
    change c * inner (𝕜 := ℂ) p x - inner (𝕜 := ℂ) p ((r : ℂ) • p) = 0
    rw [hpp']
    have hr' : c * inner (𝕜 := ℂ) p x = (r : ℂ) := by
      simpa [x', mul_comm] using hr
    exact sub_eq_zero.mpr hr'
  have hyp : inner (𝕜 := ℂ) y p = 0 := by
    simpa [inner_eq_zero_symm] using hpy
  have hysq : ‖y‖ ^ 2 + r ^ 2 = 1 := by
    have hydecomp : x' = y + (r : ℂ) • p := by
      dsimp [y, x']
      abel
    have horth : inner (𝕜 := ℂ) y ((r : ℂ) • p) = 0 := by
      simp [hyp]
    have hnorm :=
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero y ((r : ℂ) • p) horth
    rw [← hydecomp] at hnorm
    have hrnorm : ‖(r : ℂ) • p‖ ^ 2 = r ^ 2 := by
      simp [norm_smul, hp, Real.norm_eq_abs, abs_of_nonneg hr0, sq]
    nlinarith [hnorm, hx']
  refine ⟨c, r, y, hc, hr0, ?_, hyp, hysq⟩
  dsimp [x', y]
  abel

lemma exists_phase_coordSphere_data_of_unit
    (hdim : 3 ≤ Module.finrank ℂ H)
    {p x : H} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) :
    ∃ c : ℂ, ∃ u v : H, ∃ z : ℝ × ℝ × ℝ,
      ‖c‖ = 1 ∧
      ‖u‖ = 1 ∧
      ‖v‖ = 1 ∧
      inner (𝕜 := ℂ) u v = 0 ∧
      inner (𝕜 := ℂ) u p = 0 ∧
      inner (𝕜 := ℂ) v p = 0 ∧
      z ∈ coordSphereSet ∧
      0 ≤ z.2.2 ∧
      c • x = coordPoint u v p z := by
  rcases exists_phase_orthogonal_decomp_of_unit hp hx with
    ⟨c, r, y, hc, hr0, hdecomp, hyp, hysq⟩
  by_cases hy0 : y = 0
  · have hdim2 : 2 ≤ Module.finrank ℂ H := by omega
    rcases exists_unit_orthogonal_to_unit hdim2 hp with ⟨u, hu, hup⟩
    rcases exists_orthonormal_completion_of_pair hdim hu hp hup with
      ⟨v, hv, huv, hvp⟩
    have hyNorm : ‖y‖ = 0 := by simpa [hy0]
    have hr1 : r = 1 := by
      have hrsq : r ^ 2 = 1 := by
        nlinarith [hysq, hyNorm]
      nlinarith [hr0, hrsq]
    refine ⟨c, u, v, poleCoord, hc, hu, hv, huv, hup, hvp, ?_, ?_, ?_⟩
    · simp [coordSphereSet, poleCoord]
    · simp [poleCoord]
    · calc
        c • x = y + (r : ℂ) • p := hdecomp
        _ = coordPoint u v p poleCoord := by
          simp [hy0, hr1, coordPoint_poleCoord]
  · let s : ℝ := ‖y‖
    have hspos : 0 < s := by
      dsimp [s]
      exact norm_pos_iff.mpr hy0
    let u : H := ((s : ℂ)⁻¹ • y)
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]
      dsimp [s]
      field_simp [hspos.ne']
    have hup : inner (𝕜 := ℂ) u p = 0 := by
      dsimp [u]
      simp [hyp]
    rcases exists_orthonormal_completion_of_pair hdim hu hp hup with
      ⟨v, hv, huv, hvp⟩
    let z : ℝ × ℝ × ℝ := (s, (0, r))
    have hz : z ∈ coordSphereSet := by
      dsimp [coordSphereSet, z, s]
      nlinarith [hysq]
    have hyu : ((s : ℂ) • u) = y := by
      have hs1C : (s : ℂ) * (s : ℂ)⁻¹ = (1 : ℂ) := by
        field_simp [hspos.ne']
      change (s : ℝ) • ((s : ℂ)⁻¹ • y) = y
      rw [← smul_assoc]
      have hs1RtoC : (s : ℝ) • ((s : ℂ)⁻¹) = (1 : ℂ) := by
        change (s : ℂ) * (s : ℂ)⁻¹ = (1 : ℂ)
        exact hs1C
      rw [hs1RtoC, one_smul]
    refine ⟨c, u, v, z, hc, hu, hv, huv, hup, hvp, hz, hr0, ?_⟩
    calc
      c • x = y + (r : ℂ) • p := hdecomp
      _ = ((s : ℂ) • u) + ((((0 : ℝ) : ℂ) • v) + (((r : ℝ) : ℂ) • p)) := by
        rw [hyu]
        simp [add_comm, add_left_comm, add_assoc]
      _ = coordPoint u v p z := by
        simp [coordPoint, z]

lemma exists_phase_coordSphereImage_of_unit
    (hdim : 3 ≤ Module.finrank ℂ H)
    {p x : H} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) :
    ∃ c : ℂ, ∃ u v : H,
      ‖c‖ = 1 ∧
      ‖u‖ = 1 ∧
      ‖v‖ = 1 ∧
      inner (𝕜 := ℂ) u v = 0 ∧
      inner (𝕜 := ℂ) u p = 0 ∧
      inner (𝕜 := ℂ) v p = 0 ∧
      c • x ∈ coordSphereImage u v p := by
  rcases exists_phase_coordSphere_data_of_unit hdim hp hx with
    ⟨c, u, v, z, hc, hu, hv, huv, hup, hvp, hz, _, hcoord⟩
  refine ⟨c, u, v, hc, hu, hv, huv, hup, hvp, ?_⟩
  exact ⟨z, hz, hcoord.symm⟩

end
