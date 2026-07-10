import Gleason.Harmonic.Sphere.SphereFrame
import Gleason.Harmonic.Auxiliary.QuadraticBridge
import Mathlib.Analysis.InnerProductSpace.Orthonormal

noncomputable section

open Complex InnerProductSpace

def sphereTripleVec (x y z : spherePoint3) : Fin 3 → WithLp 2 (ℂ × ℝ)
  | 0 => x.1
  | 1 => y.1
  | 2 => z.1

lemma sphereTripleVec_orthonormal (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    Orthonormal ℝ (sphereTripleVec x y z) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · simp [sphereTripleVec, x.2]
  · simpa [sphereTripleVec] using hxy
  · simpa [sphereTripleVec] using hxz
  · simpa [sphereTripleVec, mul_comm, add_comm, add_left_comm, add_assoc] using hxy
  · simp [sphereTripleVec, y.2]
  · simpa [sphereTripleVec] using hyz
  · simpa [sphereTripleVec, mul_comm, add_comm, add_left_comm, add_assoc] using hxz
  · simpa [sphereTripleVec, mul_comm, add_comm, add_left_comm, add_assoc] using hyz
  · simp [sphereTripleVec, z.2]

lemma finrank_real_withLp_complex_prod_real :
    Module.finrank ℝ (WithLp 2 (ℂ × ℝ)) = 3 := by
  rw [LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (ℂ × ℝ)), Module.finrank_prod]
  simp [Complex.finrank_real_complex]

theorem sum_harmonicHomogeneousDegree_two_on_orthogonal_sphere_triple_zero
    {f : WithLp 2 (ℂ × ℝ) → ℝ} (hf : HarmonicHomogeneousDegree 2 f)
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    f x.1 + f y.1 + f z.1 = 0 := by
  let v := sphereTripleVec x y z
  have hv : Orthonormal ℝ v := sphereTripleVec_orthonormal x y z hxy hxz hyz
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (WithLp 2 (ℂ × ℝ)) := by
    rw [finrank_real_withLp_complex_prod_real]
    norm_num
  let b0 : Module.Basis (Fin 3) ℝ (WithLp 2 (ℂ × ℝ)) :=
    basisOfOrthonormalOfCardEqFinrank hv hcard
  have hb0 : (b0 : Fin 3 → WithLp 2 (ℂ × ℝ)) = v := by
    simpa [b0] using (coe_basisOfOrthonormalOfCardEqFinrank hv hcard)
  let b : OrthonormalBasis (Fin 3) ℝ (WithLp 2 (ℂ × ℝ)) :=
    b0.toOrthonormalBasis (by simpa [hb0] using hv)
  have hΔ : Δ f 0 = 0 := by
    simpa using (hf.1 0).2.eq_of_nhds
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := f) b] at hΔ
  have hterm : ∀ i : Fin 3, (iteratedFDeriv ℝ 2 f 0) ![b i, b i] = 2 * f (b i) := by
    intro i
    have h :=
      bilinearIteratedFDerivTwo_eq_two_mul_of_two_homogeneous
        (E := WithLp 2 (ℂ × ℝ)) (f := f) (hcont := (hf.1 0).1) hf.2 (b i)
    simpa [bilinearIteratedFDerivTwo_eq_iteratedFDeriv] using h
  simp only [hterm, Fin.sum_univ_three] at hΔ
  have hb0x : b 0 = x.1 := by
    have h := congrFun hb0 0
    simpa [b, v, sphereTripleVec] using h
  have hb0y : b 1 = y.1 := by
    have h := congrFun hb0 1
    simpa [b, v, sphereTripleVec] using h
  have hb0z : b 2 = z.1 := by
    have h := congrFun hb0 2
    simpa [b, v, sphereTripleVec] using h
  have hΔ' : 2 * f x.1 + 2 * f y.1 + 2 * f z.1 = 0 := by
    simpa [hb0x, hb0y, hb0z] using hΔ
  linarith

theorem harmonicSphereDegreeSubmodule_zero_le_sphereFrameSubmodule :
    harmonicSphereDegreeSubmodule 0 ≤ sphereFrameSubmodule := by
  intro g hg
  rcases hg with ⟨f, hf, rfl⟩
  rcases hf with ⟨_, hfHom⟩
  intro x y z hxy hxz hyz
  have hx : f x.1 = f 0 := by simpa using (hfHom 0 x.1).symm
  have hy : f y.1 = f 0 := by simpa using (hfHom 0 y.1).symm
  have hz : f z.1 = f 0 := by simpa using (hfHom 0 z.1).symm
  have h1 : f sphereE1.1 = f 0 := by simpa using (hfHom 0 sphereE1.1).symm
  have h2 : f sphereE2.1 = f 0 := by simpa using (hfHom 0 sphereE2.1).symm
  have h3 : f sphereE3.1 = f 0 := by simpa using (hfHom 0 sphereE3.1).symm
  simp [sphereRestrictionLinear, hx, hy, hz, h1, h2, h3]

theorem harmonicSphereDegreeSubmodule_two_le_sphereFrameSubmodule :
    harmonicSphereDegreeSubmodule 2 ≤ sphereFrameSubmodule := by
  intro g hg
  rcases hg with ⟨f, hf, rfl⟩
  intro x y z hxy hxz hyz
  have hxyz :=
    sum_harmonicHomogeneousDegree_two_on_orthogonal_sphere_triple_zero
      hf x y z hxy hxz hyz
  have hbase :=
    sum_harmonicHomogeneousDegree_two_on_orthogonal_sphere_triple_zero
      hf sphereE1 sphereE2 sphereE3
      sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  simp [sphereRestrictionLinear, hxyz, hbase]
