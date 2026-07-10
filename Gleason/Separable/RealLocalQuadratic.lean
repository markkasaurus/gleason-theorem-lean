import Gleason.Separable.BasisDecomposition
import Gleason.Continuity.Theorem

/-!
# Local Quadraticity over the Real Field

An orthonormal triple identifies its span with the standard real
three-dimensional Hilbert space. The restriction of a projection measure to
the corresponding unit sphere is a nonnegative sphere frame function and is
therefore quadratic.
-/

noncomputable section

open scoped InnerProductSpace

namespace ClassicalGleason.Separable

universe v

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

abbrev RealSphereAmbient := WithLp 2 (ℂ × ℝ)

def realTripleVec (u v w : H) : Fin 3 → H
  | 0 => u
  | 1 => v
  | 2 => w

omit [CompleteSpace H] in
theorem realTripleVec_orthonormal (u v w : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner ℝ u v = 0) (huw : inner ℝ u w = 0)
    (hvw : inner ℝ v w = 0) :
    Orthonormal ℝ (realTripleVec u v w) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · simp [realTripleVec, hu]
  · simpa [realTripleVec] using huv
  · simpa [realTripleVec] using huw
  · simpa [realTripleVec, real_inner_comm] using huv
  · simp [realTripleVec, hv]
  · simpa [realTripleVec] using hvw
  · simpa [realTripleVec, real_inner_comm] using huw
  · simpa [realTripleVec, real_inner_comm] using hvw
  · simp [realTripleVec, hw]

def realTripleLinearMap (u v w : H) : RealSphereAmbient →ₗ[ℝ] H :=
  (sphereStdBasis.constr ℝ) (realTripleVec u v w)

omit [CompleteSpace H] in
@[simp]
theorem realTripleLinearMap_apply_basis (u v w : H) (i : Fin 3) :
    realTripleLinearMap u v w (sphereStdBasis i) = realTripleVec u v w i := by
  exact Module.Basis.constr_basis sphereStdBasis ℝ (realTripleVec u v w) i

def realTripleLinearIsometry (u v w : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner ℝ u v = 0) (huw : inner ℝ u w = 0)
    (hvw : inner ℝ v w = 0) :
    RealSphereAmbient →ₗᵢ[ℝ] H :=
  (realTripleLinearMap u v w).isometryOfOrthonormal
    sphereStdBasis_orthonormal
    (by
      have hcomp :
          ((realTripleLinearMap u v w : RealSphereAmbient → H) ∘
              (sphereStdBasis : Fin 3 → RealSphereAmbient)) =
            realTripleVec u v w := by
        funext i
        exact realTripleLinearMap_apply_basis u v w i
      rw [hcomp]
      exact realTripleVec_orthonormal u v w hu hv hw huv huw hvw)

omit [CompleteSpace H] in
@[simp]
theorem realTripleLinearIsometry_apply_basis
    (u v w : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner ℝ u v = 0) (huw : inner ℝ u w = 0)
    (hvw : inner ℝ v w = 0) (i : Fin 3) :
    realTripleLinearIsometry u v w hu hv hw huv huw hvw (sphereStdBasis i) =
      realTripleVec u v w i := by
  exact realTripleLinearMap_apply_basis u v w i

omit [CompleteSpace H] in
@[simp]
theorem realTripleLinearIsometry_apply_sphereE1
    (u v w : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner ℝ u v = 0) (huw : inner ℝ u w = 0)
    (hvw : inner ℝ v w = 0) :
    realTripleLinearIsometry u v w hu hv hw huv huw hvw sphereE1.1 = u := by
  simpa [sphereStdBasis_apply, sphereTripleVec, realTripleVec] using
    realTripleLinearIsometry_apply_basis u v w hu hv hw huv huw hvw 0

omit [CompleteSpace H] in
@[simp]
theorem realTripleLinearIsometry_apply_sphereE2
    (u v w : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner ℝ u v = 0) (huw : inner ℝ u w = 0)
    (hvw : inner ℝ v w = 0) :
    realTripleLinearIsometry u v w hu hv hw huv huw hvw sphereE2.1 = v := by
  simpa [sphereStdBasis_apply, sphereTripleVec, realTripleVec] using
    realTripleLinearIsometry_apply_basis u v w hu hv hw huv huw hvw 1

omit [CompleteSpace H] in
@[simp]
theorem realTripleLinearIsometry_apply_sphereE3
    (u v w : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (huv : inner ℝ u v = 0) (huw : inner ℝ u w = 0)
    (hvw : inner ℝ v w = 0) :
    realTripleLinearIsometry u v w hu hv hw huv huw hvw sphereE3.1 = w := by
  simpa [sphereStdBasis_apply, sphereTripleVec, realTripleVec] using
    realTripleLinearIsometry_apply_basis u v w hu hv hw huv huw hvw 2

namespace OrthogonalProjection

/-- Projection onto the range of a finite-dimensional linear isometry. -/
def rangeOfRealTripleIsometry
    (e : RealSphereAmbient →ₗᵢ[ℝ] H) : OrthogonalProjection ℝ H := by
  let K := LinearMap.range e.toLinearMap
  letI : FiniteDimensional ℝ K := e.equivRange.toLinearEquiv.finiteDimensional
  letI : CompleteSpace K := FiniteDimensional.complete ℝ K
  exact ⟨K.starProjection, isStarProjection_starProjection⟩

@[simp]
theorem rangeOfRealTripleIsometry_val
    (e : RealSphereAmbient →ₗᵢ[ℝ] H) :
    (rangeOfRealTripleIsometry e).1 =
      (LinearMap.range e.toLinearMap).starProjection :=
  rfl

theorem rankOne_mul_rankOne_eq_zero_of_unit
    {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = 0) :
    (rankOne (𝕜 := ℝ) u).1 * (rankOne (𝕜 := ℝ) v).1 = 0 := by
  ext x
  rw [ContinuousLinearMap.mul_apply, rankOne_apply_of_unit v hv,
    rankOne_apply_of_unit u hu]
  simp [inner_smul_right, huv]

end OrthogonalProjection

namespace ProjectionMeasure

set_option maxHeartbeats 1200000 in
/-- The sum of the values on the rank-one projections associated with an
orthonormal sphere triple is the value of the projection onto the range of the
ambient isometry. -/
theorem sum_rankOne_mapped_sphereTriple
    (m : ProjectionMeasure ℝ H) (e : RealSphereAmbient →ₗᵢ[ℝ] H)
    (x y z : spherePoint3)
    (hxy : inner ℝ x.1 y.1 = 0)
    (hxz : inner ℝ x.1 z.1 = 0)
    (hyz : inner ℝ y.1 z.1 = 0) :
    m.μ (OrthogonalProjection.rankOne (𝕜 := ℝ) (e x.1)) +
        m.μ (OrthogonalProjection.rankOne (𝕜 := ℝ) (e y.1)) +
        m.μ (OrthogonalProjection.rankOne (𝕜 := ℝ) (e z.1)) =
      m.μ (OrthogonalProjection.rangeOfRealTripleIsometry e) := by
  let t : Fin 3 → RealSphereAmbient := sphereTripleVec x y z
  let P : Fin 3 → OrthogonalProjection ℝ H := fun i =>
    OrthogonalProjection.rankOne (e (t i))
  have ht : Orthonormal ℝ t :=
    sphereTripleVec_orthonormal x y z hxy hxz hyz
  have hPt : ∀ i : Fin 3, ‖e (t i)‖ = 1 := by
    intro i
    exact (e.norm_map (t i)).trans (ht.norm_eq_one i)
  have hP : Pairwise (fun i j => (P i).1 * (P j).1 = 0) := by
    intro i j hij
    apply OrthogonalProjection.rankOne_mul_rankOne_eq_zero_of_unit
      (hPt i) (hPt j)
    rw [e.inner_map_map]
    exact ht.inner_eq_zero hij
  have h01 : (P 0).1 * (P 1).1 = 0 := hP (by decide)
  have h02 : (P 0).1 * (P 2).1 = 0 := hP (by decide)
  have h12 : (P 1).1 * (P 2).1 = 0 := hP (by decide)
  let P01 := OrthogonalProjection.add (P 0) (P 1) h01
  have h012 : P01.1 * (P 2).1 = 0 := by
    change ((P 0).1 + (P 1).1) * (P 2).1 = 0
    rw [add_mul, h02, h12, add_zero]
  let R := OrthogonalProjection.add P01 (P 2) h012
  have hR : R = OrthogonalProjection.rangeOfRealTripleIsometry e := by
    apply OrthogonalProjection.ext
    ext a
    let K := LinearMap.range e.toLinearMap
    letI : FiniteDimensional ℝ K := e.equivRange.toLinearEquiv.finiteDimensional
    letI : CompleteSpace K := FiniteDimensional.complete ℝ K
    let b0 : Module.Basis (Fin 3) ℝ K :=
      (sphereTripleBasis x y z hxy hxz hyz).map e.equivRange.toLinearEquiv
    have hb0 : Orthonormal ℝ b0 := by
      simpa [b0] using
        (sphereTripleBasis_orthonormal x y z hxy hxz hyz).mapLinearIsometryEquiv
          e.equivRange
    let bON : OrthonormalBasis (Fin 3) ℝ K := b0.toOrthonormalBasis hb0
    let bONLift : OrthonormalBasis (ULift.{v} (Fin 3)) ℝ K :=
      bON.reindex (Equiv.ulift.symm)
    let b : HilbertBasis (ULift.{v} (Fin 3)) ℝ K := bONLift.toHilbertBasis
    have hb_apply : ∀ i : ULift.{v} (Fin 3), ((b i : K) : H) = e (t i.down) := by
      intro i
      simp [b, bONLift, bON, b0, t, sphereTripleBasis_apply]
      exact LinearIsometry.equivRange_apply_coe e _
    have hsumK := OrthogonalProjection.hasSum_rankOne_basis (𝕜 := ℝ) b a
    have hsumK' :
        HasSum (fun i : ULift.{v} (Fin 3) => (P i.down).1 a)
          ((OrthogonalProjection.rangeOfRealTripleIsometry e).1 a) := by
      simpa only [P, hb_apply, OrthogonalProjection.rangeOfRealTripleIsometry_val] using hsumK
    have hsumRFin : HasSum (fun i : Fin 3 => (P i).1 a) (R.1 a) := by
      simpa [R, P01, OrthogonalProjection.add, Fin.sum_univ_three] using
        (hasSum_fintype (f := fun i : Fin 3 => (P i).1 a))
    have hsumR : HasSum (fun i : ULift.{v} (Fin 3) => (P i.down).1 a) (R.1 a) := by
      exact (Equiv.ulift.hasSum_iff.mpr hsumRFin)
    exact hsumR.unique hsumK'
  have h01m := m.additive (P 0) (P 1) h01
  have h012m := m.additive P01 (P 2) h012
  have hP01 : m.μ P01 = m.μ (P 0) + m.μ (P 1) := by
    simpa [P01] using h01m
  have h012m' :
      m.μ (OrthogonalProjection.rangeOfRealTripleIsometry e) =
        (m.μ (P 0) + m.μ (P 1)) + m.μ (P 2) := by
    calc
      m.μ (OrthogonalProjection.rangeOfRealTripleIsometry e) = m.μ R := by rw [hR]
      _ = m.μ P01 + m.μ (P 2) := by simpa [R] using h012m
      _ = (m.μ (P 0) + m.μ (P 1)) + m.μ (P 2) := by rw [hP01]
  simpa [P, t, sphereTripleVec] using h012m'.symm

/-- The sphere frame obtained by restricting a projection measure along a
real three-dimensional linear isometry. -/
def sphereFrameOfIsometry
    (m : ProjectionMeasure ℝ H) (e : RealSphereAmbient →ₗᵢ[ℝ] H)
    (x : spherePoint3) : ℝ :=
  m.quadraticValue (e x.1)

theorem sphereFrameOfIsometry_nonneg
    (m : ProjectionMeasure ℝ H) (e : RealSphereAmbient →ₗᵢ[ℝ] H) :
    ∀ x : spherePoint3, 0 ≤ sphereFrameOfIsometry m e x := by
  intro x
  exact m.quadraticValue_nonneg _

theorem sphereFrameOfIsometry_isSphereFrameFunction
    (m : ProjectionMeasure ℝ H) (e : RealSphereAmbient →ₗᵢ[ℝ] H) :
    IsSphereFrameFunction (sphereFrameOfIsometry m e) := by
  intro x y z hxy hxz hyz
  have hxyz := m.sum_rankOne_mapped_sphereTriple e x y z hxy hxz hyz
  have hstd := m.sum_rankOne_mapped_sphereTriple e sphereE1 sphereE2 sphereE3
    sphereE1_inner_sphereE2 sphereE1_inner_sphereE3 sphereE2_inner_sphereE3
  have hvalue : ∀ p : spherePoint3,
      sphereFrameOfIsometry m e p =
        m.μ (OrthogonalProjection.rankOne (𝕜 := ℝ) (e p.1)) := by
    intro p
    simp [sphereFrameOfIsometry, quadraticValue, e.norm_map p.1, p.2]
  simpa only [hvalue] using hxyz.trans hstd.symm

/-- On the range of every real three-dimensional linear isometry, the
homogeneous function associated with a projection measure is quadratic. -/
theorem exists_quadraticMap_on_realTripleIsometry
    (m : ProjectionMeasure ℝ H) (e : RealSphereAmbient →ₗᵢ[ℝ] H) :
    ∃ Q : QuadraticMap ℝ RealSphereAmbient ℝ,
      ∀ x : RealSphereAmbient, m.quadraticValue (e x) = Q x := by
  let f : spherePoint3 → ℝ := sphereFrameOfIsometry m e
  have hf : IsSphereFrameFunction f :=
    sphereFrameOfIsometry_isSphereFrameFunction m e
  have hnonneg : ∀ x : spherePoint3, 0 ≤ f x :=
    sphereFrameOfIsometry_nonneg m e
  obtain ⟨Q, hQ⟩ := s2_nonnegative_frame_is_quadratic f hf hnonneg
  refine ⟨Q, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  let u : RealSphereAmbient := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := by
    simpa [u] using norm_smul_inv_norm (𝕜 := ℝ) hx
  let us : spherePoint3 := ⟨u, hu⟩
  have hxu : ‖x‖ • u = x := by
    simp [u, smul_smul, hx]
  have hunit : m.quadraticValue (e u) = Q u := by
    simpa [f, sphereFrameOfIsometry, us] using hQ us
  calc
    m.quadraticValue (e x) = m.quadraticValue (e (‖x‖ • u)) := by rw [hxu]
    _ = m.quadraticValue (‖x‖ • e u) := by rw [e.map_smul]
    _ = ‖x‖ ^ 2 * m.quadraticValue (e u) := by
      simpa using m.quadraticValue_smul ‖x‖ (e u)
    _ = ‖x‖ ^ 2 * Q u := by rw [hunit]
    _ = Q (‖x‖ • u) := by
      simpa [pow_two] using (Q.map_smul ‖x‖ u).symm
    _ = Q x := by rw [hxu]

end ProjectionMeasure

end ClassicalGleason.Separable
