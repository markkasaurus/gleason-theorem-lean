import Gleason.Continuity.GlobalOscillation
import Gleason.Harmonic.Sphere.SphereFrameQ02

noncomputable section

open GleasonBridge RankOne Set Complex Real InnerProductSpace
open scoped Topology

def spherePointCoord (x : spherePoint3) : ℝ × ℝ × ℝ :=
  (x.1.fst.re, (x.1.fst.im, x.1.snd))

lemma spherePointCoord_sq_sum (x : spherePoint3) :
    (spherePointCoord x).1 ^ 2 +
        (spherePointCoord x).2.1 ^ 2 +
        (spherePointCoord x).2.2 ^ 2 = 1 := by
  have hinner :=
    (WithLp.prod_inner_apply (𝕜 := ℝ) x.1 x.1)
  have hnormsq : ‖x.1‖ ^ 2 = ‖x.1.fst‖ ^ 2 + x.1.snd ^ 2 := by
    simpa [inner_self_eq_norm_sq_to_K, pow_two] using hinner
  have hcomplex : ‖x.1.fst‖ ^ 2 = x.1.fst.re ^ 2 + x.1.fst.im ^ 2 := by
    simpa [pow_two] using (Complex.sq_norm (x.1.fst))
  have hx2 : ‖x.1‖ ^ 2 = 1 := by
    nlinarith [x.2]
  have hsum : x.1.fst.re ^ 2 + x.1.fst.im ^ 2 + x.1.snd ^ 2 = 1 := by
    nlinarith [hx2, hnormsq, hcomplex]
  simpa [spherePointCoord] using hsum

lemma spherePointCoord_mem_coordSphereSet (x : spherePoint3) :
    spherePointCoord x ∈ coordSphereSet := by
  exact spherePointCoord_sq_sum x

@[simp] lemma spherePointCoord_sphereE1 :
    spherePointCoord sphereE1 = coordBase := by
  ext <;> simp [spherePointCoord, sphereE1, coordBase]

@[simp] lemma spherePointCoord_sphereE2 :
    spherePointCoord sphereE2 = vCoord := by
  ext <;> simp [spherePointCoord, sphereE2, vCoord]

@[simp] lemma spherePointCoord_sphereE3 :
    spherePointCoord sphereE3 = poleCoord := by
  ext <;> simp [spherePointCoord, sphereE3, poleCoord]

lemma coordDot_spherePointCoord (x y : spherePoint3) :
    coordDot (spherePointCoord x) (spherePointCoord y) = inner (𝕜 := ℝ) x.1 y.1 := by
  simp [spherePointCoord, coordDot, Complex.mul_re, add_assoc, mul_comm]

lemma continuous_spherePointCoord : Continuous spherePointCoord := by
  let fstCLM : WithLp 2 (ℂ × ℝ) → ℂ := @WithLp.fst 2 ℂ ℝ
  let sndCLM : WithLp 2 (ℂ × ℝ) → ℝ := @WithLp.snd 2 ℂ ℝ
  have hfstCLM : Continuous fstCLM := by
    simpa [fstCLM] using (WithLp.continuous_fst 2 ℂ ℝ)
  have hsndCLM : Continuous sndCLM := by
    simpa [sndCLM] using (WithLp.continuous_snd 2 ℂ ℝ)
  have hfst : Continuous fun x : spherePoint3 => (x.1.fst : ℂ) := by
    simpa [fstCLM] using hfstCLM.comp continuous_subtype_val
  have hsnd : Continuous fun x : spherePoint3 => (x.1.snd : ℝ) := by
    simpa [sndCLM] using hsndCLM.comp continuous_subtype_val
  have hfstre : Continuous (fun x : spherePoint3 => (x.1.fst).re) :=
    Complex.continuous_re.comp hfst
  have hfstim : Continuous (fun x : spherePoint3 => (x.1.fst).im) :=
    Complex.continuous_im.comp hfst
  change Continuous (fun x : spherePoint3 => ((x.1.fst).re, ((x.1.fst).im, x.1.snd)))
  exact hfstre.prodMk (hfstim.prodMk hsnd)

def coordSphereFrameFun
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (μ : FrameFunction H) (u v p : H) :
    spherePoint3 → ℝ :=
  fun x => frame_quadratic μ (coordPoint u v p (spherePointCoord x))

def uvpVec
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v p : H) : Fin 3 → H
  | 0 => u
  | 1 => v
  | 2 => p

def coordSphereVec
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (u v p : H) (x y z : spherePoint3) : Fin 3 → H
  | 0 => coordPoint u v p (spherePointCoord x)
  | 1 => coordPoint u v p (spherePointCoord y)
  | 2 => coordPoint u v p (spherePointCoord z)

lemma uvpVec_orthonormal
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0) :
    Orthonormal ℂ (uvpVec u v p) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · simp [uvpVec, hu]
  · simpa [uvpVec] using huv
  · simpa [uvpVec] using hup
  · simpa [uvpVec, inner_eq_zero_symm] using huv
  · simp [uvpVec, hv]
  · simpa [uvpVec] using hvp
  · simpa [uvpVec, inner_eq_zero_symm] using hup
  · simpa [uvpVec, inner_eq_zero_symm] using hvp
  · simp [uvpVec, hp]

lemma coordSphereVec_orthonormal
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (x y z : spherePoint3)
    (hxy : inner (𝕜 := ℝ) x.1 y.1 = 0)
    (hxz : inner (𝕜 := ℝ) x.1 z.1 = 0)
    (hyz : inner (𝕜 := ℝ) y.1 z.1 = 0) :
    Orthonormal ℂ (coordSphereVec u v p x y z) := by
  have hyx : inner (𝕜 := ℝ) y.1 x.1 = 0 := by
    rw [real_inner_comm]
    exact hxy
  have hzx : inner (𝕜 := ℝ) z.1 x.1 = 0 := by
    rw [real_inner_comm]
    exact hxz
  have hzy : inner (𝕜 := ℝ) z.1 y.1 = 0 := by
    rw [real_inner_comm]
    exact hyz
  have hxy' : coordDot (spherePointCoord x) (spherePointCoord y) = 0 := by
    have htmp := coordDot_spherePointCoord x y
    rw [hxy] at htmp
    exact htmp
  have hxz' : coordDot (spherePointCoord x) (spherePointCoord z) = 0 := by
    have htmp := coordDot_spherePointCoord x z
    rw [hxz] at htmp
    exact htmp
  have hyx' : coordDot (spherePointCoord y) (spherePointCoord x) = 0 := by
    have htmp := coordDot_spherePointCoord y x
    rw [hyx] at htmp
    exact htmp
  have hyz' : coordDot (spherePointCoord y) (spherePointCoord z) = 0 := by
    have htmp := coordDot_spherePointCoord y z
    rw [hyz] at htmp
    exact htmp
  have hzx' : coordDot (spherePointCoord z) (spherePointCoord x) = 0 := by
    have htmp := coordDot_spherePointCoord z x
    rw [hzx] at htmp
    exact htmp
  have hzy' : coordDot (spherePointCoord z) (spherePointCoord y) = 0 := by
    have htmp := coordDot_spherePointCoord z y
    rw [hzy] at htmp
    exact htmp
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j
  · simp [coordSphereVec, coordPoint_norm, spherePointCoord_sq_sum, hu, hv, hp, huv, hup, hvp]
  · simpa [coordSphereVec, hxy'] using
      (inner_coordPoint_coordPoint hu hv hp huv hup hvp
        (spherePointCoord x) (spherePointCoord y))
  · simpa [coordSphereVec, hxz'] using
      (inner_coordPoint_coordPoint hu hv hp huv hup hvp
        (spherePointCoord x) (spherePointCoord z))
  · simpa [coordSphereVec, hyx'] using
      (inner_coordPoint_coordPoint hu hv hp huv hup hvp
        (spherePointCoord y) (spherePointCoord x))
  · simp [coordSphereVec, coordPoint_norm, spherePointCoord_sq_sum, hu, hv, hp, huv, hup, hvp]
  · simpa [coordSphereVec, hyz'] using
      (inner_coordPoint_coordPoint hu hv hp huv hup hvp
        (spherePointCoord y) (spherePointCoord z))
  · simpa [coordSphereVec, hzx'] using
      (inner_coordPoint_coordPoint hu hv hp huv hup hvp
        (spherePointCoord z) (spherePointCoord x))
  · simpa [coordSphereVec, hzy'] using
      (inner_coordPoint_coordPoint hu hv hp huv hup hvp
        (spherePointCoord z) (spherePointCoord y))
  · simp [coordSphereVec, coordPoint_norm, spherePointCoord_sq_sum, hu, hv, hp, huv, hup, hvp]

lemma span_range_uvpVec
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u v p : H) :
    Submodule.span ℂ (Set.range (uvpVec u v p)) =
      Submodule.span ℂ ({u, v, p} : Set H) := by
  have hset : Set.range (uvpVec u v p) = ({u, v, p} : Set H) := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [uvpVec]
    · intro hq
      simp at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨0, by simp [uvpVec]⟩
      · exact ⟨1, by simp [uvpVec]⟩
      · exact ⟨2, by simp [uvpVec]⟩
  rw [hset]

lemma span_range_coordSphereVec
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (u v p : H) (x y z : spherePoint3) :
    Submodule.span ℂ (Set.range (coordSphereVec u v p x y z)) =
      Submodule.span ℂ ({coordPoint u v p (spherePointCoord x),
        coordPoint u v p (spherePointCoord y),
        coordPoint u v p (spherePointCoord z)} : Set H) := by
  have hset :
      Set.range (coordSphereVec u v p x y z) =
        ({coordPoint u v p (spherePointCoord x),
          coordPoint u v p (spherePointCoord y),
          coordPoint u v p (spherePointCoord z)} : Set H) := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [coordSphereVec]
    · intro hq
      simp at hq
      rcases hq with rfl | rfl | rfl
      · exact ⟨0, by simp [coordSphereVec]⟩
      · exact ⟨1, by simp [coordSphereVec]⟩
      · exact ⟨2, by simp [coordSphereVec]⟩
  rw [hset]

theorem coordSphereFrameFun_mem_sphereFrameSubmodule_of_zero_at_p
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic μ p = 0) :
    coordSphereFrameFun μ u v p ∈ sphereFrameSubmodule := by
  intro x y z hxy hxz hyz
  let xH : H := coordPoint u v p (spherePointCoord x)
  let yH : H := coordPoint u v p (spherePointCoord y)
  let zH : H := coordPoint u v p (spherePointCoord z)
  let K : Submodule ℂ H := Submodule.span ℂ ({u, v, p} : Set H)
  let S : Submodule ℂ H := Submodule.span ℂ ({xH, yH, zH} : Set H)
  have huvp_on : Orthonormal ℂ (uvpVec u v p) :=
    uvpVec_orthonormal hu hv hp huv hup hvp
  have hxyz_on : Orthonormal ℂ (coordSphereVec u v p x y z) :=
    coordSphereVec_orthonormal hu hv hp huv hup hvp x y z hxy hxz hyz
  have hKfin : Module.finrank ℂ K = 3 := by
    dsimp [K]
    rw [← span_range_uvpVec u v p]
    simpa using finrank_span_eq_card huvp_on.linearIndependent
  have hSfin : Module.finrank ℂ S = 3 := by
    dsimp [S, xH, yH, zH]
    rw [← span_range_coordSphereVec u v p x y z]
    simpa using finrank_span_eq_card hxyz_on.linearIndependent
  have hSle : S ≤ K := by
    have hsubset : ({xH, yH, zH} : Set H) ⊆ K := by
      intro q hq
      simp at hq
      rcases hq with rfl | rfl | rfl
      · dsimp [xH, K]
        exact coordPoint_mem_span u v p (spherePointCoord x)
      · dsimp [yH, K]
        exact coordPoint_mem_span u v p (spherePointCoord y)
      · dsimp [zH, K]
        exact coordPoint_mem_span u v p (spherePointCoord z)
    dsimp [S]
    exact Submodule.span_le.mpr hsubset
  have hSK : S = K := by
    apply Submodule.eq_of_le_of_finrank_le hSle
    simp [hKfin, hSfin]
  have hxH_norm : ‖xH‖ = 1 := by
    dsimp [xH]
    exact coordPoint_norm hu hv hp huv hup hvp (spherePointCoord_sq_sum x)
  have hyH_norm : ‖yH‖ = 1 := by
    dsimp [yH]
    exact coordPoint_norm hu hv hp huv hup hvp (spherePointCoord_sq_sum y)
  have hzH_norm : ‖zH‖ = 1 := by
    dsimp [zH]
    exact coordPoint_norm hu hv hp huv hup hvp (spherePointCoord_sq_sum z)
  have hxyH : inner (𝕜 := ℂ) xH yH = 0 := by
    dsimp [xH, yH]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    simp [coordDot_spherePointCoord, hxy]
  have hxzH : inner (𝕜 := ℂ) xH zH = 0 := by
    dsimp [xH, zH]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    simp [coordDot_spherePointCoord, hxz]
  have hyzH : inner (𝕜 := ℂ) yH zH = 0 := by
    dsimp [yH, zH]
    rw [inner_coordPoint_coordPoint hu hv hp huv hup hvp]
    simp [coordDot_spherePointCoord, hyz]
  have hsum_xyz :
      frame_quadratic μ xH + frame_quadratic μ yH + frame_quadratic μ zH =
        μ.μ (GleasonRankOne.projectionOntoSpan (H := H) ({xH, yH, zH} : Set H)) :=
    GleasonRankOne.three_vector_sum (H := H) μ xH yH zH
      hxH_norm hyH_norm hzH_norm hxyH hxzH hyzH
  have hsum_uvp :
      frame_quadratic μ u + frame_quadratic μ v + frame_quadratic μ p =
        μ.μ (GleasonRankOne.projectionOntoSpan (H := H) ({u, v, p} : Set H)) :=
    GleasonRankOne.three_vector_sum (H := H) μ u v p hu hv hp huv hup hvp
  have hproj :
      GleasonRankOne.projectionOntoSpan (H := H) ({xH, yH, zH} : Set H) =
        GleasonRankOne.projectionOntoSpan (H := H) ({u, v, p} : Set H) := by
    dsimp [S, K] at hSK
    simpa [GleasonRankOne.projectionOntoSpan] using
      congrArg (GleasonRankOne.projectionOntoSubmodule (H := H)) hSK
  have hsum :
      frame_quadratic μ xH + frame_quadratic μ yH + frame_quadratic μ zH =
        frame_quadratic μ u + frame_quadratic μ v + frame_quadratic μ p := by
    rw [hsum_xyz, hsum_uvp, hproj]
  simpa [coordSphereFrameFun, xH, yH, zH, hp0, coordPoint_base, coordPoint_vCoord,
    coordPoint_poleCoord, spherePointCoord_sphereE1, spherePointCoord_sphereE2,
    spherePointCoord_sphereE3] using hsum

theorem continuous_coordSphereFrameFun_of_zero_at_p
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic μ p = 0) :
    Continuous (coordSphereFrameFun μ u v p) := by
  have hcontOn :=
    frame_quadratic_continuousOn_coordSphere_of_zero_at_p
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hp0
  have hmaps : MapsTo spherePointCoord (Set.univ : Set spherePoint3) coordSphereSet := by
    intro x hx
    exact spherePointCoord_mem_coordSphereSet x
  have hcomp : ContinuousOn (coordSphereFrameFun μ u v p) Set.univ := by
    simpa [coordSphereFrameFun] using
      ContinuousOn.comp hcontOn continuous_spherePointCoord.continuousOn hmaps
  simpa [continuousOn_univ] using hcomp

def coordSphereFrameContinuousMap
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H)
    (u v p : H)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic μ p = 0) :
    C(spherePoint3, ℝ) :=
  ⟨coordSphereFrameFun μ u v p,
    continuous_coordSphereFrameFun_of_zero_at_p
      (hdim := hdim) (μ := μ) hu hv hp huv hup hvp hp0⟩

theorem coordSphereFrameContinuousMap_mem_continuousSphereFrameSubmodule_of_zero_at_p
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
    (hdim : 3 ≤ Module.finrank ℂ H)
    (μ : FrameFunction H)
    {u v p : H}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hp : ‖p‖ = 1)
    (huv : inner (𝕜 := ℂ) u v = 0)
    (hup : inner (𝕜 := ℂ) u p = 0)
    (hvp : inner (𝕜 := ℂ) v p = 0)
    (hp0 : frame_quadratic μ p = 0) :
    coordSphereFrameContinuousMap hdim μ u v p hu hv hp huv hup hvp hp0 ∈
      continuousSphereFrameSubmodule := by
  show coordSphereFrameFun μ u v p ∈ sphereFrameSubmodule
  exact coordSphereFrameFun_mem_sphereFrameSubmodule_of_zero_at_p
    (μ := μ) hu hv hp huv hup hvp hp0
