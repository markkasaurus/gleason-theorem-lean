import Gleason.Harmonic.HighDegree.EvenBoundedDecomposition

noncomputable section

open Complex InnerProductSpace

instance evenBoundedHarmonicPolyHomogeneousImageSubmodule_finiteDimensional (N : ℕ) :
    FiniteDimensional ℝ ↥(evenBoundedHarmonicPolyHomogeneousImageSubmodule N) := by
  rw [evenBoundedHarmonicPolyHomogeneousImageSubmodule]
  infer_instance

def lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} (hN : 1 ≤ N) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N →ₗ[ℝ]
      lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN :=
  Submodule.linearProjOfIsCompl
    (lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN)
    (highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (isCompl_lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
      hN)

def highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} (hN : 1 ≤ N) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N →ₗ[ℝ]
      highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
  Submodule.linearProjOfIsCompl
    (highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN)
    (isCompl_lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
      hN).symm

@[simp] theorem lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_left
    {N : ℕ} (hN : 1 ≤ N)
    (f : lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN) :
    lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f = f := by
  simpa [lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule] using
    Submodule.linearProjOfIsCompl_apply_left
      (p := lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN)
      (q := highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
      (h :=
        isCompl_lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
          hN)
      f

@[simp] theorem highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_left
    {N : ℕ} (hN : 1 ≤ N)
    (f : highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f = f := by
  simpa [highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule] using
    Submodule.linearProjOfIsCompl_apply_left
      (p := highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
      (q := lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN)
      (h :=
        (isCompl_lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
          hN).symm)
      f

theorem lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_eq_zero_iff
    {N : ℕ} (hN : 1 ≤ N)
    {f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N} :
    lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f = 0 ↔
      f ∈ highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N := by
  simpa [lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule] using
    (Submodule.linearProjOfIsCompl_apply_eq_zero_iff
      (p := lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN)
      (q := highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
      (h :=
        isCompl_lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
          hN))

theorem highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_eq_zero_iff
    {N : ℕ} (hN : 1 ≤ N)
    {f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N} :
    highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f = 0 ↔
      f ∈ lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN := by
  simpa [highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule] using
    (Submodule.linearProjOfIsCompl_apply_eq_zero_iff
      (p := highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
      (q := lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN)
      (h :=
        (isCompl_lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
          hN).symm))

theorem highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_eq_zero_of_mem_frame
    {N : ℕ} (hN : 1 ≤ N)
    {f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N}
    (hf : (f : C(spherePoint3, ℝ)) ∈ continuousSphereFrameSubmodule) :
    highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f = 0 := by
  rw [highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_eq_zero_iff]
  have hf_even :
      (f : C(spherePoint3, ℝ)) ∈
        evenBoundedHarmonicPolyHomogeneousImageSubmodule N ⊓ continuousSphereFrameSubmodule := by
    exact ⟨f.property, hf⟩
  rw [evenBoundedHarmonicPolyHomogeneousImageSubmodule_inf_continuousSphereFrameSubmodule_eq_low hN]
    at hf_even
  exact hf_even

def ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} (hN : 1 ≤ N) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N →ₗ[ℝ] C(spherePoint3, ℝ) :=
  (evenBoundedHarmonicPolyHomogeneousImageSubmodule N).subtype.comp
    ((lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN).subtype.comp
      (lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN))

def ambientHighProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule
    {N : ℕ} (hN : 1 ≤ N) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N →ₗ[ℝ] C(spherePoint3, ℝ) :=
  (evenBoundedHarmonicPolyHomogeneousImageSubmodule N).subtype.comp
    ((highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).subtype.comp
      (highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN))

@[simp] theorem ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply
    {N : ℕ} (hN : 1 ≤ N)
    (f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f =
      (lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f : C(spherePoint3, ℝ)) := by
  rfl

@[simp] theorem ambientHighProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply
    {N : ℕ} (hN : 1 ≤ N)
    (f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    ambientHighProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f =
      (highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f : C(spherePoint3, ℝ)) := by
  rfl

@[simp] theorem ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_low
    {N : ℕ} (hN : 1 ≤ N)
    (f : lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN) :
    ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN
      ((lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN).subtype f) =
        (f : C(spherePoint3, ℝ)) := by
  simp [ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule]

@[simp] theorem ambientHighProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_high
    {N : ℕ} (hN : 1 ≤ N)
    (f : highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    ambientHighProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN
      ((highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).subtype f) =
        (f : C(spherePoint3, ℝ)) := by
  change
    (((highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN)
        ((highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).subtype f) :
      highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
      C(spherePoint3, ℝ)) = (f : C(spherePoint3, ℝ))
  exact congrArg
      (fun g : highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N =>
        (g : C(spherePoint3, ℝ)))
      (highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_left hN f)

@[simp] theorem ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_high
    {N : ℕ} (hN : 1 ≤ N)
    (f : highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN
      ((highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).subtype f) = 0 := by
  change
    (((lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN)
        ((highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).subtype f) :
      lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN) :
      C(spherePoint3, ℝ)) = 0
  have h0 :
      lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN
        ((highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).subtype f) = 0 := by
    rw [lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_eq_zero_iff]
    exact f.property
  exact congrArg
    (fun g : lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN =>
      (g : C(spherePoint3, ℝ)))
    h0

@[simp] theorem ambientHighProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_low
    {N : ℕ} (hN : 1 ≤ N)
    (f : lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN) :
    ambientHighProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN
      ((lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN).subtype f) = 0 := by
  simp [ambientHighProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule,
    highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_eq_zero_iff]

theorem ambientLowProj_add_ambientHighProj_eq_self
    {N : ℕ} (hN : 1 ≤ N)
    (f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f +
      ambientHighProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f =
        (f : C(spherePoint3, ℝ)) := by
  let hCompl :=
    isCompl_lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule_highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule
      hN
  have hsum := Submodule.IsCompl.projection_add_projection_eq_self hCompl f
  change
    ((lowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f :
        lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN) :
      evenBoundedHarmonicPolyHomogeneousImageSubmodule N) +
      ((highProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f :
        highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
      evenBoundedHarmonicPolyHomogeneousImageSubmodule N) = f at hsum
  exact congrArg
    (fun g : evenBoundedHarmonicPolyHomogeneousImageSubmodule N => (g : C(spherePoint3, ℝ))) hsum

noncomputable def ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM
    {N : ℕ} (hN : 1 ≤ N) :
    evenBoundedHarmonicPolyHomogeneousImageSubmodule N →L[ℝ] C(spherePoint3, ℝ) :=
  LinearMap.toContinuousLinearMap
    (ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN)

@[simp] theorem ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM_apply
    {N : ℕ} (hN : 1 ≤ N)
    (f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM hN f =
      ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f := by
  simp [ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM]

theorem norm_ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le
    {N : ℕ} (hN : 1 ≤ N)
    (f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N) :
    ‖ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f‖
      ≤ ‖ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM hN‖ * ‖(f : C(spherePoint3, ℝ))‖ := by
  simpa using
    (ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM hN).le_opNorm f

theorem norm_low_le_const_mul_norm_sub_of_mem_highEvenBounded
    {N : ℕ} (hN : 1 ≤ N)
    {h l : C(spherePoint3, ℝ)}
    (hh : h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (hl : l ∈ lowHarmonicPolyHomogeneousImageSubmodule) :
    ‖l‖ ≤
      ‖ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM hN‖ * ‖h - l‖ := by
  let f : evenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
    ⟨h - l,
      Submodule.sub_mem _ (highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule N hh)
        (lowHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule hN hl)⟩
  have hproj :
      ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN f = -l := by
    let hHighSub : highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N :=
      ⟨⟨h,
          highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule N hh⟩,
        by
          simpa [highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule] using hh⟩
    let lLowSub : lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN :=
      ⟨⟨l,
          lowHarmonicPolyHomogeneousImageSubmodule_le_evenBoundedHarmonicPolyHomogeneousImageSubmodule hN hl⟩,
        by
          simpa [lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule] using hl⟩
    have hf_eq :
        f =
          (highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).subtype hHighSub -
            (lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN).subtype lLowSub := by
      ext
      rfl
    have hhigh :
        ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN
            ((highInEvenBoundedHarmonicPolyHomogeneousImageSubmodule N).subtype hHighSub) = 0 := by
      simpa [hHighSub] using
        ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_high hN hHighSub
    have hlow :
        ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN
            ((lowInEvenBoundedHarmonicPolyHomogeneousImageSubmodule hN).subtype lLowSub) = l := by
      simpa [lLowSub] using
        ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_apply_low hN lLowSub
    rw [hf_eq, map_sub]
    rw [hhigh, hlow]
    simp
  have hbound :=
    norm_ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmodule_le hN f
  rw [hproj, norm_neg] at hbound
  simpa using hbound

theorem norm_sphereE3_le_one_add_const_mul_norm_sub_of_mem_highEvenBounded
    {N : ℕ} (hN : 1 ≤ N)
    {h l : C(spherePoint3, ℝ)}
    (hh : h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N)
    (hl : l ∈ lowHarmonicPolyHomogeneousImageSubmodule) :
    ‖h sphereE3‖ ≤
      (1 + ‖ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM hN‖) * ‖h - l‖ := by
  have hlbound :
      ‖l‖ ≤
        ‖ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM hN‖ * ‖h - l‖ :=
    norm_low_le_const_mul_norm_sub_of_mem_highEvenBounded hN hh hl
  have hdist : ‖h sphereE3 - l sphereE3‖ ≤ ‖h - l‖ := by
    simpa [ContinuousMap.sub_apply, norm_sub_rev] using
      (h - l).norm_coe_le_norm sphereE3
  calc
    ‖h sphereE3‖ ≤ ‖h sphereE3 - l sphereE3‖ + ‖l sphereE3‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        norm_add_le (h sphereE3 - l sphereE3) (l sphereE3)
    _ ≤ ‖h - l‖ + ‖l‖ := by
      gcongr
      exact l.norm_coe_le_norm sphereE3
    _ ≤ ‖h - l‖ +
          ‖ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM hN‖ * ‖h - l‖ := by
        gcongr
    _ = (1 + ‖ambientLowProjEvenBoundedHarmonicPolyHomogeneousImageSubmoduleCLM hN‖) * ‖h - l‖ := by
        ring
