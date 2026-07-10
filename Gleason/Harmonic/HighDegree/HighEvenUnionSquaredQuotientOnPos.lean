import Gleason.Harmonic.HighDegree.HighEvenUnionSquaredProfileGeneric
import Gleason.Harmonic.HighDegree.HighEvenBoundedSquaredQuotientDegree
import Gleason.Harmonic.Profile.DegreeLTSquaredQuotientDefectBound
import Gleason.Harmonic.Zonal.NorthZonalSquaredProfileFixedContinuousTame
import Gleason.Harmonic.Profile.SquaredQuotientFactorUniqueness
import Gleason.Harmonic.Profile.SquaredProfileScaling

noncomputable section

open scoped Topology
open Complex InnerProductSpace Polynomial

def sqCenteredNorthZonalQuotientRaw (g : C(spherePoint3, ℝ)) (u : unitIcc) : ℝ :=
  if u.1 = 0 then 0 else sqCenteredNorthZonalProfile g u / u.1

def halfUnitIcc : unitIcc := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩

@[simp] theorem halfUnitIcc_val :
    (halfUnitIcc : ℝ) = (1 / 2 : ℝ) := by
  rfl

@[simp] lemma sqCenteredNorthZonalQuotientRaw_neg
    (g : C(spherePoint3, ℝ)) (u : unitIcc) :
    sqCenteredNorthZonalQuotientRaw (-g) u = - sqCenteredNorthZonalQuotientRaw g u := by
  by_cases hu0 : u.1 = 0
  · simp [sqCenteredNorthZonalQuotientRaw, hu0]
  · simp [sqCenteredNorthZonalQuotientRaw, hu0, sqCenteredNorthZonalProfile, centeredNorthZonalProfile,
      northZonalProfile, sub_eq_add_neg]
    ring

private lemma sqCenteredNorthZonalProfile_zero_eq_zero_local
    (g : C(spherePoint3, ℝ)) :
    sqCenteredNorthZonalProfile g zeroUnitIcc = 0 := by
  rw [sqCenteredNorthZonalProfile_apply]
  have hzero :
      (⟨Real.sqrt (↑zeroUnitIcc), by
        constructor
        · nlinarith [Real.sqrt_nonneg (↑zeroUnitIcc)]
        · have hsq : (Real.sqrt (↑zeroUnitIcc)) ^ 2 = (↑zeroUnitIcc : ℝ) := by
            exact Real.sq_sqrt zeroUnitIcc.2.1
          nlinarith [zeroUnitIcc.2.2, Real.sqrt_nonneg (↑zeroUnitIcc), hsq]⟩
        : Set.Icc (-1 : ℝ) 1) = zeroIcc := by
    apply Subtype.ext
    simp [zeroUnitIcc, zeroIcc]
  rw [hzero]
  simp [centeredNorthZonalProfile, northZonalProfile]

lemma sqCenteredNorthZonalProfile_eq_mul_sqCenteredNorthZonalQuotientRaw
    (g : C(spherePoint3, ℝ)) (u : unitIcc) :
    sqCenteredNorthZonalProfile g u = u.1 * sqCenteredNorthZonalQuotientRaw g u := by
  by_cases hu0 : u.1 = 0
  · have huz : u = zeroUnitIcc := by
      apply Subtype.ext
      exact hu0
    subst huz
    rw [sqCenteredNorthZonalProfile_zero_eq_zero_local]
    simp [sqCenteredNorthZonalQuotientRaw, zeroUnitIcc]
  · simp [sqCenteredNorthZonalQuotientRaw, hu0]
    field_simp [hu0]

theorem continuousOn_sqCenteredNorthZonalQuotientOnPos
    (g : C(spherePoint3, ℝ)) :
    ContinuousOn (fun u : unitIcc => sqCenteredNorthZonalProfile g u / u.1) {u : unitIcc | 0 < u.1} := by
  refine (continuous_sqCenteredNorthZonalProfile g).continuousOn.div continuous_subtype_val.continuousOn ?_
  intro u hu
  exact ne_of_gt hu

theorem sqCenteredNorthZonalQuotientRaw_weighted_fixed_of_mem_frame
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (u : unitIcc) :
    u.1 *
        (2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            Real.cos θ ^ 2 *
              sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u))) =
      sqCenteredNorthZonalProfile g u := by
  have hgpc : g ∈ continuousSphereGreatCirclePointConstraintSubmodule := by
    rw [continuousSphereGreatCirclePointConstraintSubmodule_eq_continuousSphereFrameSubmodule]
    exact hgframe
  calc
    u.1 *
        (2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            Real.cos θ ^ 2 *
              sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u)))
      = 2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            u.1 * (Real.cos θ ^ 2 *
              sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u))) := by
            rw [intervalIntegral.integral_const_mul]
            ring
    _ = 2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            sqCenteredNorthZonalProfile g (sqMulCosSelfMap θ u)) := by
            congr 2
            apply intervalIntegral.integral_congr_ae
            filter_upwards with θ
            rw [sqCenteredNorthZonalProfile_eq_mul_sqCenteredNorthZonalQuotientRaw]
            simp [sqMulCosSelfMap, mul_assoc, mul_comm]
    _ = sqCenteredNorthZonalProfile g u :=
      sqCenteredNorthZonalProfile_special_equation_of_mem_pointConstraint hgpc hgz u

theorem sqCenteredNorthZonalQuotientRaw_fixed_on_pos_of_mem_frame
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u : unitIcc}
    (hu : 0 < u.1) :
    2 * (((2 * Real.pi)⁻¹ : ℝ) *
      ∫ θ in 0..2 * Real.pi,
        Real.cos θ ^ 2 *
          sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u)) =
      sqCenteredNorthZonalQuotientRaw g u := by
  have hweighted :=
    sqCenteredNorthZonalQuotientRaw_weighted_fixed_of_mem_frame hgframe hgz u
  have hu0 : u.1 ≠ 0 := ne_of_gt hu
  have hraw :
      sqCenteredNorthZonalProfile g u = u.1 * sqCenteredNorthZonalQuotientRaw g u :=
    sqCenteredNorthZonalProfile_eq_mul_sqCenteredNorthZonalQuotientRaw g u
  rw [hraw] at hweighted
  exact (mul_left_cancel₀ hu0 hweighted)

lemma continuous_cos_sq_mul_sqCenteredNorthZonalQuotientRaw_comp
    (g : C(spherePoint3, ℝ)) {u : unitIcc}
    (hu : 0 < u.1) :
    Continuous (fun θ : ℝ =>
      Real.cos θ ^ 2 * sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u)) := by
  have hu0 : u.1 ≠ 0 := ne_of_gt hu
  have harg : Continuous fun θ : ℝ => sqMulCosSelfMap θ u := by
    exact Continuous.subtype_mk
      ((continuous_const : Continuous fun _ : ℝ => u.1).mul
        ((Real.continuous_cos).pow 2))
      (fun θ => mul_cos_sq_mem_Icc u θ)
  have hEq :
      (fun θ : ℝ =>
        Real.cos θ ^ 2 * sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u)) =
      fun θ : ℝ => sqCenteredNorthZonalProfile g (sqMulCosSelfMap θ u) / u.1 := by
    funext θ
    have hprof :
        sqCenteredNorthZonalProfile g (sqMulCosSelfMap θ u) =
          (u.1 * Real.cos θ ^ 2) *
            sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u) := by
      have hraw :=
      sqCenteredNorthZonalProfile_eq_mul_sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u)
      change
        sqCenteredNorthZonalProfile g (sqMulCosSelfMap θ u) =
          (sqMulCosSelfMap θ u).1 *
            sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u) at hraw
      change sqCenteredNorthZonalProfile g (sqMulCosSelfMap θ u) =
        (u.1 * Real.cos θ ^ 2) *
          sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u) at hraw
      simpa [mul_assoc, mul_left_comm, mul_comm] using hraw
    have hdiv := congrArg (fun x : ℝ => x / u.1) hprof
    simpa [hu0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv.symm
  rw [hEq]
  simpa using ((continuous_sqCenteredNorthZonalProfile g).comp harg).div_const u.1

lemma eq_zero_of_nonneg_continuous_intervalIntegral_zero_at
    {f : ℝ → ℝ}
    (hcont : Continuous f)
    (hnonneg : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 ≤ f θ)
    (hint0 : ∫ θ in 0..2 * Real.pi, f θ = 0)
    {θ0 : ℝ}
    (hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    f θ0 = 0 := by
  by_contra hne
  have hθ0Icc : θ0 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := ⟨le_of_lt hθ0.1, le_of_lt hθ0.2⟩
  have hpos0 : 0 < f θ0 := by
    have hnonneg0 := hnonneg θ0 hθ0Icc
    exact lt_of_le_of_ne hnonneg0 (Ne.symm hne)
  have hlt :
      (0 : ℝ) < ∫ θ in 0..2 * Real.pi, f θ := by
    have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
    have hzeroCont : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc (0 : ℝ) (2 * Real.pi)) :=
      continuousOn_const
    have hcontOn : ContinuousOn f (Set.Icc (0 : ℝ) (2 * Real.pi)) := hcont.continuousOn
    have hle :
        ∀ x ∈ Set.Ioc (0 : ℝ) (2 * Real.pi), (0 : ℝ) ≤ f x := by
      intro x hx
      exact hnonneg x ⟨le_of_lt hx.1, hx.2⟩
    have hltpt : ∃ c ∈ Set.Icc (0 : ℝ) (2 * Real.pi), (0 : ℝ) < f c := ⟨θ0, hθ0Icc, hpos0⟩
    simpa using
      (intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        hπ hzeroCont hcontOn hle hltpt)
  linarith

theorem sqCenteredNorthZonalQuotientRaw_eq_of_isMaxOn_initialSegment
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u : unitIcc}
    (hu : 0 < u.1)
    (hmax :
      IsMaxOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
        {v : unitIcc | 0 < v.1 ∧ v.1 ≤ u.1} u) :
    ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ u.1 →
      sqCenteredNorthZonalQuotientRaw g v = sqCenteredNorthZonalQuotientRaw g u := by
  intro v hv hvu
  by_cases huv : v.1 = u.1
  · exact congrArg (sqCenteredNorthZonalQuotientRaw g) (Subtype.ext huv)
  rw [isMaxOn_iff] at hmax
  have hvlt : v.1 < u.1 := lt_of_le_of_ne hvu huv
  let r : ℝ := v.1 / u.1
  have hr0 : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (div_lt_one hu).2 hvlt
  let θ0 : ℝ := Real.arccos (Real.sqrt r)
  have hθ0pos : 0 < θ0 := by
    have hsqrt_lt : Real.sqrt r < 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt hr0.le hr1
    exact Real.arccos_pos.mpr hsqrt_lt
  have hθ0lt : θ0 < 2 * Real.pi := by
    have hsqrt_pos : 0 < Real.sqrt r := by
      exact Real.sqrt_pos.mpr hr0
    have hlt' : θ0 < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hsqrt_pos
    linarith [Real.pi_pos]
  let F : ℝ → ℝ := fun θ =>
    (sqCenteredNorthZonalQuotientRaw g u -
      sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u)) *
        Real.cos θ ^ 2
  have hFcont : Continuous F := by
    have hcontQ := continuous_cos_sq_mul_sqCenteredNorthZonalQuotientRaw_comp g hu
    have hconst :
        Continuous (fun θ : ℝ => sqCenteredNorthZonalQuotientRaw g u * Real.cos θ ^ 2) := by
      exact continuous_const.mul (Real.continuous_cos.pow 2)
    suffices Continuous (fun θ : ℝ =>
        sqCenteredNorthZonalQuotientRaw g u * Real.cos θ ^ 2 -
          Real.cos θ ^ 2 * sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u)) by
      simpa [F, sub_mul, mul_comm, mul_left_comm, mul_assoc] using this
    exact hconst.sub hcontQ
  have hFnonneg :
      ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 ≤ F θ := by
    intro θ hθ
    by_cases hcos0 : Real.cos θ = 0
    · simp [F, hcos0]
    · have hpos : 0 < (sqMulCosSelfMap θ u).1 := by
        simpa [sqMulCosSelfMap, hcos0, hu, sq_pos_iff]
      have hle :
          sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u) ≤
            sqCenteredNorthZonalQuotientRaw g u := by
        have harg_le : (sqMulCosSelfMap θ u).1 ≤ u.1 := by
          change u.1 * Real.cos θ ^ 2 ≤ u.1
          have hcos_le : Real.cos θ ^ 2 ≤ 1 := by
            simpa using Real.cos_sq_le_one θ
          nlinarith [u.2.1, hcos_le]
        exact hmax (sqMulCosSelfMap θ u) ⟨hpos, harg_le⟩
      have hcossq_nonneg : 0 ≤ Real.cos θ ^ 2 := by positivity
      have hsub_nonneg :
          0 ≤ sqCenteredNorthZonalQuotientRaw g u -
              sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u) := by
        linarith
      exact mul_nonneg hsub_nonneg hcossq_nonneg
  have hFint :
      ∫ θ in 0..2 * Real.pi, F θ = 0 := by
    have hfixu :=
      sqCenteredNorthZonalQuotientRaw_fixed_on_pos_of_mem_frame hgframe hgz hu
    have hcosSq :
        ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 = Real.pi := by
      rw [integral_cos_sq]
      simp
    have hEqInt :
        ∫ θ in 0..2 * Real.pi, F θ
          = ∫ θ in 0..2 * Real.pi,
                sqCenteredNorthZonalQuotientRaw g u * Real.cos θ ^ 2 -
                  Real.cos θ ^ 2 *
                    sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u) := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro θ
      intro hθ
      simp [F]
      ring
    have hFrewrite :
        ∫ θ in 0..2 * Real.pi, F θ
          = (∫ θ in 0..2 * Real.pi,
                sqCenteredNorthZonalQuotientRaw g u * Real.cos θ ^ 2) -
              (∫ θ in 0..2 * Real.pi,
                Real.cos θ ^ 2 *
                  sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u)) := by
      rw [hEqInt, intervalIntegral.integral_sub]
      · exact (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
      · exact (continuous_cos_sq_mul_sqCenteredNorthZonalQuotientRaw_comp g hu).intervalIntegrable _ _
    have hfixu' :
        ∫ θ in 0..2 * Real.pi,
            Real.cos θ ^ 2 *
              sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ u)
          = Real.pi * sqCenteredNorthZonalQuotientRaw g u := by
      have htwoPi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp [htwoPi_ne, Real.pi_ne_zero] at hfixu
      linarith
    rw [hFrewrite, intervalIntegral.integral_const_mul, hcosSq, hfixu']
    ring
  have hFzero :
      F θ0 = 0 :=
    eq_zero_of_nonneg_continuous_intervalIntegral_zero_at hFcont hFnonneg hFint
      ⟨hθ0pos, hθ0lt⟩
  have hsqrt_le_one : Real.sqrt r ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (le_of_lt hr1)
  have hcos :
      Real.cos θ0 = Real.sqrt r := by
    dsimp [θ0]
    exact Real.cos_arccos (by nlinarith [Real.sqrt_nonneg r]) hsqrt_le_one
  have hsq :
      Real.cos θ0 ^ 2 = r := by
    calc
      Real.cos θ0 ^ 2 = (Real.sqrt r) ^ 2 := by rw [hcos]
      _ = r := by
            rw [Real.sq_sqrt]
            exact le_of_lt hr0
  have hscale : sqMulCosSelfMap θ0 u = v := by
    apply Subtype.ext
    change u.1 * Real.cos θ0 ^ 2 = v.1
    rw [hsq]
    dsimp [r]
    field_simp [show (u.1 : ℝ) ≠ 0 by exact ne_of_gt hu]
  have hcos_ne : Real.cos θ0 ≠ 0 := by
    rw [hcos]
    exact ne_of_gt (Real.sqrt_pos.mpr hr0)
  have hcos_sq_pos : 0 < Real.cos θ0 ^ 2 := by positivity
  have hsub_zero :
      sqCenteredNorthZonalQuotientRaw g u -
        sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ0 u) = 0 := by
    have :
        (sqCenteredNorthZonalQuotientRaw g u -
          sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ0 u)) *
            Real.cos θ0 ^ 2 = 0 := by
      simpa [F] using hFzero
    have hmul0 :=
      mul_eq_zero.mp this
    exact hmul0.resolve_right (pow_ne_zero 2 hcos_ne)
  simpa [hscale] using (sub_eq_zero.mp hsub_zero).symm

theorem sqCenteredNorthZonalQuotientRaw_eq_of_isMinOn_initialSegment
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u : unitIcc}
    (hu : 0 < u.1)
    (hmin :
      IsMinOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
        {v : unitIcc | 0 < v.1 ∧ v.1 ≤ u.1} u) :
    ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ u.1 →
      sqCenteredNorthZonalQuotientRaw g v = sqCenteredNorthZonalQuotientRaw g u := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have hmaxNeg :
      IsMaxOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw (-g) v)
        {v : unitIcc | 0 < v.1 ∧ v.1 ≤ u.1} u := by
    rw [isMinOn_iff] at hmin
    rw [isMaxOn_iff]
    intro x hx
    have hxmin := hmin x hx
    simpa using neg_le_neg hxmin
  intro v hv hvu
  have hEq :=
    sqCenteredNorthZonalQuotientRaw_eq_of_isMaxOn_initialSegment hnegFrame hnegZonal hu hmaxNeg hv hvu
  simpa using hEq

theorem sqCenteredNorthZonalQuotientRaw_eq_const_of_eq_const_on_initialSegment
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 : unitIcc}
    (hu0 : 0 < u0.1)
    {c : ℝ}
    (hconst0 :
      ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ u0.1 →
        sqCenteredNorthZonalQuotientRaw g v = c) :
    ∀ {u : unitIcc}, u0.1 ≤ u.1 →
      sqCenteredNorthZonalQuotientRaw g u = c := by
  intro u hu0u
  by_cases hu : 0 < u.1
  · by_cases huc : sqCenteredNorthZonalQuotientRaw g u = c
    · exact huc
    · let s : Set unitIcc := {v : unitIcc | u0.1 ≤ v.1 ∧ v.1 ≤ u.1}
      let f : unitIcc → ℝ := fun v => sqCenteredNorthZonalProfile g v / v.1
      have hsClosed : IsClosed s := by
        refine (isClosed_le continuous_const continuous_subtype_val).inter ?_
        exact isClosed_le continuous_subtype_val continuous_const
      have hsCompact : IsCompact s := hsClosed.isCompact
      have hsNonempty : s.Nonempty := ⟨u, ⟨hu0u, le_rfl⟩⟩
      have hconts : ContinuousOn f s := by
        refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
        intro v hv
        exact lt_of_lt_of_le hu0 hv.1
      rcases hsCompact.exists_isMaxOn hsNonempty hconts with ⟨vmax, hvmax, hmax⟩
      rcases hsCompact.exists_isMinOn hsNonempty hconts with ⟨vmin, hvmin, hmin⟩
      rw [isMaxOn_iff] at hmax
      rw [isMinOn_iff] at hmin
      have hvmax_pos : 0 < vmax.1 := lt_of_lt_of_le hu0 hvmax.1
      have hvmin_pos : 0 < vmin.1 := lt_of_lt_of_le hu0 hvmin.1
      have hmax_ge_u :
          sqCenteredNorthZonalQuotientRaw g u ≤ sqCenteredNorthZonalQuotientRaw g vmax := by
        have := hmax u ⟨hu0u, le_rfl⟩
        simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu, ne_of_gt hvmax_pos] using this
      have hmin_le_u :
          sqCenteredNorthZonalQuotientRaw g vmin ≤ sqCenteredNorthZonalQuotientRaw g u := by
        have := hmin u ⟨hu0u, le_rfl⟩
        simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu, ne_of_gt hvmin_pos] using this
      rcases lt_or_gt_of_ne huc with hlt | hgt
      · have hltmin : sqCenteredNorthZonalQuotientRaw g vmin < c := lt_of_le_of_lt hmin_le_u hlt
        have hpre_min :
            IsMinOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
              {v : unitIcc | 0 < v.1 ∧ v.1 ≤ vmin.1} vmin := by
          rw [isMinOn_iff]
          intro x hx
          by_cases hx0 : x.1 ≤ u0.1
          · rw [hconst0 hx.1 hx0]
            linarith
          · have hu0lt : u0.1 < x.1 := lt_of_not_ge hx0
            have hxs : x ∈ s := ⟨le_of_lt hu0lt, le_trans hx.2 hvmin.2⟩
            have := hmin x hxs
            simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hx.1, ne_of_gt hvmin_pos] using this
        have hconst :
            ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ vmin.1 →
              sqCenteredNorthZonalQuotientRaw g v =
                sqCenteredNorthZonalQuotientRaw g vmin := by
          exact sqCenteredNorthZonalQuotientRaw_eq_of_isMinOn_initialSegment
            (g := g) hgframe hgz (u := vmin) hvmin_pos hpre_min
        have hvmin_eq_c : sqCenteredNorthZonalQuotientRaw g vmin = c := by
          calc
            sqCenteredNorthZonalQuotientRaw g vmin = sqCenteredNorthZonalQuotientRaw g u0 := by
              symm
              exact hconst hu0 hvmin.1
            _ = c := hconst0 hu0 le_rfl
        exfalso
        linarith
      · have hcmax : c < sqCenteredNorthZonalQuotientRaw g vmax := lt_of_lt_of_le hgt hmax_ge_u
        have hpre_max :
            IsMaxOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
              {v : unitIcc | 0 < v.1 ∧ v.1 ≤ vmax.1} vmax := by
          rw [isMaxOn_iff]
          intro x hx
          by_cases hx0 : x.1 ≤ u0.1
          · rw [hconst0 hx.1 hx0]
            linarith
          · have hu0lt : u0.1 < x.1 := lt_of_not_ge hx0
            have hxs : x ∈ s := ⟨le_of_lt hu0lt, le_trans hx.2 hvmax.2⟩
            have := hmax x hxs
            simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hx.1, ne_of_gt hvmax_pos] using this
        have hconst :
            ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ vmax.1 →
              sqCenteredNorthZonalQuotientRaw g v =
                sqCenteredNorthZonalQuotientRaw g vmax := by
          exact sqCenteredNorthZonalQuotientRaw_eq_of_isMaxOn_initialSegment
            (g := g) hgframe hgz (u := vmax) hvmax_pos hpre_max
        have hvmax_eq_c : sqCenteredNorthZonalQuotientRaw g vmax = c := by
          calc
            sqCenteredNorthZonalQuotientRaw g vmax = sqCenteredNorthZonalQuotientRaw g u0 := by
              symm
              exact hconst hu0 hvmax.1
            _ = c := hconst0 hu0 le_rfl
        exfalso
        linarith
  · have hfalse : False := by
      linarith [hu0, hu0u, u.2.1]
    exact False.elim hfalse

theorem sqCenteredNorthZonalQuotientRaw_eq_limit_of_tendsto_zero
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {c : ℝ}
    (hlim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc) (𝓝 c)) :
    ∀ {u : unitIcc}, 0 < u.1 → sqCenteredNorthZonalQuotientRaw g u = c := by
  intro u hu
  by_cases huc : sqCenteredNorthZonalQuotientRaw g u = c
  · exact huc
  rcases lt_or_gt_of_ne huc with hlt | hgt
  · let ε : ℝ := (c - sqCenteredNorthZonalQuotientRaw g u) / 4
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    rcases
        (Metric.tendsto_nhdsWithin_nhds.mp hlim) ε hε with
      ⟨δ, hδ, hnear⟩
    let u0 : unitIcc := ⟨min (δ / 2) (u.1 / 2), by
      constructor
      · positivity
      · have huhalf : u.1 / 2 ≤ 1 := by nlinarith [u.2.2]
        exact le_trans (min_le_right _ _) huhalf⟩
    have hu0pos : 0 < u0.1 := by
      dsimp [u0]
      positivity
    have hu0ltδ : u0.1 < δ := by
      dsimp [u0]
      have : min (δ / 2) (u.1 / 2) ≤ δ / 2 := min_le_left _ _
      have hδ2 : δ / 2 < δ := by linarith
      exact lt_of_le_of_lt this hδ2
    have hu0ltu : u0.1 < u.1 := by
      dsimp [u0]
      have : min (δ / 2) (u.1 / 2) ≤ u.1 / 2 := min_le_right _ _
      linarith
    have hu0near : |sqCenteredNorthZonalQuotientRaw g u0 - c| < ε := by
      have hdist : dist u0 zeroUnitIcc < δ := by
        change |(u0 : ℝ) - 0| < δ
        simpa [abs_of_nonneg hu0pos.le] using hu0ltδ
      simpa [Real.dist_eq] using hnear hu0pos hdist
    have hu0gt : sqCenteredNorthZonalQuotientRaw g u0 > sqCenteredNorthZonalQuotientRaw g u := by
      have hlow : c - ε < sqCenteredNorthZonalQuotientRaw g u0 := by
        have hleft := (abs_lt.mp hu0near).1
        linarith
      dsimp [ε] at hlow
      linarith
    let seg : Set unitIcc := {v : unitIcc | u0.1 ≤ v.1 ∧ v.1 ≤ u.1}
    let f : unitIcc → ℝ := fun v => sqCenteredNorthZonalProfile g v / v.1
    have hsegClosed : IsClosed seg := by
      refine (isClosed_le continuous_const continuous_subtype_val).inter ?_
      exact isClosed_le continuous_subtype_val continuous_const
    have hsegCompact : IsCompact seg := hsegClosed.isCompact
    have hsegNonempty : seg.Nonempty := ⟨u, ⟨hu0ltu.le, le_rfl⟩⟩
    have hcontSeg : ContinuousOn f seg := by
      refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
      intro v hv
      exact lt_of_lt_of_le hu0pos hv.1
    rcases hsegCompact.exists_isMinOn hsegNonempty hcontSeg with ⟨vmin, hvmin, hmin⟩
    rw [isMinOn_iff] at hmin
    have hvmin_pos : 0 < vmin.1 := lt_of_lt_of_le hu0pos hvmin.1
    have hmin_le_u : sqCenteredNorthZonalQuotientRaw g vmin ≤ sqCenteredNorthZonalQuotientRaw g u := by
      have := hmin u ⟨hu0ltu.le, le_rfl⟩
      simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu, ne_of_gt hvmin_pos] using this
    have hu0_not_min : sqCenteredNorthZonalQuotientRaw g vmin < sqCenteredNorthZonalQuotientRaw g u0 := by
      linarith
    have hpre_min :
        IsMinOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
          {v : unitIcc | 0 < v.1 ∧ v.1 ≤ vmin.1} vmin := by
      rw [isMinOn_iff]
      intro x hx
      by_cases hxlt : x.1 < u0.1
      · have hxdist : dist x zeroUnitIcc < δ := by
          have hxδ : x.1 < δ := lt_trans hxlt hu0ltδ
          change |(x : ℝ) - 0| < δ
          simpa [abs_of_nonneg hx.1.le] using hxδ
        have hxnear : |sqCenteredNorthZonalQuotientRaw g x - c| < ε := by
          simpa [Real.dist_eq] using hnear hx.1 hxdist
        have hxlower : c - ε < sqCenteredNorthZonalQuotientRaw g x := by
          have hleft := (abs_lt.mp hxnear).1
          linarith
        have hvmin_lt : sqCenteredNorthZonalQuotientRaw g vmin < c - ε := by
          dsimp [ε]
          linarith [hmin_le_u, hlt]
        linarith
      · have hu0le : u0.1 ≤ x.1 := le_of_not_gt hxlt
        have hxs' : x ∈ seg := ⟨hu0le, le_trans hx.2 hvmin.2⟩
        have := hmin x hxs'
        simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hx.1, ne_of_gt hvmin_pos] using this
    have hconst :
        ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ vmin.1 →
          sqCenteredNorthZonalQuotientRaw g v = sqCenteredNorthZonalQuotientRaw g vmin := by
      exact sqCenteredNorthZonalQuotientRaw_eq_of_isMinOn_initialSegment
        (g := g) hgframe hgz (u := vmin) hvmin_pos hpre_min
    have hu0eq : sqCenteredNorthZonalQuotientRaw g u0 = sqCenteredNorthZonalQuotientRaw g vmin := by
      exact hconst hu0pos hvmin.1
    linarith [hmin_le_u, hu0gt, hu0eq]
  · let ε : ℝ := (sqCenteredNorthZonalQuotientRaw g u - c) / 4
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    rcases
        (Metric.tendsto_nhdsWithin_nhds.mp hlim) ε hε with
      ⟨δ, hδ, hnear⟩
    let u0 : unitIcc := ⟨min (δ / 2) (u.1 / 2), by
      constructor
      · positivity
      · have huhalf : u.1 / 2 ≤ 1 := by nlinarith [u.2.2]
        exact le_trans (min_le_right _ _) huhalf⟩
    have hu0pos : 0 < u0.1 := by
      dsimp [u0]
      positivity
    have hu0ltδ : u0.1 < δ := by
      dsimp [u0]
      have : min (δ / 2) (u.1 / 2) ≤ δ / 2 := min_le_left _ _
      have hδ2 : δ / 2 < δ := by linarith
      exact lt_of_le_of_lt this hδ2
    have hu0ltu : u0.1 < u.1 := by
      dsimp [u0]
      have : min (δ / 2) (u.1 / 2) ≤ u.1 / 2 := min_le_right _ _
      linarith
    have hu0near : |sqCenteredNorthZonalQuotientRaw g u0 - c| < ε := by
      have hdist : dist u0 zeroUnitIcc < δ := by
        change |(u0 : ℝ) - 0| < δ
        simpa [abs_of_nonneg hu0pos.le] using hu0ltδ
      simpa [Real.dist_eq] using hnear hu0pos hdist
    have hu0lt : sqCenteredNorthZonalQuotientRaw g u0 < sqCenteredNorthZonalQuotientRaw g u := by
      have hhigh : sqCenteredNorthZonalQuotientRaw g u0 < c + ε := by
        have hright := (abs_lt.mp hu0near).2
        linarith
      dsimp [ε] at hhigh
      linarith
    let seg : Set unitIcc := {v : unitIcc | u0.1 ≤ v.1 ∧ v.1 ≤ u.1}
    let f : unitIcc → ℝ := fun v => sqCenteredNorthZonalProfile g v / v.1
    have hsegClosed : IsClosed seg := by
      refine (isClosed_le continuous_const continuous_subtype_val).inter ?_
      exact isClosed_le continuous_subtype_val continuous_const
    have hsegCompact : IsCompact seg := hsegClosed.isCompact
    have hsegNonempty : seg.Nonempty := ⟨u, ⟨hu0ltu.le, le_rfl⟩⟩
    have hcontSeg : ContinuousOn f seg := by
      refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
      intro v hv
      exact lt_of_lt_of_le hu0pos hv.1
    rcases hsegCompact.exists_isMaxOn hsegNonempty hcontSeg with ⟨vmax, hvmax, hmax⟩
    rw [isMaxOn_iff] at hmax
    have hvmax_pos : 0 < vmax.1 := lt_of_lt_of_le hu0pos hvmax.1
    have hmax_ge_u : sqCenteredNorthZonalQuotientRaw g u ≤ sqCenteredNorthZonalQuotientRaw g vmax := by
      have := hmax u ⟨hu0ltu.le, le_rfl⟩
      simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu, ne_of_gt hvmax_pos] using this
    have hu0_not_max : sqCenteredNorthZonalQuotientRaw g u0 < sqCenteredNorthZonalQuotientRaw g vmax := by
      linarith
    have hpre_max :
        IsMaxOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
          {v : unitIcc | 0 < v.1 ∧ v.1 ≤ vmax.1} vmax := by
      rw [isMaxOn_iff]
      intro x hx
      by_cases hxlt : x.1 < u0.1
      · have hxdist : dist x zeroUnitIcc < δ := by
          have hxδ : x.1 < δ := lt_trans hxlt hu0ltδ
          change |(x : ℝ) - 0| < δ
          simpa [abs_of_nonneg hx.1.le] using hxδ
        have hxnear : |sqCenteredNorthZonalQuotientRaw g x - c| < ε := by
          simpa [Real.dist_eq] using hnear hx.1 hxdist
        have hxupper : sqCenteredNorthZonalQuotientRaw g x < c + ε := by
          have hright := (abs_lt.mp hxnear).2
          linarith
        have hvmax_gt : c + ε < sqCenteredNorthZonalQuotientRaw g vmax := by
          dsimp [ε]
          linarith [hmax_ge_u, hgt]
        linarith
      · have hu0le : u0.1 ≤ x.1 := le_of_not_gt hxlt
        have hxs' : x ∈ seg := ⟨hu0le, le_trans hx.2 hvmax.2⟩
        have := hmax x hxs'
        simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hx.1, ne_of_gt hvmax_pos] using this
    have hconst :
        ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ vmax.1 →
          sqCenteredNorthZonalQuotientRaw g v = sqCenteredNorthZonalQuotientRaw g vmax := by
      exact sqCenteredNorthZonalQuotientRaw_eq_of_isMaxOn_initialSegment
        (g := g) hgframe hgz (u := vmax) hvmax_pos hpre_max
    have hu0eq : sqCenteredNorthZonalQuotientRaw g u0 = sqCenteredNorthZonalQuotientRaw g vmax := by
      exact hconst hu0pos hvmax.1
    linarith [hmax_ge_u, hu0lt, hu0eq]

theorem sqCenteredNorthZonalQuotientRaw_eq_value_at_one_of_eventually_gt_near_zero
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {c : ℝ}
    (hone : sqCenteredNorthZonalQuotientRaw g oneUnitIcc = c)
    (hevent :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ {u : unitIcc}, 0 < u.1 → u.1 < δ →
          c < sqCenteredNorthZonalQuotientRaw g u) :
    ∀ {u : unitIcc}, 0 < u.1 → sqCenteredNorthZonalQuotientRaw g u = c := by
  rcases hevent with ⟨δ, hδ, heventδ⟩
  let u1 : unitIcc := oneUnitIcc
  have hone' : sqCenteredNorthZonalQuotientRaw g u1 = c := by
    simpa [u1] using hone
  have hno_lt :
      ∀ {u : unitIcc}, 0 < u.1 → ¬ sqCenteredNorthZonalQuotientRaw g u < c := by
    intro u hu hlt
    by_cases huδ : u.1 < δ
    · have hgt : c < sqCenteredNorthZonalQuotientRaw g u := heventδ hu huδ
      linarith
    · let u0 : unitIcc := ⟨δ / 2, by
        constructor
        · positivity
        · have : δ / 2 < (1 : ℝ) := by
            have hδ1 : δ ≤ 1 := by
              linarith [u.2.2]
            linarith
          linarith⟩
      have hu0pos : 0 < u0.1 := by
        dsimp [u0]
        positivity
      have hu0lt : u0.1 < δ := by
        dsimp [u0]
        linarith
      have hu0leu : u0.1 ≤ u.1 := by
        have hδle : δ ≤ u.1 := le_of_not_gt huδ
        dsimp [u0]
        linarith
      let seg : Set unitIcc := {v : unitIcc | u0.1 ≤ v.1 ∧ v.1 ≤ u.1}
      let f : unitIcc → ℝ := fun v => sqCenteredNorthZonalProfile g v / v.1
      have hsegClosed : IsClosed seg := by
        refine (isClosed_le continuous_const continuous_subtype_val).inter ?_
        exact isClosed_le continuous_subtype_val continuous_const
      have hsegCompact : IsCompact seg := hsegClosed.isCompact
      have hsegNonempty : seg.Nonempty := ⟨u, ⟨hu0leu, le_rfl⟩⟩
      have hcontSeg : ContinuousOn f seg := by
        refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
        intro v hv
        exact lt_of_lt_of_le hu0pos hv.1
      rcases hsegCompact.exists_isMinOn hsegNonempty hcontSeg with ⟨vmin, hvmin, hmin⟩
      rw [isMinOn_iff] at hmin
      have hvmin_pos : 0 < vmin.1 := lt_of_lt_of_le hu0pos hvmin.1
      have hvmin_lt : sqCenteredNorthZonalQuotientRaw g vmin < c := by
        have hminu : sqCenteredNorthZonalQuotientRaw g vmin ≤ sqCenteredNorthZonalQuotientRaw g u := by
          have := hmin u ⟨hu0leu, le_rfl⟩
          simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu, ne_of_gt hvmin_pos] using this
        linarith
      have hpre_min :
          IsMinOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
            {v : unitIcc | 0 < v.1 ∧ v.1 ≤ vmin.1} vmin := by
        rw [isMinOn_iff]
        intro x hx
        by_cases hxu0 : x.1 < u0.1
        · have hxgt : c < sqCenteredNorthZonalQuotientRaw g x := by
            exact heventδ hx.1 (lt_trans hxu0 hu0lt)
          linarith
        · have hu0lex : u0.1 ≤ x.1 := le_of_not_gt hxu0
          have hxs : x ∈ seg := ⟨hu0lex, le_trans hx.2 hvmin.2⟩
          have := hmin x hxs
          simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hx.1, ne_of_gt hvmin_pos] using this
      have hconst :
          ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ vmin.1 →
            sqCenteredNorthZonalQuotientRaw g v = sqCenteredNorthZonalQuotientRaw g vmin := by
        exact sqCenteredNorthZonalQuotientRaw_eq_of_isMinOn_initialSegment
          (g := g) hgframe hgz (u := vmin) hvmin_pos hpre_min
      have hu0eq : sqCenteredNorthZonalQuotientRaw g u0 = sqCenteredNorthZonalQuotientRaw g vmin := by
        exact hconst hu0pos hvmin.1
      have hu0gt : c < sqCenteredNorthZonalQuotientRaw g u0 := heventδ hu0pos hu0lt
      linarith [hvmin_lt, hu0eq, hu0gt]
  intro u hu
  have hminOne :
      IsMinOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
        {v : unitIcc | 0 < v.1 ∧ v.1 ≤ u1.1} u1 := by
    rw [isMinOn_iff]
    intro x hx
    have hnotlt : ¬ sqCenteredNorthZonalQuotientRaw g x < c := hno_lt hx.1
    have hxc : c ≤ sqCenteredNorthZonalQuotientRaw g x := not_lt.mp hnotlt
    simpa [hone'] using hxc
  have hconst :
      ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ u1.1 →
        sqCenteredNorthZonalQuotientRaw g v = sqCenteredNorthZonalQuotientRaw g u1 := by
    intro v hv hv1
    have hu1 : 0 < u1.1 := by
      simp [u1, oneUnitIcc]
    exact sqCenteredNorthZonalQuotientRaw_eq_of_isMinOn_initialSegment
      (g := g) hgframe hgz (u := u1) hu1 hminOne hv hv1
  have huOne : u.1 ≤ u1.1 := by
    simpa [u1] using u.2.2
  simpa [hone'] using hconst hu huOne

theorem sqCenteredNorthZonalQuotientRaw_eq_value_at_one_of_eventually_lt_near_zero
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {c : ℝ}
    (hone : sqCenteredNorthZonalQuotientRaw g oneUnitIcc = c)
    (hevent :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ {u : unitIcc}, 0 < u.1 → u.1 < δ →
          sqCenteredNorthZonalQuotientRaw g u < c) :
    ∀ {u : unitIcc}, 0 < u.1 → sqCenteredNorthZonalQuotientRaw g u = c := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have honeNeg : sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc = -c := by
    rw [sqCenteredNorthZonalQuotientRaw_neg, hone]
  have heventNeg :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ {u : unitIcc}, 0 < u.1 → u.1 < δ →
          (-c) < sqCenteredNorthZonalQuotientRaw (-g) u := by
    rcases hevent with ⟨δ, hδ, hδprop⟩
    refine ⟨δ, hδ, ?_⟩
    intro u hu huδ
    have hlt : sqCenteredNorthZonalQuotientRaw g u < c := hδprop hu huδ
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg hlt
  intro u hu
  have hEq :=
    sqCenteredNorthZonalQuotientRaw_eq_value_at_one_of_eventually_gt_near_zero
      (g := -g) hnegFrame hnegZonal honeNeg heventNeg hu
  have hEq' : -sqCenteredNorthZonalQuotientRaw g u = -c := by
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using hEq
  linarith

theorem sqCenteredNorthZonalQuotientRaw_eq_value_at_anchor_of_eventually_gt_near_zero
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 : unitIcc}
    (hu0 : 0 < u0.1)
    {c : ℝ}
    (hu0eq : sqCenteredNorthZonalQuotientRaw g u0 = c)
    (hevent :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ {u : unitIcc}, 0 < u.1 → u.1 < δ →
          c < sqCenteredNorthZonalQuotientRaw g u) :
    ∀ {u : unitIcc}, 0 < u.1 → sqCenteredNorthZonalQuotientRaw g u = c := by
  rcases hevent with ⟨δ, hδ, heventδ⟩
  have hno_lt :
      ∀ {u : unitIcc}, 0 < u.1 → ¬ sqCenteredNorthZonalQuotientRaw g u < c := by
    intro u hu hlt
    by_cases huδ : u.1 < δ
    · have hgt : c < sqCenteredNorthZonalQuotientRaw g u := heventδ hu huδ
      linarith
    · let w : unitIcc := ⟨δ / 2, by
        constructor
        · positivity
        · have : δ / 2 < (1 : ℝ) := by
            have hδ1 : δ ≤ 1 := by
              linarith [u.2.2]
            linarith
          linarith⟩
      have hwPos : 0 < w.1 := by
        dsimp [w]
        positivity
      have hwLt : w.1 < δ := by
        dsimp [w]
        linarith
      have hwLeu : w.1 ≤ u.1 := by
        have hδle : δ ≤ u.1 := le_of_not_gt huδ
        dsimp [w]
        linarith
      let seg : Set unitIcc := {v : unitIcc | w.1 ≤ v.1 ∧ v.1 ≤ u.1}
      let f : unitIcc → ℝ := fun v => sqCenteredNorthZonalProfile g v / v.1
      have hsegClosed : IsClosed seg := by
        refine (isClosed_le continuous_const continuous_subtype_val).inter ?_
        exact isClosed_le continuous_subtype_val continuous_const
      have hsegCompact : IsCompact seg := hsegClosed.isCompact
      have hsegNonempty : seg.Nonempty := ⟨u, ⟨hwLeu, le_rfl⟩⟩
      have hcontSeg : ContinuousOn f seg := by
        refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
        intro v hv
        exact lt_of_lt_of_le hwPos hv.1
      rcases hsegCompact.exists_isMinOn hsegNonempty hcontSeg with ⟨vmin, hvmin, hmin⟩
      rw [isMinOn_iff] at hmin
      have hvminPos : 0 < vmin.1 := lt_of_lt_of_le hwPos hvmin.1
      have hvminLt : sqCenteredNorthZonalQuotientRaw g vmin < c := by
        have hminu : sqCenteredNorthZonalQuotientRaw g vmin ≤ sqCenteredNorthZonalQuotientRaw g u := by
          have := hmin u ⟨hwLeu, le_rfl⟩
          simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu, ne_of_gt hvminPos] using this
        linarith
      have hpreMin :
          IsMinOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
            {v : unitIcc | 0 < v.1 ∧ v.1 ≤ vmin.1} vmin := by
        rw [isMinOn_iff]
        intro x hx
        by_cases hxw : x.1 < w.1
        · have hxgt : c < sqCenteredNorthZonalQuotientRaw g x := by
            exact heventδ hx.1 (lt_trans hxw hwLt)
          linarith
        · have hwLex : w.1 ≤ x.1 := le_of_not_gt hxw
          have hxs : x ∈ seg := ⟨hwLex, le_trans hx.2 hvmin.2⟩
          have := hmin x hxs
          simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hx.1, ne_of_gt hvminPos] using this
      have hconst :
          ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ vmin.1 →
            sqCenteredNorthZonalQuotientRaw g v = sqCenteredNorthZonalQuotientRaw g vmin := by
        exact sqCenteredNorthZonalQuotientRaw_eq_of_isMinOn_initialSegment
          (g := g) hgframe hgz (u := vmin) hvminPos hpreMin
      have hwEq : sqCenteredNorthZonalQuotientRaw g w = sqCenteredNorthZonalQuotientRaw g vmin := by
        exact hconst hwPos hvmin.1
      have hwGt : c < sqCenteredNorthZonalQuotientRaw g w := heventδ hwPos hwLt
      linarith [hvminLt, hwEq, hwGt]
  have hminSeg :
      IsMinOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
        {v : unitIcc | 0 < v.1 ∧ v.1 ≤ u0.1} u0 := by
    rw [isMinOn_iff]
    intro x hx
    have hnotlt : ¬ sqCenteredNorthZonalQuotientRaw g x < c := hno_lt hx.1
    have hxc : c ≤ sqCenteredNorthZonalQuotientRaw g x := not_lt.mp hnotlt
    simpa [hu0eq] using hxc
  have hconst0 :
      ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ u0.1 →
        sqCenteredNorthZonalQuotientRaw g v = c := by
    intro v hv hvu0
    simpa [hu0eq] using
      sqCenteredNorthZonalQuotientRaw_eq_of_isMinOn_initialSegment
        (g := g) hgframe hgz (u := u0) hu0 hminSeg hv hvu0
  intro u hu
  by_cases huu0 : u.1 ≤ u0.1
  · exact hconst0 hu huu0
  · exact
      sqCenteredNorthZonalQuotientRaw_eq_const_of_eq_const_on_initialSegment
        (g := g) hgframe hgz (u0 := u0) hu0 (c := c) hconst0 (le_of_not_ge huu0)

theorem sqCenteredNorthZonalQuotientRaw_eq_value_at_anchor_of_eventually_lt_near_zero
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 : unitIcc}
    (hu0 : 0 < u0.1)
    {c : ℝ}
    (hu0eq : sqCenteredNorthZonalQuotientRaw g u0 = c)
    (hevent :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ {u : unitIcc}, 0 < u.1 → u.1 < δ →
          sqCenteredNorthZonalQuotientRaw g u < c) :
    ∀ {u : unitIcc}, 0 < u.1 → sqCenteredNorthZonalQuotientRaw g u = c := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have hu0eqNeg : sqCenteredNorthZonalQuotientRaw (-g) u0 = -c := by
    rw [sqCenteredNorthZonalQuotientRaw_neg, hu0eq]
  have heventNeg :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ {u : unitIcc}, 0 < u.1 → u.1 < δ →
          (-c) < sqCenteredNorthZonalQuotientRaw (-g) u := by
    rcases hevent with ⟨δ, hδ, hδprop⟩
    refine ⟨δ, hδ, ?_⟩
    intro u hu huδ
    have hlt : sqCenteredNorthZonalQuotientRaw g u < c := hδprop hu huδ
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg hlt
  intro u hu
  have hEq :=
    sqCenteredNorthZonalQuotientRaw_eq_value_at_anchor_of_eventually_gt_near_zero
      (g := -g) hnegFrame hnegZonal hu0 hu0eqNeg heventNeg hu
  have hEq' : -sqCenteredNorthZonalQuotientRaw g u = -c := by
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using hEq
  linarith

theorem exists_eq_value_at_anchor_near_zero_of_not_const_of_mem_frame
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 : unitIcc}
    (hu0 : 0 < u0.1)
    {c : ℝ}
    (hu0eq : sqCenteredNorthZonalQuotientRaw g u0 = c)
    (hnconst :
      ∃ u : unitIcc, 0 < u.1 ∧ sqCenteredNorthZonalQuotientRaw g u ≠ c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧ sqCenteredNorthZonalQuotientRaw g u = c := by
  have hex_gt : ∃ u : unitIcc, 0 < u.1 ∧ c < sqCenteredNorthZonalQuotientRaw g u := by
    rcases hnconst with ⟨u, hu, hune⟩
    rcases lt_or_gt_of_ne hune with hlt | hgt
    · by_contra hneg
      have hmax0 :
          IsMaxOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
            {v : unitIcc | 0 < v.1 ∧ v.1 ≤ u0.1} u0 := by
        rw [isMaxOn_iff]
        intro x hx
        have hle : sqCenteredNorthZonalQuotientRaw g x ≤ c := by
          by_contra hcx
          exact hneg ⟨x, hx.1, lt_of_not_ge hcx⟩
        simpa [hu0eq] using hle
      have hconst0 :
          ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ u0.1 →
            sqCenteredNorthZonalQuotientRaw g v = c := by
        intro v hv hvu0
        simpa [hu0eq] using
          sqCenteredNorthZonalQuotientRaw_eq_of_isMaxOn_initialSegment
            (g := g) hgframe hgz (u := u0) hu0 hmax0 hv hvu0
      have hall :
          ∀ {v : unitIcc}, 0 < v.1 →
            sqCenteredNorthZonalQuotientRaw g v = c := by
        intro v hv
        by_cases hvu0 : v.1 ≤ u0.1
        · exact hconst0 hv hvu0
        · exact
            sqCenteredNorthZonalQuotientRaw_eq_const_of_eq_const_on_initialSegment
              (g := g) hgframe hgz (u0 := u0) hu0 (c := c) hconst0 (le_of_not_ge hvu0)
      have hEq : sqCenteredNorthZonalQuotientRaw g u = c := hall hu
      linarith
    · exact ⟨u, hu, hgt⟩
  have hex_lt : ∃ u : unitIcc, 0 < u.1 ∧ sqCenteredNorthZonalQuotientRaw g u < c := by
    rcases hnconst with ⟨u, hu, hune⟩
    rcases lt_or_gt_of_ne hune with hlt | hgt
    · exact ⟨u, hu, hlt⟩
    · by_contra hneg
      have hmin0 :
          IsMinOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
            {v : unitIcc | 0 < v.1 ∧ v.1 ≤ u0.1} u0 := by
        rw [isMinOn_iff]
        intro x hx
        have hle : c ≤ sqCenteredNorthZonalQuotientRaw g x := by
          by_contra hcx
          exact hneg ⟨x, hx.1, lt_of_not_ge hcx⟩
        simpa [hu0eq] using hle
      have hconst0 :
          ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ u0.1 →
            sqCenteredNorthZonalQuotientRaw g v = c := by
        intro v hv hvu0
        simpa [hu0eq] using
          sqCenteredNorthZonalQuotientRaw_eq_of_isMinOn_initialSegment
            (g := g) hgframe hgz (u := u0) hu0 hmin0 hv hvu0
      have hall :
          ∀ {v : unitIcc}, 0 < v.1 →
            sqCenteredNorthZonalQuotientRaw g v = c := by
        intro v hv
        by_cases hvu0 : v.1 ≤ u0.1
        · exact hconst0 hv hvu0
        · exact
            sqCenteredNorthZonalQuotientRaw_eq_const_of_eq_const_on_initialSegment
              (g := g) hgframe hgz (u0 := u0) hu0 (c := c) hconst0 (le_of_not_ge hvu0)
      have hEq : sqCenteredNorthZonalQuotientRaw g u = c := hall hu
      linarith
  have hnot_event_gt :
      ¬ ∃ η : ℝ, 0 < η ∧
          ∀ {u : unitIcc}, 0 < u.1 → u.1 < η →
            c < sqCenteredNorthZonalQuotientRaw g u := by
    intro hevent
    rcases hex_lt with ⟨u, hu, hlt⟩
    have hconst :=
      sqCenteredNorthZonalQuotientRaw_eq_value_at_anchor_of_eventually_gt_near_zero
        (g := g) hgframe hgz hu0 hu0eq hevent hu
    linarith
  have hnot_event_lt :
      ¬ ∃ η : ℝ, 0 < η ∧
          ∀ {u : unitIcc}, 0 < u.1 → u.1 < η →
            sqCenteredNorthZonalQuotientRaw g u < c := by
    intro hevent
    rcases hex_gt with ⟨u, hu, hgt⟩
    have hconst :=
      sqCenteredNorthZonalQuotientRaw_eq_value_at_anchor_of_eventually_lt_near_zero
        (g := g) hgframe hgz hu0 hu0eq hevent hu
    linarith
  have hlow :
      ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧ sqCenteredNorthZonalQuotientRaw g u ≤ c := by
    by_contra hno
    apply hnot_event_gt
    refine ⟨δ, hδ, ?_⟩
    intro u hu huδ
    by_contra huc
    exact hno ⟨u, hu, huδ, le_of_not_gt huc⟩
  have hhigh :
      ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧ c ≤ sqCenteredNorthZonalQuotientRaw g u := by
    by_contra hno
    apply hnot_event_lt
    refine ⟨δ, hδ, ?_⟩
    intro u hu huδ
    have : ¬ c ≤ sqCenteredNorthZonalQuotientRaw g u := by
      intro hcu
      exact hno ⟨u, hu, huδ, hcu⟩
    linarith
  rcases hlow with ⟨uLo, huLoPos, huLoLt, huLoLe⟩
  rcases hhigh with ⟨uHi, huHiPos, huHiLt, huHiGe⟩
  by_cases huLoEq : sqCenteredNorthZonalQuotientRaw g uLo = c
  · exact ⟨uLo, huLoPos, huLoLt, huLoEq⟩
  by_cases huHiEq : sqCenteredNorthZonalQuotientRaw g uHi = c
  · exact ⟨uHi, huHiPos, huHiLt, huHiEq⟩
  have huLoLtC : sqCenteredNorthZonalQuotientRaw g uLo < c := lt_of_le_of_ne huLoLe huLoEq
  have huHiGtC : c < sqCenteredNorthZonalQuotientRaw g uHi := lt_of_le_of_ne huHiGe (Ne.symm huHiEq)
  let a : unitIcc := if h : uLo.1 ≤ uHi.1 then uLo else uHi
  let b : unitIcc := if h : uLo.1 ≤ uHi.1 then uHi else uLo
  have hab : a.1 ≤ b.1 := by
    by_cases h : uLo.1 ≤ uHi.1
    · simp [a, b, h]
    · simp [a, b, h, le_of_not_ge h]
  have haPos : 0 < a.1 := by
    by_cases h : uLo.1 ≤ uHi.1 <;> simp [a, h, huLoPos, huHiPos]
  have hbPos : 0 < b.1 := by
    exact lt_of_lt_of_le haPos hab
  have hbLt : b.1 < δ := by
    by_cases h : uLo.1 ≤ uHi.1 <;> simp [b, h, huLoLt, huHiLt]
  have hcontInterval :
      ContinuousOn (sqCenteredNorthZonalQuotientRaw g) (Set.uIcc a b) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := by
      rw [Set.mem_uIcc] at hx
      rcases hx with hx | hx
      · exact hx
      · exact ⟨le_trans hab hx.1, le_trans hx.2 hab⟩
    have hxPos : 0 < x.1 := lt_of_lt_of_le haPos hxIcc.1
    have hquot :
        ContinuousAt (fun v : unitIcc => sqCenteredNorthZonalProfile g v / v.1) x :=
      (continuous_sqCenteredNorthZonalProfile g).continuousAt.div
        continuous_subtype_val.continuousAt (show x.1 ≠ 0 by linarith)
    have hEq :
        sqCenteredNorthZonalQuotientRaw g =ᶠ[𝓝 x]
          (fun v : unitIcc => sqCenteredNorthZonalProfile g v / v.1) := by
      have hpos :
          {v : unitIcc | 0 < v.1} ∈ 𝓝 x := by
        exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_subtype_val) hxPos
      filter_upwards [hpos] with v hv
      simp [sqCenteredNorthZonalQuotientRaw, ne_of_gt hv]
    exact (ContinuousAt.congr hquot hEq.symm).continuousWithinAt
  have hc_mem :
      c ∈ Set.uIcc (sqCenteredNorthZonalQuotientRaw g a) (sqCenteredNorthZonalQuotientRaw g b) := by
    rw [Set.mem_uIcc]
    by_cases h : uLo.1 ≤ uHi.1
    · left
      simpa [a, b, h] using And.intro huLoLe huHiGe
    · right
      simpa [a, b, h] using And.intro huLoLe huHiGe
  rcases intermediate_value_uIcc hcontInterval hc_mem with ⟨u, huab, huEq⟩
  have huIcc : u ∈ Set.Icc a b := by
    rw [Set.mem_uIcc] at huab
    rcases huab with huab | huab
    · exact huab
    · exact ⟨le_trans hab huab.1, le_trans huab.2 hab⟩
  have huPos : 0 < u.1 := lt_of_lt_of_le haPos huIcc.1
  have huLtδ : u.1 < δ := lt_of_le_of_lt huIcc.2 hbLt
  exact ⟨u, huPos, huLtδ, huEq⟩

theorem exists_eq_value_at_anchor_near_zero_of_ne_value_at_one_of_mem_frame
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 : unitIcc}
    (hu0 : 0 < u0.1)
    (hune :
      sqCenteredNorthZonalQuotientRaw g u0 ≠
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g u0 := by
  exact
    exists_eq_value_at_anchor_near_zero_of_not_const_of_mem_frame
      (g := g) hgframe hgz hu0 rfl
      ⟨oneUnitIcc, by simp [oneUnitIcc], by simpa using hune.symm⟩ hδ

theorem exists_eq_value_at_one_near_zero_of_not_const_of_mem_frame
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hnconst :
      ∃ u : unitIcc, 0 < u.1 ∧
        sqCenteredNorthZonalQuotientRaw g u ≠ sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧
      sqCenteredNorthZonalQuotientRaw g u = sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  have hex_gt : ∃ u : unitIcc, 0 < u.1 ∧ c < sqCenteredNorthZonalQuotientRaw g u := by
    rcases hnconst with ⟨u, hu, hune⟩
    rcases lt_or_gt_of_ne hune with hlt | hgt
    · by_contra hneg
      have hmaxOne :
          IsMaxOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
            {v : unitIcc | 0 < v.1 ∧ v.1 ≤ oneUnitIcc.1} oneUnitIcc := by
        rw [isMaxOn_iff]
        intro x hx
        have hle : sqCenteredNorthZonalQuotientRaw g x ≤ c := by
          by_contra hcx
          exact hneg ⟨x, hx.1, lt_of_not_ge hcx⟩
        simpa [c] using hle
      have hconst :
          ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ oneUnitIcc.1 →
            sqCenteredNorthZonalQuotientRaw g v = sqCenteredNorthZonalQuotientRaw g oneUnitIcc :=
        sqCenteredNorthZonalQuotientRaw_eq_of_isMaxOn_initialSegment
          (g := g) hgframe hgz (u := oneUnitIcc) (by simp [oneUnitIcc]) hmaxOne
      linarith [hlt, hconst hu u.2.2]
    · exact ⟨u, hu, by simpa [c] using hgt⟩
  have hex_lt : ∃ u : unitIcc, 0 < u.1 ∧ sqCenteredNorthZonalQuotientRaw g u < c := by
    rcases hnconst with ⟨u, hu, hune⟩
    rcases lt_or_gt_of_ne hune with hlt | hgt
    · exact ⟨u, hu, by simpa [c] using hlt⟩
    · by_contra hneg
      have hminOne :
          IsMinOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
            {v : unitIcc | 0 < v.1 ∧ v.1 ≤ oneUnitIcc.1} oneUnitIcc := by
        rw [isMinOn_iff]
        intro x hx
        have hle : c ≤ sqCenteredNorthZonalQuotientRaw g x := by
          by_contra hcx
          exact hneg ⟨x, hx.1, lt_of_not_ge hcx⟩
        simpa [c] using hle
      have hconst :
          ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ oneUnitIcc.1 →
            sqCenteredNorthZonalQuotientRaw g v = sqCenteredNorthZonalQuotientRaw g oneUnitIcc :=
        sqCenteredNorthZonalQuotientRaw_eq_of_isMinOn_initialSegment
          (g := g) hgframe hgz (u := oneUnitIcc) (by simp [oneUnitIcc]) hminOne
      linarith [hgt, hconst hu u.2.2]
  have hnot_event_gt :
      ¬ ∃ η : ℝ, 0 < η ∧
          ∀ {u : unitIcc}, 0 < u.1 → u.1 < η →
            c < sqCenteredNorthZonalQuotientRaw g u := by
    intro hevent
    rcases hex_lt with ⟨u, hu, hlt⟩
    have hconst :=
      sqCenteredNorthZonalQuotientRaw_eq_value_at_one_of_eventually_gt_near_zero
        (g := g) hgframe hgz (hone := rfl) hevent hu
    linarith [hlt, hconst]
  have hnot_event_lt :
      ¬ ∃ η : ℝ, 0 < η ∧
          ∀ {u : unitIcc}, 0 < u.1 → u.1 < η →
            sqCenteredNorthZonalQuotientRaw g u < c := by
    intro hevent
    rcases hex_gt with ⟨u, hu, hgt⟩
    have hconst :=
      sqCenteredNorthZonalQuotientRaw_eq_value_at_one_of_eventually_lt_near_zero
        (g := g) hgframe hgz (hone := rfl) hevent hu
    linarith [hgt, hconst]
  have hlow :
      ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧ sqCenteredNorthZonalQuotientRaw g u ≤ c := by
    by_contra hno
    apply hnot_event_gt
    refine ⟨δ, hδ, ?_⟩
    intro u hu huδ
    by_contra huc
    exact hno ⟨u, hu, huδ, le_of_not_gt huc⟩
  have hhigh :
      ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧ c ≤ sqCenteredNorthZonalQuotientRaw g u := by
    by_contra hno
    apply hnot_event_lt
    refine ⟨δ, hδ, ?_⟩
    intro u hu huδ
    have : ¬ c ≤ sqCenteredNorthZonalQuotientRaw g u := by
      intro hcu
      exact hno ⟨u, hu, huδ, hcu⟩
    linarith
  rcases hlow with ⟨uLo, huLoPos, huLoLt, huLoLe⟩
  rcases hhigh with ⟨uHi, huHiPos, huHiLt, huHiGe⟩
  by_cases huLoEq : sqCenteredNorthZonalQuotientRaw g uLo = c
  · exact ⟨uLo, huLoPos, huLoLt, by simpa [c] using huLoEq⟩
  by_cases huHiEq : sqCenteredNorthZonalQuotientRaw g uHi = c
  · exact ⟨uHi, huHiPos, huHiLt, by simpa [c] using huHiEq⟩
  have huLoLtC : sqCenteredNorthZonalQuotientRaw g uLo < c := lt_of_le_of_ne huLoLe huLoEq
  have huHiGtC : c < sqCenteredNorthZonalQuotientRaw g uHi := lt_of_le_of_ne huHiGe (Ne.symm huHiEq)
  let a : unitIcc := if h : uLo.1 ≤ uHi.1 then uLo else uHi
  let b : unitIcc := if h : uLo.1 ≤ uHi.1 then uHi else uLo
  have hab : a.1 ≤ b.1 := by
    by_cases h : uLo.1 ≤ uHi.1
    · simp [a, b, h]
    · simp [a, b, h, le_of_not_ge h]
  have haPos : 0 < a.1 := by
    by_cases h : uLo.1 ≤ uHi.1 <;> simp [a, h, huLoPos, huHiPos]
  have hbPos : 0 < b.1 := by
    exact lt_of_lt_of_le haPos hab
  have hbLt : b.1 < δ := by
    by_cases h : uLo.1 ≤ uHi.1 <;> simp [b, h, huLoLt, huHiLt]
  have hcontInterval :
      ContinuousOn (sqCenteredNorthZonalQuotientRaw g) (Set.uIcc a b) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := by
      rw [Set.mem_uIcc] at hx
      rcases hx with hx | hx
      · exact hx
      · exact ⟨le_trans hab hx.1, le_trans hx.2 hab⟩
    have hxPos : 0 < x.1 := lt_of_lt_of_le haPos hxIcc.1
    have hquot :
        ContinuousAt (fun v : unitIcc => sqCenteredNorthZonalProfile g v / v.1) x :=
      (continuous_sqCenteredNorthZonalProfile g).continuousAt.div
        continuous_subtype_val.continuousAt (show x.1 ≠ 0 by linarith)
    have hEq :
        sqCenteredNorthZonalQuotientRaw g =ᶠ[𝓝 x]
          (fun v : unitIcc => sqCenteredNorthZonalProfile g v / v.1) := by
      have hpos :
          {v : unitIcc | 0 < v.1} ∈ 𝓝 x := by
        exact IsOpen.mem_nhds (isOpen_lt continuous_const continuous_subtype_val) hxPos
      filter_upwards [hpos] with v hv
      simp [sqCenteredNorthZonalQuotientRaw, ne_of_gt hv]
    exact (ContinuousAt.congr hquot hEq.symm).continuousWithinAt
  have hc_mem :
      c ∈ Set.uIcc (sqCenteredNorthZonalQuotientRaw g a) (sqCenteredNorthZonalQuotientRaw g b) := by
    rw [Set.mem_uIcc]
    by_cases h : uLo.1 ≤ uHi.1
    · left
      simpa [a, b, h] using And.intro huLoLe huHiGe
    · right
      have h' : uHi.1 ≤ uLo.1 := le_of_not_ge h
      simpa [a, b, h] using And.intro huLoLe huHiGe
  rcases intermediate_value_uIcc hcontInterval hc_mem with ⟨u, huab, huEq⟩
  have huIcc : u ∈ Set.Icc a b := by
    rw [Set.mem_uIcc] at huab
    rcases huab with huab | huab
    · exact huab
    · exact ⟨le_trans hab huab.1, le_trans huab.2 hab⟩
  have huPos : 0 < u.1 := lt_of_lt_of_le haPos huIcc.1
  have huLtδ : u.1 < δ := lt_of_le_of_lt huIcc.2 hbLt
  exact ⟨u, huPos, huLtδ, by simpa [c] using huEq⟩

theorem exists_le_ge_value_at_one_near_zero_of_not_const_of_mem_frame
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    (hnconst :
      ∃ u : unitIcc, 0 < u.1 ∧
        sqCenteredNorthZonalQuotientRaw g u ≠ sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    {δ : ℝ} (hδ : 0 < δ) :
    (∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧
      sqCenteredNorthZonalQuotientRaw g u ≤ sqCenteredNorthZonalQuotientRaw g oneUnitIcc) ∧
    (∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤ sqCenteredNorthZonalQuotientRaw g u) := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  have hex_gt : ∃ u : unitIcc, 0 < u.1 ∧ c < sqCenteredNorthZonalQuotientRaw g u := by
    rcases hnconst with ⟨u, hu, hune⟩
    rcases lt_or_gt_of_ne hune with hlt | hgt
    · by_contra hneg
      have hmaxOne :
          IsMaxOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
            {v : unitIcc | 0 < v.1 ∧ v.1 ≤ oneUnitIcc.1} oneUnitIcc := by
        rw [isMaxOn_iff]
        intro x hx
        have hle : sqCenteredNorthZonalQuotientRaw g x ≤ c := by
          by_contra hcx
          exact hneg ⟨x, hx.1, lt_of_not_ge hcx⟩
        simpa [c] using hle
      have hconst :
          ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ oneUnitIcc.1 →
            sqCenteredNorthZonalQuotientRaw g v = sqCenteredNorthZonalQuotientRaw g oneUnitIcc :=
        sqCenteredNorthZonalQuotientRaw_eq_of_isMaxOn_initialSegment
          (g := g) hgframe hgz (u := oneUnitIcc) (by simp [oneUnitIcc]) hmaxOne
      linarith [hlt, hconst hu u.2.2]
    · exact ⟨u, hu, by simpa [c] using hgt⟩
  have hex_lt : ∃ u : unitIcc, 0 < u.1 ∧ sqCenteredNorthZonalQuotientRaw g u < c := by
    rcases hnconst with ⟨u, hu, hune⟩
    rcases lt_or_gt_of_ne hune with hlt | hgt
    · exact ⟨u, hu, by simpa [c] using hlt⟩
    · by_contra hneg
      have hminOne :
          IsMinOn (fun v : unitIcc => sqCenteredNorthZonalQuotientRaw g v)
            {v : unitIcc | 0 < v.1 ∧ v.1 ≤ oneUnitIcc.1} oneUnitIcc := by
        rw [isMinOn_iff]
        intro x hx
        have hle : c ≤ sqCenteredNorthZonalQuotientRaw g x := by
          by_contra hcx
          exact hneg ⟨x, hx.1, lt_of_not_ge hcx⟩
        simpa [c] using hle
      have hconst :
          ∀ {v : unitIcc}, 0 < v.1 → v.1 ≤ oneUnitIcc.1 →
            sqCenteredNorthZonalQuotientRaw g v = sqCenteredNorthZonalQuotientRaw g oneUnitIcc :=
        sqCenteredNorthZonalQuotientRaw_eq_of_isMinOn_initialSegment
          (g := g) hgframe hgz (u := oneUnitIcc) (by simp [oneUnitIcc]) hminOne
      linarith [hgt, hconst hu u.2.2]
  have hnot_event_gt :
      ¬ ∃ η : ℝ, 0 < η ∧
          ∀ {u : unitIcc}, 0 < u.1 → u.1 < η →
            c < sqCenteredNorthZonalQuotientRaw g u := by
    intro hevent
    rcases hex_lt with ⟨u, hu, hlt⟩
    have hconst :=
      sqCenteredNorthZonalQuotientRaw_eq_value_at_one_of_eventually_gt_near_zero
        (g := g) hgframe hgz (hone := rfl) hevent hu
    linarith [hlt, hconst]
  have hnot_event_lt :
      ¬ ∃ η : ℝ, 0 < η ∧
          ∀ {u : unitIcc}, 0 < u.1 → u.1 < η →
            sqCenteredNorthZonalQuotientRaw g u < c := by
    intro hevent
    rcases hex_gt with ⟨u, hu, hgt⟩
    have hconst :=
      sqCenteredNorthZonalQuotientRaw_eq_value_at_one_of_eventually_lt_near_zero
        (g := g) hgframe hgz (hone := rfl) hevent hu
    linarith [hgt, hconst]
  have hlow :
      ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧ sqCenteredNorthZonalQuotientRaw g u ≤ c := by
    by_contra hno
    apply hnot_event_gt
    refine ⟨δ, hδ, ?_⟩
    intro u hu huδ
    by_contra huc
    exact hno ⟨u, hu, huδ, le_of_not_gt huc⟩
  have hhigh :
      ∃ u : unitIcc, 0 < u.1 ∧ u.1 < δ ∧ c ≤ sqCenteredNorthZonalQuotientRaw g u := by
    by_contra hno
    apply hnot_event_lt
    refine ⟨δ, hδ, ?_⟩
    intro u hu huδ
    have : ¬ c ≤ sqCenteredNorthZonalQuotientRaw g u := by
      intro hcu
      exact hno ⟨u, hu, huδ, hcu⟩
    linarith
  exact ⟨by simpa [c] using hlow, by simpa [c] using hhigh⟩

theorem exists_lt_value_at_one_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u <
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  by_contra hno
  push_neg at hno
  let F : ℝ → ℝ := fun θ =>
    Real.cos θ ^ 2 * sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ a) -
      c * Real.cos θ ^ 2
  have hFcont : Continuous F := by
    have hcontQ := continuous_cos_sq_mul_sqCenteredNorthZonalQuotientRaw_comp g ha
    have hconst : Continuous (fun θ : ℝ => c * Real.cos θ ^ 2) := by
      exact continuous_const.mul (Real.continuous_cos.pow 2)
    simpa [F, mul_comm, mul_left_comm, mul_assoc] using hcontQ.sub hconst
  have hFnonneg :
      ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 ≤ F θ := by
    intro θ hθ
    by_cases hcos0 : Real.cos θ = 0
    · simp [F, hcos0]
    · let x : unitIcc := sqMulCosSelfMap θ a
      have hxpos : 0 < x.1 := by
        simpa [x, sqMulCosSelfMap, hcos0, sq_pos_iff] using mul_pos ha (sq_pos_iff.mpr hcos0)
      have hcx : c ≤ sqCenteredNorthZonalQuotientRaw g x := by
        by_cases hxhalf : a.1 / 2 ≤ x.1
        · by_cases hxa : x = a
          · simpa [c, hxa] using haEq.ge
          · let uθ : unitIcc := ⟨x.1 / a.1, by
              constructor
              · positivity
              · have hxleA : x.1 ≤ a.1 := by
                  dsimp [x, sqMulCosSelfMap]
                  nlinarith [Real.cos_sq_le_one θ, a.2.1]
                have hxleA' : x.1 ≤ 1 * a.1 := by simpa using hxleA
                exact (div_le_iff₀ ha).2 hxleA'⟩
            have huHalf : (1 / 2 : ℝ) ≤ uθ.1 := by
              change (1 / 2 : ℝ) ≤ x.1 / a.1
              have hxhalf' : (1 / 2 : ℝ) * a.1 ≤ x.1 := by
                nlinarith
              exact (le_div_iff₀ ha).2 hxhalf'
            have huLt : uθ.1 < 1 := by
              change x.1 / a.1 < 1
              have hxlt : x.1 < a.1 := by
                have hxle : x.1 ≤ a.1 := by
                  dsimp [x, sqMulCosSelfMap]
                  nlinarith [Real.cos_sq_le_one θ, a.2.1]
                have hxne : x.1 ≠ a.1 := by
                  intro hxeq
                  apply hxa
                  exact Subtype.ext hxeq
                exact lt_of_le_of_ne hxle hxne
              exact (div_lt_one ha).2 hxlt
            have hscale : sqScaleMap a uθ = x := by
              apply Subtype.ext
              change a.1 * uθ.1 = x.1
              simp [uθ]
              field_simp [show (a.1 : ℝ) ≠ 0 by exact ne_of_gt ha]
            have hcx' :
                c < sqCenteredNorthZonalQuotientRaw g x := by
              simpa [c, hscale] using hgt (u := uθ) huHalf huLt
            exact le_of_lt hcx'
        · have hxltHalf : x.1 < a.1 / 2 := lt_of_not_ge hxhalf
          exact hno (u := x) hxpos hxltHalf
      have hsub_nonneg : 0 ≤ sqCenteredNorthZonalQuotientRaw g x - c := by
        linarith
      have hcossq_nonneg : 0 ≤ Real.cos θ ^ 2 := by positivity
      calc
        0 ≤ (sqCenteredNorthZonalQuotientRaw g x - c) * Real.cos θ ^ 2 := by
          exact mul_nonneg hsub_nonneg hcossq_nonneg
        _ = F θ := by
          simp [F, x]
          ring
  have hFint :
      ∫ θ in 0..2 * Real.pi, F θ = 0 := by
    have hfixa :=
      sqCenteredNorthZonalQuotientRaw_fixed_on_pos_of_mem_frame hgframe hgz ha
    have hfixa' :
        2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            Real.cos θ ^ 2 *
              sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ a)) = c := by
      simpa [c, haEq] using hfixa
    have hcosSq :
        ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 = Real.pi := by
      rw [integral_cos_sq]
      simp
    have hfixInt :
        ∫ θ in 0..2 * Real.pi,
            Real.cos θ ^ 2 *
              sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ a)
          = Real.pi * c := by
      have htwoPi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp [htwoPi_ne, Real.pi_ne_zero] at hfixa'
      linarith
    rw [show F =
        (fun θ : ℝ =>
          Real.cos θ ^ 2 *
            sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ a) -
              c * Real.cos θ ^ 2) by
          funext θ; simp [F]]
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul, hcosSq, hfixInt]
      ring
    · exact (continuous_cos_sq_mul_sqCenteredNorthZonalQuotientRaw_comp g ha).intervalIntegrable _ _
    · exact (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  let uThreeQuarter : unitIcc := ⟨(3 / 4 : ℝ), by constructor <;> norm_num⟩
  let θ0 : ℝ := Real.arccos (Real.sqrt (3 / 4 : ℝ))
  have hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
    have hsqrt_lt : Real.sqrt (3 / 4 : ℝ) < 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hsqrt_pos : 0 < Real.sqrt (3 / 4 : ℝ) := by
      exact Real.sqrt_pos.mpr (by norm_num)
    refine ⟨Real.arccos_pos.mpr hsqrt_lt, ?_⟩
    have hlt' : θ0 < Real.pi / 2 := by
      dsimp [θ0]
      exact Real.arccos_lt_pi_div_two.mpr hsqrt_pos
    linarith [Real.pi_pos]
  have hscaleThreeQuarter :
      sqMulCosSelfMap θ0 a = sqScaleMap a uThreeQuarter := by
    apply Subtype.ext
    change a.1 * Real.cos θ0 ^ 2 = a.1 * uThreeQuarter.1
    have hcos :
        Real.cos θ0 = Real.sqrt (3 / 4 : ℝ) := by
      dsimp [θ0]
      exact Real.cos_arccos (by
        nlinarith [Real.sqrt_nonneg (3 / 4 : ℝ)]) (by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by norm_num))
    have hsq : Real.cos θ0 ^ 2 = (3 / 4 : ℝ) := by
      rw [hcos]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 / 4 by norm_num)]
    simp [uThreeQuarter, sqScaleMap, sqMulCosSelfMap, hsq]
  have hgtThreeQuarter :
      c < sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ0 a) := by
    have huHalf : (1 / 2 : ℝ) ≤ uThreeQuarter.1 := by
      change (1 / 2 : ℝ) ≤ (3 / 4 : ℝ)
      norm_num
    have huLt : uThreeQuarter.1 < 1 := by
      change (3 / 4 : ℝ) < 1
      norm_num
    simpa [c, hscaleThreeQuarter] using hgt (u := uThreeQuarter) huHalf huLt
  have hFpos : 0 < F θ0 := by
    have hcossq_pos : 0 < Real.cos θ0 ^ 2 := by
      have hsq : Real.cos θ0 ^ 2 = (3 / 4 : ℝ) := by
        rw [show Real.cos θ0 = Real.sqrt (3 / 4 : ℝ) by
          dsimp [θ0]
          exact Real.cos_arccos (by
            nlinarith [Real.sqrt_nonneg (3 / 4 : ℝ)]) (by
            rw [← Real.sqrt_one]
            exact Real.sqrt_le_sqrt (by norm_num))]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 / 4 by norm_num)]
      rw [hsq]
      norm_num
    calc
      0 < (sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ0 a) - c) * Real.cos θ0 ^ 2 := by
        have hsub : 0 < sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ0 a) - c := by
          linarith
        exact mul_pos hsub hcossq_pos
      _ = F θ0 := by
        simp [F]
        ring
  have hFzero :
      F θ0 = 0 :=
    eq_zero_of_nonneg_continuous_intervalIntegral_zero_at hFcont hFnonneg hFint hθ0
  linarith

theorem exists_gt_value_at_one_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
        sqCenteredNorthZonalQuotientRaw g u := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have hnegEq :
      sqCenteredNorthZonalQuotientRaw (-g) a =
        sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc := by
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg haEq
  have hnegGt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw (-g) (sqScaleMap a u) := by
    intro u hu hu1
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (hlt hu hu1)
  rcases
      exists_lt_value_at_one_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hnegFrame hnegZonal ha hnegEq hnegGt with
    ⟨u, huPos, huHalfLt, huValLt⟩
  refine ⟨u, huPos, huHalfLt, ?_⟩
  simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg huValLt

theorem exists_lt_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u <
        sqCenteredNorthZonalQuotientRaw g u0 := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g u0
  by_contra hno
  push_neg at hno
  let F : ℝ → ℝ := fun θ =>
    Real.cos θ ^ 2 * sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ a) -
      c * Real.cos θ ^ 2
  have hFcont : Continuous F := by
    have hcontQ := continuous_cos_sq_mul_sqCenteredNorthZonalQuotientRaw_comp g ha
    have hconst : Continuous (fun θ : ℝ => c * Real.cos θ ^ 2) := by
      exact continuous_const.mul (Real.continuous_cos.pow 2)
    simpa [F, mul_comm, mul_left_comm, mul_assoc] using hcontQ.sub hconst
  have hFnonneg :
      ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), 0 ≤ F θ := by
    intro θ hθ
    by_cases hcos0 : Real.cos θ = 0
    · simp [F, hcos0]
    · let x : unitIcc := sqMulCosSelfMap θ a
      have hxpos : 0 < x.1 := by
        simpa [x, sqMulCosSelfMap, hcos0, sq_pos_iff] using mul_pos ha (sq_pos_iff.mpr hcos0)
      have hcx : c ≤ sqCenteredNorthZonalQuotientRaw g x := by
        by_cases hxhalf : a.1 / 2 ≤ x.1
        · by_cases hxa : x = a
          · simpa [c, hxa] using haEq.ge
          · let uθ : unitIcc := ⟨x.1 / a.1, by
              constructor
              · positivity
              · have hxleA : x.1 ≤ a.1 := by
                  dsimp [x, sqMulCosSelfMap]
                  nlinarith [Real.cos_sq_le_one θ, a.2.1]
                have hxleA' : x.1 ≤ 1 * a.1 := by simpa using hxleA
                exact (div_le_iff₀ ha).2 hxleA'⟩
            have huHalf : (1 / 2 : ℝ) ≤ uθ.1 := by
              change (1 / 2 : ℝ) ≤ x.1 / a.1
              have hxhalf' : (1 / 2 : ℝ) * a.1 ≤ x.1 := by
                nlinarith
              exact (le_div_iff₀ ha).2 hxhalf'
            have huLt : uθ.1 < 1 := by
              change x.1 / a.1 < 1
              have hxlt : x.1 < a.1 := by
                have hxle : x.1 ≤ a.1 := by
                  dsimp [x, sqMulCosSelfMap]
                  nlinarith [Real.cos_sq_le_one θ, a.2.1]
                have hxne : x.1 ≠ a.1 := by
                  intro hxeq
                  apply hxa
                  exact Subtype.ext hxeq
                exact lt_of_le_of_ne hxle hxne
              exact (div_lt_one ha).2 hxlt
            have hscale : sqScaleMap a uθ = x := by
              apply Subtype.ext
              change a.1 * uθ.1 = x.1
              simp [uθ]
              field_simp [show (a.1 : ℝ) ≠ 0 by exact ne_of_gt ha]
            have hcx' :
                c < sqCenteredNorthZonalQuotientRaw g x := by
              simpa [c, hscale] using hgt (u := uθ) huHalf huLt
            exact le_of_lt hcx'
        · have hxltHalf : x.1 < a.1 / 2 := lt_of_not_ge hxhalf
          exact hno (u := x) hxpos hxltHalf
      have hsub_nonneg : 0 ≤ sqCenteredNorthZonalQuotientRaw g x - c := by
        linarith
      have hcossq_nonneg : 0 ≤ Real.cos θ ^ 2 := by positivity
      calc
        0 ≤ (sqCenteredNorthZonalQuotientRaw g x - c) * Real.cos θ ^ 2 := by
          exact mul_nonneg hsub_nonneg hcossq_nonneg
        _ = F θ := by
          simp [F, x]
          ring
  have hFint :
      ∫ θ in 0..2 * Real.pi, F θ = 0 := by
    have hfixa :=
      sqCenteredNorthZonalQuotientRaw_fixed_on_pos_of_mem_frame hgframe hgz ha
    have hfixa' :
        2 * (((2 * Real.pi)⁻¹ : ℝ) *
          ∫ θ in 0..2 * Real.pi,
            Real.cos θ ^ 2 *
              sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ a)) = c := by
      exact hfixa.trans <| by simpa [c] using haEq
    have hcosSq :
        ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 = Real.pi := by
      rw [integral_cos_sq]
      simp
    have hfixInt :
        ∫ θ in 0..2 * Real.pi,
            Real.cos θ ^ 2 *
              sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ a)
          = Real.pi * c := by
      have htwoPi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp [htwoPi_ne, Real.pi_ne_zero] at hfixa'
      linarith
    rw [show F =
        (fun θ : ℝ =>
          Real.cos θ ^ 2 *
            sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ a) -
              c * Real.cos θ ^ 2) by
          funext θ; simp [F]]
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul, hcosSq, hfixInt]
      ring
    · exact (continuous_cos_sq_mul_sqCenteredNorthZonalQuotientRaw_comp g ha).intervalIntegrable _ _
    · exact (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  let uThreeQuarter : unitIcc := ⟨(3 / 4 : ℝ), by constructor <;> norm_num⟩
  let θ0 : ℝ := Real.arccos (Real.sqrt (3 / 4 : ℝ))
  have hθ0 : θ0 ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
    have hsqrt_lt : Real.sqrt (3 / 4 : ℝ) < 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hsqrt_pos : 0 < Real.sqrt (3 / 4 : ℝ) := by
      exact Real.sqrt_pos.mpr (by norm_num)
    refine ⟨Real.arccos_pos.mpr hsqrt_lt, ?_⟩
    have hlt' : θ0 < Real.pi / 2 := by
      dsimp [θ0]
      exact Real.arccos_lt_pi_div_two.mpr hsqrt_pos
    linarith [Real.pi_pos]
  have hscaleThreeQuarter :
      sqMulCosSelfMap θ0 a = sqScaleMap a uThreeQuarter := by
    apply Subtype.ext
    change a.1 * Real.cos θ0 ^ 2 = a.1 * uThreeQuarter.1
    have hcos :
        Real.cos θ0 = Real.sqrt (3 / 4 : ℝ) := by
      dsimp [θ0]
      exact Real.cos_arccos (by
        nlinarith [Real.sqrt_nonneg (3 / 4 : ℝ)]) (by
        rw [← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (by norm_num))
    have hsq : Real.cos θ0 ^ 2 = (3 / 4 : ℝ) := by
      rw [hcos]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 / 4 by norm_num)]
    simp [uThreeQuarter, hsq]
  have hgtThreeQuarter :
      c < sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ0 a) := by
    have huHalf : (1 / 2 : ℝ) ≤ uThreeQuarter.1 := by
      change (1 / 2 : ℝ) ≤ (3 / 4 : ℝ)
      norm_num
    have huLt : uThreeQuarter.1 < 1 := by
      change (3 / 4 : ℝ) < 1
      norm_num
    simpa [c, hscaleThreeQuarter] using hgt (u := uThreeQuarter) huHalf huLt
  have hFpos : 0 < F θ0 := by
    have hcossq_pos : 0 < Real.cos θ0 ^ 2 := by
      have hsq : Real.cos θ0 ^ 2 = (3 / 4 : ℝ) := by
        rw [show Real.cos θ0 = Real.sqrt (3 / 4 : ℝ) by
          dsimp [θ0]
          exact Real.cos_arccos (by
            nlinarith [Real.sqrt_nonneg (3 / 4 : ℝ)]) (by
            rw [← Real.sqrt_one]
            exact Real.sqrt_le_sqrt (by norm_num))]
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 / 4 by norm_num)]
      rw [hsq]
      norm_num
    calc
      0 < (sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ0 a) - c) * Real.cos θ0 ^ 2 := by
        have hsub : 0 < sqCenteredNorthZonalQuotientRaw g (sqMulCosSelfMap θ0 a) - c := by
          linarith
        exact mul_pos hsub hcossq_pos
      _ = F θ0 := by
        simp [F]
        ring
  have hFzero :
      F θ0 = 0 :=
    eq_zero_of_nonneg_continuous_intervalIntegral_zero_at hFcont hFnonneg hFint hθ0
  linarith

theorem exists_gt_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g u0) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u0 <
        sqCenteredNorthZonalQuotientRaw g u := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have hnegEq :
      sqCenteredNorthZonalQuotientRaw (-g) a =
        sqCenteredNorthZonalQuotientRaw (-g) u0 := by
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg haEq
  have hnegGt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw (-g) u0 <
          sqCenteredNorthZonalQuotientRaw (-g) (sqScaleMap a u) := by
    intro u hu hu1
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (hlt hu hu1)
  rcases
      exists_lt_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hnegFrame hnegZonal ha hnegEq hnegGt with
    ⟨u, huPos, huHalfLt, huValLt⟩
  refine ⟨u, huPos, huHalfLt, ?_⟩
  simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg huValLt

theorem exists_lt_value_at_anchor_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g u0 ∧
      ∀ {δ : ℝ}, 0 < δ →
        ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
          sqCenteredNorthZonalQuotientRaw g y =
            sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_lt_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz ha haEq hgt with
    ⟨x, hxPos, hxLtHalf, hxLt⟩
  refine ⟨x, hxPos, hxLtHalf, hxLt, ?_⟩
  intro δ hδ
  exact
    exists_eq_value_at_anchor_near_zero_of_not_const_of_mem_frame
      (g := g) hgframe hgz hxPos rfl
      ⟨u0, hu0, Ne.symm (ne_of_lt hxLt)⟩ hδ

theorem exists_gt_value_at_anchor_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g u0) :
    ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u0 <
        sqCenteredNorthZonalQuotientRaw g x ∧
      ∀ {δ : ℝ}, 0 < δ →
        ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
          sqCenteredNorthZonalQuotientRaw g y =
            sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_gt_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell
        hgframe hgz ha haEq hlt with
    ⟨x, hxPos, hxLtHalf, hxGt⟩
  refine ⟨x, hxPos, hxLtHalf, hxGt, ?_⟩
  intro δ hδ
  exact
    exists_eq_value_at_anchor_near_zero_of_not_const_of_mem_frame
      (g := g) hgframe hgz hxPos rfl
      ⟨u0, hu0, ne_of_lt hxGt⟩ hδ

theorem exists_lt_value_at_anchor_below_half_without_punctured_lower_bound_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g u0 ∧
      ¬ ∃ δ : ℝ, 0 < δ ∧
          ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
            sqCenteredNorthZonalQuotientRaw g x <
              sqCenteredNorthZonalQuotientRaw g y := by
  rcases
      exists_lt_value_at_anchor_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz hu0 ha haEq hgt with
    ⟨x, hxPos, hxLtHalf, hxLt, hnear⟩
  refine ⟨x, hxPos, hxLtHalf, hxLt, ?_⟩
  intro hpre
  rcases hpre with ⟨δ, hδ, hδprop⟩
  rcases hnear hδ with ⟨y, hyPos, hyLt, hyEq⟩
  have hygt :
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g y := hδprop hyPos hyLt
  rw [hyEq] at hygt
  exact lt_irrefl _ hygt

theorem exists_gt_value_at_anchor_below_half_without_punctured_upper_bound_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g u0) :
    ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u0 <
        sqCenteredNorthZonalQuotientRaw g x ∧
      ¬ ∃ δ : ℝ, 0 < δ ∧
          ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
            sqCenteredNorthZonalQuotientRaw g y <
              sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_gt_value_at_anchor_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_lt_on_halfShell
        hgframe hgz hu0 ha haEq hlt with
    ⟨x, hxPos, hxLtHalf, hxGt, hnear⟩
  refine ⟨x, hxPos, hxLtHalf, hxGt, ?_⟩
  intro hpre
  rcases hpre with ⟨δ, hδ, hδprop⟩
  rcases hnear hδ with ⟨y, hyPos, hyLt, hyEq⟩
  have hylt :
      sqCenteredNorthZonalQuotientRaw g y <
        sqCenteredNorthZonalQuotientRaw g x := hδprop hyPos hyLt
  rw [hyEq] at hylt
  exact lt_irrefl _ hylt

theorem exists_lt_value_at_one_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      ∀ {δ : ℝ}, 0 < δ →
        ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
          sqCenteredNorthZonalQuotientRaw g y =
            sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_lt_value_at_one_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz ha haEq hgt with
    ⟨x, hxPos, hxLtHalf, hxLt⟩
  refine ⟨x, hxPos, hxLtHalf, hxLt, ?_⟩
  intro δ hδ
  exact
    exists_eq_value_at_anchor_near_zero_of_ne_value_at_one_of_mem_frame
      hgframe hgz hxPos (ne_of_lt hxLt) hδ

theorem exists_gt_value_at_one_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc) :
    ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
        sqCenteredNorthZonalQuotientRaw g x ∧
      ∀ {δ : ℝ}, 0 < δ →
        ∃ y : unitIcc, 0 < y.1 ∧ y.1 < δ ∧
          sqCenteredNorthZonalQuotientRaw g y =
            sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_gt_value_at_one_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell
        hgframe hgz ha haEq hlt with
    ⟨x, hxPos, hxLtHalf, hxGt⟩
  refine ⟨x, hxPos, hxLtHalf, hxGt, ?_⟩
  intro δ hδ
  exact
    exists_eq_value_at_anchor_near_zero_of_ne_value_at_one_of_mem_frame
      hgframe hgz hxPos (ne_of_gt hxGt) hδ

theorem exists_lt_value_at_one_below_half_without_punctured_lower_bound_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      ¬ ∃ δ : ℝ, 0 < δ ∧
          ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
            sqCenteredNorthZonalQuotientRaw g x <
              sqCenteredNorthZonalQuotientRaw g y := by
  rcases
      exists_lt_value_at_one_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz ha haEq hgt with
    ⟨x, hxPos, hxLtHalf, hxLt, hnear⟩
  refine ⟨x, hxPos, hxLtHalf, hxLt, ?_⟩
  intro hpre
  rcases hpre with ⟨δ, hδ, hδprop⟩
  rcases hnear hδ with ⟨y, hyPos, hyLt, hyEq⟩
  have hygt :
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g y := hδprop hyPos hyLt
  rw [hyEq] at hygt
  exact lt_irrefl _ hygt

theorem exists_gt_value_at_one_below_half_without_punctured_upper_bound_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc) :
    ∃ x : unitIcc, 0 < x.1 ∧ x.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
        sqCenteredNorthZonalQuotientRaw g x ∧
      ¬ ∃ δ : ℝ, 0 < δ ∧
          ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
            sqCenteredNorthZonalQuotientRaw g y <
              sqCenteredNorthZonalQuotientRaw g x := by
  rcases
      exists_gt_value_at_one_below_half_with_eq_value_near_zero_of_eq_value_at_scale_of_forall_lt_on_halfShell
        hgframe hgz ha haEq hlt with
    ⟨x, hxPos, hxLtHalf, hxGt, hnear⟩
  refine ⟨x, hxPos, hxLtHalf, hxGt, ?_⟩
  intro hpre
  rcases hpre with ⟨δ, hδ, hδprop⟩
  rcases hnear hδ with ⟨y, hyPos, hyLt, hyEq⟩
  have hylt :
      sqCenteredNorthZonalQuotientRaw g y <
        sqCenteredNorthZonalQuotientRaw g x := hδprop hyPos hyLt
  rw [hyEq] at hylt
  exact lt_irrefl _ hylt

theorem exists_eq_value_at_one_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  have honePos : 0 < (oneUnitIcc : unitIcc).1 := by
    simp [oneUnitIcc]
  have honeNe : (oneUnitIcc : unitIcc).1 ≠ 0 := ne_of_gt honePos
  rcases
      exists_lt_value_at_one_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz ha haEq hgt with
    ⟨u0, hu0Pos, hu0Lt, hu0LtVal⟩
  let uHalf : unitIcc := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  let b : unitIcc := ⟨a.1 / 2, by
    constructor
    · positivity
    · have : a.1 / 2 ≤ (1 : ℝ) / 2 := by
        gcongr
        exact a.2.2
      linarith⟩
  have hbPos : 0 < b.1 := by
    dsimp [b]
    positivity
  have hbEqScale : sqScaleMap a uHalf = b := by
    apply Subtype.ext
    simp [sqScaleMap, b, uHalf]
    ring
  have hbGtVal :
      c < sqCenteredNorthZonalQuotientRaw g b := by
    have hhalf : (1 / 2 : ℝ) ≤ uHalf.1 := by
      change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
      exact le_rfl
    have hhalfLt : uHalf.1 < 1 := by
      change (1 / 2 : ℝ) < 1
      norm_num
    simpa [c, hbEqScale, uHalf] using hgt (u := uHalf) hhalf hhalfLt
  have hu0b : u0 ≤ b := hu0Lt.le
  let f : unitIcc → ℝ := fun v => sqCenteredNorthZonalProfile g v / v.1
  have hconts : ContinuousOn f (Set.uIcc u0 b) := by
    rw [Set.uIcc_of_le hu0b]
    refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
    intro v hv
    exact lt_of_lt_of_le hu0Pos hv.1
  have hfu0_le_fb : f u0 ≤ f b := by
    simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu0Pos, ne_of_gt hbPos, honeNe] using
      le_trans hu0LtVal.le hbGtVal.le
  have hc_mem :
      c ∈ Set.uIcc (f u0) (f b) := by
    rw [Set.uIcc_of_le hfu0_le_fb]
    simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu0Pos, ne_of_gt hbPos, honeNe] using
      And.intro hu0LtVal.le hbGtVal.le
  rcases intermediate_value_uIcc hconts hc_mem with ⟨u, huMem, huEq⟩
  have huIcc : u ∈ Set.Icc u0 b := by
    simpa [Set.uIcc_of_le hu0b] using huMem
  have huPos : 0 < u.1 := lt_of_lt_of_le hu0Pos huIcc.1
  have huLt : u.1 < a.1 / 2 := by
    have hfb_ne_c : f b ≠ c := by
      intro hfbEq
      have : sqCenteredNorthZonalQuotientRaw g b = c := by
        simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hbPos] using hfbEq
      linarith
    have hlt_or_eq : u.1 < b.1 ∨ u.1 = b.1 := lt_or_eq_of_le huIcc.2
    cases hlt_or_eq with
    | inl hlt =>
        simpa [b] using hlt
    | inr heq =>
        exfalso
        have hub : u = b := Subtype.ext heq
        subst hub
        exact hfb_ne_c huEq
  exact ⟨u, huPos, huLt, by
    simpa [c, f, sqCenteredNorthZonalQuotientRaw, ne_of_gt huPos, honeNe] using huEq⟩

theorem exists_eq_value_at_one_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  have honePos : 0 < (oneUnitIcc : unitIcc).1 := by
    simp [oneUnitIcc]
  have honeNe : (oneUnitIcc : unitIcc).1 ≠ 0 := ne_of_gt honePos
  rcases
      exists_gt_value_at_one_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell
        hgframe hgz ha haEq hlt with
    ⟨u0, hu0Pos, hu0Lt, hu0GtVal⟩
  let uHalf : unitIcc := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  let b : unitIcc := ⟨a.1 / 2, by
    constructor
    · positivity
    · have : a.1 / 2 ≤ (1 : ℝ) / 2 := by
        gcongr
        exact a.2.2
      linarith⟩
  have hbPos : 0 < b.1 := by
    dsimp [b]
    positivity
  have hbEqScale : sqScaleMap a uHalf = b := by
    apply Subtype.ext
    simp [sqScaleMap, b, uHalf]
    ring
  have hbLtVal :
      sqCenteredNorthZonalQuotientRaw g b < c := by
    have hhalf : (1 / 2 : ℝ) ≤ uHalf.1 := by
      change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
      exact le_rfl
    have hhalfLt : uHalf.1 < 1 := by
      change (1 / 2 : ℝ) < 1
      norm_num
    simpa [c, hbEqScale, uHalf] using hlt (u := uHalf) hhalf hhalfLt
  have hu0b : u0 ≤ b := hu0Lt.le
  let f : unitIcc → ℝ := fun v => sqCenteredNorthZonalProfile g v / v.1
  have hconts : ContinuousOn f (Set.uIcc u0 b) := by
    rw [Set.uIcc_of_le hu0b]
    refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
    intro v hv
    exact lt_of_lt_of_le hu0Pos hv.1
  have hfb_le_fu0 : f b ≤ f u0 := by
    simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu0Pos, ne_of_gt hbPos, honeNe] using
      le_trans hbLtVal.le hu0GtVal.le
  have hc_mem :
      c ∈ Set.uIcc (f u0) (f b) := by
    rw [Set.mem_uIcc]
    right
    simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu0Pos, ne_of_gt hbPos, honeNe] using
      And.intro hbLtVal.le hu0GtVal.le
  rcases intermediate_value_uIcc hconts hc_mem with ⟨u, huMem, huEq⟩
  have huIcc : u ∈ Set.Icc u0 b := by
    simpa [Set.uIcc_of_le hu0b] using huMem
  have huPos : 0 < u.1 := lt_of_lt_of_le hu0Pos huIcc.1
  have huLt : u.1 < a.1 / 2 := by
    have hfb_ne_c : f b ≠ c := by
      intro hfbEq
      have : sqCenteredNorthZonalQuotientRaw g b = c := by
        simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hbPos] using hfbEq
      linarith
    have hlt_or_eq : u.1 < b.1 ∨ u.1 = b.1 := lt_or_eq_of_le huIcc.2
    cases hlt_or_eq with
    | inl hlt =>
        simpa [b] using hlt
    | inr heq =>
        exfalso
        have hub : u = b := Subtype.ext heq
        subst hub
        exact hfb_ne_c huEq
  exact ⟨u, huPos, huLt, by
    simpa [c, f, sqCenteredNorthZonalQuotientRaw, ne_of_gt huPos, honeNe] using huEq⟩

theorem exists_eq_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g u0 := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g u0
  have hu0Ne : u0.1 ≠ 0 := ne_of_gt hu0
  rcases
      exists_lt_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz ha haEq hgt with
    ⟨u1, hu1Pos, hu1Lt, hu1LtVal⟩
  let uHalf : unitIcc := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  let b : unitIcc := ⟨a.1 / 2, by
    constructor
    · positivity
    · have : a.1 / 2 ≤ (1 : ℝ) / 2 := by
        gcongr
        exact a.2.2
      linarith⟩
  have hbPos : 0 < b.1 := by
    dsimp [b]
    positivity
  have hbEqScale : sqScaleMap a uHalf = b := by
    apply Subtype.ext
    simp [sqScaleMap, b, uHalf]
    ring
  have hbGtVal :
      c < sqCenteredNorthZonalQuotientRaw g b := by
    have hhalf : (1 / 2 : ℝ) ≤ uHalf.1 := by
      change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
      exact le_rfl
    have hhalfLt : uHalf.1 < 1 := by
      change (1 / 2 : ℝ) < 1
      norm_num
    simpa [c, hbEqScale, uHalf] using hgt (u := uHalf) hhalf hhalfLt
  have hu1b : u1 ≤ b := hu1Lt.le
  let f : unitIcc → ℝ := fun v => sqCenteredNorthZonalProfile g v / v.1
  have hconts : ContinuousOn f (Set.uIcc u1 b) := by
    rw [Set.uIcc_of_le hu1b]
    refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
    intro v hv
    exact lt_of_lt_of_le hu1Pos hv.1
  have hfu1_le_fb : f u1 ≤ f b := by
    simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu1Pos, ne_of_gt hbPos, hu0Ne] using
      le_trans hu1LtVal.le hbGtVal.le
  have hc_mem :
      c ∈ Set.uIcc (f u1) (f b) := by
    rw [Set.uIcc_of_le hfu1_le_fb]
    simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu1Pos, ne_of_gt hbPos, hu0Ne] using
      And.intro hu1LtVal.le hbGtVal.le
  rcases intermediate_value_uIcc hconts hc_mem with ⟨u, huMem, huEq⟩
  have huIcc : u ∈ Set.Icc u1 b := by
    simpa [Set.uIcc_of_le hu1b] using huMem
  have huPos : 0 < u.1 := lt_of_lt_of_le hu1Pos huIcc.1
  have huLt : u.1 < a.1 / 2 := by
    have hfb_ne_c : f b ≠ c := by
      intro hfbEq
      have : sqCenteredNorthZonalQuotientRaw g b = c := by
        simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hbPos] using hfbEq
      linarith
    have hlt_or_eq : u.1 < b.1 ∨ u.1 = b.1 := lt_or_eq_of_le huIcc.2
    cases hlt_or_eq with
    | inl hlt =>
        simpa [b] using hlt
    | inr heq =>
        exfalso
        have hub : u = b := Subtype.ext heq
        subst hub
        exact hfb_ne_c huEq
  exact ⟨u, huPos, huLt, by
    simpa [c, f, sqCenteredNorthZonalQuotientRaw, ne_of_gt huPos, hu0Ne] using huEq⟩

theorem exists_eq_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g u0) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g u0 := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g u0
  have hu0Ne : u0.1 ≠ 0 := ne_of_gt hu0
  rcases
      exists_gt_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_lt_on_halfShell
        hgframe hgz ha haEq hlt with
    ⟨u1, hu1Pos, hu1Lt, hu1GtVal⟩
  let uHalf : unitIcc := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  let b : unitIcc := ⟨a.1 / 2, by
    constructor
    · positivity
    · have : a.1 / 2 ≤ (1 : ℝ) / 2 := by
        gcongr
        exact a.2.2
      linarith⟩
  have hbPos : 0 < b.1 := by
    dsimp [b]
    positivity
  have hbEqScale : sqScaleMap a uHalf = b := by
    apply Subtype.ext
    simp [sqScaleMap, b, uHalf]
    ring
  have hbLtVal :
      sqCenteredNorthZonalQuotientRaw g b < c := by
    have hhalf : (1 / 2 : ℝ) ≤ uHalf.1 := by
      change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
      exact le_rfl
    have hhalfLt : uHalf.1 < 1 := by
      change (1 / 2 : ℝ) < 1
      norm_num
    simpa [c, hbEqScale, uHalf] using hlt (u := uHalf) hhalf hhalfLt
  have hu1b : u1 ≤ b := hu1Lt.le
  let f : unitIcc → ℝ := fun v => sqCenteredNorthZonalProfile g v / v.1
  have hconts : ContinuousOn f (Set.uIcc u1 b) := by
    rw [Set.uIcc_of_le hu1b]
    refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
    intro v hv
    exact lt_of_lt_of_le hu1Pos hv.1
  have hfb_le_fu1 : f b ≤ f u1 := by
    simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu1Pos, ne_of_gt hbPos, hu0Ne] using
      le_trans hbLtVal.le hu1GtVal.le
  have hc_mem :
      c ∈ Set.uIcc (f u1) (f b) := by
    rw [Set.mem_uIcc]
    right
    simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu1Pos, ne_of_gt hbPos, hu0Ne] using
      And.intro hbLtVal.le hu1GtVal.le
  rcases intermediate_value_uIcc hconts hc_mem with ⟨u, huMem, huEq⟩
  have huIcc : u ∈ Set.Icc u1 b := by
    simpa [Set.uIcc_of_le hu1b] using huMem
  have huPos : 0 < u.1 := lt_of_lt_of_le hu1Pos huIcc.1
  have huLt : u.1 < a.1 / 2 := by
    have hfb_ne_c : f b ≠ c := by
      intro hfbEq
      have : sqCenteredNorthZonalQuotientRaw g b = c := by
        simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hbPos] using hfbEq
      linarith
    have hlt_or_eq : u.1 < b.1 ∨ u.1 = b.1 := lt_or_eq_of_le huIcc.2
    cases hlt_or_eq with
    | inl hlt =>
        simpa [b] using hlt
    | inr heq =>
        exfalso
        have hub : u = b := Subtype.ext heq
        subst hub
        exact hfb_ne_c huEq
  exact ⟨u, huPos, huLt, by
    simpa [c, f, sqCenteredNorthZonalQuotientRaw, ne_of_gt huPos, hu0Ne] using huEq⟩

theorem exists_eq_value_at_anchor_below_half_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g u0 ∧
      ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g v := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g u0
  have hu0Ne : u0.1 ≠ 0 := ne_of_gt hu0
  rcases
      exists_eq_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz hu0 ha haEq hgt with
    ⟨u1, hu1Pos, hu1Lt, hu1Eq⟩
  let b : unitIcc := ⟨a.1 / 2, by
    constructor
    · positivity
    · have : a.1 / 2 ≤ (1 : ℝ) / 2 := by
        gcongr
        exact a.2.2
      linarith⟩
  have hbPos : 0 < b.1 := by
    dsimp [b]
    positivity
  have hbEqScale : sqScaleMap a halfUnitIcc = b := by
    apply Subtype.ext
    simp [sqScaleMap, b, halfUnitIcc]
    ring
  have hbGt :
      c < sqCenteredNorthZonalQuotientRaw g b := by
    have hhalf : (1 / 2 : ℝ) ≤ (halfUnitIcc : unitIcc).1 := by
      change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
      exact le_rfl
    have hhalfLt : (halfUnitIcc : unitIcc).1 < 1 := by
      change (1 / 2 : ℝ) < 1
      norm_num
    simpa [c, hbEqScale] using hgt (u := halfUnitIcc) hhalf hhalfLt
  let f : unitIcc → ℝ := fun x => sqCenteredNorthZonalProfile g x / x.1
  let s : Set unitIcc := {v : unitIcc |
    u1.1 ≤ v.1 ∧ v.1 ≤ a.1 / 2 ∧ f v = c}
  have hsClosed : IsClosed s := by
    let t : Set unitIcc := {v : unitIcc | u1.1 ≤ v.1 ∧ v.1 ≤ a.1 / 2}
    have htClosed : IsClosed t := by
      refine (isClosed_le continuous_const continuous_subtype_val).inter ?_
      exact isClosed_le continuous_subtype_val continuous_const
    have hcontT : ContinuousOn f t := by
      refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
      intro v hv
      exact lt_of_lt_of_le hu1Pos hv.1
    have hclosedEq :
        IsClosed (t ∩ f ⁻¹' ({c} : Set ℝ)) :=
      ContinuousOn.preimage_isClosed_of_isClosed hcontT htClosed isClosed_singleton
    convert hclosedEq using 1
    ext v
    simp [s, t, Set.mem_preimage, and_assoc]
  have hsNonempty : s.Nonempty := by
    refine ⟨u1, ?_⟩
    refine ⟨le_rfl, hu1Lt.le, ?_⟩
    simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu1Pos, hu0Ne] using hu1Eq
  have hsCompact : IsCompact s := hsClosed.isCompact
  rcases hsCompact.exists_isMaxOn hsNonempty continuous_subtype_val.continuousOn with
    ⟨umax, humax, humaxMax⟩
  rw [isMaxOn_iff] at humaxMax
  have humaxPos : 0 < umax.1 := lt_of_lt_of_le hu1Pos humax.1
  have humaxEq : sqCenteredNorthZonalQuotientRaw g umax = c := by
    simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt humaxPos, hu0Ne] using humax.2.2
  have humaxLt : umax.1 < a.1 / 2 := by
    have humaxLe : umax.1 ≤ a.1 / 2 := humax.2.1
    by_contra hnot
    have humaxEqHalf : umax.1 = a.1 / 2 := le_antisymm humaxLe (le_of_not_gt hnot)
    have hub : umax = b := by
      apply Subtype.ext
      simpa [b] using humaxEqHalf
    subst hub
    linarith [hbGt, humaxEq]
  refine ⟨umax, humaxPos, humaxLt, humaxEq, ?_⟩
  intro v huv hva
  have hvPos : 0 < v.1 := lt_trans humaxPos huv
  by_contra hnot
  have hvc : sqCenteredNorthZonalQuotientRaw g v ≤ c := by
    exact le_of_not_gt hnot
  have hvLeB : v.1 ≤ b.1 := by
    simpa [b] using hva
  have hvb : v ≤ b := by
    exact Subtype.coe_le_coe.mp hvLeB
  have hrootAbove :
      ∃ w : unitIcc, v.1 ≤ w.1 ∧ w.1 ≤ a.1 / 2 ∧
        f w = c := by
    by_cases hvEq : sqCenteredNorthZonalQuotientRaw g v = c
    · refine ⟨v, le_rfl, hva, ?_⟩
      simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hvPos, hu0Ne] using hvEq
    · have hvLtC : sqCenteredNorthZonalQuotientRaw g v < c := lt_of_le_of_ne hvc hvEq
      have hcont : ContinuousOn f (Set.uIcc v b) := by
        rw [Set.uIcc_of_le hvb]
        refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
        intro x hx
        exact lt_of_lt_of_le hvPos hx.1
      have hc_mem : c ∈ Set.uIcc (f v) (f b) := by
        have hvc' : f v < c := by
          simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hvPos, hu0Ne] using hvLtC
        have hbc' : c < f b := by
          simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hbPos, hu0Ne] using hbGt
        rw [Set.mem_uIcc]
        left
        exact ⟨hvc'.le, hbc'.le⟩
      rcases intermediate_value_uIcc hcont hc_mem with ⟨w, hwMem, hwEq⟩
      have hwIcc : w ∈ Set.Icc v b := by
        simpa [Set.uIcc_of_le hvb] using hwMem
      refine ⟨w, hwIcc.1, ?_, ?_⟩
      · simpa [b] using hwIcc.2
      · simpa using hwEq
  rcases hrootAbove with ⟨w, hvw, hwa, hwEq⟩
  have huw : umax.1 < w.1 := lt_of_lt_of_le huv hvw
  have hw_mem : w ∈ s := ⟨le_trans humax.1 huw.le, hwa, hwEq⟩
  have hmax := humaxMax w hw_mem
  exact not_lt_of_ge hmax huw

theorem exists_eq_value_at_anchor_below_half_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g u0) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g u0 ∧
      ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g v <
          sqCenteredNorthZonalQuotientRaw g u0 := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have hnegEq :
      sqCenteredNorthZonalQuotientRaw (-g) a =
        sqCenteredNorthZonalQuotientRaw (-g) u0 := by
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg haEq
  have hnegGt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw (-g) u0 <
          sqCenteredNorthZonalQuotientRaw (-g) (sqScaleMap a u) := by
    intro u hu hu1
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (hlt hu hu1)
  rcases
      exists_eq_value_at_anchor_below_half_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hnegFrame hnegZonal hu0 ha hnegEq hnegGt with
    ⟨u, huPos, huLt, huEq, huAbove⟩
  refine ⟨u, huPos, huLt, ?_, ?_⟩
  · simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg huEq
  · intro v huv hva
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (huAbove huv hva)

theorem exists_eq_value_at_one_below_half_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g v := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  have honePos : 0 < (oneUnitIcc : unitIcc).1 := by
    simp [oneUnitIcc]
  have honeNe : (oneUnitIcc : unitIcc).1 ≠ 0 := ne_of_gt honePos
  rcases
      exists_eq_value_at_one_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz ha haEq hgt with
    ⟨u0, hu0Pos, hu0Lt, hu0Eq⟩
  let b : unitIcc := ⟨a.1 / 2, by
    constructor
    · positivity
    · have : a.1 / 2 ≤ (1 : ℝ) / 2 := by
        gcongr
        exact a.2.2
      linarith⟩
  have hbPos : 0 < b.1 := by
    dsimp [b]
    positivity
  have hbEqScale : sqScaleMap a halfUnitIcc = b := by
    apply Subtype.ext
    simp [sqScaleMap, b, halfUnitIcc]
    ring
  have hbGt :
      c < sqCenteredNorthZonalQuotientRaw g b := by
    have hhalf : (1 / 2 : ℝ) ≤ (halfUnitIcc : unitIcc).1 := by
      change (1 / 2 : ℝ) ≤ (1 / 2 : ℝ)
      exact le_rfl
    have hhalfLt : (halfUnitIcc : unitIcc).1 < 1 := by
      change (1 / 2 : ℝ) < 1
      norm_num
    simpa [c, hbEqScale] using hgt (u := halfUnitIcc) hhalf hhalfLt
  let f : unitIcc → ℝ := fun x => sqCenteredNorthZonalProfile g x / x.1
  let s : Set unitIcc := {v : unitIcc |
    u0.1 ≤ v.1 ∧ v.1 ≤ a.1 / 2 ∧ f v = c}
  have hsClosed : IsClosed s := by
    let t : Set unitIcc := {v : unitIcc | u0.1 ≤ v.1 ∧ v.1 ≤ a.1 / 2}
    have htClosed : IsClosed t := by
      refine (isClosed_le continuous_const continuous_subtype_val).inter ?_
      exact isClosed_le continuous_subtype_val continuous_const
    have hcontT : ContinuousOn f t := by
      refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
      intro v hv
      exact lt_of_lt_of_le hu0Pos hv.1
    have hclosedEq :
        IsClosed (t ∩ f ⁻¹' ({c} : Set ℝ)) :=
      ContinuousOn.preimage_isClosed_of_isClosed hcontT htClosed isClosed_singleton
    convert hclosedEq using 1
    ext v
    simp [s, t, Set.mem_preimage, and_assoc]
  have hsNonempty : s.Nonempty := by
    refine ⟨u0, ?_⟩
    refine ⟨le_rfl, hu0Lt.le, ?_⟩
    simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hu0Pos, honeNe] using hu0Eq
  have hsCompact : IsCompact s := hsClosed.isCompact
  rcases hsCompact.exists_isMaxOn hsNonempty continuous_subtype_val.continuousOn with
    ⟨umax, humax, humaxMax⟩
  rw [isMaxOn_iff] at humaxMax
  have humaxPos : 0 < umax.1 := lt_of_lt_of_le hu0Pos humax.1
  have humaxEq : sqCenteredNorthZonalQuotientRaw g umax = c := by
    simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt humaxPos] using humax.2.2
  have humaxLt : umax.1 < a.1 / 2 := by
    have humaxLe : umax.1 ≤ a.1 / 2 := humax.2.1
    by_contra hnot
    have humaxEqHalf : umax.1 = a.1 / 2 := le_antisymm humaxLe (le_of_not_gt hnot)
    have hub : umax = b := by
      apply Subtype.ext
      simpa [b] using humaxEqHalf
    subst hub
    linarith [hbGt, humaxEq]
  refine ⟨umax, humaxPos, humaxLt, humaxEq, ?_⟩
  intro v huv hva
  have hvPos : 0 < v.1 := lt_trans humaxPos huv
  by_contra hnot
  have hvc : sqCenteredNorthZonalQuotientRaw g v ≤ c := by
    exact le_of_not_gt hnot
  have hvLeB : v.1 ≤ b.1 := by
    simpa [b] using hva
  have hvb : v ≤ b := by
    exact Subtype.coe_le_coe.mp hvLeB
  have hrootAbove :
      ∃ w : unitIcc, v.1 ≤ w.1 ∧ w.1 ≤ a.1 / 2 ∧
        f w = c := by
    by_cases hvEq : sqCenteredNorthZonalQuotientRaw g v = c
    · refine ⟨v, le_rfl, hva, ?_⟩
      simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hvPos] using hvEq
    · have hvLtC : sqCenteredNorthZonalQuotientRaw g v < c := lt_of_le_of_ne hvc hvEq
      have hcont : ContinuousOn f (Set.uIcc v b) := by
        rw [Set.uIcc_of_le hvb]
        refine (continuousOn_sqCenteredNorthZonalQuotientOnPos g).mono ?_
        intro x hx
        exact lt_of_lt_of_le hvPos hx.1
      have hc_mem : c ∈ Set.uIcc (f v) (f b) := by
        have hvc' : f v < c := by
          simpa [f, sqCenteredNorthZonalQuotientRaw, ne_of_gt hvPos] using hvLtC
        have hbc' : c < f b := by
          simpa [f, c, sqCenteredNorthZonalQuotientRaw, ne_of_gt hbPos] using hbGt
        rw [Set.mem_uIcc]
        left
        exact ⟨hvc'.le, hbc'.le⟩
      rcases intermediate_value_uIcc hcont hc_mem with ⟨w, hwMem, hwEq⟩
      have hwIcc : w ∈ Set.Icc v b := by
        simpa [Set.uIcc_of_le hvb] using hwMem
      refine ⟨w, hwIcc.1, ?_, ?_⟩
      · simpa [b] using hwIcc.2
      · simpa using hwEq
  rcases hrootAbove with ⟨w, hvw, hwa, hwEq⟩
  have huw : umax.1 < w.1 := lt_of_lt_of_le huv hvw
  have hw_mem : w ∈ s := ⟨le_trans humax.1 huw.le, hwa, hwEq⟩
  have hmax := humaxMax w hw_mem
  exact not_lt_of_ge hmax huw

theorem exists_eq_value_at_one_below_half_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc) :
    ∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 2 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g v <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have hnegEq :
      sqCenteredNorthZonalQuotientRaw (-g) a =
        sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc := by
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg haEq
  have hnegGt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw (-g) (sqScaleMap a u) := by
    intro u hu hu1
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (hlt hu hu1)
  rcases
      exists_eq_value_at_one_below_half_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hnegFrame hnegZonal ha hnegEq hnegGt with
    ⟨u, huPos, huLt, huEq, huAbove⟩
  refine ⟨u, huPos, huLt, ?_, ?_⟩
  · simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg huEq
  · intro v huv hva
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (huAbove huv hva)

theorem next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
          sqCenteredNorthZonalQuotientRaw g u0 ∧
        sqCenteredNorthZonalQuotientRaw g u0 ≤
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
    (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g u0 ∧
      ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g v) := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g u0
  let b : unitIcc := sqScaleMap a halfUnitIcc
  by_cases hbr :
      ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) ≤ c ∧
        c ≤ sqCenteredNorthZonalQuotientRaw g (sqScaleMap b v)
  · exact Or.inl (by simpa [c, b] using hbr)
  · right
    have hsplit :
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          c < sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u)) ∨
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) < c) := by
      by_cases hlow :
          ∃ u : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) ≤ c
      · right
        intro u hu
        have hnotge :
            ¬ c ≤ sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) := by
          intro hcu
          rcases hlow with ⟨v, hv, hvle⟩
          exact hbr ⟨v, u, hv, hu, hvle, hcu⟩
        linarith
      · left
        intro u hu
        have hnotle :
            ¬ sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) ≤ c := by
          intro huc
          exact hlow ⟨u, hu, huc⟩
        linarith
    have hnextGt :
        ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          c < sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) := by
      rcases hsplit with hgt' | hlt'
      · exact hgt'
      · have hhalf : (1 / 2 : ℝ) ≤ (halfUnitIcc : unitIcc).1 := by
          norm_num [halfUnitIcc]
        have hhalfLt : (halfUnitIcc : unitIcc).1 < 1 := by
          norm_num [halfUnitIcc]
        have htop :
            c < sqCenteredNorthZonalQuotientRaw g b := by
          simpa [c, b] using hgt (u := halfUnitIcc) hhalf hhalfLt
        have hone : (1 / 2 : ℝ) ≤ (oneUnitIcc : unitIcc).1 := by
          norm_num [oneUnitIcc]
        have htopLt : sqCenteredNorthZonalQuotientRaw g (sqScaleMap b oneUnitIcc) < c := by
          exact hlt' hone
        have hscaleOne : sqScaleMap b oneUnitIcc = b := by
          apply Subtype.ext
          simp [sqScaleMap, oneUnitIcc]
        have hfalse : False := by
          rw [hscaleOne] at htopLt
          linarith
        intro u hu
        exact False.elim hfalse
    rcases
        exists_eq_value_at_anchor_below_half_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
          hgframe hgz hu0 ha haEq hgt with
      ⟨u, huPos, huLtHalf, huEq, huAbove⟩
    have huLtQuarter : u.1 < a.1 / 4 := by
      by_contra huNotLt
      have huGeQuarter : a.1 / 4 ≤ u.1 := by
        exact le_of_not_gt huNotLt
      have hbEq : b.1 = a.1 / 2 := by
        dsimp [b]
        rw [sqScaleMap_apply]
        change a.1 * (1 / 2 : ℝ) = a.1 / 2
        ring
      have hbPos : 0 < b.1 := by
        rw [hbEq]
        positivity
      let w : unitIcc := ⟨u.1 / b.1, by
        constructor
        · positivity
        · have huLeB : u.1 ≤ b.1 := by
            rw [hbEq]
            exact huLtHalf.le
          have huLeB' : u.1 ≤ 1 * b.1 := by
            simpa [one_mul] using huLeB
          exact (div_le_iff₀ hbPos).2 huLeB'⟩
      have hwHalf : (1 / 2 : ℝ) ≤ w.1 := by
        change (1 / 2 : ℝ) ≤ u.1 / b.1
        have hnum : (1 / 2 : ℝ) * b.1 ≤ u.1 := by
          rw [hbEq]
          nlinarith
        exact (le_div_iff₀ hbPos).2 hnum
      have hscale : sqScaleMap b w = u := by
        apply Subtype.ext
        change b.1 * w.1 = u.1
        simp [w]
        field_simp [show (b.1 : ℝ) ≠ 0 by exact ne_of_gt hbPos]
      have hcontr :
          c < sqCenteredNorthZonalQuotientRaw g u := by
        simpa [c, hscale] using hnextGt (u := w) hwHalf
      rw [huEq] at hcontr
      linarith
    exact ⟨u, huPos, huLtQuarter, huEq, huAbove⟩

theorem next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g u0 ∧
      sqCenteredNorthZonalQuotientRaw g u0 ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
    (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g u0) := by
  rcases
      next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz hu0 ha haEq hgt with
    hbr | hroot
  · exact Or.inl hbr
  · rcases hroot with ⟨u, huPos, huLt, huEq, _⟩
    exact Or.inr ⟨u, huPos, huLt, huEq⟩

theorem next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g u0) :
    (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
          sqCenteredNorthZonalQuotientRaw g u0 ∧
        sqCenteredNorthZonalQuotientRaw g u0 ≤
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
    (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g u0 ∧
      ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g v <
          sqCenteredNorthZonalQuotientRaw g u0) := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have hnegEq :
      sqCenteredNorthZonalQuotientRaw (-g) a =
        sqCenteredNorthZonalQuotientRaw (-g) u0 := by
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg haEq
  have hnegGt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw (-g) u0 <
          sqCenteredNorthZonalQuotientRaw (-g) (sqScaleMap a u) := by
    intro u hu hu1
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (hlt hu hu1)
  rcases
      next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hnegFrame hnegZonal hu0 ha hnegEq hnegGt with
    hbr | hroot
  · rcases hbr with ⟨u, v, hu, hv, huLe, hvLe⟩
    refine Or.inl ⟨v, u, hv, hu, ?_, ?_⟩
    · simpa [sqCenteredNorthZonalQuotientRaw_neg] using hvLe
    · simpa [sqCenteredNorthZonalQuotientRaw_neg] using huLe
  · rcases hroot with ⟨u, huPos, huLt, huEq, huAbove⟩
    refine Or.inr ⟨u, huPos, huLt, ?_, ?_⟩
    · simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg huEq
    · intro v huv hva
      simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (huAbove huv hva)

theorem next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g u0) :
    (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g u0 ∧
      sqCenteredNorthZonalQuotientRaw g u0 ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
    (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g u0) := by
  rcases
      next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell
        hgframe hgz hu0 ha haEq hlt with
    hbr | hroot
  · exact Or.inl hbr
  · rcases hroot with ⟨u, huPos, huLt, huEq, _⟩
    exact Or.inr ⟨u, huPos, huLt, huEq⟩

theorem False_of_eq_value_at_anchor_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_exists_lt_witness_and_eventually_gt_above_witness
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a u x : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (huPos : 0 < u.1)
    (huLtQuarter : u.1 < a.1 / 4)
    (huEq :
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g u0)
    (huAbove :
      ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g v)
    (hxPos : 0 < x.1)
    (hxLtHalf : x.1 < a.1 / 2)
    (hxLt :
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g u0)
    (hpre :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g y) :
    False := by
  have hconst :
      ∀ {y : unitIcc}, 0 < y.1 →
        sqCenteredNorthZonalQuotientRaw g y =
          sqCenteredNorthZonalQuotientRaw g x := by
    exact
      sqCenteredNorthZonalQuotientRaw_eq_value_at_anchor_of_eventually_gt_near_zero
        (g := g) hgframe hgz hxPos rfl hpre
  have hux :
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g x := hconst huPos
  rw [huEq] at hux
  linarith [hxLt, hux]

theorem next_halfShell_bracket_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_punctured_lower_bound_above_below_half_anchor_witnesses
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u))
    (hpre :
      ∀ {x : unitIcc}, 0 < x.1 → x.1 < a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g x <
          sqCenteredNorthZonalQuotientRaw g u0 →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
            sqCenteredNorthZonalQuotientRaw g x <
              sqCenteredNorthZonalQuotientRaw g y) :
    ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g u0 ∧
      sqCenteredNorthZonalQuotientRaw g u0 ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v) := by
  rcases
      next_halfShell_bracket_or_eq_value_at_anchor_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz hu0 ha haEq hgt with
    hbr | hroot
  · exact hbr
  · rcases hroot with ⟨u, huPos, huLtQuarter, huEq, huAbove⟩
    rcases
        exists_lt_value_at_anchor_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
          hgframe hgz ha haEq hgt with
      ⟨x, hxPos, hxLtHalf, hxLt⟩
    exact False.elim <|
      False_of_eq_value_at_anchor_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_exists_lt_witness_and_eventually_gt_above_witness
        hgframe hgz hu0 ha huPos huLtQuarter huEq huAbove hxPos hxLtHalf hxLt
        (hpre hxPos hxLtHalf hxLt)

theorem next_halfShell_bracket_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_punctured_upper_bound_below_below_half_anchor_witnesses
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {u0 a : unitIcc}
    (hu0 : 0 < u0.1)
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g u0)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g u0)
    (hpre :
      ∀ {x : unitIcc}, 0 < x.1 → x.1 < a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g x →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
            sqCenteredNorthZonalQuotientRaw g y <
              sqCenteredNorthZonalQuotientRaw g x) :
    ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g u0 ∧
      sqCenteredNorthZonalQuotientRaw g u0 ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v) := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have hnegEq :
      sqCenteredNorthZonalQuotientRaw (-g) a =
        sqCenteredNorthZonalQuotientRaw (-g) u0 := by
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg haEq
  have hnegGt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw (-g) u0 <
          sqCenteredNorthZonalQuotientRaw (-g) (sqScaleMap a u) := by
    intro u hu hu1
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (hlt hu hu1)
  have hnegPre :
      ∀ {x : unitIcc}, 0 < x.1 → x.1 < a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw (-g) x <
          sqCenteredNorthZonalQuotientRaw (-g) u0 →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
            sqCenteredNorthZonalQuotientRaw (-g) x <
              sqCenteredNorthZonalQuotientRaw (-g) y := by
    intro x hxPos hxLt hxLtNeg
    have hxGt :
        sqCenteredNorthZonalQuotientRaw g u0 <
          sqCenteredNorthZonalQuotientRaw g x := by
      simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg hxLtNeg
    rcases hpre hxPos hxLt hxGt with ⟨δ, hδ, hδprop⟩
    refine ⟨δ, hδ, ?_⟩
    intro y hyPos hyLt
    have hyLtOrig :
        sqCenteredNorthZonalQuotientRaw g y <
          sqCenteredNorthZonalQuotientRaw g x := hδprop hyPos hyLt
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg hyLtOrig
  rcases
      next_halfShell_bracket_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_punctured_lower_bound_above_below_half_anchor_witnesses
        hnegFrame hnegZonal hu0 ha hnegEq hnegGt hnegPre with
    ⟨u, v, hu, hv, huLe, hvLe⟩
  refine ⟨v, u, hv, hu, ?_, ?_⟩
  · simpa [sqCenteredNorthZonalQuotientRaw_neg] using hvLe
  · simpa [sqCenteredNorthZonalQuotientRaw_neg] using huLe

theorem next_halfShell_bracket_or_eq_value_at_one_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
    (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g v) := by
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  let b : unitIcc := sqScaleMap a halfUnitIcc
  by_cases hbr :
      ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) ≤ c ∧
        c ≤ sqCenteredNorthZonalQuotientRaw g (sqScaleMap b v)
  · exact Or.inl (by simpa [c, b] using hbr)
  · right
    have hsplit :
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          c < sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u)) ∨
        (∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) < c) := by
      by_cases hlow :
          ∃ u : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧
            sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) ≤ c
      · right
        intro u hu
        have hnotge :
            ¬ c ≤ sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) := by
          intro hcu
          rcases hlow with ⟨v, hv, hvle⟩
          exact hbr ⟨v, u, hv, hu, hvle, hcu⟩
        linarith
      · left
        intro u hu
        have hnotle :
            ¬ sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) ≤ c := by
          intro huc
          exact hlow ⟨u, hu, huc⟩
        linarith
    have hnextGt :
        ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 →
          c < sqCenteredNorthZonalQuotientRaw g (sqScaleMap b u) := by
      rcases hsplit with hgt' | hlt'
      · exact hgt'
      · have hhalf : (1 / 2 : ℝ) ≤ (halfUnitIcc : unitIcc).1 := by
          norm_num [halfUnitIcc]
        have hhalfLt : (halfUnitIcc : unitIcc).1 < 1 := by
          norm_num [halfUnitIcc]
        have htop :
            c < sqCenteredNorthZonalQuotientRaw g b := by
          simpa [c, b] using hgt (u := halfUnitIcc) hhalf hhalfLt
        have hone : (1 / 2 : ℝ) ≤ (oneUnitIcc : unitIcc).1 := by
          norm_num [oneUnitIcc]
        have htopLt : sqCenteredNorthZonalQuotientRaw g (sqScaleMap b oneUnitIcc) < c := by
          exact hlt' hone
        have hscaleOne : sqScaleMap b oneUnitIcc = b := by
          apply Subtype.ext
          simp [sqScaleMap, oneUnitIcc]
        have hfalse : False := by
          rw [hscaleOne] at htopLt
          linarith
        intro u hu
        exact False.elim hfalse
    rcases
        exists_eq_value_at_one_below_half_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
          hgframe hgz ha haEq hgt with
      ⟨u, huPos, huLtHalf, huEq, huAbove⟩
    have huLtQuarter : u.1 < a.1 / 4 := by
      by_contra huNotLt
      have huGeQuarter : a.1 / 4 ≤ u.1 := by
        exact le_of_not_gt huNotLt
      have hbEq : b.1 = a.1 / 2 := by
        dsimp [b]
        rw [sqScaleMap_apply]
        change a.1 * (1 / 2 : ℝ) = a.1 / 2
        ring
      have hbPos : 0 < b.1 := by
        rw [hbEq]
        positivity
      let w : unitIcc := ⟨u.1 / b.1, by
        constructor
        · positivity
        · have huLeB : u.1 ≤ b.1 := by
            rw [hbEq]
            exact huLtHalf.le
          have huLeB' : u.1 ≤ 1 * b.1 := by
            simpa [one_mul] using huLeB
          exact (div_le_iff₀ hbPos).2 huLeB'⟩
      have hwHalf : (1 / 2 : ℝ) ≤ w.1 := by
        change (1 / 2 : ℝ) ≤ u.1 / b.1
        have hnum : (1 / 2 : ℝ) * b.1 ≤ u.1 := by
          rw [hbEq]
          nlinarith
        exact (le_div_iff₀ hbPos).2 hnum
      have hscale : sqScaleMap b w = u := by
        apply Subtype.ext
        change b.1 * w.1 = u.1
        simp [w]
        field_simp [show (b.1 : ℝ) ≠ 0 by exact ne_of_gt hbPos]
      have hcontr :
          c < sqCenteredNorthZonalQuotientRaw g u := by
        simpa [c, hscale] using hnextGt (u := w) hwHalf
      rw [huEq] at hcontr
      linarith
    exact ⟨u, huPos, huLtQuarter, huEq, huAbove⟩

theorem next_halfShell_bracket_or_eq_value_at_one_below_quarter_of_eq_value_at_scale_of_forall_gt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u)) :
    (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
    (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc) := by
  rcases
      next_halfShell_bracket_or_eq_value_at_one_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz ha haEq hgt with
    hbr | hroot
  · exact Or.inl hbr
  · rcases hroot with ⟨u, huPos, huLt, huEq, _⟩
    exact Or.inr ⟨u, huPos, huLt, huEq⟩

theorem next_halfShell_bracket_or_eq_value_at_one_below_quarter_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc) :
    (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
    (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g v <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc) := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have hnegEq :
      sqCenteredNorthZonalQuotientRaw (-g) a =
        sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc := by
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg haEq
  have hnegGt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw (-g) (sqScaleMap a u) := by
    intro u hu hu1
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (hlt hu hu1)
  rcases
      next_halfShell_bracket_or_eq_value_at_one_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hnegFrame hnegZonal ha hnegEq hnegGt with
    hbr | hroot
  · rcases hbr with ⟨u, v, hu, hv, huLe, hvLe⟩
    refine Or.inl ⟨v, u, hv, hu, ?_, ?_⟩
    · simpa [sqCenteredNorthZonalQuotientRaw_neg] using hvLe
    · simpa [sqCenteredNorthZonalQuotientRaw_neg] using huLe
  · rcases hroot with ⟨u, huPos, huLt, huEq, huAbove⟩
    refine Or.inr ⟨u, huPos, huLt, ?_, ?_⟩
    · simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg huEq
    · intro v huv hva
      simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (huAbove huv hva)

theorem next_halfShell_bracket_or_eq_value_at_one_below_quarter_of_eq_value_at_scale_of_forall_lt_on_halfShell
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc) :
    (∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v)) ∨
    (∃ u : unitIcc, 0 < u.1 ∧ u.1 < a.1 / 4 ∧
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc) := by
  rcases
      next_halfShell_bracket_or_eq_value_at_one_below_quarter_with_forall_lt_above_of_eq_value_at_scale_of_forall_lt_on_halfShell
        hgframe hgz ha haEq hlt with
    hbr | hroot
  · exact Or.inl hbr
  · rcases hroot with ⟨u, huPos, huLt, huEq, _⟩
    exact Or.inr ⟨u, huPos, huLt, huEq⟩

theorem False_of_eq_value_at_one_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_exists_lt_witness_and_eventually_gt_above_witness
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a u x : unitIcc}
    (ha : 0 < a.1)
    (huPos : 0 < u.1)
    (huLtQuarter : u.1 < a.1 / 4)
    (huEq :
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (huAbove :
      ∀ {v : unitIcc}, u.1 < v.1 → v.1 ≤ a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g v)
    (hxPos : 0 < x.1)
    (hxLtHalf : x.1 < a.1 / 2)
    (hxLt :
      sqCenteredNorthZonalQuotientRaw g x <
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hpre :
      ∃ δ : ℝ, 0 < δ ∧
        ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
          sqCenteredNorthZonalQuotientRaw g x <
            sqCenteredNorthZonalQuotientRaw g y) :
    False := by
  have hconst :
      ∀ {y : unitIcc}, 0 < y.1 →
        sqCenteredNorthZonalQuotientRaw g y =
          sqCenteredNorthZonalQuotientRaw g x := by
    exact
      sqCenteredNorthZonalQuotientRaw_eq_value_at_anchor_of_eventually_gt_near_zero
        (g := g) hgframe hgz hxPos rfl hpre
  have hux :
      sqCenteredNorthZonalQuotientRaw g u =
        sqCenteredNorthZonalQuotientRaw g x := hconst huPos
  rw [huEq] at hux
  linarith [hxLt, hux]

theorem next_halfShell_bracket_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_punctured_lower_bound_above_below_half_witnesses
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u))
    (hpre :
      ∀ {x : unitIcc}, 0 < x.1 → x.1 < a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g x <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
            sqCenteredNorthZonalQuotientRaw g x <
              sqCenteredNorthZonalQuotientRaw g y) :
    ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v) := by
  rcases
      next_halfShell_bracket_or_eq_value_at_one_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_forall_gt_on_halfShell
        hgframe hgz ha haEq hgt with
    hbr | hroot
  · exact hbr
  · rcases hroot with ⟨u, huPos, huLtQuarter, huEq, huAbove⟩
    rcases
        exists_lt_value_at_one_below_half_of_eq_value_at_scale_of_forall_gt_on_halfShell
          hgframe hgz ha haEq hgt with
      ⟨x, hxPos, hxLtHalf, hxLt⟩
    exact False.elim <|
      False_of_eq_value_at_one_below_quarter_with_forall_gt_above_of_eq_value_at_scale_of_exists_lt_witness_and_eventually_gt_above_witness
        hgframe hgz ha huPos huLtQuarter huEq huAbove hxPos hxLtHalf hxLt
        (hpre hxPos hxLtHalf hxLt)

theorem next_halfShell_bracket_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_punctured_upper_bound_below_below_half_witnesses
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hpre :
      ∀ {x : unitIcc}, 0 < x.1 → x.1 < a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g x →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
            sqCenteredNorthZonalQuotientRaw g y <
              sqCenteredNorthZonalQuotientRaw g x) :
    ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v) := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have hnegEq :
      sqCenteredNorthZonalQuotientRaw (-g) a =
        sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc := by
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg haEq
  have hnegGt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw (-g) (sqScaleMap a u) := by
    intro u hu hu1
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (hlt hu hu1)
  have hnegPre :
      ∀ {x : unitIcc}, 0 < x.1 → x.1 < a.1 / 2 →
        sqCenteredNorthZonalQuotientRaw (-g) x <
          sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ {y : unitIcc}, 0 < y.1 → y.1 < δ →
            sqCenteredNorthZonalQuotientRaw (-g) x <
              sqCenteredNorthZonalQuotientRaw (-g) y := by
    intro x hxPos hxLtHalf hxLt
    rcases hpre hxPos hxLtHalf (by simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg hxLt) with
      ⟨δ, hδ, hδprop⟩
    refine ⟨δ, hδ, ?_⟩
    intro y hyPos hyLt
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (hδprop hyPos hyLt)
  rcases
      next_halfShell_bracket_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_punctured_lower_bound_above_below_half_witnesses
        hnegFrame hnegZonal ha hnegEq hnegGt hnegPre with
    ⟨u, v, hu, hv, huLe, hvLe⟩
  refine ⟨v, u, hv, hu, ?_, ?_⟩
  · simpa [sqCenteredNorthZonalQuotientRaw_neg] using hvLe
  · simpa [sqCenteredNorthZonalQuotientRaw_neg] using huLe

theorem next_halfShell_bracket_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_tendsto_value_at_one
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hgt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u))
    (hlim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc)
        (𝓝 (sqCenteredNorthZonalQuotientRaw g oneUnitIcc))) :
    ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v) := by
  apply
    next_halfShell_bracket_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_punctured_lower_bound_above_below_half_witnesses
      hgframe hgz ha haEq hgt
  intro x hxPos hxLtHalf hxLt
  let c : ℝ := sqCenteredNorthZonalQuotientRaw g oneUnitIcc
  let η : ℝ := (c - sqCenteredNorthZonalQuotientRaw g x) / 2
  have hη : 0 < η := by
    dsimp [η, c]
    linarith
  rcases (Metric.tendsto_nhdsWithin_nhds.mp hlim) η hη with ⟨δ, hδ, hnear⟩
  refine ⟨δ, hδ, ?_⟩
  intro y hyPos hyLt
  have hydist : dist y zeroUnitIcc < δ := by
    change |(y : ℝ) - 0| < δ
    simpa [abs_of_nonneg hyPos.le] using hyLt
  have hynear : |sqCenteredNorthZonalQuotientRaw g y - c| < η := by
    simpa [Real.dist_eq, c] using hnear hyPos hydist
  have hygt : c - η < sqCenteredNorthZonalQuotientRaw g y := by
    have hleft := (abs_lt.mp hynear).1
    linarith
  dsimp [η, c] at hygt ⊢
  linarith

theorem next_halfShell_bracket_of_eq_value_at_scale_of_forall_lt_on_halfShell_of_tendsto_value_at_one
    {g : C(spherePoint3, ℝ)}
    (hgframe : g ∈ continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {a : unitIcc}
    (ha : 0 < a.1)
    (haEq :
      sqCenteredNorthZonalQuotientRaw g a =
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hlt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap a u) <
          sqCenteredNorthZonalQuotientRaw g oneUnitIcc)
    (hlim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw g u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc)
        (𝓝 (sqCenteredNorthZonalQuotientRaw g oneUnitIcc))) :
    ∃ u v : unitIcc, (1 / 2 : ℝ) ≤ u.1 ∧ (1 / 2 : ℝ) ≤ v.1 ∧
      sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) u) ≤
        sqCenteredNorthZonalQuotientRaw g oneUnitIcc ∧
      sqCenteredNorthZonalQuotientRaw g oneUnitIcc ≤
        sqCenteredNorthZonalQuotientRaw g (sqScaleMap (sqScaleMap a halfUnitIcc) v) := by
  have hnegFrame : (-g) ∈ continuousSphereFrameSubmodule := by
    simpa using continuousSphereFrameSubmodule.neg_mem hgframe
  have hnegZonal : IsNorthZonal (-g) := by
    intro t
    simpa using congrArg Neg.neg (hgz t)
  have hnegEq :
      sqCenteredNorthZonalQuotientRaw (-g) a =
        sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc := by
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using congrArg Neg.neg haEq
  have hnegGt :
      ∀ {u : unitIcc}, (1 / 2 : ℝ) ≤ u.1 → u.1 < 1 →
        sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc <
          sqCenteredNorthZonalQuotientRaw (-g) (sqScaleMap a u) := by
    intro u hu hu1
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using neg_lt_neg (hlt hu hu1)
  have hnegLim :
      Filter.Tendsto (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw (-g) u)
        (𝓝[{u : unitIcc | 0 < u.1}] zeroUnitIcc)
        (𝓝 (sqCenteredNorthZonalQuotientRaw (-g) oneUnitIcc)) := by
    have hcomp :
        (fun u : unitIcc => sqCenteredNorthZonalQuotientRaw (-g) u) =
          fun u : unitIcc => - sqCenteredNorthZonalQuotientRaw g u := by
      funext u
      simp [sqCenteredNorthZonalQuotientRaw_neg]
    rw [hcomp]
    simpa [sqCenteredNorthZonalQuotientRaw_neg] using hlim.neg
  rcases
      next_halfShell_bracket_of_eq_value_at_scale_of_forall_gt_on_halfShell_of_tendsto_value_at_one
        hnegFrame hnegZonal ha hnegEq hnegGt hnegLim with
    ⟨u, v, hu, hv, huLe, hvLe⟩
  refine ⟨v, u, hv, hu, ?_, ?_⟩
  · simpa [sqCenteredNorthZonalQuotientRaw_neg] using hvLe
  · simpa [sqCenteredNorthZonalQuotientRaw_neg] using huLe


theorem exists_sqquotient_poly_uniform_near_on_Icc_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {δ ε : ℝ}
    (hδ : 0 < δ)
    (_hδ1 : δ ≤ 1)
    (hε : 0 < ε) :
    ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
      h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
      IsNorthZonal h ∧
      (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
      ∀ u : Set.Icc (0 : ℝ) 1, δ ≤ u.1 →
        |q.eval u.1 - sqCenteredNorthZonalProfile g u / u.1| < ε := by
  let η : ℝ := δ * ε
  have hη : 0 < η := by positivity
  rcases
      exists_sqquotient_poly_almost_fixed_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
        hg hgz hη with
    ⟨h, q, hhHigh, hhz, hq, hdist, hdefect⟩
  refine ⟨h, q, hhHigh, hhz, hq, ?_⟩
  intro u hu
  have hu0 : u.1 ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le hδ hu)
  have hdist' :
      ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < η := hdist
  have hpoint :
      |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| < η := by
    have hle :
        |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u|
          ≤ ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ := by
      have hpt :=
        (sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g).norm_coe_le_norm u
      simpa [sqCenteredNorthZonalContinuousMap, ContinuousMap.sub_apply, Real.norm_eq_abs]
        using hpt
    exact lt_of_le_of_lt hle hdist'
  have hquot0 :
      q.eval u.1 - sqCenteredNorthZonalProfile g u / u.1 =
        (sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u) / u.1 := by
    have hhu : sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1 := hq u
    rw [hhu]
    field_simp [hu0]
  have hquot :
      |q.eval u.1 - sqCenteredNorthZonalProfile g u / u.1|
        = |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| / u.1 := by
    rw [hquot0, abs_div, abs_of_nonneg u.2.1]
  rw [hquot]
  have huδ : 0 < u.1 := lt_of_lt_of_le hδ hu
  have hmul : |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| / u.1 < ε := by
    have hnum : |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| < u.1 * ε := by
      calc
        |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| < η := hpoint
        _ = δ * ε := by rfl
        _ ≤ u.1 * ε := by
              gcongr
    let a : ℝ := |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u|
    have hnum' : a < ε * u.1 := by
      simpa [a, mul_comm] using hnum
    have hdiv' : a / u.1 < ε := (div_lt_iff₀ huδ).2 hnum'
    simpa [a]
  exact hmul

theorem exists_sqquotient_poly_uniform_near_and_almost_fixed_on_Icc_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {δ ε : ℝ}
    (hδ : 0 < δ)
    (_hδ1 : δ ≤ 1)
    (hε : 0 < ε) :
    ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
      h ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule ∧
      IsNorthZonal h ∧
      (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
      (∀ u : Set.Icc (0 : ℝ) 1, δ ≤ u.1 →
        |q.eval u.1 - sqCenteredNorthZonalProfile g u / u.1| < ε) ∧
      (∀ u : Set.Icc (0 : ℝ) 1, δ ≤ u.1 →
        |northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc) u - q.eval u.1| < ε) := by
  let η : ℝ := δ * ε / 3
  have hη : 0 < η := by positivity
  rcases
      exists_sqquotient_poly_almost_fixed_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
        hg hgz hη with
    ⟨h, q, hhHigh, hhz, hq, hdist, hdefect⟩
  refine ⟨h, q, hhHigh, hhz, hq, ?_, ?_⟩
  · intro u hu
    have hu0 : u.1 ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le hδ hu)
    have hdist' :
        ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ < η := hdist
    have hpoint :
        |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| < η := by
      have hle :
          |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u|
            ≤ ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ := by
        have hpt :=
          (sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g).norm_coe_le_norm u
        simpa [sqCenteredNorthZonalContinuousMap, ContinuousMap.sub_apply, Real.norm_eq_abs]
          using hpt
      exact lt_of_le_of_lt hle hdist'
    have hquot0 :
        q.eval u.1 - sqCenteredNorthZonalProfile g u / u.1 =
          (sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u) / u.1 := by
      have hhu : sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1 := hq u
      rw [hhu]
      field_simp [hu0]
    have hquot :
        |q.eval u.1 - sqCenteredNorthZonalProfile g u / u.1|
          = |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| / u.1 := by
      rw [hquot0, abs_div, abs_of_nonneg u.2.1]
    rw [hquot]
    have huδ : 0 < u.1 := lt_of_lt_of_le hδ hu
    have hnum : |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| < u.1 * ε := by
      calc
        |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| < η := hpoint
        _ = δ * ε / 3 := by rfl
        _ ≤ δ * ε := by nlinarith
        _ ≤ u.1 * ε := by gcongr
    have hdiv : |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| / u.1 < ε := by
      let a : ℝ := |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u|
      have hnum' : a < ε * u.1 := by
        simpa [a, mul_comm] using hnum
      have hdiv' : a / u.1 < ε := (div_lt_iff₀ huδ).2 hnum'
      simpa [a]
    exact hdiv
  · intro u hu
    have huδ : 0 < u.1 := lt_of_lt_of_le hδ hu
    have hpoly :
        sqCenteredNorthZonalContinuousMap h = sqProfilePolynomialMap (X * q) := by
      ext v
      change sqCenteredNorthZonalProfile h v = (X * q).eval v.1
      rw [hq v]
      simp
    have hdefect' :
        dist (northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)))
            (sqProfilePolynomialMap (X * q)) < δ * ε := by
      calc
        dist (northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)))
            (sqProfilePolynomialMap (X * q))
          = ‖northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h) -
                sqCenteredNorthZonalContinuousMap h‖ := by
              rw [hpoly]
              simp [dist_eq_norm]
        _ < 3 * η := by simpa [dist_eq_norm] using hdefect
        _ = δ * ε := by
              field_simp
              ring
    let d : C(unitIcc, ℝ) :=
      northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc) - q.toContinuousMapOn unitIcc
    have hsqMul :
        sqMulContinuousMap d =
          northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)) -
            sqProfilePolynomialMap (X * q) := by
      ext v
      rw [sqMulContinuousMap_apply, ContinuousMap.sub_apply, northZonalSqQuotientAverage_apply,
        ContinuousMap.sub_apply, northZonalSqProfileAverage_apply]
      simp [d, sqProfilePolynomialMap, sqMulContinuousMap_apply]
      have hconst :
          ∫ θ in 0..2 * Real.pi, v.1 * (Real.cos θ ^ 2 * q.eval (v.1 * Real.cos θ ^ 2)) =
            v.1 * ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * q.eval (v.1 * Real.cos θ ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      have hconst' :
          ∫ θ in 0..2 * Real.pi, v.1 * Real.cos θ ^ 2 * q.eval (v.1 * Real.cos θ ^ 2) =
            v.1 * ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * q.eval (v.1 * Real.cos θ ^ 2) := by
        simpa [mul_assoc] using hconst
      rw [hconst']
      ring
    have hpoint :
        |u.1 * d u| < δ * ε := by
      have hle :
          |u.1 * d u| ≤
            dist (northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)))
              (sqProfilePolynomialMap (X * q)) := by
        calc
          |u.1 * d u| = |(sqMulContinuousMap d) u| := by
            simp [sqMulContinuousMap_apply]
          _ ≤ ‖sqMulContinuousMap d‖ := by
            simpa [Real.norm_eq_abs] using (sqMulContinuousMap d).norm_coe_le_norm u
          _ = dist (northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)))
                (sqProfilePolynomialMap (X * q)) := by
              simpa [dist_eq_norm, hsqMul]
      exact lt_of_le_of_lt hle hdefect'
    have hnum' : |u.1 * d u| < u.1 * ε := by
      calc
        |u.1 * d u| < δ * ε := hpoint
        _ ≤ u.1 * ε := by gcongr
    have hdiv : |d u| < ε := by
      have htmp : u.1 * |d u| < u.1 * ε := by
        simpa [abs_of_nonneg u.2.1, abs_mul] using hnum'
      nlinarith
    simpa [d, ContinuousMap.sub_apply, Real.dist_eq] using hdiv

theorem exists_sqquotient_poly_uniform_near_and_almost_fixed_with_stage_on_Icc_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
    {g : C(spherePoint3, ℝ)}
    (hg :
      g ∈ highEvenUnionHarmonicPolyHomogeneousImageSubmodule.topologicalClosure ⊓
            continuousSphereFrameSubmodule)
    (hgz : IsNorthZonal g)
    {δ ε : ℝ}
    (hδ : 0 < δ)
    (_hδ1 : δ ≤ 1)
    (hε : 0 < ε) :
    ∃ N : ℕ, ∃ h : C(spherePoint3, ℝ), ∃ q : ℝ[X],
      h ∈ highEvenBoundedHarmonicPolyHomogeneousImageSubmodule N ∧
      IsNorthZonal h ∧
      (∀ u : Set.Icc (0 : ℝ) 1, sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1) ∧
      q ∈ Polynomial.degreeLT ℝ N ∧
      dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
          (q.toContinuousMapOn unitIcc) ≤
        degreeLTSqMulNormConst N * (δ * ε) ∧
      (∀ u : Set.Icc (0 : ℝ) 1, δ ≤ u.1 →
        |q.eval u.1 - sqCenteredNorthZonalProfile g u / u.1| < ε) ∧
      (∀ u : Set.Icc (0 : ℝ) 1, δ ≤ u.1 →
        |northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc) u - q.eval u.1| < ε) := by
  let η : ℝ := δ * ε / 3
  have hη : 0 < η := by positivity
  rcases
      exists_sqquotient_poly_almost_fixed_of_mem_topologicalClosure_highEvenUnion_inf_frame_of_isNorthZonal
        hg hgz hη with
    ⟨h, q0, hhHigh, hhz, hq0, hdist, hdefect⟩
  have hmono : Directed (· ≤ ·) highEvenBoundedHarmonicPolyHomogeneousImageSubmodule := by
    intro N M
    exact ⟨max N M,
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_left _ _),
      highEvenBoundedHarmonicPolyHomogeneousImageSubmodule_mono (Nat.le_max_right _ _)⟩
  rw [highEvenUnionHarmonicPolyHomogeneousImageSubmodule] at hhHigh
  rcases
      (Submodule.mem_iSup_of_directed highEvenBoundedHarmonicPolyHomogeneousImageSubmodule hmono).mp hhHigh with
    ⟨N, hhN⟩
  rcases exists_sqquotient_poly_degree_of_mem_highEvenBounded_of_isNorthZonal hhN hhz with
    ⟨q, hqdeg, hq⟩
  have hqq0 : q = q0 := by
    apply sqquotient_factor_polynomial_unique_on_unitIcc
    intro u
    rw [← hq u, ← hq0 u]
  subst q0
  refine ⟨N, h, q, hhN, hhz, hq, hqdeg, ?_, ?_, ?_⟩
  · have hpoly :
        sqCenteredNorthZonalContinuousMap h = sqProfilePolynomialMap (X * q) := by
      ext u
      change sqCenteredNorthZonalProfile h u = (X * q).eval u.1
      rw [hq u]
      simp
    have hdefect' :
        sqProfilePolynomialDefect (X * q) < δ * ε := by
      calc
        sqProfilePolynomialDefect (X * q)
          = ‖northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)) -
                sqProfilePolynomialMap (X * q)‖ := by
              simp [sqProfilePolynomialDefect, dist_eq_norm]
        _ = ‖northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h) -
                sqCenteredNorthZonalContinuousMap h‖ := by
              rw [hpoly]
        _ < 3 * η := by simpa using hdefect
        _ = δ * ε := by
              field_simp
              ring
    calc
      dist (northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc))
          (q.toContinuousMapOn unitIcc)
        ≤ degreeLTSqMulNormConst N * sqProfilePolynomialDefect (X * q) :=
            norm_quotientDefect_le_degreeLTSqMulNormConst_mul_sqprofileDefect hqdeg
      _ ≤ degreeLTSqMulNormConst N * (δ * ε) := by
            have hconst_nonneg : 0 ≤ degreeLTSqMulNormConst N := by
              unfold degreeLTSqMulNormConst
              positivity
            exact mul_le_mul_of_nonneg_left (le_of_lt hdefect') hconst_nonneg
  · intro u hu
    have hu0 : u.1 ≠ 0 := by
      exact ne_of_gt (lt_of_lt_of_le hδ hu)
    have hpoint :
        |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| < η := by
      have hle :
          |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u|
            ≤ ‖sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g‖ := by
        have hpt :=
          (sqCenteredNorthZonalContinuousMap h - sqCenteredNorthZonalContinuousMap g).norm_coe_le_norm u
        simpa [sqCenteredNorthZonalContinuousMap, ContinuousMap.sub_apply, Real.norm_eq_abs]
          using hpt
      exact lt_of_le_of_lt hle hdist
    have hquot0 :
        q.eval u.1 - sqCenteredNorthZonalProfile g u / u.1 =
          (sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u) / u.1 := by
      have hhu : sqCenteredNorthZonalProfile h u = u.1 * q.eval u.1 := hq u
      rw [hhu]
      field_simp [hu0]
    have hquot :
        |q.eval u.1 - sqCenteredNorthZonalProfile g u / u.1|
          = |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| / u.1 := by
      rw [hquot0, abs_div, abs_of_nonneg u.2.1]
    rw [hquot]
    have huδ : 0 < u.1 := lt_of_lt_of_le hδ hu
    have hnum : |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| < u.1 * ε := by
      calc
        |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u| < η := hpoint
        _ = δ * ε / 3 := by rfl
        _ ≤ δ * ε := by nlinarith
        _ ≤ u.1 * ε := by gcongr
    let a : ℝ := |sqCenteredNorthZonalProfile h u - sqCenteredNorthZonalProfile g u|
    have hnum' : a < ε * u.1 := by
      simpa [a, mul_comm] using hnum
    have hdiv' : a / u.1 < ε := (div_lt_iff₀ huδ).2 hnum'
    simpa [a]
  · intro u hu
    have huδ : 0 < u.1 := lt_of_lt_of_le hδ hu
    have hpoly :
        sqCenteredNorthZonalContinuousMap h = sqProfilePolynomialMap (X * q) := by
      ext v
      change sqCenteredNorthZonalProfile h v = (X * q).eval v.1
      rw [hq v]
      simp
    have hdefect' :
        dist (northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)))
            (sqProfilePolynomialMap (X * q)) < δ * ε := by
      calc
        dist (northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)))
            (sqProfilePolynomialMap (X * q))
          = ‖northZonalSqProfileAverage (sqCenteredNorthZonalContinuousMap h) -
                sqCenteredNorthZonalContinuousMap h‖ := by
              rw [hpoly]
              simp [dist_eq_norm]
        _ < 3 * η := by simpa [dist_eq_norm] using hdefect
        _ = δ * ε := by
              field_simp
              ring
    let d : C(unitIcc, ℝ) :=
      northZonalSqQuotientAverage (q.toContinuousMapOn unitIcc) - q.toContinuousMapOn unitIcc
    have hsqMul :
        sqMulContinuousMap d =
          northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)) -
            sqProfilePolynomialMap (X * q) := by
      ext v
      rw [sqMulContinuousMap_apply, ContinuousMap.sub_apply, northZonalSqQuotientAverage_apply,
        ContinuousMap.sub_apply, northZonalSqProfileAverage_apply]
      simp [d, sqProfilePolynomialMap, sqMulContinuousMap_apply]
      have hconst :
          ∫ θ in 0..2 * Real.pi, v.1 * (Real.cos θ ^ 2 * q.eval (v.1 * Real.cos θ ^ 2)) =
            v.1 * ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * q.eval (v.1 * Real.cos θ ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      have hconst' :
          ∫ θ in 0..2 * Real.pi, v.1 * Real.cos θ ^ 2 * q.eval (v.1 * Real.cos θ ^ 2) =
            v.1 * ∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * q.eval (v.1 * Real.cos θ ^ 2) := by
        simpa [mul_assoc] using hconst
      rw [hconst']
      ring
    have hpoint :
        |u.1 * d u| < δ * ε := by
      have hle :
          |u.1 * d u| ≤
            dist (northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)))
              (sqProfilePolynomialMap (X * q)) := by
        calc
          |u.1 * d u| = |(sqMulContinuousMap d) u| := by
            simp [sqMulContinuousMap_apply]
          _ ≤ ‖sqMulContinuousMap d‖ := by
            simpa [Real.norm_eq_abs] using (sqMulContinuousMap d).norm_coe_le_norm u
          _ = dist (northZonalSqProfileAverage (sqProfilePolynomialMap (X * q)))
                (sqProfilePolynomialMap (X * q)) := by
              simpa [dist_eq_norm, hsqMul]
      exact lt_of_le_of_lt hle hdefect'
    have hnum' : |u.1 * d u| < u.1 * ε := by
      calc
        |u.1 * d u| < δ * ε := hpoint
        _ ≤ u.1 * ε := by gcongr
    have hdiv : |d u| < ε := by
      have htmp : u.1 * |d u| < u.1 * ε := by
        simpa [abs_of_nonneg u.2.1, abs_mul] using hnum'
      nlinarith
    simpa [d, ContinuousMap.sub_apply, Real.dist_eq] using hdiv
