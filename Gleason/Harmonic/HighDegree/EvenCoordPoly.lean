import Gleason.Harmonic.HighDegree.EvenDensity
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section

open Complex InnerProductSpace

def sphereCoordVec : Fin 3 → C(spherePoint3, ℝ)
  | 0 => sphereCoordRe
  | 1 => sphereCoordIm
  | 2 => sphereCoordZ

@[simp] lemma sphereCoordVec_zero :
    sphereCoordVec 0 = sphereCoordRe := rfl

@[simp] lemma sphereCoordVec_one :
    sphereCoordVec 1 = sphereCoordIm := rfl

@[simp] lemma sphereCoordVec_two :
    sphereCoordVec 2 = sphereCoordZ := rfl

def sphereCoordMvEval : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] C(spherePoint3, ℝ) :=
  MvPolynomial.aeval sphereCoordVec

theorem sphereCoordinateSubalgebra_eq_range_sphereCoordMvEval :
    sphereCoordinateSubalgebra = sphereCoordMvEval.range := by
  have hrange :
      Set.range sphereCoordVec = ({sphereCoordRe, sphereCoordIm, sphereCoordZ} :
        Set C(spherePoint3, ℝ)) := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [sphereCoordVec]
    · intro hf
      rcases (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hf) with
        rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  simpa [sphereCoordinateSubalgebra, sphereCoordMvEval, hrange] using
    (Algebra.adjoin_range_eq_range_aeval (R := ℝ) (f := sphereCoordVec))

theorem mem_sphereCoordinateSubalgebra_iff_exists_mvPolynomial
    {f : C(spherePoint3, ℝ)} :
    f ∈ sphereCoordinateSubalgebra ↔ ∃ p : MvPolynomial (Fin 3) ℝ, sphereCoordMvEval p = f := by
  rw [sphereCoordinateSubalgebra_eq_range_sphereCoordMvEval, AlgHom.mem_range]

def sphereCoordPolyAntipode :
    MvPolynomial (Fin 3) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.aeval fun i => -MvPolynomial.X i

@[simp] lemma sphereCoordPolyAntipode_X (i : Fin 3) :
    sphereCoordPolyAntipode (MvPolynomial.X i) = -MvPolynomial.X i := by
  simp [sphereCoordPolyAntipode]

@[simp] lemma sphereCoordPolyAntipode_C (r : ℝ) :
    sphereCoordPolyAntipode (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [sphereCoordPolyAntipode]

@[simp] lemma sphereCoordMvEval_X (i : Fin 3) :
    sphereCoordMvEval (MvPolynomial.X i) = sphereCoordVec i := by
  simp [sphereCoordMvEval]

@[simp] lemma sphereCoordMvEval_polyAntipode (p : MvPolynomial (Fin 3) ℝ) :
    sphereCoordMvEval (sphereCoordPolyAntipode p) =
      sphereAntipodeAlgHom (sphereCoordMvEval p) := by
  calc
    sphereCoordMvEval (sphereCoordPolyAntipode p)
        = MvPolynomial.aeval (fun i : Fin 3 => -sphereCoordVec i) p := by
            simpa [sphereCoordMvEval, sphereCoordPolyAntipode] using
              (MvPolynomial.aeval_bind₁ sphereCoordVec (fun i : Fin 3 => -MvPolynomial.X i) p)
    _ = MvPolynomial.aeval (fun i : Fin 3 => sphereAntipodeAlgHom (sphereCoordVec i)) p := by
          congr with i
          fin_cases i <;>
            simp [sphereAntipodeAlgHom_sphereCoordRe, sphereAntipodeAlgHom_sphereCoordIm,
              sphereAntipodeAlgHom_sphereCoordZ]
    _ = sphereAntipodeAlgHom (sphereCoordMvEval p) := by
          symm
          simpa [sphereCoordMvEval] using
            (MvPolynomial.comp_aeval_apply (f := sphereCoordVec) sphereAntipodeAlgHom p)

def sphereCoordPolyEvenSymm :
    MvPolynomial (Fin 3) ℝ →ₗ[ℝ] MvPolynomial (Fin 3) ℝ :=
  ((2 : ℝ)⁻¹) • (LinearMap.id + sphereCoordPolyAntipode.toLinearMap)

@[simp] lemma sphereCoordPolyEvenSymm_apply
    (p : MvPolynomial (Fin 3) ℝ) :
    sphereCoordPolyEvenSymm p =
      ((2 : ℝ)⁻¹) • (p + sphereCoordPolyAntipode p) := by
  simp [sphereCoordPolyEvenSymm]

@[simp] lemma sphereCoordPolyAntipode_evenSymm
    (p : MvPolynomial (Fin 3) ℝ) :
    sphereCoordPolyAntipode (sphereCoordPolyEvenSymm p) = sphereCoordPolyEvenSymm p := by
  rw [sphereCoordPolyEvenSymm_apply, map_smul, map_add]
  have hInvol :
      sphereCoordPolyAntipode (sphereCoordPolyAntipode p) = p := by
    simpa [sphereCoordPolyAntipode] using
      (MvPolynomial.aeval_bind₁ (S := MvPolynomial (Fin 3) ℝ)
        (fun i : Fin 3 => -MvPolynomial.X i)
        (fun i : Fin 3 => -MvPolynomial.X i) p)
  simp [hInvol, add_comm]

@[simp] lemma sphereCoordMvEval_evenSymm
    (p : MvPolynomial (Fin 3) ℝ) :
    sphereCoordMvEval (sphereCoordPolyEvenSymm p) =
      sphereEvenSymm (sphereCoordMvEval p) := by
  rw [sphereCoordPolyEvenSymm_apply, sphereEvenSymm, sphereEvenSymmLinear]
  ext x
  simp [sphereCoordMvEval_polyAntipode, sphereAntipodeAlgHom_apply]

theorem exists_even_mvPolynomial_of_mem_continuousSphereEvenCoordinateSubmodule
    {f : C(spherePoint3, ℝ)}
    (hf : f ∈ continuousSphereEvenCoordinateSubmodule) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      sphereCoordMvEval p = f ∧ sphereCoordPolyAntipode p = p := by
  rcases hf with ⟨hfA, hfE⟩
  rcases (mem_sphereCoordinateSubalgebra_iff_exists_mvPolynomial.mp hfA) with ⟨q, hq⟩
  refine ⟨sphereCoordPolyEvenSymm q, ?_, sphereCoordPolyAntipode_evenSymm q⟩
  rw [sphereCoordMvEval_evenSymm, hq]
  exact sphereEvenSymm_eq_of_mem_continuousSphereEvenSubmodule hfE

def sphereCoordPolyEvenSubmodule : Submodule ℝ (MvPolynomial (Fin 3) ℝ) where
  carrier := {p | sphereCoordPolyAntipode p = p}
  zero_mem' := by
    simp [sphereCoordPolyAntipode]
  add_mem' := by
    intro p q hp hq
    change sphereCoordPolyAntipode p = p at hp
    change sphereCoordPolyAntipode q = q at hq
    simp [map_add, hp, hq]
  smul_mem' := by
    intro c p hp
    change sphereCoordPolyAntipode p = p at hp
    simp [map_smul, hp]

theorem sphereCoordMvEval_mem_continuousSphereEvenCoordinateSubmodule_of_mem_evenSubmodule
    {p : MvPolynomial (Fin 3) ℝ}
    (hp : p ∈ sphereCoordPolyEvenSubmodule) :
    sphereCoordMvEval p ∈ continuousSphereEvenCoordinateSubmodule := by
  rcases hp with hp
  refine ⟨?_, ?_⟩
  · rw [sphereCoordinateSubalgebra_eq_range_sphereCoordMvEval]
    exact ⟨p, rfl⟩
  · intro x
    have hpEq : sphereCoordPolyAntipode p = p := hp
    have hEval :
        sphereCoordMvEval p = sphereAntipodeAlgHom (sphereCoordMvEval p) := by
      calc
        sphereCoordMvEval p = sphereCoordMvEval (sphereCoordPolyAntipode p) := by
          rw [hpEq]
        _ = sphereAntipodeAlgHom (sphereCoordMvEval p) := sphereCoordMvEval_polyAntipode p
    have h := congrArg (fun g : C(spherePoint3, ℝ) => g x) hEval
    simpa [sphereAntipodeAlgHom_apply] using h.symm

theorem continuousSphereEvenCoordinateSubmodule_eq_map_sphereCoordPolyEvenSubmodule :
    continuousSphereEvenCoordinateSubmodule =
      sphereCoordPolyEvenSubmodule.map sphereCoordMvEval.toLinearMap := by
  apply le_antisymm
  · intro f hf
    rcases exists_even_mvPolynomial_of_mem_continuousSphereEvenCoordinateSubmodule hf with
      ⟨p, hpEval, hpEven⟩
    exact ⟨p, hpEven, hpEval⟩
  · rintro f ⟨p, hp, rfl⟩
    exact sphereCoordMvEval_mem_continuousSphereEvenCoordinateSubmodule_of_mem_evenSubmodule hp

theorem continuousSphereFrameSubmodule_le_evenPolynomialImageClosure :
    continuousSphereFrameSubmodule ≤
      (sphereCoordPolyEvenSubmodule.map sphereCoordMvEval.toLinearMap).topologicalClosure := by
  simpa [continuousSphereEvenCoordinateSubmodule_eq_map_sphereCoordPolyEvenSubmodule] using
    continuousSphereFrameSubmodule_le_evenCoordinateClosure
