import Mathlib

noncomputable section

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

theorem exists_ortho_vector_of_dim_ge_3
    (hdim : 3 ≤ Module.finrank ℂ H) (u v : H) :
    ∃ w : H, w ≠ 0 ∧ inner (𝕜 := ℂ) w u = 0 ∧ inner (𝕜 := ℂ) w v = 0 := by
  classical
  let s : Finset H := {u, v}
  let S : Submodule ℂ H := Submodule.span ℂ (s : Set H)

  have hS : Module.finrank ℂ ↥S ≤ 2 := by
    have h1 : Module.finrank ℂ ↥S ≤ s.card := by
      -- `finrank_span_finset_le_card` is the finset version (global theorem)
      simpa [Set.finrank, S] using (finrank_span_finset_le_card (R := ℂ) s)
    have h2 : s.card ≤ 2 := by
      -- card (insert u {v}) ≤ card {v} + 1 = 2
      simpa [s] using (Finset.card_insert_le (a := u) (s := ({v} : Finset H)))
    exact le_trans h1 h2

  have hsum :
      Module.finrank ℂ ↥S + Module.finrank ℂ ↥(Sᗮ) = Module.finrank ℂ H := by
    simpa using (Submodule.finrank_add_finrank_orthogonal (K := S))

  have hpos : 0 < Module.finrank ℂ ↥(Sᗮ) := by
    have h3 : 3 ≤ Module.finrank ℂ ↥S + Module.finrank ℂ ↥(Sᗮ) := by
      simpa [hsum] using hdim
    have h1 : 1 ≤ Module.finrank ℂ ↥(Sᗮ) := by
      omega
    exact Nat.succ_le_iff.mp h1

  rcases (Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := ↥(Sᗮ))).1 hpos with ⟨w, hw0⟩
  have hwS : ∀ z ∈ S, inner (𝕜 := ℂ) z (w : H) = 0 :=
    (Submodule.mem_orthogonal (K := S) (v := (w : H))).1 w.property

  have huS : u ∈ S := Submodule.subset_span (by simp [s])
  have hvS : v ∈ S := Submodule.subset_span (by simp [s])

  refine ⟨(w : H), ?_, (inner_eq_zero_symm).1 (hwS u huS), (inner_eq_zero_symm).1 (hwS v hvS)⟩
  intro h
  apply hw0
  ext
  simpa using h
