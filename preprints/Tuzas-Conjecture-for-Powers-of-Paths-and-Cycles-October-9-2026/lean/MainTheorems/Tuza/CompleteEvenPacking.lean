import MainTheorems.Tuza.SkolemDecomposition
import MainTheorems.Tuza.RestrictedPacking

namespace ResearchMain.Tuza

theorem complete_packing_deleted (n : ℕ)
    (D : TriangleDecomposition (⊤ : SimpleGraph (Fin (n + 1)))) :
    ∃ P : Finset (Finset (Fin n)), Packing (⊤ : SimpleGraph (Fin n)) P ∧
      3 * P.card + 3 * (n / 2) = (n + 1).choose 2 := by
  classical
  obtain ⟨Q, hQ, hcard⟩ := exists_vertex_deleted_packing D (Fin.last n)
  let e : {x : Fin (n + 1) // x ≠ Fin.last n} ≃ Fin n := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl]
    simp)
  let f : (⊤ : SimpleGraph {x : Fin (n + 1) // x ≠ Fin.last n}) ≃g
      (⊤ : SimpleGraph (Fin n)) := {
    toEquiv := e
    map_rel_iff' := by intro x y; simp }
  refine ⟨Q.map ⟨Finset.map e.toEmbedding, Finset.map_injective _⟩, hQ.map f.toEmbedding, ?_⟩
  simpa using hcard

theorem complete_packing_even {n : ℕ} (hn : Even n)
    (D : TriangleDecomposition (⊤ : SimpleGraph (Fin (n + 1)))) :
    ∃ P : Finset (Finset (Fin n)), Packing (⊤ : SimpleGraph (Fin n)) P ∧
      3 * P.card + n / 2 = n.choose 2 := by
  obtain ⟨P, hP, hcard⟩ := complete_packing_deleted n D
  have hm := Nat.even_iff.mp hn
  have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    exact Nat.add_comm _ _
  rw [hchoose] at hcard
  exact ⟨P, hP, by omega⟩

theorem complete_packing_zero_residue (m : ℕ) :
    ∃ P : Finset (Finset (Fin (6 * m))), Packing (⊤ : SimpleGraph (Fin (6 * m))) P ∧
      3 * P.card + (6 * m) / 2 = (6 * m).choose 2 := by
  obtain ⟨D⟩ := exists_complete_decomposition_one m
  exact complete_packing_even (by rw [Nat.even_iff]; omega) D

theorem complete_packing_two_residue (m : ℕ) :
    ∃ P : Finset (Finset (Fin (6 * m + 2))), Packing (⊤ : SimpleGraph (Fin (6 * m + 2))) P ∧
      3 * P.card + (6 * m + 2) / 2 = (6 * m + 2).choose 2 := by
  obtain ⟨D⟩ := exists_complete_decomposition_three m
  exact complete_packing_even (by rw [Nat.even_iff]; omega) D

end ResearchMain.Tuza
