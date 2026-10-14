import MainTheorems.Tuza.DeletedFactors
import MainTheorems.Tuza.DecompositionTransport

namespace ResearchMain.Tuza

theorem deleted_one_factor (n : ℕ) (S : SteinerOperation (Fin (n + 1))) :
    Nonempty (FactorDecomposition (Fin n) (Fin 1)) := by
  classical
  let R : Set (Fin (n + 1)) := {Fin.last n}
  obtain ⟨D⟩ := S.exists_deleted_factor_decomposition R (S.closed_singleton (Fin.last n))
  let e : {x : Fin (n + 1) // x ∉ R} ≃ Fin n := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl]
    simp [R])
  let f : R ≃ Fin 1 := Fintype.equivOfCardEq (by simp [R])
  exact D.congr e f

theorem deleted_three_factors (n : ℕ) (S : SteinerOperation (Fin (n + 3))) :
    Nonempty (FactorDecomposition (Fin n) (Fin 3)) := by
  classical
  let a : Fin (n + 3) := ⟨0, by omega⟩
  let b : Fin (n + 3) := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    change 0 = 1 at hv
    omega
  let R : Set (Fin (n + 3)) := S.block a b
  have hRcard : Fintype.card R = 3 := (Fintype.card_coe _).trans (S.block_clique hab).2
  obtain ⟨D⟩ := S.exists_deleted_factor_decomposition R (S.closed_block a b)
  let e : {x : Fin (n + 3) // x ∉ R} ≃ Fin n := Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin]
    rw [hRcard]
    omega)
  let f : R ≃ Fin 3 := Fintype.equivOfCardEq (by simpa using hRcard)
  exact D.congr e f

end ResearchMain.Tuza
