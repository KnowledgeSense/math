import MainTheorems.Tuza.BoseDecomposition
import MainTheorems.Tuza.SkolemInvolution
import MainTheorems.Tuza.SkolemQuasigroup

namespace ResearchMain.Tuza

theorem exists_steinerOperation_one (m : ℕ) :
    Nonempty (SteinerOperation (Fin (6 * m + 1))) := by
  classical
  cases m with
  | zero =>
    change Nonempty (SteinerOperation (Fin 1))
    exact ⟨{
      third := fun x _ => x
      comm := fun _ _ => Subsingleton.elim _ _
      involutive := fun _ _ => Subsingleton.elim _ _
      idempotent := fun _ => rfl }⟩
  | succ m =>
    let _ : NeZero (2 * (m + 1)) := ⟨by omega⟩
    let S := skolemOperation (skolemQuasigroup (m + 1))
    let e : SkolemPoint (Fin (m + 1)) ≃ Fin (6 * (m + 1) + 1) :=
      Fintype.equivOfCardEq (by
        simp only [SkolemPoint, Fintype.card_option, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool, ZMod.card]
        ring)
    exact ⟨S.congr e⟩

theorem exists_complete_decomposition_one (m : ℕ) :
    Nonempty (TriangleDecomposition (⊤ : SimpleGraph (Fin (6 * m + 1)))) := by
  obtain ⟨S⟩ := exists_steinerOperation_one m
  exact ⟨S.decomposition⟩

theorem complete_packing_one (m : ℕ) :
    ∃ P : Finset (Finset (Fin (6 * m + 1))), Packing (⊤ : SimpleGraph (Fin (6 * m + 1))) P ∧
      3 * P.card = (6 * m + 1).choose 2 := by
  obtain ⟨S⟩ := exists_steinerOperation_one m
  exact ⟨S.blocks, S.blocks_packing, by simpa using S.blocks_card⟩

end ResearchMain.Tuza
