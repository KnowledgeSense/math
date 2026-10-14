import MainTheorems.Tuza.BoseOperation

namespace ResearchMain.Tuza

namespace SteinerOperation

variable {V W : Type*}

def congr (S : SteinerOperation V) (e : V ≃ W) : SteinerOperation W where
  third x y := e (S.third (e.symm x) (e.symm y))
  comm x y := congrArg e (S.comm _ _)
  involutive x y := by
    simp only [Equiv.symm_apply_apply, S.involutive, Equiv.apply_symm_apply]
  idempotent x := by simp only [S.idempotent, Equiv.apply_symm_apply]

end SteinerOperation

theorem exists_steinerOperation_three (m : ℕ) :
    Nonempty (SteinerOperation (Fin (6 * m + 3))) := by
  classical
  have hq : Odd (2 * m + 1) := ⟨m, rfl⟩
  let _ : NeZero (2 * m + 1) := ⟨hq.pos.ne'⟩
  let D := doublingEquiv (zmod_double_injective hq)
  let S := boseOperation D (fun _ => rfl)
  let e : (ZMod (2 * m + 1) × ZMod 3) ≃ Fin (6 * m + 3) :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_prod, ZMod.card, Fintype.card_fin]; ring)
  exact ⟨S.congr e⟩

theorem exists_complete_decomposition_three (m : ℕ) :
    Nonempty (TriangleDecomposition (⊤ : SimpleGraph (Fin (6 * m + 3)))) := by
  obtain ⟨S⟩ := exists_steinerOperation_three m
  exact ⟨S.decomposition⟩

theorem complete_packing_three (m : ℕ) :
    ∃ P : Finset (Finset (Fin (6 * m + 3))), Packing (⊤ : SimpleGraph (Fin (6 * m + 3))) P ∧
      3 * P.card = (6 * m + 3).choose 2 := by
  obtain ⟨S⟩ := exists_steinerOperation_three m
  exact ⟨S.blocks, S.blocks_packing, by simpa using S.blocks_card⟩

end ResearchMain.Tuza
