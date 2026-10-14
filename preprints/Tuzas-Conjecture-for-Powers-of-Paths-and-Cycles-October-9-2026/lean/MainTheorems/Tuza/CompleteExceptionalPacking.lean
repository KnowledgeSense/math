import MainTheorems.Tuza.FiveFactorDecomposition
import MainTheorems.Tuza.FactorAttachment
import MainTheorems.Tuza.CenterPacking
import MainTheorems.Tuza.FanRestriction
import MainTheorems.Tuza.RestrictedPacking

namespace ResearchMain.Tuza

theorem complete_packing_five_residue (m : ℕ) :
    ∃ P : Finset (Finset (Fin (6 * m + 5))), Packing (⊤ : SimpleGraph (Fin (6 * m + 5))) P ∧
      3 * P.card + 4 = (6 * m + 5).choose 2 := by
  classical
  obtain ⟨D⟩ := five_factor_decomposition m
  obtain ⟨B⟩ := attach_factors D
  have hb : 3 * B.triangles.card + 10 = (6 * m + 5).choose 2 := by
    have hc := fanGraph_card (F := Fin 5) (V := Fin (6 * m))
    rw [← B.card] at hc
    have hf : (5 : ℕ).choose 2 = 10 := by decide
    simpa only [Fintype.card_fin, hf, Nat.add_comm] using hc
  obtain ⟨R, hR, hRcard⟩ := add_center_packing B.packing twoCenterTriangles_packing
  rw [twoCenterTriangles_card] at hRcard
  obtain ⟨P, hP, hPcard⟩ := complete_packing_transport hR (6 * m + 5) (by simp; omega)
  exact ⟨P, hP, by omega⟩

theorem complete_packing_four_residue (m : ℕ) :
    ∃ P : Finset (Finset (Fin (6 * m + 4))), Packing (⊤ : SimpleGraph (Fin (6 * m + 4))) P ∧
      3 * P.card + (6 * m + 4) / 2 + 1 = (6 * m + 4).choose 2 := by
  classical
  obtain ⟨D⟩ := five_factor_decomposition m
  obtain ⟨B⟩ := attach_factors D
  have hc := fanGraph_card (F := Fin 5) (V := Fin (6 * m))
  have hf : (5 : ℕ).choose 2 = 10 := by decide
  have hfan : (fanGraph (Fin 5) (Fin (6 * m))).edgeFinset.card + 10 =
      (6 * m + 5).choose 2 := by
    simpa only [Fintype.card_fin, hf, Nat.add_comm] using hc
  obtain ⟨Q, hQ, hQcard⟩ := exists_vertex_removed_packing B (.inl (Fin.last 4))
  rw [fanGraph_degree_left, Fintype.card_fin] at hQcard
  obtain ⟨e⟩ := removed_five_centers (V := Fin (6 * m))
  let U := Q.map ⟨Finset.map e.toEquiv.toEmbedding, Finset.map_injective _⟩
  have hU : Packing (fanGraph (Fin 4) (Fin (6 * m))) U := hQ.map e.toEmbedding
  have hUcard : U.card = Q.card := Finset.card_map _
  obtain ⟨R, hR, hRcard⟩ := add_center_packing hU oneCenterTriangle_packing
  rw [oneCenterTriangle_card, hUcard] at hRcard
  obtain ⟨P, hP, hPcard⟩ := complete_packing_transport hR (6 * m + 4) (by simp; omega)
  have hchoose : (6 * m + 5).choose 2 = (6 * m + 4).choose 2 + (6 * m + 4) := by
    change (6 * m + 4 + 1).choose 2 = _
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    exact Nat.add_comm _ _
  rw [hchoose] at hfan
  exact ⟨P, hP, by omega⟩

end ResearchMain.Tuza
