import MainTheorems.PathCycleTuza.SkolemExistence

namespace ResearchMain.PathCycleTuza

theorem hookFlag_le_one (m : ℕ) : hookFlag m ≤ 1 := by unfold hookFlag; split_ifs <;> omega

theorem hookFlag_positive (m : ℕ) (h : hookFlag m = 1) : 0 < m := by
  unfold hookFlag at h
  split_ifs at h; omega

def skolemPositions (m δ : ℕ) : Finset ℕ :=
  if δ = 1 then (Finset.Icc 1 (2 * m + 1)).erase (2 * m) else Finset.Icc 1 (2 * m)

theorem skolemPositions_card (m : ℕ) : (skolemPositions m (hookFlag m)).card = 2 * m := by
  unfold skolemPositions
  split_ifs with h
  · have hm := hookFlag_positive m h
    rw [Finset.card_erase_of_mem (by simp; omega)]
    simp
  · simp

theorem SkolemData.endpoint_mem {m : ℕ} (D : SkolemData m (hookFlag m)) (p : Fin m × Bool) :
    D.endpoint p ∈ skolemPositions m (hookFlag m) := by
  have hp := D.positive p.1
  have hb := D.bounded p.1 p.2
  unfold skolemPositions
  split_ifs with h
  · have ho := D.omits p.1 p.2 h
    have hb' : D.endpoint p ≤ 2 * m + 1 := by simpa only [endpoint, h] using hb
    simp only [Finset.mem_erase, Finset.mem_Icc]
    exact ⟨ho, by unfold endpoint; omega, hb'⟩
  · have hz : hookFlag m = 0 := by have := hookFlag_le_one m; omega
    have hb' : D.endpoint p ≤ 2 * m := by simpa only [endpoint, hz, Nat.add_zero] using hb
    exact Finset.mem_Icc.mpr ⟨by unfold endpoint; omega, hb'⟩

theorem SkolemData.endpoint_image {m : ℕ} (D : SkolemData m (hookFlag m)) :
    Finset.univ.image D.endpoint = skolemPositions m (hookFlag m) := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact D.endpoint_mem p
  · rw [Finset.card_image_of_injective _ D.endpoint_injective, skolemPositions_card]
    simp [mul_comm]

theorem positiveIndex_image (m : ℕ) :
    Finset.univ.image (fun i : Fin m => i.val + 1) = Finset.Icc 1 m := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨by omega, by omega⟩
  · intro hx
    exact ⟨⟨x - 1, by omega⟩, by simp; omega⟩

end ResearchMain.PathCycleTuza
