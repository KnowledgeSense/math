import MainTheorems.Tuza.SparseReduction
import MainTheorems.Tuza.MonochromeGraph
import MainTheorems.Tuza.CompletePacking

namespace ResearchMain.Tuza

theorem balanced_complete_count (n : ℕ) :
    (halfUp n).choose 2 + (n - halfUp n).choose 2 ≤ 2 * completeCount n := by
  by_cases hn : n ≤ 4
  · interval_cases n <;> decide
  · let r := halfUp n
    let s := n - halfUp n
    have hbal := halfUp_balanced n
    have hsum : (r : ℤ) + s = n := by exact_mod_cast halfUp_add n
    have hr := choose_two_integer r
    have hs := choose_two_integer s
    have hc := complete_count_bound n
    have hdelta : ((r : ℤ) - s) ^ 2 ≤ 1 := by
      have hcase : (r : ℤ) - s = 0 ∨ (r : ℤ) - s = 1 := by omega
      rcases hcase with h | h <;> rw [h] <;> norm_num
    have hlarge : 15 ≤ (n : ℤ) * ((n : ℤ) - 2) := by
      have h₁ : 0 ≤ (n : ℤ) - 5 := by omega
      have h₂ : 0 ≤ (n : ℤ) + 3 := by omega
      nlinarith [mul_nonneg h₁ h₂]
    have hid : 2 * ((r : ℤ) ^ 2 + (s : ℤ) ^ 2) = (n : ℤ) ^ 2 + ((r : ℤ) - s) ^ 2 := by
      rw [← hsum]
      ring
    have hbound : (r.choose 2 : ℤ) + (s.choose 2 : ℤ) ≤ 2 * (completeCount n : ℤ) := by
      nlinarith
    exact_mod_cast hbound

theorem complete_cover_bound (n : ℕ) :
    coverNumber (⊤ : SimpleGraph (Fin n)) ≤ (halfUp n).choose 2 + (n - halfUp n).choose 2 := by
  let c : Fin n → Bool := fun i => decide (i.val < halfUp n)
  have he : monochromeGraph (⊤ : SimpleGraph (Fin n)) c = splitClique n (halfUp n) := by
    ext i j
    simp [monochromeGraph, c]
  have hedge : (monochromeGraph (⊤ : SimpleGraph (Fin n)) c).edgeFinset =
      (splitClique n (halfUp n)).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    rw [he]
  have hc := number_le_cover (monochromeGraph_covers (⊤ : SimpleGraph (Fin n)) c)
  rwa [hedge, splitClique_card n _ (halfUp_le n)] at hc

theorem complete_inequality (n : ℕ) : Inequality (⊤ : SimpleGraph (Fin n)) := by
  obtain ⟨P, hP, hcard⟩ := complete_packing n
  have hp := packing_le_number hP
  rw [hcard] at hp
  exact (complete_cover_bound n).trans ((balanced_complete_count n).trans (Nat.mul_le_mul_left 2 hp))

theorem complete_graph_inequality (V : Type*) [Fintype V] [DecidableEq V] :
    Inequality (⊤ : SimpleGraph V) := by
  classical
  let e := (Fintype.equivFin V).symm
  let f : (⊤ : SimpleGraph (Fin (Fintype.card V))) ≃g (⊤ : SimpleGraph V) :=
    { toEquiv := e
      map_rel_iff' := by intro x y; exact not_congr e.injective.eq_iff }
  exact (inequality_iso f).mp (complete_inequality _)

theorem FerrersProfile.empty_inequality {a b : ℕ} (d : FerrersProfile a b) (h : a = 0 ∨ b = 0) :
    Inequality d.graph := by
  have he : d.graph = (⊤ : SimpleGraph (Fin a ⊕ Fin b)) := by
    ext x y
    rcases h with rfl | rfl
    · cases x with
      | inl i => exact Fin.elim0 i
      | inr i =>
        cases y with
        | inl j => exact Fin.elim0 j
        | inr j => simp
    · cases x with
      | inl i =>
        cases y with
        | inl j => simp
        | inr j => exact Fin.elim0 j
      | inr i => exact Fin.elim0 i
  rw [he]
  exact complete_graph_inequality _

end ResearchMain.Tuza
