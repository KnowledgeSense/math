import MainTheorems.PathCycleTuza.Basic
import MainTheorems.PathCycleTuza.SkolemMass
import MainTheorems.Tuza.MonochromeGraph

namespace ResearchMain.PathCycleTuza

open Tuza

def parityColor {n : ℕ} (x : Fin n) : Bool := decide (x.val % 2 = 0)

abbrev ParityIndex (n k : ℕ) := Σ i : Fin (k / 2), Fin (n - 2 * (i.val + 1))

def parityEdge (n k : ℕ) (p : ParityIndex n k) : Sym2 (Fin n) :=
  let hx := p.2.isLt
  s(⟨p.2.val, by omega⟩, ⟨p.2.val + 2 * (p.1.val + 1), by omega⟩)

theorem parityEdge_injective (n k : ℕ) : Function.Injective (parityEdge n k) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  simp only [parityEdge, Sym2.eq_iff, Fin.ext_iff] at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · have hij : i = j := Fin.ext (by omega)
    subst j
    exact congrArg (Sigma.mk i) (Fin.ext (by omega))
  · omega

theorem parity_adj_iff {n k : ℕ} (x y : Fin n) :
    (monochromeGraph (pathPower n k) parityColor).Adj x y ↔
      x.val ≠ y.val ∧ Nat.dist x.val y.val ≤ k ∧ x.val % 2 = y.val % 2 := by
  change (x ≠ y ∧ Nat.dist x.val y.val ≤ k) ∧
      decide (x.val % 2 = 0) = decide (y.val % 2 = 0) ↔ _
  have hne : x ≠ y ↔ x.val ≠ y.val := not_congr Fin.ext_iff
  rw [decide_eq_decide, hne]
  omega

theorem parityEdge_exists {n k : ℕ} (x y : Fin n) (hxy : x.val < y.val)
    (hd : y.val - x.val ≤ k) (hp : x.val % 2 = y.val % 2) :
    ∃ p : ParityIndex n k, parityEdge n k p = s(x, y) := by
  let d := (y.val - x.val) / 2
  have hlen : 2 * d = y.val - x.val := by dsimp only [d]; omega
  have hd0 : 0 < d := by omega
  have hdk : d ≤ k / 2 := by omega
  let i : Fin (k / 2) := ⟨d - 1, by omega⟩
  let q : Fin (n - 2 * (i.val + 1)) := ⟨x.val, by dsimp only [i]; have := y.isLt; omega⟩
  refine ⟨⟨i, q⟩, ?_⟩
  apply congrArg₂ Sym2.mk
  · apply Fin.ext
    rfl
  · apply Fin.ext
    dsimp [parityEdge, i, q]
    omega

theorem path_parity_edges (n k : ℕ) :
    (monochromeGraph (pathPower n k) parityColor).edgeFinset =
      Finset.univ.image (parityEdge n k) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | hf x y =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, parity_adj_iff]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases lt_or_gt_of_ne h.1 with hxy | hyx
      · exact parityEdge_exists x y hxy (by unfold Nat.dist at h; omega) h.2.2
      · obtain ⟨p, hp⟩ := parityEdge_exists (k := k) y x hyx (by unfold Nat.dist at h; omega) h.2.2.symm
        exact ⟨p, hp.trans Sym2.eq_swap⟩
    · rintro ⟨p, hp⟩
      have hrel : (monochromeGraph (pathPower n k) parityColor).Adj
          ⟨p.2.val, by have := p.2.isLt; omega⟩
          ⟨p.2.val + 2 * (p.1.val + 1), by have := p.2.isLt; omega⟩ := by
        rw [parity_adj_iff]
        dsimp
        have hi := p.1.isLt
        unfold Nat.dist
        omega
      have hedge : parityEdge n k p ∈ (monochromeGraph (pathPower n k) parityColor).edgeFinset := by
        apply SimpleGraph.mem_edgeFinset.mpr
        exact hrel
      rw [hp] at hedge
      rwa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, parity_adj_iff] at hedge

theorem path_parity_cover_sum (n k : ℕ) :
    coverNumber (pathPower n k) ≤ ∑ i : Fin (k / 2), (n - 2 * (i.val + 1)) := by
  classical
  have h := number_le_cover (monochromeGraph_covers (pathPower n k) parityColor)
  rw [path_parity_edges, Finset.card_image_of_injective _ (parityEdge_injective n k),
    Finset.card_univ] at h
  simpa only [ParityIndex, Fintype.card_sigma, Fintype.card_fin] using h

theorem path_parity_sum (n h : ℕ) (hn : 2 * h + 1 ≤ n) :
    (∑ i : Fin h, (n - 2 * (i.val + 1))) = h * (n - h - 1) := by
  have hi := positiveIndex_sum_twice h
  have hs : (∑ i : Fin h, ((n - 2 * (i.val + 1) : ℕ) : ℤ)) =
      (h : ℤ) * n - 2 * ∑ i : Fin h, ((i.val : ℤ) + 1) := by
    calc
      _ = ∑ i : Fin h, ((n : ℤ) - 2 * ((i.val : ℤ) + 1)) := by
        apply Finset.sum_congr rfl
        intro i him
        rw [Nat.cast_sub (by have := i.isLt; omega)]
        simp
      _ = _ := by simp [Finset.sum_sub_distrib, Finset.mul_sum]
  have he : ((∑ i : Fin h, (n - 2 * (i.val + 1)) : ℕ) : ℤ) = (h * (n - h - 1) : ℕ) := by
    rw [Nat.cast_sum, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    simp only [Nat.cast_one]
    nlinarith
  exact_mod_cast he

theorem path_parity_cover (n k : ℕ) (hn : k + 1 ≤ n) :
    coverNumber (pathPower n k) ≤ k / 2 * (n - k / 2 - 1) := by
  have h := path_parity_cover_sum n k
  rw [path_parity_sum n (k / 2) (by omega)] at h
  exact h

end ResearchMain.PathCycleTuza
