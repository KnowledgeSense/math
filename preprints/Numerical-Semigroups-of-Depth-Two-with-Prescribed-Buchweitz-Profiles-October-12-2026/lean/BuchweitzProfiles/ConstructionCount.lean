import BuchweitzProfiles.ConstructionSet
import BuchweitzProfiles.LargeGenerators
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace BuchweitzProfiles

/-- The finite set in Section 3, with its large generators indexed by the
actual finite list of pairs. -/
def digitSet (N h : Nat) (d t : Fin h → Nat) : Finset Nat :=
  insert 0 (smallGenerators ((2*(2*N+2)+1)*(h+1)) (h+1)) ∪
    Finset.univ.image (fun j => largeGenerator N (h+1) (d j) (t j) (j.val+1))

private theorem digitSet_residue (N h : Nat) (d t : Fin h → Nat)
    (hN : 2 ≤ N) (hd : ∀ j, 2 ≤ d j ∧ d j ≤ N+1)
    (ht : ∀ j, t j ≤ 2*d j-2) (j : Fin h) :
    largeGenerator N (h+1) (d j) (t j) (j.val+1) % (h+1) = h-j.val := by
  rw [largeGenerator_mod N (h+1) (d j) (t j) (j.val+1) hN (by omega)
    (hd j).1 (hd j).2 (ht j) (by omega) (by omega)]
  omega

/-- All set elements satisfy the bound needed for a genuine depth-two semigroup. -/
theorem digitSet_bound (N h : Nat) (d t : Fin h → Nat)
    (hN : 2 ≤ N) (hd : ∀ j, 2 ≤ d j ∧ d j ≤ N+1)
    (ht : ∀ j, t j ≤ 2*d j-2) :
    ∀ c ∈ digitSet N h d t, c ≤ constructionCutoff N (h+1)-2 := by
  intro c hc
  rcases Finset.mem_union.mp hc with hc | hc
  · exact smallGenerators_bound N (h+1) c hN (by omega) hc
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
    exact (largeGenerator_bounds N (h+1) (d j) (t j) (j.val+1) hN (by omega)
      (hd j).1 (hd j).2 (ht j) (by omega) (by omega)).2.1

theorem digitSet_zero (N h : Nat) (d t : Fin h → Nat) : 0 ∈ digitSet N h d t :=
  Finset.mem_union_left _ (Finset.mem_insert_self _ _)

theorem digitSet_positive (N h : Nat) (d t : Fin h → Nat) :
    ∃ c ∈ digitSet N h d t, 0 < c := by
  obtain ⟨c, hc, hp⟩ := smallGenerators_positive N (h+1) (by omega)
  exact ⟨c, Finset.mem_union_left _ hc, hp⟩

theorem digitSet_card (N h : Nat) (d t : Fin h → Nat)
    (hN : 2 ≤ N) (hd : ∀ j, 2 ≤ d j ∧ d j ≤ N+1)
    (ht : ∀ j, t j ≤ 2*d j-2) : (digitSet N h d t).card = h+4 := by
  unfold digitSet
  rw [indexed_union_card _ _ _ (h+1)]
  · rw [smallGenerators_card N (h+1) (by omega)]
    simp
    omega
  · intro x hx
    exact Nat.dvd_of_mod_eq_zero (smallGenerators_mod N (h+1) x hx)
  · intro j _
    rw [digitSet_residue N h d t hN hd ht j]
    omega
  · intro i _ j _ he
    rw [digitSet_residue N h d t hN hd ht i, digitSet_residue N h d t hN hd ht j] at he
    apply Fin.ext
    omega

/-- The exact all-order counting identity of Proposition 4.3 for the actual
finite set constructed from any pairs satisfying the stated bounds. -/
theorem digitSet_count (N h : Nat) (d t : Fin h → Nat)
    (hN : 2 ≤ N) (hd : ∀ j, 2 ≤ d j ∧ d j ≤ N+1)
    (ht : ∀ j, t j ≤ 2*d j-2) (n : Nat) (hn : 1 ≤ n) :
    (truncatedCount (digitSet N h d t) (constructionCutoff N (h+1)) n : Int) =
      rowCount Finset.univ (2*N+2) d t n := by
  let U := insert 0 (smallGenerators ((2*(2*N+2)+1)*(h+1)) (h+1))
  let v := fun j : Fin h => largeGenerator N (h+1) (d j) (t j) (j.val+1)
  have hcount := truncatedCount_indexed_union Finset.univ v U
    (constructionCutoff N (h+1)) (h+1) n hn
  have hlarge : ∀ i ∈ (Finset.univ : Finset (Fin h)), ∀ j ∈ Finset.univ,
      constructionCutoff N (h+1) ≤ v i + v j := by
    intro i _ j _
    have hi := (largeGenerator_bounds N (h+1) (d i) (t i) (i.val+1) hN (by omega)
      (hd i).1 (hd i).2 (ht i) (by omega) (by omega)).2.2
    have hj := (largeGenerator_bounds N (h+1) (d j) (t j) (j.val+1) hN (by omega)
      (hd j).1 (hd j).2 (ht j) (by omega) (by omega)).2.2
    dsimp [v]
    omega
  have hdiv : ∀ k x, x ∈ sumset U k → h+1 ∣ x := by
    intro k x hx
    exact small_sum_divisible (2*N+2) (h+1) k hx
  have hres0 : ∀ j ∈ (Finset.univ : Finset (Fin h)), v j % (h+1) ≠ 0 := by
    intro j _
    dsimp [v]
    rw [digitSet_residue N h d t hN hd ht j]
    omega
  have hresinj : ∀ i ∈ (Finset.univ : Finset (Fin h)), ∀ j ∈ Finset.univ,
      v i % (h+1) = v j % (h+1) → i = j := by
    intro i _ j _ he
    dsimp [v] at he
    rw [digitSet_residue N h d t hN hd ht i, digitSet_residue N h d t hN hd ht j] at he
    apply Fin.ext
    omega
  specialize hcount hlarge hdiv hres0 hresinj
  change (truncatedCount (U ∪ Finset.univ.image v) (constructionCutoff N (h+1)) n : Int) = _
  rw [hcount]
  push_cast
  unfold rowCount smallRowCount
  congr 1
  · have hh := truncatedCount_small (2*N+2) (h+1) n (by omega)
    change (truncatedCount U (constructionCutoff N (h+1)) n : Int) = _
    dsimp [U, constructionCutoff]
    rw [hh]
    push_cast
    rfl
  · apply Finset.sum_congr rfl
    intro j _
    apply largeContribution_card (2*N+2) (h+1) (d j) (t j) (j.val+1) (v j)
      (constructionCutoff N (h+1)) n (by have := (hd j).2; omega) (by omega)
      (hd j).1 (ht j) (by omega) (by omega) hn
    dsimp [v]
    rw [largeGenerator_cast N (h+1) (d j) (t j) (j.val+1) hN (by omega)
      (hd j).1 (hd j).2 (ht j) (by omega) (by omega)]
    push_cast
    ring

end BuchweitzProfiles
