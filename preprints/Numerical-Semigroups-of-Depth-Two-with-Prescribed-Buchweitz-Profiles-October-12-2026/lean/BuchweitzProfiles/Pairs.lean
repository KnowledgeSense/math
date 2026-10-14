import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! The finite multiset of Euclidean-division pairs, represented by a list. -/
namespace BuchweitzProfiles

/-- One distinguished remainder and the remaining zero remainders at a stage. -/
def pairBlock (d e r : Nat) : List (Nat × Nat) :=
  (d,r) :: List.replicate (e-1) (d,0)

/-- All stages from 2 through `k+1`, in descending order. -/
def pairBlocks (q r : Nat → Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | k+1 => pairBlock (k+2) (q (k+1)-q (k+2)) (r (k+2)) ++ pairBlocks q r k

/-- The list of pairs prescribed in Section 3. -/
def constructionPairs (q r : Nat → Nat) (N : Nat) : List (Nat × Nat) :=
  pairBlocks q r (N-1) ++ List.replicate (q N) (N+1,0)

theorem length_pairBlock (d e r : Nat) (he : 0 < e) :
    (pairBlock d e r).length = e := by simp [pairBlock]; omega

theorem length_pairBlocks (q r : Nat → Nat) (k : Nat)
    (hq : ∀ n, 1 ≤ n → n ≤ k → q (n+1) < q n) :
    (pairBlocks q r k).length + q (k+1) = q 1 := by
  induction k with
  | zero => simp [pairBlocks]
  | succ k ih =>
    have hh : q (k+2) < q (k+1) := by simpa only [Nat.add_assoc] using hq (k+1) (by omega) (by omega)
    have hi := ih (by intro n hn hnk; exact hq n hn (by omega))
    simp only [pairBlocks, List.length_append]
    rw [length_pairBlock _ _ _ (by omega)]
    have he : k+1+1=k+2 := by omega
    simp only [Nat.add_assoc, Nat.reduceAdd] at *
    omega

theorem length_constructionPairs (q r : Nat → Nat) (N : Nat) (hN : 1 ≤ N)
    (hq : ∀ n, 1 ≤ n → n < N → q (n+1) < q n) :
    (constructionPairs q r N).length = q 1 := by
  have hh := length_pairBlocks q r (N-1) (by intro n hn hnN; exact hq n hn (by omega))
  have he : N-1+1=N := by omega
  simpa [constructionPairs, he] using hh

theorem mem_pairBlock {d e r : Nat} {p : Nat × Nat} (hp : p ∈ pairBlock d e r) :
    p.1 = d ∧ (p.2 = r ∨ p.2 = 0) := by
  simp only [pairBlock, List.mem_cons, List.mem_replicate] at hp
  rcases hp with rfl | ⟨_, rfl⟩ <;> simp

theorem pairBlocks_bounds (q r : Nat → Nat) (k : Nat)
    (hr : ∀ n, 2 ≤ n → n ≤ k+1 → r n ≤ 2*n-2)
    {p : Nat × Nat} (hp : p ∈ pairBlocks q r k) :
    2 ≤ p.1 ∧ p.1 ≤ k+1 ∧ p.2 ≤ 2*p.1-2 := by
  induction k with
  | zero => simp [pairBlocks] at hp
  | succ k ih =>
    simp only [pairBlocks, List.mem_append] at hp
    rcases hp with hp | hp
    · obtain ⟨hd, ht⟩ := mem_pairBlock hp
      have hh := hr (k+2) (by omega) (by omega)
      rcases ht with ht | ht <;> omega
    · have hh := ih (by intro n hn hnk; exact hr n hn (by omega)) hp
      omega

theorem constructionPairs_bounds (q r : Nat → Nat) (N : Nat) (hN : 2 ≤ N)
    (hr : ∀ n, 2 ≤ n → n ≤ N → r n ≤ 2*n-2)
    {p : Nat × Nat} (hp : p ∈ constructionPairs q r N) :
    2 ≤ p.1 ∧ p.1 ≤ N+1 ∧ p.2 ≤ 2*p.1-2 ∧ (p.1=N+1 → p.2=0) := by
  simp only [constructionPairs, List.mem_append, List.mem_replicate] at hp
  rcases hp with hp | ⟨_, rfl⟩
  · have hh := pairBlocks_bounds q r (N-1) (by intro n hn hnN; exact hr n hn (by omega)) hp
    omega
  · simp; omega

/-- The number of pairs whose first coordinate is strictly above `n`. -/
def pairTailCount (n : Nat) (ps : List (Nat × Nat)) : Nat :=
  (ps.filter (fun p => n < p.1)).length

@[simp] theorem pairTailCount_append (n : Nat) (ps qs : List (Nat × Nat)) :
    pairTailCount n (ps++qs) = pairTailCount n ps + pairTailCount n qs := by
  simp [pairTailCount]

theorem pairTailCount_block (d e r n : Nat) (he : 0 < e) :
    pairTailCount n (pairBlock d e r) = if n<d then e else 0 := by
  by_cases h : n<d
  all_goals simp [pairTailCount, pairBlock, h]
  omega

theorem pairTailCount_above (q r : Nat → Nat) (k n : Nat) (hn : k+1 ≤ n) :
    pairTailCount n (pairBlocks q r k) = 0 := by
  induction k with
  | zero => simp [pairTailCount, pairBlocks]
  | succ k ih =>
    rw [pairBlocks, pairTailCount_append]
    have hh := ih (by omega)
    have hn' : ¬n<k+2 := by omega
    simp [pairTailCount, pairBlock, hn'] at *
    exact hh

theorem pairTailCount_blocks (q r : Nat → Nat) (k n : Nat)
    (hq : ∀ i, 1 ≤ i → i ≤ k → q (i+1) < q i)
    (hn : 1 ≤ n) (hnk : n ≤ k+1) :
    pairTailCount n (pairBlocks q r k) + q (k+1) = q n := by
  induction k with
  | zero =>
    have he : n=1 := by omega
    subst n
    simp [pairBlocks, pairTailCount]
  | succ k ih =>
    by_cases hn' : n ≤ k+1
    · have hh : q (k+2) < q (k+1) := by
        simpa only [Nat.add_assoc] using hq (k+1) (by omega) (by omega)
      have hi := ih (by intro i hi hik; exact hq i hi (by omega)) hn'
      rw [pairBlocks, pairTailCount_append,
        pairTailCount_block _ _ _ _ (by omega), ite_eq_left (show n<k+2 by omega)]
      simp only [Nat.add_assoc, Nat.reduceAdd] at *
      omega
    · have he : n=k+1+1 := by omega
      rw [pairTailCount_above q r (k+1) n (by omega), Nat.zero_add, he]

theorem pairTailCount_construction (q r : Nat → Nat) (N n : Nat)
    (hq : ∀ i, 1 ≤ i → i < N → q (i+1) < q i)
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    pairTailCount n (constructionPairs q r N) = q n := by
  have hh := pairTailCount_blocks q r (N-1) n
    (by intro i hi hiN; exact hq i hi (by omega)) hn (by omega)
  have he : N-1+1=N := by omega
  simp only [he] at hh
  rw [constructionPairs, pairTailCount_append]
  have hlast : pairTailCount n (List.replicate (q N) (N+1,0)) = q N := by
    simp [pairTailCount, show n<N+1 by omega]
  rw [hlast]
  exact hh

/-- Sum of the second coordinates at a specified stage. -/
def pairStageMass (n : Nat) (ps : List (Nat × Nat)) : Nat :=
  (ps.map (fun p => if p.1=n then p.2 else 0)).sum

@[simp] theorem pairStageMass_append (n : Nat) (ps qs : List (Nat × Nat)) :
    pairStageMass n (ps++qs) = pairStageMass n ps + pairStageMass n qs := by
  simp [pairStageMass]

theorem pairStageMass_block (d e r n : Nat) :
    pairStageMass n (pairBlock d e r) = if d=n then r else 0 := by
  by_cases h : d=n <;> simp [pairStageMass, pairBlock, h]

theorem pairStageMass_above (q r : Nat → Nat) (k n : Nat) (hn : k+1 < n) :
    pairStageMass n (pairBlocks q r k) = 0 := by
  induction k with
  | zero => simp [pairStageMass, pairBlocks]
  | succ k ih =>
    rw [pairBlocks, pairStageMass_append, pairStageMass_block,
      ite_eq_right (show k+2 ≠ n by omega), Nat.zero_add]
    exact ih (by omega)

theorem pairStageMass_blocks (q r : Nat → Nat) (k n : Nat)
    (hn : 2 ≤ n) (hnk : n ≤ k+1) :
    pairStageMass n (pairBlocks q r k) = r n := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [pairBlocks, pairStageMass_append, pairStageMass_block]
    by_cases he : k+2=n
    · rw [ite_eq_left he, he, pairStageMass_above q r k n (by omega), Nat.add_zero]
    · rw [ite_eq_right he, Nat.zero_add]
      exact ih (by omega)

theorem pairStageMass_construction (q r : Nat → Nat) (N n : Nat)
    (hn : 2 ≤ n) (hnN : n ≤ N) :
    pairStageMass n (constructionPairs q r N) = r n := by
  rw [constructionPairs, pairStageMass_append,
    pairStageMass_blocks q r (N-1) n hn (by omega)]
  have he : pairStageMass n (List.replicate (q N) (N+1,0)) = 0 := by
    simp [pairStageMass]
  rw [he, Nat.add_zero]

theorem list_filter_length_eq_sum_indicator {α : Type*} (p : α → Prop)
    [DecidablePred p] (ps : List α) :
    (ps.filter (fun x => p x)).length = (ps.map (fun x => if p x then 1 else 0)).sum := by
  induction ps with
  | nil => simp
  | cons a ps ih =>
    by_cases h : p a <;> simp [h, ih, Nat.add_comm]

/-- Converting the list count into the finite-index count used in the sumset formula. -/
theorem pairTailCount_eq_card (n : Nat) (ps : List (Nat × Nat)) :
    pairTailCount n ps =
      (Finset.univ.filter (fun i : Fin ps.length => n < ps[i.val].1)).card := by
  rw [Finset.card_filter]
  unfold pairTailCount
  rw [list_filter_length_eq_sum_indicator]
  rw [← List.ofFn_getElem_eq_map ps (fun p => if n<p.1 then 1 else 0), List.sum_ofFn]

theorem pairStageMass_eq_sum (n : Nat) (ps : List (Nat × Nat)) :
    pairStageMass n ps =
      ∑ i : Fin ps.length, if ps[i.val].1=n then ps[i.val].2 else 0 := by
  unfold pairStageMass
  rw [← List.ofFn_getElem_eq_map ps (fun p => if p.1=n then p.2 else 0), List.sum_ofFn]

/-- The two pair statistics in precisely the finite-sum form of the profile bridge. -/
theorem constructionPairs_statistics (q r : Nat → Nat) (N n : Nat)
    (hq : ∀ i, 1 ≤ i → i < N → q (i+1) < q i)
    (hn : 2 ≤ n) (hnN : n ≤ N) :
    let ps := constructionPairs q r N
    ((Finset.univ.filter (fun i : Fin ps.length => n+1 ≤ ps[i.val].1)).card : ℤ) * (2*(n:ℤ)-1) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin ps.length => n=ps[i.val].1), (ps[i.val].2 : ℤ) =
      (2*(n:ℤ)-1)*(q n:ℤ)+(r n:ℤ) := by
  dsimp
  let ps := constructionPairs q r N
  have hc := pairTailCount_construction q r N n hq (by omega) hnN
  rw [pairTailCount_eq_card] at hc
  have hf : (Finset.univ.filter (fun i : Fin ps.length => n+1 ≤ ps[i.val].1)) =
      Finset.univ.filter (fun i : Fin ps.length => n<ps[i.val].1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  change ((Finset.univ.filter (fun i : Fin ps.length => n+1 ≤ ps[i.val].1)).card : ℤ) * _ + _ = _
  rw [hf, hc]
  have hm := pairStageMass_construction q r N n hn hnN
  rw [pairStageMass_eq_sum] at hm
  have hs : (∑ i ∈ Finset.univ.filter (fun i : Fin ps.length => n=ps[i.val].1), (ps[i.val].2 : ℤ)) = (r n:ℤ) := by
    rw [Finset.sum_filter]
    have he : (∑ i : Fin ps.length, if n=ps[i.val].1 then (ps[i.val].2:ℤ) else 0) =
        ((∑ i : Fin ps.length, if ps[i.val].1=n then ps[i.val].2 else 0 : Nat):ℤ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : n=ps[i.val].1 <;> simp [h, eq_comm]
    rw [he, hm]
  rw [hs]
  rw [mul_comm]

end BuchweitzProfiles
