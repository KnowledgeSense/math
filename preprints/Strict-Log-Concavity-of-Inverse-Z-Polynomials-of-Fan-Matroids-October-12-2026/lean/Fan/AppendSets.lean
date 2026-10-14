import Fan.SeparatedConfigurations

namespace Fan

noncomputable def bitSet (b : Bool) : Finset (Fin 1) := if b then Finset.univ else ∅

@[simp] theorem mem_bitSet (b : Bool) (i : Fin 1) : i∈bitSet b ↔ b=true := by
  fin_cases i
  cases b <;> simp [bitSet]

noncomputable def appendSet {n : ℕ} (S : Finset (Fin n)) (b : Bool) : Finset (Fin (n+1)) :=
  joinSets S (bitSet b)

@[simp] theorem mem_append_cast {n : ℕ} (S : Finset (Fin n)) (b : Bool) (i : Fin n) :
    i.castSucc∈appendSet S b ↔ i∈S := mem_join_left S (bitSet b) i

@[simp] theorem mem_append_last {n : ℕ} (S : Finset (Fin n)) (b : Bool) :
    Fin.last n∈appendSet S b ↔ b=true := by
  change (0 : Fin 1).natAdd n∈joinSets S (bitSet b) ↔ _
  rw [mem_join_right,mem_bitSet]

noncomputable def appendPair {n : ℕ} (p : Pair n) (b c : Bool) : Pair (n+1) :=
  (appendSet p.1 b,appendSet p.2 c)

@[simp] theorem leftPair_append {n : ℕ} (p : Pair n) (b c : Bool) :
    leftPair (appendPair p b c)=p := leftPair_join p (bitSet b,bitSet c)

theorem bitSet_subset_iff (b c : Bool) : bitSet b⊆bitSet c ↔ b≤c := by
  cases b <;> cases c <;> simp [bitSet]

theorem appendSet_subset_iff {n : ℕ} (S T : Finset (Fin n)) (b c : Bool) :
    appendSet S b⊆appendSet T c ↔ S⊆T ∧ b≤c := by
  rw [appendSet,appendSet,joinSets_subset_iff,bitSet_subset_iff]

theorem appendPair_le_iff {n : ℕ} (p q : Pair n) (b c d e : Bool) :
    appendPair p b c ≤ appendPair q d e ↔ p≤q ∧ b≤d ∧ c≤e := by
  change (appendSet p.1 b⊆appendSet q.1 d ∧ appendSet p.2 c⊆appendSet q.2 e) ↔ _
  rw [appendSet_subset_iff,appendSet_subset_iff]
  change ((p.1⊆q.1 ∧ b≤d) ∧ (p.2⊆q.2 ∧ c≤e)) ↔ (p.1⊆q.1 ∧ p.2⊆q.2) ∧ b≤d ∧ c≤e
  tauto

noncomputable def lastBit {n : ℕ} (S : Finset (Fin (n+1))) : Bool :=
  decide (Fin.last n∈S)

@[simp] theorem lastBit_eq_true {n : ℕ} (S : Finset (Fin (n+1))) :
    lastBit S=true ↔ Fin.last n∈S := by classical simp [lastBit]

@[simp] theorem lastBit_append {n : ℕ} (S : Finset (Fin n)) (b : Bool) :
    lastBit (appendSet S b)=b := by
  apply Bool.eq_iff_iff.mpr
  simp only [lastBit_eq_true,mem_append_last]

theorem appendSet_left_last {n : ℕ} (S : Finset (Fin (n+1))) :
    appendSet (leftSet S) (lastBit S)=S := by
  ext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp only [mem_append_last,lastBit_eq_true]
  · simp only [mem_append_cast,mem_leftSet]
    rfl

theorem appendPair_left_last {n : ℕ} (p : Pair (n+1)) :
    appendPair (leftPair p) (lastBit p.1) (lastBit p.2)=p := by
  apply Prod.ext <;> exact appendSet_left_last _

theorem appendSet_union {n : ℕ} (S T : Finset (Fin n)) (b c : Bool) :
    appendSet S b ∪ appendSet T c=appendSet (S∪T) (b||c) := by
  ext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · simp only [Finset.mem_union,mem_append_last,Bool.or_eq_true]
  · simp only [Finset.mem_union,mem_append_cast]

theorem appendSet_card {n : ℕ} (S : Finset (Fin n)) (b : Bool) :
    (appendSet S b).card=S.card+if b then 1 else 0 := by
  rw [appendSet,joinSets_card]
  cases b <;> simp [bitSet]

end Fan
