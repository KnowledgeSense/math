import MainTheorems.PreorderGamma.TransportBases

namespace ResearchMain.PreorderGamma

open scoped BigOperators
open PreorderReciprocity

variable {L R : Type*} [Fintype L] [Fintype R]
variable {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}

noncomputable def transportSingletonColumns (p : NaturalTransport r d s) (a : L) :
    Finset R := by
  classical
  exact (transportSplitColumns p)ᶜ.filter fun b => 0 < p.flow a b

@[simp] theorem mem_transportSingletonColumns {p : NaturalTransport r d s} {a : L}
    {b : R} : b ∈ transportSingletonColumns p a ↔
      b ∉ transportSplitColumns p ∧ 0 < p.flow a b := by
  classical
  simp [transportSingletonColumns]

noncomputable def transportSplitRowFlow (p : NaturalTransport r d s) (a : L) : ℕ :=
  ∑ b ∈ transportSplitColumns p, p.flow a b

theorem transport_singleton_column_flow (p : NaturalTransport r d s) (b : R)
    (hcard : (transportColumnRows p b).card = 1) (a : L) :
    p.flow a b = if 0 < p.flow a b then s b else 0 := by
  classical
  by_cases ha : 0 < p.flow a b
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard
    have hac : a = c := by
      have hm := mem_transportColumnRows.mpr ha
      rw [hc] at hm
      exact Finset.mem_singleton.mp hm
    have hz : ∀ e, e ≠ a → p.flow e b = 0 := by
      intro e he
      by_contra hn
      have hm := mem_transportColumnRows.mpr (Nat.pos_of_ne_zero hn)
      rw [hc] at hm
      exact he ((Finset.mem_singleton.mp hm).trans hac.symm)
    have hsum : (∑ e, p.flow e b) = p.flow a b := by
      apply Finset.sum_eq_single a
      · intro e he hea
        exact hz e hea
      · simp
    rw [p.column_sum] at hsum
    simp only [ite_eq_left ha]
    exact hsum.symm
  · simp only [ite_eq_right ha]
    omega

theorem scaled_nonsplit_column_flow (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) (b : R)
    (hb : b ∉ transportSplitColumns p) (a : Option L) :
    p.flow a b = if 0 < p.flow a b then k else 0 := by
  have hlo := Finset.card_pos.mpr (transportColumnRows_nonempty p b (by omega))
  have hhi := scaled_column_support_card_le_two r x hpos k hk p htree b
  have hne : (transportColumnRows p b).card ≠ 2 := fun h =>
    hb (mem_transportSplitColumns.mpr h)
  exact transport_singleton_column_flow p b (by omega) a

theorem scaled_split_singleton_balance (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) (a : Option L) :
    transportSplitRowFlow p a + k * (transportSingletonColumns p a).card =
      scaledDemand (R := R) k x a := by
  classical
  have hout : (∑ b ∈ (transportSplitColumns p)ᶜ, p.flow a b) =
      k * (transportSingletonColumns p a).card := by
    calc
      _ = ∑ b ∈ (transportSplitColumns p)ᶜ, if 0 < p.flow a b then k else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact scaled_nonsplit_column_flow r x hpos k hk p htree b
          (Finset.mem_compl.mp hb) a
      _ = _ := by
        simp only [transportSingletonColumns, Finset.card_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        split_ifs <;> simp
  rw [← hout]
  exact (Finset.sum_add_sum_compl (transportSplitColumns p) (p.flow a)).trans
    (p.row_sum a)

omit [Fintype L] [Fintype R] in
theorem nat_remainder_le_of_balance (k t c z v : ℕ) (hv : v < k)
    (h : t + k * c = k * z + v) : v ≤ t := by
  by_cases hc : c ≤ z
  · have hm := Nat.mul_le_mul_left k hc
    omega
  · have hc' : z + 1 ≤ c := by omega
    have hm : k * z + k ≤ k * c := by
      simpa only [Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left k hc'
    omega

theorem scaled_split_row_flow_lower (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) (a : L) :
    k - 1 ≤ transportSplitRowFlow p (some a) := by
  have hbalance := scaled_split_singleton_balance r x hpos k hk p htree (some a)
  change transportSplitRowFlow p (some a) +
    k * (transportSingletonColumns p (some a)).card = k * x a - 1 at hbalance
  have hkpos : 0 < k := by omega
  have hxpos : 0 < x a := hpos a
  have hmul : k ≤ k * x a := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left k hxpos
  have h : transportSplitRowFlow p (some a) +
      k * (transportSingletonColumns p (some a)).card =
      k * (x a - 1) + (k - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    omega
  exact nat_remainder_le_of_balance k _ _ _ (k - 1) (by omega) h

theorem scaled_split_dummy_flow_lower (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) :
    Fintype.card L ≤ transportSplitRowFlow p none := by
  have hbalance := scaled_split_singleton_balance r x hpos k hk p htree none
  exact nat_remainder_le_of_balance k _ _ _ (Fintype.card L) hk hbalance

theorem scaled_split_flow_total (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) :
    (∑ a, transportSplitRowFlow p a) = k * Fintype.card L := by
  classical
  unfold transportSplitRowFlow
  rw [Finset.sum_comm]
  simp_rw [p.column_sum]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id,
    scaled_split_columns_card r x hpos k hk p htree, Nat.mul_comm]

theorem scaled_split_row_flow (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) :
    (∀ a : L, transportSplitRowFlow p (some a) = k - 1) ∧
      transportSplitRowFlow p none = Fintype.card L := by
  classical
  have hlow := scaled_split_row_flow_lower r x hpos k hk p htree
  have hdummy := scaled_split_dummy_flow_lower r x hpos k hk p htree
  have htotal := scaled_split_flow_total r x hpos k hk p htree
  rw [Fintype.sum_option] at htotal
  have hsumlow : Fintype.card L * (k - 1) ≤
      ∑ a : L, transportSplitRowFlow p (some a) := by
    calc
      _ = ∑ _ : L, (k - 1) := by simp
      _ ≤ _ := Finset.sum_le_sum fun a ha => hlow a
  have hkpos : 0 < k := by omega
  have hmul : k * Fintype.card L = Fintype.card L * (k - 1) + Fintype.card L := by
    calc
      _ = Fintype.card L * k := Nat.mul_comm _ _
      _ = Fintype.card L * (k - 1 + 1) := by rw [Nat.sub_add_cancel hkpos]
      _ = _ := by rw [Nat.mul_add, Nat.mul_one]
  have hsum : (∑ a : L, transportSplitRowFlow p (some a)) =
      Fintype.card L * (k - 1) := by omega
  constructor
  · have heq : (∑ _ : L, (k - 1)) =
        ∑ a : L, transportSplitRowFlow p (some a) := by simpa using hsum.symm
    have hpoint := (Finset.sum_eq_sum_iff_of_le (fun a ha => hlow a)).mp heq
    intro a
    exact (hpoint a (Finset.mem_univ a)).symm
  · omega

theorem scaled_demand_eq_one_add_singletons (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) (a : L) :
    x a = 1 + (transportSingletonColumns p (some a)).card := by
  have hbalance := scaled_split_singleton_balance r x hpos k hk p htree (some a)
  rw [(scaled_split_row_flow r x hpos k hk p htree).1 a] at hbalance
  change k - 1 + k * (transportSingletonColumns p (some a)).card =
    k * x a - 1 at hbalance
  have hkpos : 0 < k := by omega
  have hmul : k ≤ k * x a := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left k (hpos a)
  have heq : k * x a = k * (1 + (transportSingletonColumns p (some a)).card) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  exact Nat.eq_of_mul_eq_mul_left hkpos heq

end ResearchMain.PreorderGamma
