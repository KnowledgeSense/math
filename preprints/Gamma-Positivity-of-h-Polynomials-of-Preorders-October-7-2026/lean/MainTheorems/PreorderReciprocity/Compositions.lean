import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.RingTheory.Binomial
import Lean.Elab.Tactic.NormCast

namespace ResearchMain.PreorderReciprocity

instance weakCompositionFinite (r a : ℕ) :
    Finite {d : Fin r → ℕ // ∑ i, d i = a} :=
  Finite.of_equiv (Sym (Fin r) a) (Sym.equivNatSumOfFintype (Fin r) a)

theorem weak_composition_count (r a : ℕ) :
    Nat.card {d : Fin r → ℕ // ∑ i, d i = a} = Nat.multichoose r a := by
  rw [← Nat.card_congr (Sym.equivNatSumOfFintype (Fin r) a),
    Sym.natCard_sym_eq_multichoose]
  simp

noncomputable def boundedCompositionEquiv (s k : ℕ) :
    {d : Fin s → ℕ // ∑ i, d i ≤ k} ≃
      {d : Option (Fin s) → ℕ // ∑ i, d i = k} := by
  refine
    { toFun := fun d => ⟨Option.elim' (k - ∑ i, d.val i) d.val, ?_⟩
      invFun := fun d => ⟨fun i => d.val (some i), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [Fintype.sum_option]
    exact Nat.sub_add_cancel d.property
  · have h := d.property
    change (∑ i : Fin s, d.val (some i)) ≤ k
    rw [Fintype.sum_option] at h
    omega
  · intro d
    rfl
  · intro d
    apply Subtype.ext
    funext i
    cases i with
    | none =>
      have h := d.property
      rw [Fintype.sum_option] at h
      change k - ∑ i, d.val (some i) = d.val none
      omega
    | some i => rfl

instance boundedCompositionFinite (s k : ℕ) :
    Finite {d : Fin s → ℕ // ∑ i, d i ≤ k} :=
  Finite.of_equiv (Sym (Option (Fin s)) k)
    ((Sym.equivNatSumOfFintype (Option (Fin s)) k).trans (boundedCompositionEquiv s k).symm)

theorem bounded_composition_count (s k : ℕ) :
    Nat.card {d : Fin s → ℕ // ∑ i, d i ≤ k} = Nat.choose (s + k) k := by
  rw [Nat.card_congr (boundedCompositionEquiv s k),
    ← Nat.card_congr (Sym.equivNatSumOfFintype (Option (Fin s)) k),
    Sym.natCard_sym_eq_multichoose]
  simp [Nat.multichoose_eq]

theorem choose_multichoose_nat (r a : ℕ) :
    Ring.choose ((r : ℚ) + a - 1) a = (Nat.multichoose r a : ℚ) := by
  by_cases hz : r + a = 0
  · have hr : r = 0 := by omega
    have ha : a = 0 := by omega
    subst r
    subst a
    simp
  · have hp : 1 ≤ r + a := by omega
    have hc : ((r + a - 1 : ℕ) : ℚ) = (r : ℚ) + a - 1 := by
      rw [Nat.cast_sub hp, Nat.cast_add, Nat.cast_one]
    rw [← hc, Ring.choose_natCast, Nat.multichoose_eq]

noncomputable def binaryCompositionEquiv (r a : ℕ) :
    {d : Fin r → ℕ // (∑ i, d i) = a ∧ ∀ i, d i ≤ 1} ≃
      {S : Finset (Fin r) // S.card = a} := by
  refine
    { toFun := fun d => ⟨Finset.univ.filter fun i => 0 < d.val i, ?_⟩
      invFun := fun S => ⟨fun i => if i ∈ S.val then 1 else 0, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [Finset.card_filter]
    have hvalue : ∀ i, (if 0 < d.val i then 1 else 0) = d.val i := by
      intro i
      have hbound := d.property.2 i
      split_ifs <;> omega
    simp_rw [hvalue]
    exact d.property.1
  · refine ⟨?_, ?_⟩
    · rw [← Finset.card_filter]
      simpa using S.property
    · intro i
      change (if i ∈ S.val then 1 else 0) ≤ 1
      split_ifs <;> omega
  · intro d
    apply Subtype.ext
    funext i
    change (if i ∈ Finset.univ.filter (fun j => 0 < d.val j) then 1 else 0) = d.val i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hbound := d.property.2 i
    split_ifs <;> omega
  · intro S
    apply Subtype.ext
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> simp_all

instance binaryCompositionFinite (r a : ℕ) :
    Finite {d : Fin r → ℕ // (∑ i, d i) = a ∧ ∀ i, d i ≤ 1} :=
  Finite.of_equiv {S : Finset (Fin r) // S.card = a} (binaryCompositionEquiv r a).symm

theorem binary_composition_count (r a : ℕ) :
    Nat.card {d : Fin r → ℕ // (∑ i, d i) = a ∧ ∀ i, d i ≤ 1} = Nat.choose r a := by
  rw [Nat.card_congr (binaryCompositionEquiv r a), Nat.card_eq_fintype_card]
  simpa only [Fintype.card_fin] using Fintype.card_finset_len (α := Fin r) a

end ResearchMain.PreorderReciprocity
