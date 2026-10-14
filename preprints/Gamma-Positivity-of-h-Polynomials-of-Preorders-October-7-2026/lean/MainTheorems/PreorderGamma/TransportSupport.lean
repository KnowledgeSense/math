import MainTheorems.PreorderGamma.TransportPerturbations
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

variable {L R : Type*} [Fintype L] [Fintype R]
variable {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}

def transportSupportGraph (p : NaturalTransport r d s) : SimpleGraph (L ⊕ R) where
  Adj u v := match u, v with
    | Sum.inl a, Sum.inr b => 0 < p.flow a b
    | Sum.inr b, Sum.inl a => 0 < p.flow a b
    | _, _ => False
  symm := ⟨by intro u v; cases u <;> cases v <;> simp⟩
  loopless := ⟨by intro u; cases u <;> simp⟩

@[simp] theorem supportGraph_adj_left_right (p : NaturalTransport r d s) (a : L) (b : R) :
    (transportSupportGraph p).Adj (Sum.inl a) (Sum.inr b) ↔ 0 < p.flow a b := Iff.rfl

@[simp] theorem supportGraph_adj_right_left (p : NaturalTransport r d s) (a : L) (b : R) :
    (transportSupportGraph p).Adj (Sum.inr b) (Sum.inl a) ↔ 0 < p.flow a b := Iff.rfl

noncomputable def walkForward (p : NaturalTransport r d s) {u v : L ⊕ R}
    (w : (transportSupportGraph p).Walk u v) (a : L) (b : R) : ℕ :=
  w.darts.countP fun e => decide (e.fst = Sum.inl a ∧ e.snd = Sum.inr b)

noncomputable def walkBackward (p : NaturalTransport r d s) {u v : L ⊕ R}
    (w : (transportSupportGraph p).Walk u v) (a : L) (b : R) : ℕ :=
  w.darts.countP fun e => decide (e.fst = Sum.inr b ∧ e.snd = Sum.inl a)

@[simp] theorem walkForward_nil (p : NaturalTransport r d s) (u : L ⊕ R)
    (a : L) (b : R) : walkForward p (.nil : (transportSupportGraph p).Walk u u) a b = 0 := by
  classical
  simp [walkForward]

@[simp] theorem walkBackward_nil (p : NaturalTransport r d s) (u : L ⊕ R)
    (a : L) (b : R) : walkBackward p (.nil : (transportSupportGraph p).Walk u u) a b = 0 := by
  classical
  simp [walkBackward]

theorem walkForward_cons (p : NaturalTransport r d s) {u v w : L ⊕ R}
    (h : (transportSupportGraph p).Adj u v) (q : (transportSupportGraph p).Walk v w)
    (a : L) (b : R) :
    walkForward p (.cons h q) a b =
      (if u = Sum.inl a ∧ v = Sum.inr b then 1 else 0) + walkForward p q a b := by
  classical
  simp [walkForward, List.countP_cons, Nat.add_comm]

theorem walkBackward_cons (p : NaturalTransport r d s) {u v w : L ⊕ R}
    (h : (transportSupportGraph p).Adj u v) (q : (transportSupportGraph p).Walk v w)
    (a : L) (b : R) :
    walkBackward p (.cons h q) a b =
      (if u = Sum.inr b ∧ v = Sum.inl a then 1 else 0) + walkBackward p q a b := by
  classical
  simp [walkBackward, List.countP_cons, Nat.add_comm]

theorem support_adj_row_balance (p : NaturalTransport r d s) {u v : L ⊕ R}
    (h : (transportSupportGraph p).Adj u v) (a : L) :
    (∑ b : R, if u = Sum.inl a ∧ v = Sum.inr b then 1 else 0) +
        (if v = Sum.inl a then 1 else 0) =
      (∑ b : R, if u = Sum.inr b ∧ v = Sum.inl a then 1 else 0) +
        (if u = Sum.inl a then 1 else 0) := by
  classical
  cases u with
  | inl a₀ =>
    cases v with
    | inl a₁ => exact False.elim h
    | inr b₀ => by_cases ha : a₀ = a <;> simp [ha]
  | inr b₀ =>
    cases v with
    | inl a₀ => by_cases ha : a₀ = a <;> simp [ha]
    | inr b₁ => exact False.elim h

theorem support_adj_column_balance (p : NaturalTransport r d s) {u v : L ⊕ R}
    (h : (transportSupportGraph p).Adj u v) (b : R) :
    (∑ a : L, if u = Sum.inl a ∧ v = Sum.inr b then 1 else 0) +
        (if u = Sum.inr b then 1 else 0) =
      (∑ a : L, if u = Sum.inr b ∧ v = Sum.inl a then 1 else 0) +
        (if v = Sum.inr b then 1 else 0) := by
  classical
  cases u with
  | inl a₀ =>
    cases v with
    | inl a₁ => exact False.elim h
    | inr b₀ => by_cases hb : b₀ = b <;> simp [hb]
  | inr b₀ =>
    cases v with
    | inl a₀ => by_cases hb : b₀ = b <;> simp [hb]
    | inr b₁ => exact False.elim h

theorem walk_row_balance (p : NaturalTransport r d s) {u v : L ⊕ R}
    (w : (transportSupportGraph p).Walk u v) (a : L) :
    (∑ b, walkForward p w a b) + (if v = Sum.inl a then 1 else 0) =
      (∑ b, walkBackward p w a b) + (if u = Sum.inl a then 1 else 0) := by
  classical
  induction w with
  | nil => simp
  | @cons u v w h q ih =>
    have hlocal := support_adj_row_balance p h a
    simp_rw [walkForward_cons, walkBackward_cons, Finset.sum_add_distrib]
    omega

theorem walk_column_balance (p : NaturalTransport r d s) {u v : L ⊕ R}
    (w : (transportSupportGraph p).Walk u v) (b : R) :
    (∑ a, walkForward p w a b) + (if u = Sum.inr b then 1 else 0) =
      (∑ a, walkBackward p w a b) + (if v = Sum.inr b then 1 else 0) := by
  classical
  induction w with
  | nil => simp
  | @cons u v w h q ih =>
    have hlocal := support_adj_column_balance p h b
    simp_rw [walkForward_cons, walkBackward_cons, Finset.sum_add_distrib]
    omega

theorem walk_edge_count (p : NaturalTransport r d s) {u v : L ⊕ R}
    (w : (transportSupportGraph p).Walk u v) (a : L) (b : R) :
    walkForward p w a b + walkBackward p w a b =
      w.edges.count s(Sum.inl a, Sum.inr b) := by
  classical
  induction w with
  | nil => simp
  | @cons u v w h q ih =>
    rw [walkForward_cons, walkBackward_cons, SimpleGraph.Walk.edges_cons]
    simp only [List.count_cons, beq_iff_eq, Sym2.eq_iff]
    cases u <;> cases v
    · exact False.elim h
    · simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inr_ne_inl, Sum.inl_ne_inr,
        and_false, or_false, ite_false]
      split_ifs <;> omega
    · simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inr_ne_inl, Sum.inl_ne_inr,
        and_false, false_or, ite_false]
      split_ifs <;> omega
    · exact False.elim h

theorem walk_transfer_le (p : NaturalTransport r d s) {u v : L ⊕ R}
    (w : (transportSupportGraph p).Walk u v) (hw : w.IsTrail) (a : L) (b : R) :
    walkForward p w a b ≤ p.flow a b ∧ walkBackward p w a b ≤ p.flow a b := by
  classical
  have hcount := walk_edge_count p w a b
  have hle := hw.count_edges_le_one s(Sum.inl a, Sum.inr b)
  by_cases hmem : s(Sum.inl a, Sum.inr b) ∈ w.edges
  · have hpos : 0 < p.flow a b := w.adj_of_mem_edges hmem
    omega
  · have hz := List.count_eq_zero_of_not_mem hmem
    omega

noncomputable def closedTrailTransfer (p : NaturalTransport r d s) {u : L ⊕ R}
    (w : (transportSupportGraph p).Walk u u) (hw : w.IsTrail) : BalancedTransfer p where
  increase := walkForward p w
  decrease := walkBackward p w
  increase_le := fun a b => (walk_transfer_le p w hw a b).1
  decrease_le := fun a b => (walk_transfer_le p w hw a b).2
  row_balance := fun a => Nat.add_right_cancel (walk_row_balance p w a)
  column_balance := fun b => Nat.add_right_cancel (walk_column_balance p w b)

theorem minimum_transport_support_acyclic (p : NaturalTransport r d s)
    (hp : ∀ q : NaturalTransport r d s, transportCost p ≤ transportCost q) :
    (transportSupportGraph p).IsAcyclic := by
  classical
  intro u w hw
  have heq := minimum_transport_no_balanced_transfer p hp (closedTrailTransfer p w hw.isTrail)
  have hnil : ¬w.Nil := hw.not_nil
  obtain ⟨e, he⟩ : ∃ e, e ∈ w.edges := by
    exact w.edges.exists_mem_of_ne_nil ((SimpleGraph.Walk.edges_eq_nil).not.mpr hnil)
  obtain ⟨u', v', he⟩ := Sym2.exists.mp ⟨e, he⟩
  have hadj := w.adj_of_mem_edges he
  cases u' with
  | inl a =>
    cases v' with
    | inl a' => exact False.elim hadj
    | inr b =>
      have hc := hw.isTrail.count_edges_eq_one he
      have hb := walk_edge_count p w a b
      have hf := congrFun (congrFun heq a) b
      change walkForward p w a b = walkBackward p w a b at hf
      omega
  | inr b =>
    cases v' with
    | inl a =>
      have he' : s(Sum.inl a, Sum.inr b) ∈ w.edges := by simpa only [Sym2.eq_swap] using he
      have hc := hw.isTrail.count_edges_eq_one he'
      have hb := walk_edge_count p w a b
      have hf := congrFun (congrFun heq a) b
      change walkForward p w a b = walkBackward p w a b at hf
      omega
    | inr b' => exact False.elim hadj

end ResearchMain.PreorderGamma



