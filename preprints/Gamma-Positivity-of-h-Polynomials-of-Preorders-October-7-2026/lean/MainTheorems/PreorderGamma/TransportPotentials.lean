import MainTheorems.PreorderGamma.TransportTree
import MainTheorems.PreorderGamma.TransportOptimality

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

variable {L R : Type*} [Fintype L] [Fintype R]
variable {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}

noncomputable def transportArcCost (s : R → ℕ) (u v : L ⊕ R) : ℤ :=
  match u, v with
  | Sum.inl a, Sum.inr b => transportEdgeWeight s a b
  | Sum.inr b, Sum.inl a => -(transportEdgeWeight s a b : ℤ)
  | _, _ => 0

theorem transportArcCost_reverse (s : R → ℕ) (u v : L ⊕ R) :
    transportArcCost s v u = -transportArcCost s u v := by
  cases u <;> cases v <;> simp [transportArcCost]

noncomputable def transportWalkCost (p : NaturalTransport r d s) {u v : L ⊕ R}
    (w : (transportSupportGraph p).Walk u v) : ℤ :=
  (w.darts.map fun e => transportArcCost s e.fst e.snd).sum

@[simp] theorem transportWalkCost_nil (p : NaturalTransport r d s) (u : L ⊕ R) :
    transportWalkCost p (.nil : (transportSupportGraph p).Walk u u) = 0 := by
  simp [transportWalkCost]

theorem transportWalkCost_cons (p : NaturalTransport r d s) {u v w : L ⊕ R}
    (h : (transportSupportGraph p).Adj u v) (q : (transportSupportGraph p).Walk v w) :
    transportWalkCost p (.cons h q) = transportArcCost s u v + transportWalkCost p q := by
  simp [transportWalkCost]

theorem transportWalkCost_concat (p : NaturalTransport r d s) {u v w : L ⊕ R}
    (q : (transportSupportGraph p).Walk u v) (h : (transportSupportGraph p).Adj v w) :
    transportWalkCost p (q.concat h) = transportWalkCost p q + transportArcCost s v w := by
  simp [transportWalkCost]

theorem transportWalkCost_eq_matrix_difference (p : NaturalTransport r d s)
    {u v : L ⊕ R} (w : (transportSupportGraph p).Walk u v) :
    transportWalkCost p w = (transportMatrixCost s (walkForward p w) : ℤ) -
      transportMatrixCost s (walkBackward p w) := by
  induction w with
  | nil => simp [transportMatrixCost_eq_sum]
  | @cons u v w h q ih =>
    rw [transportWalkCost_cons]
    cases u with
    | inl a₀ =>
      cases v with
      | inl a₁ => exact False.elim h
      | inr b₀ =>
        have hf : walkForward p (.cons h q) = fun a b =>
            transportUnitEdge a₀ b₀ a b + walkForward p q a b := by
          funext a b
          simp only [walkForward_cons, Sum.inl.injEq, Sum.inr.injEq,
            transportUnitEdge, eq_comm]
        have hb : walkBackward p (.cons h q) = walkBackward p q := by
          funext a b
          simp only [walkBackward_cons, Sum.inl_ne_inr, false_and, ite_false, zero_add]
        rw [hf, hb, transportMatrixCost_add, transportMatrixCost_unitEdge]
        simp only [transportArcCost, Nat.cast_add]
        linarith
    | inr b₀ =>
      cases v with
      | inl a₀ =>
        have hf : walkForward p (.cons h q) = walkForward p q := by
          funext a b
          simp only [walkForward_cons, Sum.inr_ne_inl, false_and, ite_false, zero_add]
        have hb : walkBackward p (.cons h q) = fun a b =>
            transportUnitEdge a₀ b₀ a b + walkBackward p q a b := by
          funext a b
          simp only [walkBackward_cons, Sum.inl.injEq, Sum.inr.injEq,
            transportUnitEdge, eq_comm, and_comm]
        rw [hf, hb, transportMatrixCost_add, transportMatrixCost_unitEdge]
        simp only [transportArcCost, Nat.cast_add]
        linarith
      | inr b₁ => exact False.elim h

noncomputable def transportPathTransfer (p : NaturalTransport r d s) (a : L) (b : R)
    (hab : r a b) (w : (transportSupportGraph p).Walk (Sum.inl a) (Sum.inr b))
    (hw : w.IsTrail) : FeasibleTransfer p where
  increase := fun c e => walkBackward p w c e + transportUnitEdge a b c e
  decrease := walkForward p w
  increase_supported := by
    intro c e hce
    have hz := p.supported c e hce
    have hle := (walk_transfer_le p w hw c e).2
    have hb : walkBackward p w c e = 0 := by omega
    have he : ¬(c = a ∧ e = b) := by
      rintro ⟨rfl, rfl⟩
      exact hce hab
    simp only [hb, transportUnitEdge, ite_eq_right he, zero_add]
  decrease_le := fun c e => (walk_transfer_le p w hw c e).1
  row_balance := by
    intro c
    rw [Finset.sum_add_distrib]
    have hunit : (∑ e : R, transportUnitEdge a b c e) = if c = a then 1 else 0 := by
      by_cases hc : c = a <;> simp [transportUnitEdge, hc]
    rw [hunit]
    have hrow := walk_row_balance p w c
    simpa only [Sum.inr_ne_inl, Sum.inl_ne_inr, Sum.inl.injEq, ite_false, add_zero, eq_comm]
      using hrow.symm
  column_balance := by
    intro e
    rw [Finset.sum_add_distrib]
    have hunit : (∑ c : L, transportUnitEdge a b c e) = if e = b then 1 else 0 := by
      by_cases he : e = b <;> simp [transportUnitEdge, he]
    rw [hunit]
    have hcol := walk_column_balance p w e
    simpa only [Sum.inl_ne_inr, Sum.inr.injEq, ite_false, add_zero, eq_comm] using hcol.symm

theorem minimum_transport_path_cost_le (p : NaturalTransport r d s)
    (hp : ∀ q : NaturalTransport r d s, transportCost p ≤ transportCost q)
    (a : L) (b : R) (hab : r a b)
    (w : (transportSupportGraph p).Walk (Sum.inl a) (Sum.inr b)) (hw : w.IsTrail) :
    transportWalkCost p w ≤ transportEdgeWeight s a b := by
  have h := minimum_transport_transfer_cost_le p hp (transportPathTransfer p a b hab w hw)
  change transportMatrixCost s (walkForward p w) ≤
    transportMatrixCost s (fun c e => walkBackward p w c e + transportUnitEdge a b c e) at h
  rw [transportMatrixCost_add, transportMatrixCost_unitEdge] at h
  rw [transportWalkCost_eq_matrix_difference]
  have hi : (transportMatrixCost s (walkForward p w) : ℤ) ≤
      (transportMatrixCost s (walkBackward p w) : ℤ) + transportEdgeWeight s a b := by
    exact_mod_cast h
  linarith

noncomputable def supportTreePath (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree) (root v : L ⊕ R) :
    (transportSupportGraph p).Walk root v := Classical.choose (htree.existsUnique_path root v)

theorem supportTreePath_isPath (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree) (root v : L ⊕ R) :
    (supportTreePath p htree root v).IsPath :=
  (Classical.choose_spec (htree.existsUnique_path root v)).1

noncomputable def transportTreeVertexPotential (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree) (root v : L ⊕ R) : ℤ :=
  transportWalkCost p (supportTreePath p htree root v)

theorem transportTreeVertexPotential_adj (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree) (root u v : L ⊕ R)
    (hadj : (transportSupportGraph p).Adj u v) :
    transportTreeVertexPotential p htree root v =
      transportTreeVertexPotential p htree root u + transportArcCost s u v := by
  let pu := supportTreePath p htree root u
  let pv := supportTreePath p htree root v
  have hpu := supportTreePath_isPath p htree root u
  have hpv := supportTreePath_isPath p htree root v
  change transportWalkCost p pv = transportWalkCost p pu + transportArcCost s u v
  by_cases hv : v ∈ pu.support
  · have hpath : pu = pv.concat hadj.symm :=
      htree.isAcyclic.path_concat hpv hpu hadj.symm hv
    have hc := congrArg (fun q : (transportSupportGraph p).Walk root u => transportWalkCost p q) hpath
    rw [transportWalkCost_concat, transportArcCost_reverse] at hc
    linarith
  · have hu : u ∈ pv.support :=
      htree.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hpv hpu hadj.symm hv
    have hpath : pv = pu.concat hadj := htree.isAcyclic.path_concat hpu hpv hadj hu
    rw [hpath, transportWalkCost_concat]

theorem transportWalkCost_eq_potential_difference (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree) (root : L ⊕ R)
    {u v : L ⊕ R} (w : (transportSupportGraph p).Walk u v) :
    transportWalkCost p w = transportTreeVertexPotential p htree root v -
      transportTreeVertexPotential p htree root u := by
  induction w with
  | nil => simp
  | @cons u v w h q ih =>
    rw [transportWalkCost_cons]
    have hadj := transportTreeVertexPotential_adj p htree root u v h
    linarith

theorem minimum_transport_tree_potential_dual (p : NaturalTransport r d s)
    (hp : ∀ q : NaturalTransport r d s, transportCost p ≤ transportCost q)
    (htree : (transportSupportGraph p).IsTree) (root : L ⊕ R)
    (a : L) (b : R) (hab : r a b) :
    transportTreeVertexPotential p htree root (Sum.inr b) ≤
      (transportEdgeWeight s a b : ℤ) + transportTreeVertexPotential p htree root (Sum.inl a) := by
  let w := supportTreePath p htree (Sum.inl a) (Sum.inr b)
  have hw := (supportTreePath_isPath p htree (Sum.inl a) (Sum.inr b)).isTrail
  have hcost := minimum_transport_path_cost_le p hp a b hab w hw
  rw [transportWalkCost_eq_potential_difference p htree root w] at hcost
  linarith

theorem minimum_transport_tree_potential_tight (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree) (root : L ⊕ R)
    (a : L) (b : R) (hflow : 0 < p.flow a b) :
    (transportEdgeWeight s a b : ℤ) + transportTreeVertexPotential p htree root (Sum.inl a) =
      transportTreeVertexPotential p htree root (Sum.inr b) := by
  have h := transportTreeVertexPotential_adj p htree root (Sum.inl a) (Sum.inr b) hflow
  exact (add_comm (transportEdgeWeight s a b : ℤ)
    (transportTreeVertexPotential p htree root (Sum.inl a))).trans h.symm

theorem transport_tree_potential_ne_of_zero (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree) (root : L ⊕ R)
    (a : L) (b : R) (hab : r a b) (hz : p.flow a b = 0) :
    (transportEdgeWeight s a b : ℤ) + transportTreeVertexPotential p htree root (Sum.inl a) ≠
      transportTreeVertexPotential p htree root (Sum.inr b) := by
  intro heq
  let w := supportTreePath p htree (Sum.inl a) (Sum.inr b)
  have hw := (supportTreePath_isPath p htree (Sum.inl a) (Sum.inr b)).isTrail
  have hwalk : transportWalkCost p w = (transportEdgeWeight s a b : ℤ) := by
    rw [transportWalkCost_eq_potential_difference p htree root w]
    linarith
  rw [transportWalkCost_eq_matrix_difference] at hwalk
  have hcost : transportMatrixCost s (walkForward p w) =
      transportMatrixCost s (walkBackward p w) + transportEdgeWeight s a b := by
    have hc : (transportMatrixCost s (walkForward p w) : ℤ) =
        (transportMatrixCost s (walkBackward p w) : ℤ) + transportEdgeWeight s a b := by
      linarith
    exact_mod_cast hc
  let t := transportPathTransfer p a b hab w hw
  have htransfer : transportMatrixCost s t.decrease = transportMatrixCost s t.increase := by
    change transportMatrixCost s (walkForward p w) =
      transportMatrixCost s (fun c e => walkBackward p w c e + transportUnitEdge a b c e)
    rw [transportMatrixCost_add, transportMatrixCost_unitEdge]
    exact hcost
  have he := congrFun (congrFun (transport_equal_transfer p t htransfer) a) b
  have hle := (walk_transfer_le p w hw a b).1
  change walkBackward p w a b + transportUnitEdge a b a b = walkForward p w a b at he
  simp [transportUnitEdge] at he
  omega

theorem minimum_transport_tree_potential_strict (p : NaturalTransport r d s)
    (hp : ∀ q : NaturalTransport r d s, transportCost p ≤ transportCost q)
    (htree : (transportSupportGraph p).IsTree) (root : L ⊕ R)
    (a : L) (b : R) (hab : r a b) (hz : p.flow a b = 0) :
    transportTreeVertexPotential p htree root (Sum.inr b) <
      (transportEdgeWeight s a b : ℤ) + transportTreeVertexPotential p htree root (Sum.inl a) := by
  have hle := minimum_transport_tree_potential_dual p hp htree root a b hab
  have hne := transport_tree_potential_ne_of_zero p htree root a b hab hz
  omega

theorem minimum_transport_tree_potential_tight_iff (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree) (root : L ⊕ R)
    (a : L) (b : R) (hab : r a b) :
    (transportEdgeWeight s a b : ℤ) + transportTreeVertexPotential p htree root (Sum.inl a) =
      transportTreeVertexPotential p htree root (Sum.inr b) ↔ 0 < p.flow a b := by
  constructor
  · intro heq
    by_contra hn
    have hz : p.flow a b = 0 := by omega
    exact transport_tree_potential_ne_of_zero p htree root a b hab hz heq
  · exact minimum_transport_tree_potential_tight p htree root a b

end ResearchMain.PreorderGamma

