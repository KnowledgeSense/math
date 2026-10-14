import MainTheorems.PreorderGamma.TransportPerturbations

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

variable {L R : Type*} [Fintype L] [Fintype R]
variable {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}

structure FeasibleTransfer (p : NaturalTransport r d s) where
  increase : L → R → ℕ
  decrease : L → R → ℕ
  increase_supported : ∀ a b, ¬r a b → increase a b = 0
  decrease_le : ∀ a b, decrease a b ≤ p.flow a b
  row_balance : ∀ a, (∑ b, increase a b) = ∑ b, decrease a b
  column_balance : ∀ b, (∑ a, increase a b) = ∑ a, decrease a b

def FeasibleTransfer.perturb (p : NaturalTransport r d s) (t : FeasibleTransfer p) :
    NaturalTransport r d s := by
  let f : L → R → ℕ := fun a b => p.flow a b + t.increase a b - t.decrease a b
  have hf : ∀ a b, f a b + t.decrease a b = p.flow a b + t.increase a b := by
    intro a b
    have h := t.decrease_le a b
    dsimp [f]
    omega
  refine
    { flow := f
      supported := ?_
      row_sum := ?_
      column_sum := ?_ }
  · intro a b hab
    have hp := p.supported a b hab
    have hi := t.increase_supported a b hab
    have hd := t.decrease_le a b
    dsimp [f]
    omega
  · intro a
    have h : (∑ b, f a b) + ∑ b, t.decrease a b =
        (∑ b, p.flow a b) + ∑ b, t.increase a b := by
      simpa only [Finset.sum_add_distrib] using
        (Finset.sum_congr rfl (fun b (_ : b ∈ (Finset.univ : Finset R)) => hf a b))
    rw [t.row_balance, p.row_sum] at h
    exact Nat.add_right_cancel h
  · intro b
    have h : (∑ a, f a b) + ∑ a, t.decrease a b =
        (∑ a, p.flow a b) + ∑ a, t.increase a b := by
      simpa only [Finset.sum_add_distrib] using
        (Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset L)) => hf a b))
    rw [t.column_balance, p.column_sum] at h
    exact Nat.add_right_cancel h

theorem FeasibleTransfer.perturb_entry_balance (p : NaturalTransport r d s)
    (t : FeasibleTransfer p) (a : L) (b : R) :
    (t.perturb p).flow a b + t.decrease a b = p.flow a b + t.increase a b := by
  have h := t.decrease_le a b
  change p.flow a b + t.increase a b - t.decrease a b + t.decrease a b = _
  omega

noncomputable def transportMatrixCost (s : R → ℕ) (x : L → R → ℕ) : ℕ :=
  positionalCost ((∑ b, s b) + 2) (Fintype.equivFin (L × R)) (fun ab => x ab.1 ab.2)

theorem transportMatrixCost_eq_sum (s : R → ℕ) (x : L → R → ℕ) :
    transportMatrixCost s x = ∑ ab : L × R, x ab.1 ab.2 *
      ((∑ b, s b) + 2) ^ (Fintype.equivFin (L × R) ab).val :=
  positionalCost_eq_sum _ _ _

theorem transportMatrixCost_flow (p : NaturalTransport r d s) :
    transportMatrixCost s p.flow = transportCost p := rfl

theorem transportMatrixCost_injective_of_bound (s : R → ℕ) {x y : L → R → ℕ}
    (hx : ∀ a b, x a b < (∑ c, s c) + 2)
    (hy : ∀ a b, y a b < (∑ c, s c) + 2)
    (hcost : transportMatrixCost s x = transportMatrixCost s y) : x = y := by
  have hf := positionalCost_injective (Fintype.equivFin (L × R)) (by omega)
    (fun ab => hx ab.1 ab.2) (fun ab => hy ab.1 ab.2) hcost
  funext a b
  exact congrFun hf (a, b)

theorem transportMatrixCost_add (s : R → ℕ) (x y : L → R → ℕ) :
    transportMatrixCost s (fun a b => x a b + y a b) =
      transportMatrixCost s x + transportMatrixCost s y := by
  rw [transportMatrixCost_eq_sum, transportMatrixCost_eq_sum,
    transportMatrixCost_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ab hab
  exact add_mul _ _ _

theorem transport_cost_transfer_balance (p : NaturalTransport r d s)
    (t : FeasibleTransfer p) :
    transportCost (t.perturb p) + transportMatrixCost s t.decrease =
      transportCost p + transportMatrixCost s t.increase := by
  rw [transportCost_eq_sum, transportMatrixCost_eq_sum, transportCost_eq_sum,
    transportMatrixCost_eq_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [← add_mul, ← add_mul, t.perturb_entry_balance p ab.1 ab.2]

theorem minimum_transport_transfer_cost_le (p : NaturalTransport r d s)
    (hp : ∀ q : NaturalTransport r d s, transportCost p ≤ transportCost q)
    (t : FeasibleTransfer p) :
    transportMatrixCost s t.decrease ≤ transportMatrixCost s t.increase := by
  have hb := transport_cost_transfer_balance p t
  have hmin := hp (t.perturb p)
  omega

theorem transport_equal_transfer (p : NaturalTransport r d s) (t : FeasibleTransfer p)
    (heq : transportMatrixCost s t.decrease = transportMatrixCost s t.increase) :
    t.increase = t.decrease := by
  have hb := transport_cost_transfer_balance p t
  have hc : transportCost (t.perturb p) = transportCost p := by omega
  have hf : t.perturb p = p := transportCost_injective hc
  funext a b
  have h := t.perturb_entry_balance p a b
  rw [hf] at h
  omega

noncomputable def transportEdgeWeight (s : R → ℕ) (a : L) (b : R) : ℕ :=
  ((∑ c, s c) + 2) ^ (Fintype.equivFin (L × R) (a, b)).val

noncomputable def transportUnitEdge (a₀ : L) (b₀ : R) (a : L) (b : R) : ℕ :=
  if a = a₀ ∧ b = b₀ then 1 else 0

theorem transportMatrixCost_unitEdge (s : R → ℕ) (a : L) (b : R) :
    transportMatrixCost s (transportUnitEdge a b) = transportEdgeWeight s a b := by
  rw [transportMatrixCost_eq_sum]
  calc
    _ = transportUnitEdge a b a b *
        ((∑ c, s c) + 2) ^ (Fintype.equivFin (L × R) (a, b)).val := by
      apply Finset.sum_eq_single (a, b)
      · intro ab hab hne
        have hn : ¬(ab.1 = a ∧ ab.2 = b) := fun h => hne (Prod.ext h.1 h.2)
        simp only [transportUnitEdge, ite_eq_right hn, zero_mul]
      · exact fun h => False.elim (h (Finset.mem_univ _))
    _ = _ := by simp [transportUnitEdge, transportEdgeWeight]

theorem transportCost_eq_rows (p : NaturalTransport r d s) :
    transportCost p = ∑ a, ∑ b, p.flow a b * transportEdgeWeight s a b := by
  rw [transportCost_eq_sum]
  exact Fintype.sum_prod_type (fun ab : L × R =>
    p.flow ab.1 ab.2 * transportEdgeWeight s ab.1 ab.2)

theorem transport_potential_balance (p : NaturalTransport r d s)
    (rowPotential : L → ℤ) (columnPotential : R → ℤ) :
    (∑ a, ∑ b, (p.flow a b : ℤ) *
      ((transportEdgeWeight s a b : ℤ) + rowPotential a - columnPotential b)) =
      (transportCost p : ℤ) + (∑ a, (d a : ℤ) * rowPotential a) -
        ∑ b, (s b : ℤ) * columnPotential b := by
  have hcost : (∑ a, ∑ b, (p.flow a b : ℤ) * (transportEdgeWeight s a b : ℤ)) =
      (transportCost p : ℤ) := by
    rw [transportCost_eq_rows]
    push_cast
    rfl
  have hrow : (∑ a, ∑ b, (p.flow a b : ℤ) * rowPotential a) =
      ∑ a, (d a : ℤ) * rowPotential a := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_mul, ← Nat.cast_sum, p.row_sum]
  have hcol : (∑ a, ∑ b, (p.flow a b : ℤ) * columnPotential b) =
      ∑ b, (s b : ℤ) * columnPotential b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.sum_mul, ← Nat.cast_sum, p.column_sum]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hcost, hrow, hcol]

theorem transport_potential_certificate_minimum (p : NaturalTransport r d s)
    (rowPotential : L → ℤ) (columnPotential : R → ℤ)
    (hdual : ∀ a b, r a b → columnPotential b ≤
      (transportEdgeWeight s a b : ℤ) + rowPotential a)
    (htight : ∀ a b, 0 < p.flow a b →
      (transportEdgeWeight s a b : ℤ) + rowPotential a = columnPotential b) :
    ∀ q : NaturalTransport r d s, transportCost p ≤ transportCost q := by
  intro q
  have hpzero : (∑ a, ∑ b, (p.flow a b : ℤ) *
      ((transportEdgeWeight s a b : ℤ) + rowPotential a - columnPotential b)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    apply Finset.sum_eq_zero
    intro b hb
    by_cases hflow : p.flow a b = 0
    · simp only [hflow, Nat.cast_zero, zero_mul]
    · rw [htight a b (Nat.pos_of_ne_zero hflow), sub_self, mul_zero]
  have hqnonneg : 0 ≤ ∑ a, ∑ b, (q.flow a b : ℤ) *
      ((transportEdgeWeight s a b : ℤ) + rowPotential a - columnPotential b) := by
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    by_cases hab : r a b
    · exact mul_nonneg (Int.natCast_nonneg _) (sub_nonneg.mpr (hdual a b hab))
    · rw [q.supported a b hab, Nat.cast_zero, zero_mul]
  rw [transport_potential_balance p] at hpzero
  rw [transport_potential_balance q] at hqnonneg
  have hcost : (transportCost p : ℤ) ≤ transportCost q := by linarith
  exact_mod_cast hcost

end ResearchMain.PreorderGamma
