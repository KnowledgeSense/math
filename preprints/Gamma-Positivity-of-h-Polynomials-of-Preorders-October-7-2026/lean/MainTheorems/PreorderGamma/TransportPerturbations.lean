import MainTheorems.PreorderGamma.Transport

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]
variable {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}

structure BalancedTransfer (p : NaturalTransport r d s) where
  increase : L → R → ℕ
  decrease : L → R → ℕ
  increase_le : ∀ a b, increase a b ≤ p.flow a b
  decrease_le : ∀ a b, decrease a b ≤ p.flow a b
  row_balance : ∀ a, (∑ b, increase a b) = ∑ b, decrease a b
  column_balance : ∀ b, (∑ a, increase a b) = ∑ a, decrease a b

def BalancedTransfer.reverse {p : NaturalTransport r d s} (t : BalancedTransfer p) :
    BalancedTransfer p where
  increase := t.decrease
  decrease := t.increase
  increase_le := t.decrease_le
  decrease_le := t.increase_le
  row_balance := fun a => (t.row_balance a).symm
  column_balance := fun b => (t.column_balance b).symm

def NaturalTransport.perturb (p : NaturalTransport r d s) (t : BalancedTransfer p) :
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
    have hi := t.increase_le a b
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

theorem NaturalTransport.perturb_entry_balance (p : NaturalTransport r d s)
    (t : BalancedTransfer p) (a : L) (b : R) :
    (p.perturb t).flow a b + t.decrease a b = p.flow a b + t.increase a b := by
  have h := t.decrease_le a b
  change p.flow a b + t.increase a b - t.decrease a b + t.decrease a b = _
  omega

theorem NaturalTransport.perturb_pair_sum (p : NaturalTransport r d s)
    (t : BalancedTransfer p) (a : L) (b : R) :
    (p.perturb t).flow a b + (p.perturb t.reverse).flow a b = 2 * p.flow a b := by
  have h1 := p.perturb_entry_balance t a b
  have h2 := p.perturb_entry_balance t.reverse a b
  change (p.perturb t.reverse).flow a b + t.increase a b =
    p.flow a b + t.decrease a b at h2
  omega

theorem transportCost_perturb_pair_sum (p : NaturalTransport r d s)
    (t : BalancedTransfer p) :
    transportCost (p.perturb t) + transportCost (p.perturb t.reverse) =
      2 * transportCost p := by
  rw [transportCost_eq_sum, transportCost_eq_sum, transportCost_eq_sum,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  rw [← add_mul, p.perturb_pair_sum t ab.1 ab.2]
  ring

theorem minimum_transport_no_balanced_transfer (p : NaturalTransport r d s)
    (hp : ∀ q : NaturalTransport r d s, transportCost p ≤ transportCost q) (t : BalancedTransfer p) :
    t.increase = t.decrease := by
  have hcost := transportCost_perturb_pair_sum p t
  have h1 := hp (p.perturb t)
  have h2 := hp (p.perturb t.reverse)
  have heq : transportCost (p.perturb t) = transportCost p := by omega
  have hp' : p.perturb t = p := transportCost_injective heq
  funext a b
  have h := p.perturb_entry_balance t a b
  rw [hp'] at h
  omega

end ResearchMain.PreorderGamma

