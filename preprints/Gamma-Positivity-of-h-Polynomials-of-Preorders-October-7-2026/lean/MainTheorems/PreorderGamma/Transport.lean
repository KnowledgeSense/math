import MainTheorems.PreorderGamma.Bipartite
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]

structure NaturalTransport (r : L → R → Prop) (d : L → ℕ) (s : R → ℕ) where
  flow : L → R → ℕ
  supported : ∀ a b, ¬r a b → flow a b = 0
  row_sum : ∀ a, ∑ b, flow a b = d a
  column_sum : ∀ b, ∑ a, flow a b = s b

theorem naturalTransport_ext {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}
    {p q : NaturalTransport r d s} (h : p.flow = q.flow) : p = q := by
  cases p
  cases q
  cases h
  rfl

theorem NaturalTransport.entry_le {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}
    (p : NaturalTransport r d s) (a : L) (b : R) : p.flow a b ≤ s b := by
  rw [← p.column_sum b]
  exact Finset.single_le_sum (fun c _ => Nat.zero_le (p.flow c b)) (Finset.mem_univ a)

theorem NaturalTransport.entry_le_total {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}
    (p : NaturalTransport r d s) (a : L) (b : R) : p.flow a b ≤ ∑ c, s c :=
  (p.entry_le a b).trans
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))

theorem NaturalTransport.total_eq {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}
    (p : NaturalTransport r d s) : (∑ a, d a) = ∑ b, s b := by
  simp_rw [← p.row_sum]
  rw [Finset.sum_comm]
  simp_rw [p.column_sum]

instance (r : L → R → Prop) (d : L → ℕ) (s : R → ℕ) :
    Finite (NaturalTransport r d s) := by
  classical
  let f : NaturalTransport r d s → L → R → Fin ((∑ b, s b) + 1) :=
    fun p a b => ⟨p.flow a b, Nat.lt_succ_of_le (p.entry_le_total a b)⟩
  apply Finite.of_injective f
  intro p q hpq
  apply naturalTransport_ext
  funext a b
  exact congrArg Fin.val (congrFun (congrFun hpq a) b)

noncomputable instance (r : L → R → Prop) (d : L → ℕ) (s : R → ℕ) :
    Fintype (NaturalTransport r d s) := Fintype.ofFinite _

def positionalCost {A : Type*} {n : ℕ} (base : ℕ) (e : A ≃ Fin n) (x : A → ℕ) : ℕ :=
  Nat.ofDigits base (List.ofFn fun i => x (e.symm i))

theorem ofDigits_ofFn (base : ℕ) {n : ℕ} (x : Fin n → ℕ) :
    Nat.ofDigits base (List.ofFn x) = ∑ i, x i * base ^ i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem positionalCost_eq_sum {A : Type*} [Fintype A] {n : ℕ}
    (base : ℕ) (e : A ≃ Fin n) (x : A → ℕ) :
    positionalCost base e x = ∑ a, x a * base ^ (e a).val := by
  rw [positionalCost, ofDigits_ofFn]
  symm
  apply Fintype.sum_equiv e
  intro a
  simp

theorem positionalCost_injective {A : Type*} {n base : ℕ}
    (e : A ≃ Fin n) (hb : 1 < base) {x y : A → ℕ}
    (hx : ∀ a, x a < base) (hy : ∀ a, y a < base)
    (h : positionalCost base e x = positionalCost base e y) : x = y := by
  have hlist : (List.ofFn fun i => x (e.symm i)) =
      (List.ofFn fun i => y (e.symm i)) := by
    apply Nat.ofDigits_inj_of_len_eq hb (by simp) ?_ ?_ h
    · rw [List.forall_mem_ofFn_iff]
      exact fun i => hx (e.symm i)
    · rw [List.forall_mem_ofFn_iff]
      exact fun i => hy (e.symm i)
  have hf := List.ofFn_injective hlist
  funext a
  simpa using congrFun hf (e a)

noncomputable def transportCost {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}
    (p : NaturalTransport r d s) : ℕ :=
  positionalCost ((∑ b, s b) + 2) (Fintype.equivFin (L × R))
    (fun ab => p.flow ab.1 ab.2)

theorem transportCost_eq_sum {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}
    (p : NaturalTransport r d s) :
    transportCost p = ∑ ab : L × R, p.flow ab.1 ab.2 *
      ((∑ b, s b) + 2) ^ (Fintype.equivFin (L × R) ab).val :=
  positionalCost_eq_sum _ _ _

theorem transportCost_injective {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ} :
    Function.Injective (transportCost (r := r) (d := d) (s := s)) := by
  intro p q h
  have hp : ∀ ab : L × R, p.flow ab.1 ab.2 < (∑ b, s b) + 2 := by
    intro ab
    have h := p.entry_le_total ab.1 ab.2
    omega
  have hq : ∀ ab : L × R, q.flow ab.1 ab.2 < (∑ b, s b) + 2 := by
    intro ab
    have h := q.entry_le_total ab.1 ab.2
    omega
  have hf := positionalCost_injective (Fintype.equivFin (L × R)) (by omega) hp hq h
  apply naturalTransport_ext
  funext a b
  exact congrFun hf (a, b)

theorem exists_unique_minimum_transport {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}
    (hn : Nonempty (NaturalTransport r d s)) :
    ∃! p : NaturalTransport r d s, ∀ q : NaturalTransport r d s, transportCost p ≤ transportCost q := by
  classical
  obtain ⟨p⟩ := hn
  have hex : ∃ n : ℕ, ∃ q : NaturalTransport r d s, transportCost q = n :=
    ⟨transportCost p, p, rfl⟩
  obtain ⟨q, hq⟩ := Nat.find_spec hex
  have hmin : ∀ t : NaturalTransport r d s, transportCost q ≤ transportCost t := by
    intro t
    have h := Nat.find_min' hex (show ∃ u : NaturalTransport r d s,
      transportCost u = transportCost t from ⟨t, rfl⟩)
    rwa [← hq] at h
  refine ⟨q, hmin, ?_⟩
  intro t ht
  apply transportCost_injective
  exact le_antisymm (ht q) (hmin t)

end ResearchMain.PreorderGamma

