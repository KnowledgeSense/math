import FourGeneratedSemigroups.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section
namespace FourGeneratedSemigroups

@[simp] theorem factorizationMap_single (d : Fin 4 → ℕ) (i : Fin 4) (n : ℕ) :
    factorizationMap d (Finsupp.single i n) = n*d i := by
  classical
  simp [factorizationMap,Finsupp.single_apply]

lemma factorizationMap_eq_zero_iff (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (c : Factorization) : factorizationMap d c = 0 ↔ c=0 := by
  constructor
  · intro h
    ext i
    have hi : c i*d i ≤ factorizationMap d c :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (c j*d j)) (Finset.mem_univ i)
    have hd' := hd i
    change c i=0
    nlinarith
  · rintro rfl
    simp

lemma factorizationMap_split (d : Fin 4 → ℕ) (c : Factorization) (i : Fin 4) :
    factorizationMap d c = c i*d i + factorizationMap d (c.erase i) := by
  classical
  have he : c=Finsupp.single i (c i)+c.erase i := by
    ext j
    by_cases hji : j=i
    · subst j; simp
    · simp [hji]
  conv_lhs => rw [he,map_add,factorizationMap_single]

/-- A pure power has a factorization that avoids its own generator. -/
def CriticalRelation (d : Fin 4 → ℕ) (i : Fin 4) (q : ℕ) : Prop :=
  0<q ∧ ∃ c : Factorization, c i=0 ∧ factorizationMap d c=q*d i

lemma exists_criticalRelation (d : Fin 4 → ℕ) (hd : ∀ i,0<d i) (i : Fin 4) :
    ∃ q, CriticalRelation d i q := by
  obtain ⟨j,hji⟩ := exists_ne i
  exact ⟨d j,hd j,Finsupp.single j (d i),by simp [hji],by simp [Nat.mul_comm]⟩

/-- The least positive exponent in a critical relation, as in the paper's `aᵢᵢ`. -/
def criticalExponent (d : Fin 4 → ℕ) (hd : ∀ i,0<d i) (i : Fin 4) : ℕ := by
  classical
  exact Nat.find (exists_criticalRelation d hd i)

theorem criticalExponent_spec (d : Fin 4 → ℕ) (hd : ∀ i,0<d i) (i : Fin 4) :
    CriticalRelation d i (criticalExponent d hd i) := by
  classical
  exact Nat.find_spec (exists_criticalRelation d hd i)

theorem criticalExponent_le (d : Fin 4 → ℕ) (hd : ∀ i,0<d i) (i : Fin 4)
    (q : ℕ) (hq : CriticalRelation d i q) : criticalExponent d hd i ≤ q := by
  classical
  exact Nat.find_min' (exists_criticalRelation d hd i) hq

/-- At a critical degree, every factorization is either the pure power or avoids
that generator entirely. This is Lemma 2.1 of the cited staircase construction. -/
theorem critical_factorization_dichotomy (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (i : Fin 4) (c : Factorization)
    (hc : factorizationMap d c = criticalExponent d hd i*d i) :
    c=Finsupp.single i (criticalExponent d hd i) ∨ c i=0 := by
  let a := criticalExponent d hd i
  have hs := factorizationMap_split d c i
  have hd' := hd i
  have hci : c i ≤ a := by dsimp [a]; nlinarith
  by_cases heq : c i=a
  · left
    have herase : c.erase i=0 := by
      apply (factorizationMap_eq_zero_iff d hd _).mp
      dsimp [a] at heq
      nlinarith
    ext j
    by_cases hji : j=i
    · subst j; simpa [a] using heq
    · have hj := congrArg (fun e : Factorization => e j) herase
      simpa [Finsupp.erase_ne hji,Finsupp.single_apply,Ne.symm hji] using hj
  · right
    by_contra hn
    have hrel : CriticalRelation d i (a-c i) := by
      refine ⟨by omega,c.erase i,by simp,?_⟩
      rw [Nat.sub_mul]
      dsimp [a] at *
      omega
    have hh := criticalExponent_le d hd i (a-c i) hrel
    change a ≤ a-c i at hh
    omega

end FourGeneratedSemigroups
