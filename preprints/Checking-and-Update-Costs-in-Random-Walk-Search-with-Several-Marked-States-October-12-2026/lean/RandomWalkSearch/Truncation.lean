import RandomWalkSearch.Execution
import Mathlib.Order.CompleteLattice.Basic

/-! # Pathwise budget truncation, including unlimited coordinates -/

namespace RandomWalkSearch

universe u
variable {X : Type u}

namespace Action

def updateCharge : Action X → ℕ
  | .update .. => 1
  | _ => 0

def checkCharge : Action X → ℕ
  | .check _ => 1
  | _ => 0

end Action

@[simp] theorem updates_respond_cons (r : Tapes X) (o : Oracle X)
    (h : History X) (a : Action X) :
    History.updates (respond r o h a :: h) = h.updates + a.updateCharge := by
  cases a <;> simp [History.updates, List.countP_cons, respond,
    Event.isUpdate, Action.updateCharge]

@[simp] theorem checks_respond_cons (r : Tapes X) (o : Oracle X)
    (h : History X) (a : Action X) :
    History.checks (respond r o h a :: h) = h.checks + a.checkCharge := by
  cases a <;> simp [History.checks, List.countP_cons, respond,
    Event.isCheck, Action.checkCharge]

def Within (T Q : ℕ∞) (h : History X) : Prop :=
  (h.updates : ℕ∞) ≤ T ∧ (h.checks : ℕ∞) ≤ Q

def Allows (T Q : ℕ∞) (h : History X) (a : Action X) : Prop :=
  ((h.updates + a.updateCharge : ℕ) : ℕ∞) ≤ T ∧
  ((h.checks + a.checkCharge : ℕ) : ℕ∞) ≤ Q

/-- The policy halts without output before an operation that exceeds either cap.
An infinite cap imposes no restriction on that coordinate. -/
noncomputable def truncate (T Q : ℕ∞) (p : Policy X) : Policy X := by
  classical
  exact fun h => if Allows T Q h (p h) then p h else .output none

theorem within_of_sublist {T Q : ℕ∞} {h h' : History X}
    (hh : Within T Q h') (hsub : h.Sublist h') : Within T Q h := by
  constructor
  · exact le_trans (by exact_mod_cast (hsub.countP_le (p := Event.isUpdate))) hh.1
  · exact le_trans (by exact_mod_cast (hsub.countP_le (p := Event.isCheck))) hh.2

@[simp] theorem within_respond (T Q : ℕ∞) (r : Tapes X) (o : Oracle X)
    (h : History X) (a : Action X) :
    Within T Q (respond r o h a :: h) ↔ Allows T Q h a := by
  simp only [Within, Allows, updates_respond_cons, checks_respond_cons]

/-- The actual truncated execution satisfies both budgets, for every oracle. -/
theorem truncate_within (T Q : ℕ∞) (p : Policy X) (r : Tapes X)
    (o : Oracle X) (n : ℕ) : Within T Q (run (truncate T Q p) r o n) := by
  classical
  induction n with
  | zero => simp [Within, History.updates, History.checks]
  | succ n ih =>
    simp only [run_succ, step]
    split
    · exact ih
    · rw [within_respond]
      by_cases ha : Allows T Q (run (truncate T Q p) r o n)
          (p (run (truncate T Q p) r o n))
      · simp only [truncate, ha, ite_true]
      · simp only [truncate, ha]
        exact ih

/-- Truncation changes no finite prefix whose original costs fit the caps. -/
theorem run_truncate_eq_of_within (T Q : ℕ∞) (p : Policy X) (r : Tapes X)
    (o : Oracle X) (n : ℕ) (hn : Within T Q (run p r o n)) :
    run (truncate T Q p) r o n = run p r o n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : Within T Q (run p r o n) :=
      within_of_sublist hn (run_sublist_succ p r o n)
    rw [run_succ, ih hp, run_succ]
    unfold step
    by_cases hh : (run p r o n).halted = true
    · simp only [hh, ite_true]
    · have ha : Allows T Q (run p r o n) (p (run p r o n)) := by
        simpa only [run_succ, step, hh, Bool.false_eq_true, ite_false, within_respond] using hn
      simp only [hh, truncate, ha, ite_true]

/-- A success of the original run survives unless at least one actual total
operation count exceeds its cap. No bound on the other coordinate is needed. -/
theorem succeeds_truncate_of_cost_le (T Q : ℕ∞) (p : Policy X) (r : Tapes X)
    (o : Oracle X) (hu : updateCost p r o ≤ T) (hc : checkCost p r o ≤ Q)
    (hs : Succeeds p r o) : Succeeds (truncate T Q p) r o := by
  obtain ⟨n, x, hx, hmark⟩ := hs
  have hn : Within T Q (run p r o n) :=
    ⟨(le_iSup (fun n => ((run p r o n).updates : ℕ∞)) n).trans hu,
     (le_iSup (fun n => ((run p r o n).checks : ℕ∞)) n).trans hc⟩
  exact ⟨n, x, (run_truncate_eq_of_within T Q p r o n hn).symm ▸ hx, hmark⟩

theorem truncation_failure_subset (T Q : ℕ∞) (p : Policy X) (r : Tapes X)
    (o : Oracle X) (hs : Succeeds p r o) :
    Succeeds (truncate T Q p) r o ∨ T < updateCost p r o ∨ Q < checkCost p r o := by
  classical
  by_cases hu : updateCost p r o ≤ T
  · by_cases hc : checkCost p r o ≤ Q
    · exact Or.inl (succeeds_truncate_of_cost_le T Q p r o hu hc hs)
    · exact Or.inr (Or.inr (lt_of_not_ge hc))
  · exact Or.inr (Or.inl (lt_of_not_ge hu))

/-- The total costs of the truncated policy are genuinely bounded even on
counterfactual histories and infinite nonhalting runs. -/
theorem truncate_updateCost_le (T Q : ℕ∞) (p : Policy X) (r : Tapes X)
    (o : Oracle X) : updateCost (truncate T Q p) r o ≤ T := by
  exact iSup_le (fun n => (truncate_within T Q p r o n).1)

theorem truncate_checkCost_le (T Q : ℕ∞) (p : Policy X) (r : Tapes X)
    (o : Oracle X) : checkCost (truncate T Q p) r o ≤ Q := by
  exact iSup_le (fun n => (truncate_within T Q p r o n).2)

/-- Before truncation stops the run, its entire history is still the original
history. This proves preservation of every operational access restriction. -/
theorem run_truncate_eq_or_halted (T Q : ℕ∞) (p : Policy X) (r : Tapes X)
    (o : Oracle X) (n : ℕ) :
    run (truncate T Q p) r o n = run p r o n ∨
      (run (truncate T Q p) r o n).halted = true := by
  classical
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rcases ih with heq | hhalt
    · by_cases hh : (run p r o n).halted = true
      · exact Or.inl (by simp [run_succ, step, heq, hh])
      · by_cases ha : Allows T Q (run p r o n) (p (run p r o n))
        · exact Or.inl (by simp [run_succ, step, heq, hh, truncate, ha])
        · apply Or.inr
          simp only [run_succ, step, heq, hh, ite_false, truncate, ha, respond]
          simp [History.halted, Event.isOutput]
    · exact Or.inr (by simp [run_succ, step, hhalt])

/-- Truncation preserves any restriction on the next operation which permits
halting without output, on the genuine infinite operational semantics. -/
theorem truncate_operation_safe (T Q : ℕ∞) (p : Policy X) (r : Tapes X)
    (o : Oracle X) (Safe : History X → Action X → Prop)
    (hhalt : ∀ h, Safe h (.output none))
    (hsafe : ∀ n, (run p r o n).halted = false →
      Safe (run p r o n) (p (run p r o n)))
    (n : ℕ) (hn : (run (truncate T Q p) r o n).halted = false) :
    Safe (run (truncate T Q p) r o n)
      (truncate T Q p (run (truncate T Q p) r o n)) := by
  classical
  have heq : run (truncate T Q p) r o n = run p r o n := by
    rcases run_truncate_eq_or_halted T Q p r o n with h | h
    · exact h
    · simp [hn] at h
  rw [heq]
  unfold truncate
  split
  · exact hsafe n (heq ▸ hn)
  · exact hhalt _

/-- A pointwise bound on the next operation gives a bound on every prefix. -/
theorem run_within_of_allows (T Q : ℕ∞) (p : Policy X) (r : Tapes X)
    (o : Oracle X)
    (ha : ∀ n, (run p r o n).halted = false →
      Allows T Q (run p r o n) (p (run p r o n))) (n : ℕ) :
    Within T Q (run p r o n) := by
  induction n with
  | zero => simp [Within, History.updates, History.checks]
  | succ n ih =>
    simp only [run_succ, step]
    split
    · exact ih
    · rename_i hn
      exact (within_respond T Q r o _ _).mpr (ha n (Bool.eq_false_iff.mpr hn))

/-- Hard budgets imposed only on genuine executions transfer to every
counterfactual execution of the actual completion. -/
theorem complete_within {A : Type*} (family : A → Oracle X)
    (T Q : ℕ∞) (p : Policy X) (r : Tapes X)
    (hb : ∀ a n, Within T Q (run p r (family a) n))
    (o : Oracle X) (n : ℕ) :
    Within T Q (run (complete family p) r o n) := by
  classical
  induction n with
  | zero => simp [Within, History.updates, History.checks]
  | succ n ih =>
    simp only [run_succ, step]
    split
    · exact ih
    · rename_i hh
      rw [within_respond]
      by_cases hc : Consistent family (run (complete family p) r o n)
      · obtain ⟨a, heq⟩ := complete_prefix_realizable family p r o n hc
        simp only [complete, hc, ite_true]
        rw [heq]
        have hh' : ¬(run p r (family a) n).halted = true := heq ▸ hh
        have hn := hb a (n + 1)
        simpa only [run_succ, step, hh', Bool.false_eq_true, ite_false, within_respond] using hn
      · simp only [complete, hc, ite_false]
        exact ih

end RandomWalkSearch
