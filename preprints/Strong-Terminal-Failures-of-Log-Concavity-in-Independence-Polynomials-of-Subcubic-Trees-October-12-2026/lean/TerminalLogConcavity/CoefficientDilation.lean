import TerminalLogConcavity.RealCoefficientOrder
import TerminalLogConcavity.WeightedPath
import Mathlib.Tactic.Positivity

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

/-- A coefficient bound with a common degree-dependent dilation rate. -/
def DilationBound (p q : ℕ[X]) (s r : ℝ) : Prop :=
  ∀ n, (p.coeff n : ℝ) ≤ s*r^n*(q.coeff n : ℝ)

namespace DilationBound

theorem add {p q p' q' : ℕ[X]} {s r : ℝ} (h : DilationBound p q s r)
    (h' : DilationBound p' q' s r) : DilationBound (p+p') (q+q') s r := by
  intro n
  have hn := h n
  have hn' := h' n
  simp only [coeff_add,Nat.cast_add]
  nlinarith

theorem mul {p q p' q' : ℕ[X]} {s t r : ℝ} (hs : 0 ≤ s) (_ht : 0 ≤ t) (hr : 0 ≤ r)
    (h : DilationBound p q s r) (h' : DilationBound p' q' t r) :
    DilationBound (p*p') (q*q') (s*t) r := by
  intro n
  simp only [coeff_mul,Nat.cast_sum,Nat.cast_mul,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  have hm := mul_le_mul (h ij.1) (h' ij.2) (by positivity : (0:ℝ) ≤ p'.coeff ij.2)
    (by positivity : 0 ≤ s*r^ij.1*(q.coeff ij.1 : ℝ))
  convert hm using 1
  rw [← he,pow_add]
  ring

theorem constant {a b : ℕ} {s r : ℝ} (h : (a : ℝ) ≤ s*b) : DilationBound (C a) (C b) s r := by
  intro n
  by_cases hn : n=0
  · subst n; simpa using h
  · simp [hn]

theorem one {s r : ℝ} (hs : 1 ≤ s) : DilationBound 1 1 s r := by
  simpa using (constant (r := r) (a := 1) (b := 1) (by simpa using hs))

theorem linear {a b : ℕ} {s r : ℝ} (hs : 1 ≤ s) (hab : (a : ℝ) ≤ s*r*b) :
    DilationBound (1+C a*X) (1+C b*X) s r := by
  intro n
  cases n with
  | zero => simpa using hs
  | succ n =>
    cases n with
    | zero => simpa [coeff_one] using hab
    | succ n => simp [coeff_one]

theorem prod {α : Type*} (S : Finset α) (p q : α → ℕ[X]) (s : α → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hs : ∀ x ∈ S, 0 ≤ s x) (h : ∀ x ∈ S, DilationBound (p x) (q x) (s x) r) :
    DilationBound (∏ x ∈ S, p x) (∏ x ∈ S, q x) (∏ x ∈ S, s x) r := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact one le_rfl
  | @insert x S hx ih =>
    rw [Finset.prod_insert hx,Finset.prod_insert hx,Finset.prod_insert hx]
    apply (h x (by simp)).mul (hs x (by simp)) (Finset.prod_nonneg (fun y hy => hs y (by simp [hy]))) hr
    exact ih (fun y hy => hs y (by simp [hy])) (fun y hy => h y (by simp [hy]))

end DilationBound

theorem weightedPath_dilation {α : Type*} (l : List α) (u v : α → ℕ[X] × ℕ[X])
    (s : α → ℝ) {r : ℝ} (hr : 0 ≤ r) (hs : ∀ x ∈ l, 0 ≤ s x)
    (h : ∀ x ∈ l, DilationBound (u x).1 (v x).1 (s x) r ∧
      DilationBound (u x).2 (v x).2 (s x) r) :
    DilationBound (weightedPath (l.map u)).1 (weightedPath (l.map v)).1 (l.map s).prod r ∧
    DilationBound (weightedPath (l.map u)).2 (weightedPath (l.map v)).2 (l.map s).prod r := by
  induction l with
  | nil => exact ⟨DilationBound.one le_rfl,DilationBound.one le_rfl⟩
  | cons x l ih =>
    have hsx := hs x (by simp)
    have hsl : ∀ y ∈ l, 0 ≤ s y := fun y hy => hs y (by simp [hy])
    have hp : 0 ≤ (l.map s).prod := List.prod_nonneg (by simpa using hsl)
    obtain ⟨h0,h1⟩ := h x (by simp)
    obtain ⟨ht0,ht1⟩ := ih hsl (fun y hy => h y (by simp [hy]))
    exact ⟨(h0.mul hsx hp hr ht0).add (h1.mul hsx hp hr ht1), h0.mul hsx hp hr ht0⟩

end TerminalLogConcavity
