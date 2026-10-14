import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

noncomputable section

namespace R34

open Finset MvPolynomial
open scoped BigOperators

abbrev Poly := MvPolynomial (Fin 2) ℝ

def S : Poly := X 0
def T : Poly := X 1
def U : Poly := S + T
def V : Poly := S * T

def h (a : ℕ) : Poly := ∑ i ∈ Finset.range (a + 1), S ^ i * T ^ (a - i)

inductive SchurPositive : Poly → Prop
  | basis (a b : ℕ) : SchurPositive (V ^ b * h a)
  | zero : SchurPositive 0
  | add {f g : Poly} : SchurPositive f → SchurPositive g → SchurPositive (f + g)
  | scale (c : ℝ) {f : Poly} : 0 ≤ c → SchurPositive f → SchurPositive (C c * f)

@[simp] theorem h_zero : h 0 = 1 := by simp [h]
@[simp] theorem h_one : h 1 = U := by simp [h, Finset.sum_range_succ, U]; ring

theorem h_succ (a : ℕ) : h (a + 1) = S * h a + T ^ (a + 1) := by
  unfold h
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ a := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [Nat.add_sub_add_right, pow_succ]
  ring

theorem h_difference (a : ℕ) : (S - T) * h a = S ^ (a + 1) - T ^ (a + 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc
      (S-T)*h (a+1) = S*((S-T)*h a)+(S-T)*T^(a+1) := by rw [h_succ]; ring
      _ = S^(a+1+1)-T^(a+1+1) := by rw [ih]; simp only [pow_succ]; ring

theorem S_ne_T : S ≠ T := by
  intro heq
  have hh := congrArg (fun p : Poly => p.coeff (Finsupp.single (0 : Fin 2) 1)) heq
  norm_num [S, T, MvPolynomial.coeff_X] at hh
  have hh0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) hh
  norm_num at hh0

theorem h_product_step (a b : ℕ) :
    h (a + 1) * h (b + 1) = h (a + b + 2) + V * h a * h b := by
  have hc : (S - T) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr S_ne_T)
  apply mul_left_cancel₀ hc
  have ha := h_difference a
  have hb := h_difference b
  have has := h_difference (a + 1)
  have hbs := h_difference (b + 1)
  have hab := h_difference (a + b + 2)
  rw [pow_two]
  calc
    (S-T)*(S-T)*(h (a+1)*h (b+1)) =
        ((S-T)*h (a+1))*((S-T)*h (b+1)) := by ring
    _ = (S^(a+2)-T^(a+2))*(S^(b+2)-T^(b+2)) := by rw [has,hbs]
    _ = (S-T)*(S^(a+b+3)-T^(a+b+3)) +
        V*(S^(a+1)-T^(a+1))*(S^(b+1)-T^(b+1)) := by
      unfold V
      simp only [pow_add, pow_succ]
      ring
    _ = (S-T)*(S-T)*(h (a+b+2)+V*h a*h b) := by
      rw [← hab, ← ha, ← hb]
      ring

theorem schurPositive_h (a : ℕ) : SchurPositive (h a) := by
  simpa using SchurPositive.basis a 0

theorem schurPositive_one : SchurPositive 1 := by simpa using schurPositive_h 0

theorem schurPositive_U : SchurPositive U := by simpa using schurPositive_h 1

theorem schurPositive_V : SchurPositive V := by simpa using SchurPositive.basis 0 1

theorem schurPositive_add {f g : Poly} (hf : SchurPositive f) (hg : SchurPositive g) :
    SchurPositive (f + g) := SchurPositive.add hf hg

theorem schurPositive_scale (c : ℝ) (hc : 0 ≤ c) {f : Poly} (hf : SchurPositive f) :
    SchurPositive (C c * f) := SchurPositive.scale c hc hf

theorem schurPositive_sum {ι : Type*} (s : Finset ι) (f : ι → Poly)
    (hf : ∀ i ∈ s, SchurPositive (f i)) : SchurPositive (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SchurPositive.zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact SchurPositive.add (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem h_product (a b : ℕ) :
    h a * h b = ∑ r ∈ Finset.range (min a b + 1), V ^ r * h (a + b - 2 * r) := by
  induction a generalizing b with
  | zero => simp [h_zero]
  | succ a ih =>
    cases b with
    | zero => simp [h_zero]
    | succ b =>
      rw [h_product_step, mul_assoc V (h a) (h b), ih]
      have hm : min (a+1) (b+1) = min a b+1 := by omega
      rw [hm]
      conv_rhs => rw [Finset.sum_range_succ']
      have hsum : a+1+(b+1) = a+b+2 := by omega
      rw [hsum]
      simp only [pow_zero, one_mul]
      rw [add_comm (∑ r ∈ range (min a b+1), V^(r+1)*h (a+b+2-2*(r+1)))]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      have hn : a + b + 2 - 2 * (r + 1) = a + b - 2 * r := by omega
      rw [hn, pow_succ]
      ring

theorem schurPositive_mul_V_pow (b : ℕ) {f : Poly} (hf : SchurPositive f) :
    SchurPositive (V ^ b * f) := by
  induction hf with
  | basis a d =>
    have heq : V ^ b * (V ^ d * h a) = V ^ (b+d) * h a := by rw [pow_add]; ring
    rw [heq]
    exact SchurPositive.basis a (b+d)
  | zero => simpa using SchurPositive.zero
  | @add f g hf hg ihf ihg =>
    simpa [mul_add] using SchurPositive.add ihf ihg
  | @scale c f hc hf ih =>
    have heq : V^b*(C c*f) = C c*(V^b*f) := by ring
    rw [heq]
    exact SchurPositive.scale c hc ih

theorem schurPositive_h_product (a b : ℕ) : SchurPositive (h a * h b) := by
  rw [h_product]
  apply schurPositive_sum
  intro r hr
  exact SchurPositive.basis _ r

theorem schurPositive_mul {f g : Poly} (hf : SchurPositive f) (hg : SchurPositive g) :
    SchurPositive (f*g) := by
  induction hf with
  | basis a b =>
    induction hg with
    | basis c d =>
      have heq : (V^b*h a)*(V^d*h c) = V^(b+d)*(h a*h c) := by rw [pow_add]; ring
      rw [heq]
      exact schurPositive_mul_V_pow _ (schurPositive_h_product a c)
    | zero => simpa using SchurPositive.zero
    | @add g₁ g₂ hg₁ hg₂ ih₁ ih₂ => simpa [mul_add] using SchurPositive.add ih₁ ih₂
    | @scale c g hc hg ih =>
      have heq : (V^b*h a)*(C c*g) = C c*((V^b*h a)*g) := by ring
      rw [heq]
      exact SchurPositive.scale c hc ih
  | zero => simpa using SchurPositive.zero
  | @add f₁ f₂ hf₁ hf₂ ih₁ ih₂ => simpa [add_mul] using SchurPositive.add ih₁ ih₂
  | @scale c f hc hf ih =>
    have heq : (C c*f)*g = C c*(f*g) := by ring
    rw [heq]
    exact SchurPositive.scale c hc ih

theorem schurPositive_pow {f : Poly} (hf : SchurPositive f) (n : ℕ) :
    SchurPositive (f^n) := by
  induction n with
  | zero => simpa using schurPositive_one
  | succ n ih => simpa [pow_succ] using schurPositive_mul ih hf

abbrev coeff (e : Fin 2 →₀ ℕ) (f : Poly) : ℝ := f.coeff e

@[simp] theorem coeff_add (e : Fin 2 →₀ ℕ) (f g : Poly) : coeff e (f+g) = coeff e f+coeff e g := by simp [coeff]
@[simp] theorem coeff_sub (e : Fin 2 →₀ ℕ) (f g : Poly) : coeff e (f-g) = coeff e f-coeff e g := by simp [coeff]
@[simp] theorem coeff_zero (e : Fin 2 →₀ ℕ) : coeff e (0 : Poly) = 0 := by simp [coeff]
@[simp] theorem coeff_C_mul (e : Fin 2 →₀ ℕ) (c : ℝ) (f : Poly) : coeff e (C c*f) = c*coeff e f := by simp [coeff]
theorem coeff_monomial (e d : Fin 2 →₀ ℕ) (c : ℝ) : coeff e (monomial d c) = if d=e then c else 0 := MvPolynomial.coeff_monomial e d c

theorem coeff_X_mul (e : Fin 2 →₀ ℕ) (i : Fin 2) (f : Poly) : coeff (e+Finsupp.single i 1) (X i*f) = coeff e f := by
  change (X i*f).coeff (e+Finsupp.single i 1) = f.coeff e
  rw [add_comm e, MvPolynomial.coeff_X_mul]

def exponent (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem exponent_zero (a b : ℕ) : exponent a b 0 = a := by simp [exponent]
@[simp] theorem exponent_one (a b : ℕ) : exponent a b 1 = b := by simp [exponent]

theorem exponent_injective {a b c d : ℕ} : exponent a b = exponent c d ↔ a=c ∧ b=d := by
  constructor
  · intro he
    exact ⟨by simpa using congrArg (fun e => e 0) he, by simpa using congrArg (fun e => e 1) he⟩
  · rintro ⟨rfl,rfl⟩
    rfl

theorem power_monomial (a b : ℕ) : S^a*T^b = monomial (exponent a b) (1 : ℝ) := by
  rw [S, T, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial]
  simp [exponent]

theorem coefficient_difference_nonnegative {f : Poly} (hf : SchurPositive f)
    (a b : ℕ) (hab : b ≤ a) :
    0 ≤ coeff (exponent (a+1) b) ((S-T)*f) := by
  induction hf with
  | basis c d =>
    have heq : (S-T)*(V^d*h c) = S^(d+c+1)*T^d - S^d*T^(d+c+1) := by
      calc
        (S-T)*(V^d*h c) = V^d*((S-T)*h c) := by ring
        _ = V^d*(S^(c+1)-T^(c+1)) := by rw [h_difference]
        _ = S^(d+c+1)*T^d - S^d*T^(d+c+1) := by
          unfold V
          rw [mul_pow]
          simp only [pow_add, pow_succ]
          ring
    rw [heq, coeff_sub, power_monomial, power_monomial]
    have hne : exponent d (d+c+1) ≠ exponent (a+1) b := by
      intro he
      have he' := exponent_injective.mp he
      omega
    simp only [coeff_monomial, hne, ite_false, sub_zero]
    split_ifs <;> norm_num
  | zero => simp
  | @add f g hf hg ihf ihg => simpa [mul_add, coeff_add] using add_nonneg ihf ihg
  | @scale c f hc hf ih =>
    have heq : (S-T)*(C c*f) = C c*((S-T)*f) := by ring
    rw [heq, coeff_C_mul]
    exact mul_nonneg hc ih

theorem diagonal_difference_nonnegative {f : Poly} (hf : SchurPositive f)
    (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ coeff (exponent k k) f - coeff (exponent (k+1) (k-1)) f := by
  have hp := coefficient_difference_nonnegative hf k k (le_refl k)
  have hs : exponent (k+1) k = exponent k k + Finsupp.single 0 1 := by
    ext i
    fin_cases i <;> simp [exponent]
  have ht : exponent (k+1) k = exponent (k+1) (k-1) + Finsupp.single 1 1 := by
    ext i
    (fin_cases i <;> simp [exponent]); omega
  rw [sub_mul, coeff_sub] at hp
  have hsc : coeff (exponent (k+1) k) (S*f) = coeff (exponent k k) f := by
    rw [hs, S, coeff_X_mul]
  have htc : coeff (exponent (k+1) k) (T*f) = coeff (exponent (k+1) (k-1)) f := by
    rw [ht, T, coeff_X_mul]
  rwa [hsc, htc] at hp

def schurTerm (x : ℝ × (ℕ × ℕ)) : Poly := C x.1 * (V ^ x.2.2 * h x.2.1)

theorem schurPositive_iff_finite_sum (f : Poly) :
    SchurPositive f ↔ ∃ l : List (ℝ × (ℕ × ℕ)),
      (∀ x ∈ l, 0 ≤ x.1) ∧ f = (l.map schurTerm).sum := by
  constructor
  · intro hf
    induction hf with
    | basis a b => exact ⟨[(1,(a,b))], by simp, by simp [schurTerm]⟩
    | zero => exact ⟨[], by simp, by simp⟩
    | @add f g hf hg ihf ihg =>
      obtain ⟨l,hl,rfl⟩ := ihf
      obtain ⟨m,hm,rfl⟩ := ihg
      exact ⟨l++m, by simpa using fun x hx => (List.mem_append.mp hx).elim (hl x) (hm x),
        by simp⟩
    | @scale c f hc hf ih =>
      obtain ⟨l,hl,rfl⟩ := ih
      refine ⟨l.map (fun x => (c*x.1,x.2)), ?_, ?_⟩
      · intro x hx
        obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
        exact mul_nonneg hc (hl y hy)
      · rw [List.map_map]
        simp only [Function.comp_def, schurTerm, C_mul]
        simp only [mul_assoc]
        rw [List.sum_map_mul_left]
        rfl
  · rintro ⟨l,hl,rfl⟩
    induction l with
    | nil => simpa using SchurPositive.zero
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons]
      apply SchurPositive.add
      · exact SchurPositive.scale x.1 (hl x (by simp)) (SchurPositive.basis x.2.1 x.2.2)
      · exact ih (fun y hy => hl y (by simp [hy]))

def color (c : Bool) : Poly := if c then S else T

def edgeWeight (coupling : ℝ) (a b : Bool) : ℝ := if a=b then coupling else 1

def isingChain (n : ℕ) (coupling : Fin (n-1) → ℝ) : Poly :=
  ∑ χ : Fin n → Bool,
    (∏ i : Fin n, color (χ i)) *
      C (∏ e : Fin (n-1), edgeWeight (coupling e)
        (χ ⟨e.val, by omega⟩) (χ ⟨e.val+1, by omega⟩))

@[simp] theorem isingChain_zero (coupling : Fin (0-1) → ℝ) : isingChain 0 coupling = 1 := by
  simp [isingChain]

@[simp] theorem isingChain_one (coupling : Fin (1-1) → ℝ) : isingChain 1 coupling = U := by
  simp only [isingChain, Fintype.prod_unique, Fin.default_eq_zero, Fin.isValue]
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp [Equiv.funUnique, color, U]

end R34








