import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ext

namespace R34

/-- The five entries of a matrix invariant under exchange of the two colors. -/
@[ext] structure Kernel where
  d : ℝ
  p : ℝ
  q : ℝ
  a : ℝ
  b : ℝ

namespace Kernel

def entry (K : Kernel) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![K.d, K.p, K.p], ![K.q, K.a, K.b], ![K.q, K.b, K.a]]

def mul (K L : Kernel) : Kernel :=
  ⟨K.d * L.d + 2 * K.p * L.q,
   K.d * L.p + K.p * (L.a + L.b),
   K.q * L.d + (K.a + K.b) * L.q,
   K.q * L.p + K.a * L.a + K.b * L.b,
   K.q * L.p + K.a * L.b + K.b * L.a⟩

instance instMulKernel : Mul Kernel := ⟨mul⟩

@[simp] theorem mul_d (K L : Kernel) : (K * L).d = K.d * L.d + 2 * K.p * L.q := rfl
@[simp] theorem mul_p (K L : Kernel) : (K * L).p = K.d * L.p + K.p * (L.a + L.b) := rfl
@[simp] theorem mul_q (K L : Kernel) : (K * L).q = K.q * L.d + (K.a + K.b) * L.q := rfl
@[simp] theorem mul_a (K L : Kernel) : (K * L).a = K.q * L.p + K.a * L.a + K.b * L.b := rfl
@[simp] theorem mul_b (K L : Kernel) : (K * L).b = K.q * L.p + K.a * L.b + K.b * L.a := rfl

def transpose (K : Kernel) : Kernel := ⟨K.d, K.q, K.p, K.a, K.b⟩
def w (K : Kernel) : ℝ := K.a + K.b
def g (K : Kernel) : ℝ := K.a - K.b
def act (K : Kernel) (v : ℝ × ℝ) : ℝ × ℝ :=
  (K.d * v.1 + 2 * K.p * v.2, K.q * v.1 + K.w * v.2)

theorem entry_eq_ite (K : Kernel) : K.entry = fun i j =>
    if i = 0 then (if j = 0 then K.d else K.p)
    else if j = 0 then K.q else if i = j then K.a else K.b := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem entry_mul (K L : Kernel) : (K * L).entry = K.entry * L.entry := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [entry_eq_ite, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp <;> ring

def embed (v : ℝ × ℝ) : Fin 3 → ℝ := ![v.1, v.2, v.2]

theorem embed_eq_ite (v : ℝ × ℝ) : embed v = fun i =>
    if i = 0 then v.1 else v.2 := by
  funext i
  fin_cases i <;> rfl

theorem entry_act (K : Kernel) (v : ℝ × ℝ) :
    K.entry.mulVec (embed v) = embed (K.act v) := by
  ext i
  simp only [entry_eq_ite, embed_eq_ite, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  fin_cases i <;> simp [act, w] <;> ring

theorem entry_transpose (K : Kernel) : K.transpose.entry = K.entry.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem mul_assoc (K L M : Kernel) : (K * L) * M = K * (L * M) := by
  ext <;> simp <;> ring

theorem transpose_mul (K L : Kernel) : (K * L).transpose = L.transpose * K.transpose := by
  ext <;> simp [transpose] <;> ring

theorem act_mul (K L : Kernel) (v : ℝ × ℝ) : (K * L).act v = K.act (L.act v) := by
  ext <;> simp [act, w] <;> ring

def C : Kernel := ⟨1, 1, 1, 0, 1⟩
def B : Kernel := ⟨6, 0, 0, 0, -1⟩
def identity : Kernel := ⟨1, 0, 0, 1, 0⟩

@[simp] theorem identity_mul (K : Kernel) : identity * K = K := by
  ext <;> simp [identity]

@[simp] theorem mul_identity (K : Kernel) : K * identity = K := by
  ext <;> simp [identity]

instance instMonoidKernel : Monoid Kernel where
  one := identity
  mul := mul
  one_mul := identity_mul
  mul_one := mul_identity
  mul_assoc := mul_assoc

@[simp] theorem one_d : (1 : Kernel).d = 1 := rfl
@[simp] theorem one_p : (1 : Kernel).p = 0 := rfl
@[simp] theorem one_q : (1 : Kernel).q = 0 := rfl
@[simp] theorem one_a : (1 : Kernel).a = 1 := rfl
@[simp] theorem one_b : (1 : Kernel).b = 0 := rfl

@[simp] theorem entry_one : (1 : Kernel).entry = 1 := by
  change identity.entry = (1 : Matrix (Fin 3) (Fin 3) ℝ)
  rw [entry_eq_ite]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [identity, Matrix.one_apply]

def cPower : ℕ → Kernel
  | 0 => identity
  | n+1 => C * cPower n

@[simp] theorem cPower_one : cPower 1 = C := by simp [cPower]

theorem cPower_succ_right (n : ℕ) : cPower (n+1) = cPower n * C := by
  induction n with
  | zero => simp [cPower]
  | succ n ih =>
    change C * cPower (n+1) = (C * cPower n) * C
    rw [ih]
    exact (mul_assoc C (cPower n) C).symm

theorem entry_identity : identity.entry = 1 := by
  exact entry_one

theorem entry_cPower (n : ℕ) : (cPower n).entry = C.entry ^ n := by
  induction n with
  | zero => simp [cPower, entry_identity]
  | succ n ih => rw [cPower, entry_mul, ih, pow_succ']


theorem C_act (v : ℝ × ℝ) : C.act v = (v.1 + 2 * v.2, v.1 + v.2) := by
  ext <;> simp [C, act, w]

theorem CB_act (v : ℝ × ℝ) : (C * B).act v = (6 * v.1 - 2 * v.2, 6 * v.1 - v.2) := by
  ext <;> simp [C, B, act, w] <;> ring

@[simp] theorem C_transpose : C.transpose = C := rfl
@[simp] theorem B_transpose : B.transpose = B := rfl

theorem cPower_transpose (n : ℕ) : (cPower n).transpose = cPower n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cPower, transpose_mul, ih, C_transpose, ← cPower_succ_right]; rfl

def pairDot (v u : ℝ × ℝ) : ℝ := v.1 * u.1 + 2 * v.2 * u.2

theorem pairDot_act (K : Kernel) (v u : ℝ × ℝ) :
    pairDot v (K.act u) = pairDot (K.transpose.act v) u := by
  dsimp [pairDot, act, transpose, w]
  ring

theorem embed_dot (v u : ℝ × ℝ) : dotProduct (embed v) (embed u) = pairDot v u := by
  simp only [embed_eq_ite, dotProduct, Fin.sum_univ_three]
  simp [pairDot]
  ring

end Kernel

open Kernel

/-- Exactly the products with positive neutral gaps, indexed by the number of B factors. -/
inductive Contracted : ℕ → Kernel → Prop
  | base : Contracted 0 C
  | neutral {r K} : Contracted r K → Contracted r (C * K)
  | pair {r K} : Contracted r K → Contracted (r + 1) ((C * B) * K)

theorem Contracted.right_neutral {r K} (h : Contracted r K) : Contracted r (K * C) := by
  induction h with
  | base => exact Contracted.neutral Contracted.base
  | neutral h ih => rw [Kernel.mul_assoc]; exact Contracted.neutral ih
  | pair h ih => rw [Kernel.mul_assoc]; exact Contracted.pair ih

theorem Contracted.right_pair {r K} (h : Contracted r K) : Contracted (r + 1) ((K * B) * C) := by
  induction h with
  | base => exact Contracted.pair Contracted.base
  | neutral h ih => simpa only [Kernel.mul_assoc] using Contracted.neutral ih
  | pair h ih => simpa only [Kernel.mul_assoc] using Contracted.pair ih

theorem Contracted.transpose {r K} (h : Contracted r K) : Contracted r K.transpose := by
  induction h with
  | base => simpa using Contracted.base
  | neutral h ih => simpa [Kernel.transpose_mul] using ih.right_neutral
  | pair h ih => simpa [Kernel.transpose_mul, Kernel.mul_assoc] using ih.right_pair

theorem Contracted.prefix_neutral {r K} (h : Contracted r K) (n : ℕ) :
    Contracted r (cPower n * K) := by
  induction n with
  | zero => simpa [cPower] using h
  | succ n ih => simpa [cPower, Kernel.mul_assoc] using Contracted.neutral ih

theorem cPower_contracted (n : ℕ) : Contracted 0 (cPower (n+1)) := by
  rw [cPower_succ_right]
  exact Contracted.base.prefix_neutral n

theorem Contracted.prefix_pair {r K} (h : Contracted r K) (n : ℕ) :
    Contracted (r+1) ((cPower (n+1) * B) * K) := by
  have hh := (Contracted.pair h).prefix_neutral n
  simpa [cPower_succ_right, Kernel.mul_assoc] using hh

/-- Every exponent in a contracted kernel is represented by its predecessor. -/
def kernelWord (first : ℕ) : List ℕ → Kernel
  | [] => cPower (first+1)
  | n :: ns => (cPower (first+1) * B) * kernelWord n ns

theorem kernelWord_contracted (first : ℕ) (gaps : List ℕ) :
    Contracted gaps.length (kernelWord first gaps) := by
  induction gaps generalizing first with
  | nil => exact cPower_contracted first
  | cons n ns ih => exact (ih n).prefix_pair first

def IntegralKernel (K : Kernel) : Prop :=
  ∃ d p q a b : ℤ, K = ⟨d, p, q, a, b⟩

theorem integral_mul {K L : Kernel} (hK : IntegralKernel K)
    (hL : IntegralKernel L) : IntegralKernel (K * L) := by
  rcases hK with ⟨d,p,q,a,b,rfl⟩
  rcases hL with ⟨e,u,v,c,f,rfl⟩
  refine ⟨d*e+2*p*v, d*u+p*(c+f), q*e+(a+b)*v,
    q*u+a*c+b*f, q*u+a*f+b*c, ?_⟩
  ext <;> simp [Int.cast_add, Int.cast_mul]

theorem Contracted.integral {r K} (h : Contracted r K) : IntegralKernel K := by
  have hC : IntegralKernel C := ⟨1,1,1,0,1,by norm_num [C]⟩
  have hB : IntegralKernel B := ⟨6,0,0,0,-1,by norm_num [B]⟩
  induction h with
  | base => exact hC
  | neutral h ih => exact integral_mul hC ih
  | pair h ih => exact integral_mul (integral_mul hC hB) ih

def Cone (v : ℝ × ℝ) : Prop := 0 < v.1 ∧ 0 ≤ v.2 ∧ 2 * v.2 ≤ 3 * v.1

theorem cone_C {v : ℝ × ℝ} (h : Cone v) :
    Cone (C.act v) ∧ v.1 ≤ (C.act v).1 ∧ v.2 ≤ (C.act v).2 := by
  rw [C_act]
  rcases h with ⟨hA, hH, hi⟩
  dsimp [Cone]
  constructor
  · exact ⟨by linarith, by linarith, by linarith⟩
  · constructor <;> linarith

theorem cone_CB {v : ℝ × ℝ} (h : Cone v) :
    Cone ((C * B).act v) ∧ 3 * v.1 ≤ ((C * B).act v).1 ∧
      v.2 ≤ ((C * B).act v).2 := by
  rw [CB_act]
  rcases h with ⟨hA, hH, hi⟩
  dsimp [Cone]
  constructor
  · exact ⟨by linarith, by linarith, by linarith⟩
  · constructor <;> linarith

theorem Contracted.cone {r K} (h : Contracted r K) {v : ℝ × ℝ} (hv : Cone v) :
    Cone (K.act v) := by
  induction h with
  | base => exact (cone_C hv).1
  | neutral h ih => rw [act_mul]; exact (cone_C ih).1
  | pair h ih => rw [act_mul]; exact (cone_CB ih).1

theorem Contracted.first_column {r K} (h : Contracted r K) :
    Cone (K.d, K.q) ∧ 1 ≤ K.d ∧ 1 ≤ K.q ∧
      ((K.d = 1 ∧ K.q = 1) ∨ 3 ≤ K.d) ∧ (0 < r → 5 ≤ K.q) := by
  induction h with
  | base => norm_num [Cone, C]
  | @neutral r K h ih =>
    rcases ih with ⟨hc, hd, hq, hs, h5⟩
    have he := cone_C hc
    simp only [C_act] at he
    simp only [mul_d, mul_q, C, Cone] at *
    refine ⟨?_, by linarith, by linarith, Or.inr (by linarith), ?_⟩
    · rcases he.1 with ⟨h1,h2,h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
    intro hr
    have := h5 hr
    linarith
  | @pair r K h ih =>
    rcases ih with ⟨hc, hd, hq, hs, h5⟩
    have he := cone_CB hc
    simp only [CB_act] at he
    have hq5 : 5 ≤ 6 * K.d - K.q := by
      rcases hs with ⟨hd1, hq1⟩ | hd3
      · rw [hd1, hq1]; norm_num
      · rcases hc with ⟨_, _, hi⟩; linarith
    simp only [mul_d, mul_p, mul_q, mul_a, mul_b, C, B, Cone] at *
    refine ⟨?_, ?_, ?_, Or.inr ?_, ?_⟩
    · rcases he.1 with ⟨h1,h2,h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
    · linarith
    · linarith
    · linarith
    · intro _; linarith

theorem Contracted.second_column {r K} (h : Contracted r K) :
    Cone (2 * K.p, K.w) ∧ 2 ≤ 2 * K.p ∧ 1 ≤ K.w ∧
      ((2 * K.p = 2 ∧ K.w = 1) ∨ 4 ≤ 2 * K.p) ∧ (0 < r → 11 ≤ K.w) := by
  induction h with
  | base => norm_num [Cone, C, w]
  | @neutral r K h ih =>
    rcases ih with ⟨hc, hp, hw, hs, h11⟩
    have he := cone_C hc
    simp only [C_act] at he
    simp only [mul_p, mul_a, mul_b, C, Cone, w] at *
    refine ⟨?_, by linarith, by linarith, Or.inr (by linarith), ?_⟩
    · rcases he.1 with ⟨h1,h2,h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
    · intro hr; have := h11 hr; linarith
  | @pair r K h ih =>
    rcases ih with ⟨hc, hp, hw, hs, h11⟩
    have he := cone_CB hc
    simp only [CB_act] at he
    have hw11 : 11 ≤ 12 * K.p - K.w := by
      rcases hs with ⟨hp2, hw1⟩ | hp4
      · rw [show 12 * K.p = 6 * (2 * K.p) by ring, hp2, hw1]; norm_num
      · rcases hc with ⟨_, _, hi⟩; linarith
    simp only [mul_d, mul_p, mul_q, mul_a, mul_b, C, B, Cone, w] at *
    refine ⟨?_, ?_, ?_, Or.inr ?_, ?_⟩
    · rcases he.1 with ⟨h1,h2,h3⟩; exact ⟨by linarith, by linarith, by linarith⟩
    · linarith [he.2.1]
    · linarith
    · linarith [he.2.1]
    · intro _; linarith

theorem Contracted.delta {r K} (h : Contracted r K) (hr : 0 < r) :
    3 ≤ 8 * K.d - 4 * K.p - 4 * K.q + K.w := by
  have hx : Cone (K.act (4, -1)) ∧ 2 ≤ (K.act (4, -1)).1 ∧
      (0 < r → 6 ≤ (K.act (4, -1)).1) := by
    clear hr
    induction h with
    | base => norm_num [Cone, act, C, w]
    | @neutral r K h ih =>
      rcases ih with ⟨hc, h2, h6⟩
      rw [act_mul]
      have he := cone_C hc
      exact ⟨he.1, by linarith [he.2.1], fun hr => by linarith [h6 hr, he.2.1]⟩
    | @pair r K h ih =>
      rcases ih with ⟨hc, h2, _⟩
      rw [act_mul]
      have he := cone_CB hc
      exact ⟨he.1, by linarith [he.2.1], fun _ => by linarith [he.2.1]⟩
  rcases hx with ⟨hc, _, h6⟩
  have := h6 hr
  dsimp [Cone, act] at *
  rcases hc with ⟨_, _, hi⟩
  linarith

def IsSign (x : ℝ) : Prop := x = -1 ∨ x = 1

theorem Contracted.sign {r K} (h : Contracted r K) : IsSign K.g := by
  induction h with
  | base => exact Or.inl (by norm_num [g, C])
  | neutral h ih =>
    rcases ih with hh | hh
    · exact Or.inr (by simp only [mul_a, mul_b, g, C] at *; linarith)
    · exact Or.inl (by simp only [mul_a, mul_b, g, C] at *; linarith)
  | pair h ih =>
    rcases ih with hh | hh
    · exact Or.inr (by simp only [mul_q, mul_a, mul_b, g, C, B] at *; linarith)
    · exact Or.inl (by simp only [mul_q, mul_a, mul_b, g, C, B] at *; linarith)

structure NeutralBounds (K : Kernel) : Prop where
  pq : K.p = K.q
  dw : K.d = K.w
  p_one : 1 ≤ K.p
  pd : K.p ≤ K.d
  a_zero : 0 ≤ K.a
  b_one : 1 ≤ K.b
  ap : K.a ≤ K.p
  bp : K.b ≤ K.p

theorem Contracted.neutral_bounds {K} (h : Contracted 0 K) : NeutralBounds K := by
  have aux {r K} (hh : Contracted r K) : r = 0 → NeutralBounds K := by
    induction hh with
    | base => intro _; constructor <;> norm_num [C, w]
    | neutral h ih =>
      intro he
      have hb := ih he
      rcases hb with ⟨hpq, hdw, hp1, hpd, ha0, hb1, hap, hbp⟩
      dsimp [w] at hdw
      constructor <;> simp only [mul_d, mul_p, mul_q, mul_a, mul_b, C, w] <;> linarith
    | pair h ih => intro he; omega
  exact aux h rfl

def theta (K : Kernel) (ε : ℝ) : ℝ := K.b + K.g * ε
def thetaPrime (K : Kernel) (ε : ℝ) : ℝ := K.a - K.g * ε

/-- The four inequalities used by the signed boundary transfer. -/
structure KernelIneq (K : Kernel) (ε : ℝ) : Prop where
  p_pos : 0 < K.p
  q_pos : 0 < K.q
  p_lt : K.p < 2 * K.d
  q_lt : K.q < 2 * K.d
  theta_nonneg : 0 ≤ theta K ε
  theta_p : theta K ε ≤ 2 * K.p
  theta_q : theta K ε ≤ 2 * K.q
  prime_p_lower : -K.p ≤ thetaPrime K ε
  prime_q_lower : -K.q ≤ thetaPrime K ε
  prime_p_upper : thetaPrime K ε ≤ 2 * K.p
  prime_q_upper : thetaPrime K ε ≤ 2 * K.q
  four : 0 ≤ 4 * K.d - 2 * K.p - 2 * K.q + theta K ε

theorem Contracted.inequalities {r K} (h : Contracted r K) {ε : ℝ}
    (hε : IsSign ε) : KernelIneq K ε := by
  have hf := h.first_column
  have ht := h.transpose.first_column
  have hs := h.second_column
  have hst := h.transpose.second_column
  have hg := h.sign
  by_cases hr : r = 0
  · subst r
    have hn := h.neutral_bounds
    rcases hn with ⟨hpq, hdw, hp1, hpd, ha0, hb1, hap, hbp⟩
    rcases hg with hg | hg <;> rcases hε with hε | hε <;>
      constructor <;> (try simp only [theta, thetaPrime, hg, hε]) <;> linarith
  · have hrp : 0 < r := Nat.pos_of_ne_zero hr
    have hdel := h.delta hrp
    rcases hf with ⟨⟨hd0,hq0,hqd⟩, hd1, hq1, _, hq5⟩
    rcases ht with ⟨⟨_,hp0,hpd⟩, _, hp1, _, hp5⟩
    rcases hs with ⟨⟨_,_,hwp⟩, _, _, _, hw11⟩
    rcases hst with ⟨⟨_,_,hwq⟩, _, _, _, _⟩
    have hq := hq5 hrp
    have hp := hp5 hrp
    have hw := hw11 hrp
    dsimp [Kernel.transpose] at hpd hp0 hp1 hp hwq
    dsimp [w, g] at *
    rcases hg with hg | hg <;> rcases hε with hε | hε <;>
      constructor <;> (try simp only [theta, thetaPrime, g, hε]) <;> linarith

/-- A free vector has no required neutral factor at its final end. -/
inductive Free : ℝ × ℝ → Prop
  | one : Free (1, 1)
  | neutral {v} : Free v → Free (C.act v)
  | pair {v} : Free v → Free ((C * B).act v)

theorem Free.bounds {v} (h : Free v) : Cone v ∧ 0 < v.2 := by
  induction h with
  | one => norm_num [Cone]
  | neutral h ih =>
    have he := cone_C ih.1
    refine ⟨he.1, ?_⟩
    rw [C_act]
    rcases ih with ⟨⟨hA,_,_⟩,hH⟩; dsimp; linarith
  | pair h ih =>
    have he := cone_CB ih.1
    refine ⟨he.1, ?_⟩
    rw [CB_act]
    rcases ih with ⟨⟨hA,_,hi⟩,hH⟩; dsimp; linarith

def cVector : ℕ → ℝ × ℝ
  | 0 => (1,1)
  | n+1 => C.act (cVector n)

theorem cPower_act_one (n : ℕ) : (cPower n).act (1,1) = cVector n := by
  induction n with
  | zero => norm_num [cPower, cVector, identity, act, w]
  | succ n ih => rw [cPower, act_mul, ih, cVector]

theorem Free.cPower {v : ℝ × ℝ} (h : Free v) (n : ℕ) : Free ((cPower n).act v) := by
  induction n with
  | zero => simpa [Kernel.cPower, identity, act, w] using h
  | succ n ih => rw [Kernel.cPower, act_mul]; exact Free.neutral ih

/-- A free product has positive gaps before B and an arbitrary final neutral gap. -/
def freeWord : List ℕ → ℕ → ℝ × ℝ
  | [], last => cVector last
  | n :: ns, last => ((cPower (n+1) * B).act (freeWord ns last))

def freeKernel : List ℕ → ℕ → Kernel
  | [], last => cPower last
  | n :: ns, last => (cPower (n+1) * B) * freeKernel ns last

theorem freeKernel_act (gaps : List ℕ) (last : ℕ) :
    (freeKernel gaps last).act (1,1) = freeWord gaps last := by
  induction gaps with
  | nil => exact cPower_act_one last
  | cons n ns ih => rw [freeKernel, Kernel.act_mul, ih, freeWord]

theorem freeWord_free (gaps : List ℕ) (last : ℕ) : Free (freeWord gaps last) := by
  induction gaps with
  | nil => simpa [freeWord, ← cPower_act_one] using Free.one.cPower last
  | cons n ns ih =>
    have hh := (Free.pair ih).cPower n
    simpa [freeWord, cPower_succ_right, act_mul, Kernel.mul_assoc] using hh

theorem cVector_bounds (n : ℕ) : 0 < (cVector n).1 ∧
    0 < (cVector n).2 ∧ (cVector n).2 ≤ (cVector n).1 := by
  induction n with
  | zero => norm_num [cVector]
  | succ n ih =>
    rw [cVector, C_act]
    dsimp
    exact ⟨by linarith [ih.1,ih.2.1], by linarith [ih.1,ih.2.1], by linarith [ih.2.1]⟩

theorem free_boundary {v} (h : Free v) :
    0 < v.1 ∧ -v.1 ≤ v.2 ∧ v.2 ≤ 2 * v.1 := by
  rcases h.bounds with ⟨⟨hA,hH,hi⟩,_⟩
  exact ⟨hA, by linarith, by linarith⟩

theorem scalar_positive (n : ℕ) {v} (h : Free v) :
    0 < 6 * (cVector n).1 * v.1 - 2 * (cVector n).2 * v.2 := by
  rcases cVector_bounds n with ⟨hf0,hf1,hf⟩
  rcases h.bounds with ⟨⟨hA,hH,hi⟩,_⟩
  have hprod : (cVector n).2 * v.2 ≤ (cVector n).1 * v.2 :=
    mul_le_mul_of_nonneg_right hf hH
  have hprod2 : 2 * ((cVector n).1 * v.2) ≤ 3 * ((cVector n).1 * v.1) := by
    nlinarith [mul_le_mul_of_nonneg_left hi hf0.le]
  have hpos := mul_pos hf0 hA
  nlinarith

theorem scalar_without_pair_positive (n : ℕ) :
    0 < (cVector n).1 + 2 * (cVector n).2 := by
  have h := cVector_bounds n
  linarith [h.1,h.2.1]

theorem scalar_without_pair_matrix_positive (n : ℕ) :
    0 < dotProduct (Kernel.embed (1,1)) ((cPower n).entry.mulVec (Kernel.embed (1,1))) := by
  rw [Kernel.entry_act, Kernel.embed_dot, cPower_act_one]
  simpa [Kernel.pairDot] using scalar_without_pair_positive n

theorem scalar_word_positive (initial last : ℕ) (internal : List ℕ) :
    0 < 6 * (cVector initial).1 * (freeWord internal last).1 -
      2 * (cVector initial).2 * (freeWord internal last).2 :=
  scalar_positive initial (freeWord_free internal last)

theorem scalar_matrix_positive (initial : ℕ) {v : ℝ × ℝ} (hv : Free v) :
    0 < dotProduct (Kernel.embed (1,1))
      (((cPower initial).entry * B.entry).mulVec (Kernel.embed v)) := by
  rw [← Kernel.entry_mul, Kernel.entry_act, Kernel.embed_dot, Kernel.act_mul,
    Kernel.pairDot_act, cPower_transpose, cPower_act_one]
  have he : Kernel.pairDot (cVector initial) (B.act v) =
      6 * (cVector initial).1 * v.1 - 2 * (cVector initial).2 * v.2 := by
    dsimp [Kernel.pairDot, B, Kernel.act, Kernel.w]
    ring
  rw [he]
  exact scalar_positive initial hv

end R34


