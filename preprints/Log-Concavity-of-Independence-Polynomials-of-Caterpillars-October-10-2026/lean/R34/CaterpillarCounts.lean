import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Exact independent-set enumeration for caterpillars with arbitrary pendant counts. -/

namespace R34.CaterpillarCounts

open scoped BigOperators Classical
noncomputable section

abbrev Poly := MvPolynomial (Fin 2) ℝ
abbrev S : Poly := MvPolynomial.X 0
abbrev T : Poly := MvPolynomial.X 1
abbrev V : Poly := S * T
abbrev U : Poly := S + T

abbrev Vertex (n : ℕ) (m : Fin n → ℕ) := Fin n ⊕ (Σ i : Fin n, Fin (m i))

def Adj {n : ℕ} {m : Fin n → ℕ} : Vertex n m → Vertex n m → Prop
  | .inl i, .inl j => i.val + 1 = j.val ∨ j.val + 1 = i.val
  | .inl i, .inr l => i = l.1
  | .inr l, .inl i => l.1 = i
  | .inr _, .inr _ => False

def graph (n : ℕ) (m : Fin n → ℕ) : SimpleGraph (Vertex n m) where
  Adj := Adj
  symm := by
    constructor
    intro a b h
    cases a <;> cases b <;> simp only [Adj] at *
    · exact h.elim Or.inr Or.inl
    · exact h.symm
    · exact h.symm
  loopless := by
    constructor
    intro a
    cases a <;> simp [Adj]

noncomputable def independentCounts (n : ℕ) (m : Fin n → ℕ) (k : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Vertex n m)).powerset.filter
    (fun (A : Finset (Vertex n m)) =>
      (graph n m).IsIndepSet (A : Set (Vertex n m)) ∧ A.card = k)).card

noncomputable def independencePolynomial (n : ℕ) (m : Fin n → ℕ) (x : Poly) : Poly := by
  classical
  exact ∑ k ∈ Finset.range (Fintype.card (Vertex n m) + 1),
    (independentCounts n m k : Poly) * x ^ k

noncomputable def setPolynomial (n : ℕ) (m : Fin n → ℕ) (x : Poly) : Poly := by
  classical
  exact ∑ A : Finset (Vertex n m),
    if (graph n m).IsIndepSet (A : Set (Vertex n m)) then x ^ A.card else 0

theorem independencePolynomial_eq_setPolynomial (n : ℕ) (m : Fin n → ℕ) (x : Poly) :
    independencePolynomial n m x = setPolynomial n m x := by
  classical
  unfold independencePolynomial independentCounts setPolynomial
  simp only [Finset.powerset_univ, Finset.natCast_card_filter]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  have hc : A.card < Fintype.card (Vertex n m) + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_card (Finset.subset_univ A))
  by_cases h : (graph n m).IsIndepSet (A : Set (Vertex n m))
  · simp only [h, true_and, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_range, hc, ite_true]
  · simp [h]

abbrev Selection (n : ℕ) (m : Fin n → ℕ) :=
  (Fin n → Bool) × (∀ i : Fin n, Finset (Fin (m i)))

noncomputable def assemble {n : ℕ} {m : Fin n → ℕ} (q : Selection n m) :
    Finset (Vertex n m) := by
  classical
  exact Finset.univ.filter (fun v => match v with
    | .inl i => q.1 i = true
    | .inr l => l.2 ∈ q.2 l.1)

@[simp] theorem mem_assemble_spine {n : ℕ} {m : Fin n → ℕ} (q : Selection n m)
    (i : Fin n) : Sum.inl i ∈ assemble q ↔ q.1 i = true := by
  classical
  simp [assemble]

@[simp] theorem mem_assemble_leaf {n : ℕ} {m : Fin n → ℕ} (q : Selection n m)
    (i : Fin n) (l : Fin (m i)) : Sum.inr ⟨i, l⟩ ∈ assemble q ↔ l ∈ q.2 i := by
  classical
  simp [assemble]

noncomputable def selectionEquiv (n : ℕ) (m : Fin n → ℕ) :
    Finset (Vertex n m) ≃ Selection n m := by
  classical
  refine {
    toFun := fun A => (fun i => decide (Sum.inl i ∈ A),
      fun i => Finset.univ.filter (fun l => Sum.inr ⟨i, l⟩ ∈ A))
    invFun := assemble
    left_inv := ?_
    right_inv := ?_ }
  · intro A
    ext v
    cases v with
    | inl i => simp
    | inr l => rcases l with ⟨i, l⟩; simp
  · intro q
    apply Prod.ext
    · funext i
      simp
    · funext i
      ext l
      simp

def SpineValid {n : ℕ} (b : Fin n → Bool) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → b i = false ∨ b j = false

def LeavesValid {n : ℕ} {m : Fin n → ℕ} (q : Selection n m) : Prop :=
  ∀ i : Fin n, q.1 i = true → q.2 i = ∅

theorem assemble_independent_iff {n : ℕ} {m : Fin n → ℕ} (q : Selection n m) :
    (graph n m).IsIndepSet (assemble q : Set (Vertex n m)) ↔
      SpineValid q.1 ∧ LeavesValid q := by
  classical
  rw [SimpleGraph.isIndepSet_iff]
  constructor
  · intro h
    constructor
    · intro i j hij
      by_cases hi : q.1 i = true
      · right
        cases hj : q.1 j with
        | false => rfl
        | true =>
          have hne : (Sum.inl i : Vertex n m) ≠ Sum.inl j := by
            intro he
            have : i = j := Sum.inl.inj he
            subst j
            omega
          exact False.elim (h (mem_assemble_spine q i |>.mpr hi)
            (mem_assemble_spine q j |>.mpr hj) hne (Or.inl hij))
      · left
        cases hb : q.1 i <;> simp_all
    · intro i hi
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro l hl
      exact h (mem_assemble_spine q i |>.mpr hi)
        (mem_assemble_leaf q i l |>.mpr hl) (by simp) (by rfl)
  · rintro ⟨hb, hl⟩ a ha b hc hne hadj
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        have hi : q.1 i = true := (mem_assemble_spine q i).mp ha
        have hj : q.1 j = true := (mem_assemble_spine q j).mp hc
        rcases hadj with hij | hji
        · rcases hb i j hij with h | h <;> simp_all
        · rcases hb j i hji with h | h <;> simp_all
      | inr l =>
        rcases l with ⟨j, l⟩
        change i = j at hadj
        subst j
        have hi : q.1 i = true := (mem_assemble_spine q i).mp ha
        have hh := (mem_assemble_leaf q i l).mp hc
        rw [hl i hi] at hh
        exact Finset.notMem_empty _ hh
    | inr l =>
      cases b with
      | inl i =>
        rcases l with ⟨j, l⟩
        change j = i at hadj
        subst j
        have hi : q.1 i = true := (mem_assemble_spine q i).mp hc
        have hh := (mem_assemble_leaf q i l).mp ha
        rw [hl i hi] at hh
        exact Finset.notMem_empty _ hh
      | inr l' => exact hadj

theorem pow_card_eq_prod {α : Type*} [Fintype α] (A : Finset α) (x : Poly) :
    x ^ A.card = ∏ a : α, if a ∈ A then x else 1 := by
  classical
  simp

theorem assemble_weight {n : ℕ} {m : Fin n → ℕ} (q : Selection n m) (x : Poly) :
    x ^ (assemble q).card =
      ∏ i : Fin n, (if q.1 i = true then x else 1) * x ^ (q.2 i).card := by
  classical
  rw [pow_card_eq_prod, Fintype.prod_sum_type, Fintype.prod_sigma]
  simp only [mem_assemble_spine, mem_assemble_leaf, Finset.prod_ite_mem_eq,
    Finset.prod_const]
  rw [Finset.prod_mul_distrib]

theorem leaf_subset_sum (r : ℕ) (x : Poly) :
    (∑ L : Finset (Fin r), x ^ L.card) = (1 + x) ^ r := by
  classical
  have h := Finset.prod_one_add (f := fun _ : Fin r => x) Finset.univ
  simpa using h.symm

noncomputable def spineSum (n : ℕ) (m : Fin n → ℕ) (x : Poly) : Poly := by
  classical
  exact ∑ b : Fin n → Bool,
    if SpineValid b then ∏ i : Fin n, if b i = true then x else (1 + x) ^ (m i) else 0

theorem leaf_selection_sum {n : ℕ} {m : Fin n → ℕ} (b : Fin n → Bool) (x : Poly) :
    (∑ L : ∀ i : Fin n, Finset (Fin (m i)),
      if LeavesValid (b, L) then
        ∏ i : Fin n, (if b i = true then x else 1) * x ^ (L i).card else 0) =
      ∏ i : Fin n, if b i = true then x else (1 + x) ^ (m i) := by
  classical
  let f (i : Fin n) (L : Finset (Fin (m i))) : Poly :=
    if (b i = true → L = ∅) then (if b i = true then x else 1) * x ^ L.card else 0
  have hL : ∀ L : ∀ i : Fin n, Finset (Fin (m i)),
      (if LeavesValid (b, L) then
        ∏ i : Fin n, (if b i = true then x else 1) * x ^ (L i).card else 0) =
      ∏ i : Fin n, f i (L i) := by
    intro L
    by_cases h : LeavesValid (b, L)
    · simp only [h, ite_true]
      symm
      apply Finset.prod_congr rfl
      intro i hi
      dsimp only [f]
      rw [ite_eq_left (h i)]
    · simp only [h, ite_false]
      have hp : ¬ (∀ i : Fin n, b i = true → L i = ∅) := h
      obtain ⟨i, hi⟩ := not_forall.mp hp
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      dsimp only [f]
      rw [ite_eq_right hi]
  simp_rw [hL]
  rw [← Fintype.prod_sum f]
  apply Finset.prod_congr rfl
  intro i hi
  cases hb : b i
  · simp [f, hb, leaf_subset_sum]
  · simp [f, hb]

theorem independencePolynomial_eq_spineSum (n : ℕ) (m : Fin n → ℕ) (x : Poly) :
    independencePolynomial n m x = spineSum n m x := by
  classical
  rw [independencePolynomial_eq_setPolynomial]
  unfold setPolynomial spineSum
  rw [← (selectionEquiv n m).symm.sum_comp]
  simp only [selectionEquiv, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [assemble_independent_iff, assemble_weight]
  by_cases h : SpineValid b
  · simp only [h, true_and, ite_true]
    exact leaf_selection_sum b x
  · simp [h]

abbrev FourState := Bool × Bool

def Compatible (a b : FourState) : Prop :=
  (a.1 = false ∨ b.1 = false) ∧ (a.2 = false ∨ b.2 = false)

def FourValid {n : ℕ} (w : Fin n → FourState) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val → Compatible (w i) (w j)

def pairStateEquiv (n : ℕ) :
    ((Fin n → Bool) × (Fin n → Bool)) ≃ (Fin n → FourState) where
  toFun q i := (q.1 i, q.2 i)
  invFun w := (fun i => (w i).1, fun i => (w i).2)
  left_inv q := by cases q; rfl
  right_inv w := by funext i; exact Prod.eta _

theorem fourValid_iff {n : ℕ} (w : Fin n → FourState) :
    FourValid w ↔ SpineValid (fun i => (w i).1) ∧ SpineValid (fun i => (w i).2) := by
  constructor
  · intro h
    exact ⟨fun i j hij => (h i j hij).1, fun i j hij => (h i j hij).2⟩
  · rintro ⟨h₁, h₂⟩ i j hij
    exact ⟨h₁ i j hij, h₂ i j hij⟩

def pairWeight (r : ℕ) (a : FourState) (x y : Poly) : Poly :=
  (if a.1 = true then x else (1 + x) ^ r) *
    (if a.2 = true then y else (1 + y) ^ r)

noncomputable def fourStateSum (n : ℕ) (m : Fin n → ℕ) (x y : Poly) : Poly := by
  classical
  exact ∑ w : Fin n → FourState,
    if FourValid w then ∏ i : Fin n, pairWeight (m i) (w i) x y else 0

theorem independencePolynomial_product_eq_fourStateSum
    (n : ℕ) (m : Fin n → ℕ) (x y : Poly) :
    independencePolynomial n m x * independencePolynomial n m y =
      fourStateSum n m x y := by
  classical
  rw [independencePolynomial_eq_spineSum, independencePolynomial_eq_spineSum]
  unfold spineSum fourStateSum
  rw [Fintype.sum_mul_sum, ← Fintype.sum_prod_type',
    ← (pairStateEquiv n).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [pairStateEquiv, Equiv.coe_fn_symm_mk, fourValid_iff, pairWeight]
  by_cases h₁ : SpineValid (fun i => (w i).1)
  · by_cases h₂ : SpineValid (fun i => (w i).2)
    · simp only [h₁, h₂, true_and, ite_true]
      rw [Finset.prod_mul_distrib]
      rfl
    · simp [h₁, h₂]
  · simp [h₁]

/-- The four local weights of the union-of-leaves expansion. -/
def omega (j : ℕ) (a : FourState) : Poly :=
  match a with
  | (false, false) => (U + V) ^ j
  | (true, false) => S * T ^ j
  | (false, true) => T * S ^ j
  | (true, true) => if j = 0 then V else 0

noncomputable def Aword {n : ℕ} (j : Fin n → ℕ) : Poly := by
  classical
  exact ∑ w : Fin n → FourState,
    if FourValid w then ∏ i : Fin n, omega (j i) (w i) else 0

theorem one_add_pow (x : Poly) (r : ℕ) :
    (1 + x) ^ r = ∑ j : Fin (r + 1), (r.choose j.val : Poly) * x ^ j.val := by
  calc
    (1 + x) ^ r = ∑ j ∈ Finset.range (r + 1), (r.choose j : Poly) * x ^ j := by
      simpa [add_comm, mul_comm] using (add_pow x 1 r)
    _ = ∑ j : Fin (r + 1), (r.choose j.val : Poly) * x ^ j.val :=
      Finset.sum_range _

theorem pairWeight_eq_omega_sum (r : ℕ) (a : FourState) :
    pairWeight r a S T =
      ∑ j : Fin (r + 1), (r.choose j.val : Poly) * omega j.val a := by
  rcases a with ⟨b, c⟩
  cases b <;> cases c
  · simp only [pairWeight, Bool.false_eq_true, ↓reduceIte, omega]
    rw [← mul_pow]
    have h : (1 + S) * (1 + T) = 1 + (U + V) := by ring
    rw [h, one_add_pow]
  · simp only [pairWeight, Bool.false_eq_true, ↓reduceIte, omega]
    rw [one_add_pow, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · simp only [pairWeight, Bool.false_eq_true, ↓reduceIte, omega]
    rw [one_add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · simp only [pairWeight, ↓reduceIte, omega]
    rw [Finset.sum_eq_single (0 : Fin (r + 1))]
    · simp
    · intro j hj hne
      have hval : j.val ≠ 0 := by
        intro hz
        exact hne (Fin.ext hz)
      simp [hval]
    · simp

theorem independencePolynomial_product_binomial (n : ℕ) (m : Fin n → ℕ) :
    independencePolynomial n m S * independencePolynomial n m T =
      ∑ j : ∀ i : Fin n, Fin (m i + 1),
        (∏ i : Fin n, (Nat.choose (m i) (j i).val : Poly)) *
          Aword (fun i => (j i).val) := by
  classical
  rw [independencePolynomial_product_eq_fourStateSum]
  unfold fourStateSum Aword
  simp_rw [pairWeight_eq_omega_sum, Fintype.prod_sum]
  have h : ∀ w : Fin n → FourState,
      (if FourValid w then
        ∑ j : ∀ i : Fin n, Fin (m i + 1),
          ∏ i : Fin n, (Nat.choose (m i) (j i).val : Poly) * omega (j i).val (w i)
        else 0) =
      ∑ j : ∀ i : Fin n, Fin (m i + 1),
        if FourValid w then
          ∏ i : Fin n, (Nat.choose (m i) (j i).val : Poly) * omega (j i).val (w i)
        else 0 := by
    intro w
    by_cases hw : FourValid w <;> simp [hw]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hvalid : FourValid w <;> simp [hvalid, Finset.prod_mul_distrib]

end
end R34.CaterpillarCounts
