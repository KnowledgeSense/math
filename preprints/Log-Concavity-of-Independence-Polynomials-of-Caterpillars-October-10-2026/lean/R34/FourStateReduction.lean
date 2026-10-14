import R34.CaterpillarCounts
import R34.SchurIsing
import R34.Transfer
import R34.ModelReduction
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Induction

open scoped BigOperators Classical

namespace R34.FourStateReduction

noncomputable section

open CaterpillarCounts

abbrev Weight := FourState → Poly

def vacant : FourState := (false, false)
def double : FourState := (true, true)

/-- A path sum with an initial state and a terminal weight. -/
def partition : List Weight → Weight → FourState → Poly
  | [], f, b => f b
  | w :: xs, f, b =>
      ∑ a : FourState, if Compatible b a then w a * partition xs f a else 0

def ordinary (j : ℕ) : Weight :=
  fun a => if a = double then 0 else omega j a

def doubleWeight (j : ℕ) : Weight :=
  fun a => if a = double then omega j double else 0

def terminalVacant : Weight := fun a => if a = vacant then 1 else 0

def fullValue (word : List ℕ) : Poly :=
  partition (word.map omega) (fun _ => 1) vacant

def ordinaryValue (word : List ℕ) : Poly :=
  partition (word.map ordinary) (fun _ => 1) vacant

@[simp] theorem compatible_vacant_left (a : FourState) : Compatible vacant a := by
  simp [Compatible, vacant]

@[simp] theorem compatible_vacant_right (a : FourState) : Compatible a vacant := by
  simp [Compatible, vacant]

theorem omega_split (j : ℕ) : omega j = ordinary j + doubleWeight j := by
  funext a
  by_cases ha : a = double <;> simp [ordinary, doubleWeight, ha]

theorem partition_congr (xs : List Weight) {f g : Weight}
    (h : ∀ a, f a = g a) (b : FourState) : partition xs f b = partition xs g b := by
  exact congrArg (fun k => partition xs k b) (funext h)

theorem partition_scale (xs : List Weight) (f : Weight) (r : Poly) (b : FourState) :
    partition xs (fun a => r * f a) b = r * partition xs f b := by
  induction xs generalizing b with
  | nil => simp [partition]
  | cons w xs ih =>
    simp only [partition, ih]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : Compatible b a <;> simp [h]
    ring

theorem partition_append (xs ys : List Weight) (f : Weight) (b : FourState) :
    partition (xs ++ ys) f b = partition xs (fun a => partition ys f a) b := by
  induction xs generalizing b with
  | nil => rfl
  | cons w xs ih => simp only [List.cons_append, partition, ih]

theorem partition_add_site (xs ys : List Weight) (w z f : Weight) (b : FourState) :
    partition (xs ++ (w + z) :: ys) f b =
      partition (xs ++ w :: ys) f b + partition (xs ++ z :: ys) f b := by
  induction xs generalizing b with
  | nil =>
    simp only [List.nil_append, partition, Pi.add_apply, add_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : Compatible b a <;> simp [h]
  | cons x xs ih =>
    simp only [List.cons_append, partition, ih, mul_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : Compatible b a <;> simp [h]

theorem double_step (j : ℕ) (ys : List Weight) (f : Weight) (b : FourState) :
    partition (doubleWeight j :: ys) f b =
      omega j double * terminalVacant b * partition ys f double := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;>
    simp [partition, doubleWeight, double, vacant, terminalVacant,
      Compatible, Fintype.sum_prod_type]

theorem partition_double_site (xs ys : List Weight) (j : ℕ) (b : FourState) :
    partition (xs ++ doubleWeight j :: ys) (fun _ => 1) b =
      omega j double * partition xs terminalVacant b * partition ys (fun _ => 1) double := by
  rw [partition_append]
  simp_rw [double_step]
  have h := partition_scale xs terminalVacant
    (omega j double * partition ys (fun _ => 1) double) b
  calc
    _ = partition xs (fun a =>
        (omega j double * partition ys (fun _ => 1) double) * terminalVacant a) b := by
      apply partition_congr
      intro a
      ring
    _ = _ := by rw [h]; ring

theorem ordinary_terminal_step (j : ℕ) (b : FourState) :
    partition [ordinary j] terminalVacant b = (U + V) ^ j := by
  rcases b with ⟨b, c⟩
  cases b <;> cases c <;>
    simp [partition, terminalVacant, ordinary, omega, Compatible,
      vacant, double, Fintype.sum_prod_type, R34.U, R34.V,
      R34.S, R34.T, CaterpillarCounts.U, CaterpillarCounts.V,
      CaterpillarCounts.S, CaterpillarCounts.T]

theorem ordinary_terminal_append (xs : List ℕ) (j : ℕ) :
    partition ((xs ++ [j]).map ordinary) terminalVacant vacant =
      (U + V) ^ j * ordinaryValue xs := by
  rw [List.map_append, partition_append]
  simp only [List.map_singleton, ordinary_terminal_step]
  simpa [ordinaryValue] using
    partition_scale (xs.map ordinary) (fun _ => 1) ((U + V) ^ j) vacant

theorem full_from_double (j : ℕ) (xs : List ℕ) :
    partition ((j :: xs).map omega) (fun _ => 1) double =
      (U + V) ^ j * fullValue xs := by
  simp [partition, fullValue, double, vacant, omega, Compatible,
    Fintype.sum_prod_type, R34.U, R34.V,
    R34.S, R34.T, CaterpillarCounts.U, CaterpillarCounts.V,
    CaterpillarCounts.S, CaterpillarCounts.T]

def ValidFrom {n : ℕ} (b : FourState) (w : Fin n → FourState) : Prop :=
  (∀ i : Fin n, i.val = 0 → Compatible b (w i)) ∧ FourValid w

theorem fourValid_cons {n : ℕ} (a : FourState) (w : Fin n → FourState) :
    FourValid (Fin.cons a w) ↔
      (∀ i : Fin n, i.val = 0 → Compatible a (w i)) ∧ FourValid w := by
  constructor
  · intro h
    constructor
    · intro i hi
      simpa using h 0 i.succ (by simp [hi])
    · intro i j hij
      simpa using h i.succ j.succ (by simpa using hij)
  · rintro ⟨hfirst, htail⟩ i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have hj : j.val = 0 := by simpa using hij
        simpa using hfirst j hj
    | succ i =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        simpa using htail i j (by simpa using hij)

theorem validFrom_cons {n : ℕ} (b a : FourState) (w : Fin n → FourState) :
    ValidFrom b (Fin.cons a w) ↔ Compatible b a ∧ ValidFrom a w := by
  rw [ValidFrom, fourValid_cons]
  constructor
  · rintro ⟨hfirst, htail⟩
    exact ⟨by simpa using hfirst 0 rfl, htail⟩
  · rintro ⟨hfirst, htail⟩
    refine ⟨?_, htail⟩
    intro i hi
    have : i = 0 := Fin.ext hi
    subst i
    simpa using hfirst

@[simp] theorem validFrom_vacant {n : ℕ} (w : Fin n → FourState) :
    ValidFrom vacant w ↔ FourValid w := by simp [ValidFrom]

/-- The recursive path sum enumerates the same finite compatible assignments. -/
theorem partition_eq_finite_sum {n : ℕ} (j : Fin n → ℕ) (b : FourState) :
    partition ((List.ofFn j).map omega) (fun _ => 1) b =
      ∑ w : Fin n → FourState,
        if ValidFrom b w then ∏ i : Fin n, omega (j i) (w i) else 0 := by
  induction n generalizing b with
  | zero => simp [List.ofFn_zero, partition, ValidFrom, FourValid]
  | succ n ih =>
    rw [List.ofFn_succ]
    simp only [List.map_cons, partition]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => FourState)).sum_comp]
    conv_rhs => rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, validFrom_cons, Fin.prod_univ_succ,
      Fin.cons_zero, Fin.cons_succ]
    rw [ih]
    by_cases h : Compatible b a
    · simp only [h, true_and, ite_true, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hv : ValidFrom a w <;> simp [hv]
    · simp [h]

theorem Aword_eq_fullValue {n : ℕ} (j : Fin n → ℕ) :
    Aword j = fullValue (List.ofFn j) := by
  rw [fullValue, partition_eq_finite_sum]
  simp only [Aword, validFrom_vacant]

def mixedValue (leftWord suffix : List ℕ) : Poly :=
  partition (leftWord.map ordinary ++ suffix.map omega) (fun _ => 1) vacant

theorem terminal_schur
    (hOrdinary : ∀ word : List ℕ, SchurPositive (ordinaryValue word))
    (word : List ℕ) : SchurPositive (partition (word.map ordinary) terminalVacant vacant) := by
  rcases word.eq_nil_or_concat' with rfl | ⟨xs, j, rfl⟩
  · simpa [partition, terminalVacant] using schurPositive_one
  · rw [ordinary_terminal_append]
    exact schurPositive_mul
      (schurPositive_pow (schurPositive_add schurPositive_U schurPositive_V) j)
      (hOrdinary xs)

theorem omega_double_schur (j : ℕ) : SchurPositive (omega j double) := by
  by_cases hj : j = 0
  · simpa [omega, double, hj, CaterpillarCounts.V, CaterpillarCounts.S,
      CaterpillarCounts.T, R34.V, R34.S, R34.T] using schurPositive_V
  · simpa [omega, double, hj] using SchurPositive.zero

/-- Expanding the first remaining double-occupied site cuts the path at its
two forced vacant neighbors. -/
theorem fullValue_schur
    (hOrdinary : ∀ word : List ℕ, SchurPositive (ordinaryValue word))
    (word : List ℕ) : SchurPositive (fullValue word) := by
  have h : ∀ suffix : List ℕ,
      (∀ leftWord : List ℕ, SchurPositive (mixedValue leftWord suffix)) ∧
      SchurPositive (partition (suffix.map omega) (fun _ => 1) double) := by
    intro suffix
    induction suffix with
    | nil =>
      constructor
      · intro leftWord
        simpa [mixedValue, ordinaryValue] using hOrdinary leftWord
      · simpa [partition] using schurPositive_one
    | cons j suffix ih =>
      constructor
      · intro leftWord
        unfold mixedValue
        rw [List.map_cons, omega_split j, partition_add_site]
        apply schurPositive_add
        · simpa [mixedValue, List.map_append, List.append_assoc] using
            ih.1 (leftWord ++ [j])
        · rw [partition_double_site]
          exact schurPositive_mul
            (schurPositive_mul (omega_double_schur j) (terminal_schur hOrdinary leftWord))
            ih.2
      · rw [full_from_double]
        exact schurPositive_mul
          (schurPositive_pow (schurPositive_add schurPositive_U schurPositive_V) j)
          (by simpa [mixedValue, fullValue] using ih.1 [])
  simpa [mixedValue, fullValue] using (h word).1 []

def threeWeight (j : ℕ) : Fin 3 → Poly :=
  ![(Transfer.U + Transfer.V) ^ j, Transfer.S * Transfer.T ^ j,
    Transfer.T * Transfer.S ^ j]

def threeSite (j : ℕ) : Transfer.Mat := Matrix.diagonal (threeWeight j)

def threeRow (word : List ℕ) (b : Fin 3) : Poly :=
  ∑ a : Fin 3, Transfer.chain (word.map threeSite) b a

def ordinaryState (b : Fin 3) : FourState := ![vacant, (true, false), (false, true)] b

theorem threeRow_nil (b : Fin 3) : threeRow [] b = 1 := by
  simp [threeRow, Matrix.one_apply]

theorem threeRow_cons (j : ℕ) (word : List ℕ) (b : Fin 3) :
    threeRow (j :: word) b =
      ∑ a : Fin 3, Transfer.compatibility b a * threeWeight j a * threeRow word a := by
  have hc : Transfer.chain ((j :: word).map threeSite) =
      (Transfer.compatibility * threeSite j) * Transfer.chain (word.map threeSite) := by
    simp [Transfer.chain]
  calc
    _ = ∑ r : Fin 3, ∑ a : Fin 3,
        (Transfer.compatibility * threeSite j) b a *
          Transfer.chain (word.map threeSite) a r := by
      rw [threeRow, hc]
      rfl
    _ = ∑ a : Fin 3, Transfer.compatibility b a * threeWeight j a *
        (∑ r : Fin 3, Transfer.chain (word.map threeSite) a r) := by
      simp only [threeSite, Matrix.mul_diagonal]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = _ := rfl

def threeToFour (a0 a1 a2 : Poly) : Weight
  | (false, false) => a0
  | (true, false) => a1
  | (false, true) => a2
  | (true, true) => 0

theorem sum_four_eq_three (a0 a1 a2 : Poly) (f : Weight) (b : Fin 3) :
    (∑ a : FourState,
      if Compatible (ordinaryState b) a then threeToFour a0 a1 a2 a * f a else 0) =
      ∑ a : Fin 3, Transfer.compatibility b a * ![a0, a1, a2] a * f (ordinaryState a) := by
  rw [Fin.sum_univ_three]
  fin_cases b
  · change (∑ a : FourState,
      if Compatible (false, false) a then threeToFour a0 a1 a2 a * f a else 0) =
        1 * a0 * f (false, false) + 1 * a1 * f (true, false) + 1 * a2 * f (false, true)
    simp [Fintype.sum_prod_type, Compatible, threeToFour]
    ring
  · change (∑ a : FourState,
      if Compatible (true, false) a then threeToFour a0 a1 a2 a * f a else 0) =
        1 * a0 * f (false, false) + 0 * a1 * f (true, false) + 1 * a2 * f (false, true)
    simp [Fintype.sum_prod_type, Compatible, threeToFour]
    exact add_comm _ _
  · change (∑ a : FourState,
      if Compatible (false, true) a then threeToFour a0 a1 a2 a * f a else 0) =
        1 * a0 * f (false, false) + 1 * a1 * f (true, false) + 0 * a2 * f (false, true)
    simp [Fintype.sum_prod_type, Compatible, threeToFour]
    exact add_comm _ _

theorem ordinary_partition_eq_threeRow (word : List ℕ) (b : Fin 3) :
    partition (word.map ordinary) (fun _ => 1) (ordinaryState b) = threeRow word b := by
  induction word generalizing b with
  | nil => simp [partition, threeRow_nil]
  | cons j word ih =>
    rw [threeRow_cons]
    have hw : ordinary j = threeToFour ((Transfer.U + Transfer.V) ^ j)
        (Transfer.S * Transfer.T ^ j) (Transfer.T * Transfer.S ^ j) := by
      funext a
      rcases a with ⟨c, d⟩
      cases c <;> cases d <;> simp [ordinary, omega, double, threeToFour] <;> rfl
    simp only [List.map_cons, partition, hw]
    rw [sum_four_eq_three]
    simp only [threeWeight, ih]

theorem ordinaryValue_eq_threeValue (word : List ℕ) :
    ordinaryValue word = Transfer.value (word.map threeSite) := by
  exact ordinary_partition_eq_threeRow word 0

theorem ordinaryValue_eq_Gword (word : List ℕ) :
    ordinaryValue word = ModelReduction.Gword word :=
  ordinaryValue_eq_threeValue word

/-- The four-state compatible sum inherits positivity from all three-state words. -/
theorem Aword_schurPositive
    (hG : ∀ word : List ℕ, SchurPositive (ModelReduction.Gword word))
    {n : ℕ} (j : Fin n → ℕ) : SchurPositive (CaterpillarCounts.Aword j) := by
  rw [Aword_eq_fullValue]
  apply fullValue_schur
  intro word
  rw [ordinaryValue_eq_Gword]
  exact hG word

end

end R34.FourStateReduction
