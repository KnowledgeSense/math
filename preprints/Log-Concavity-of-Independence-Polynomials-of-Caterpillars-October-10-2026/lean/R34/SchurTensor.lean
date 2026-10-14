import R34.SchurIsing
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

noncomputable section

namespace R34

open MvPolynomial
open scoped BigOperators

abbrev ColorMatrix := Matrix Bool Bool Poly

@[simp] theorem C_two : (C (2 : ℝ) : Poly) = 2 :=
  map_ofNat (C : ℝ →+* Poly) 2

def colorDiag : ColorMatrix := fun a b => if a = b then color a else 0

def interaction (coupling : ℝ) : ColorMatrix :=
  fun a b => C (edgeWeight coupling a b)

def chainMatrix (l : List ℝ) : ColorMatrix :=
  colorDiag * (l.map (fun coupling => interaction coupling * colorDiag)).prod

def matrixTotal (A : ColorMatrix) : Poly := ∑ a : Bool, ∑ b : Bool, A a b

def listChain (l : List ℝ) : Poly := matrixTotal (chainMatrix l)

@[simp] theorem chainMatrix_nil : chainMatrix [] = colorDiag := by
  simp [chainMatrix]

@[simp] theorem listChain_nil : listChain [] = U := by
  simp [listChain, matrixTotal, colorDiag, color, U]

theorem chainMatrix_append_edge (p q : List ℝ) (a : ℝ) :
    chainMatrix (p ++ a :: q) = chainMatrix p * interaction a * chainMatrix q := by
  simp [chainMatrix, List.map_append, List.prod_append, Matrix.mul_assoc]

theorem chainMatrix_cons (a : ℝ) (q : List ℝ) :
    chainMatrix (a :: q) = colorDiag * interaction a * chainMatrix q := by
  simpa using chainMatrix_append_edge [] q a

@[simp] theorem matrixTotal_add (A B : ColorMatrix) :
    matrixTotal (A + B) = matrixTotal A + matrixTotal B := by
  simp [matrixTotal, Finset.sum_add_distrib]

@[simp] theorem matrixTotal_smul (c : Poly) (A : ColorMatrix) :
    matrixTotal (c • A) = c * matrixTotal A := by
  simp [matrixTotal, Matrix.smul_apply, smul_eq_mul]
  ring

theorem interaction_interpolate_two_one (a : ℝ) :
    interaction a = (C (a-1) : Poly) • interaction 2 + (C (2-a) : Poly) • interaction 1 := by
  funext i j
  cases i <;> cases j <;>
    simp [interaction, edgeWeight, Matrix.smul_apply, smul_eq_mul, map_sub] <;> ring

theorem interaction_interpolate_one_zero (a : ℝ) :
    interaction a = (C a : Poly) • interaction 1 + (C (1-a) : Poly) • interaction 0 := by
  funext i j
  cases i <;> cases j <;>
    simp [interaction, edgeWeight, Matrix.smul_apply, smul_eq_mul, map_sub]

theorem listChain_interpolate_two_one (p q : List ℝ) (a : ℝ) :
    listChain (p ++ a :: q) =
      C (a-1) * listChain (p ++ 2 :: q) + C (2-a) * listChain (p ++ 1 :: q) := by
  unfold listChain
  simp only [chainMatrix_append_edge]
  rw [interaction_interpolate_two_one]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem listChain_interpolate_one_zero (p q : List ℝ) (a : ℝ) :
    listChain (p ++ a :: q) =
      C a * listChain (p ++ 1 :: q) + C (1-a) * listChain (p ++ 0 :: q) := by
  unfold listChain
  simp only [chainMatrix_append_edge]
  rw [interaction_interpolate_one_zero]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem matrixTotal_one_split (A B : ColorMatrix) :
    matrixTotal (A * interaction 1 * B) = matrixTotal A * matrixTotal B := by
  simp [matrixTotal, Matrix.mul_apply, interaction, edgeWeight]
  ring

theorem listChain_one_split (p q : List ℝ) :
    listChain (p ++ 1 :: q) = listChain p * listChain q := by
  simp [listChain, chainMatrix_append_edge, matrixTotal_one_split]

theorem color_zero_contraction :
    colorDiag * interaction 0 * colorDiag = V • interaction 0 := by
  funext i j
  cases i <;> cases j <;>
    simp [colorDiag, interaction, edgeWeight, color, V, Matrix.mul_apply,
      Matrix.smul_apply, smul_eq_mul]
  ring

theorem interaction_zero_contraction (a b : ℝ) (hab : 1+a*b ≠ 0) :
    interaction a * interaction 0 * interaction b =
      (C (1+a*b) : Poly) • interaction ((a+b)/(1+a*b)) := by
  have hcancel : (1+a*b)*((a+b)/(1+a*b)) = a+b := by
    field_simp [hab]
  have hc : (1 + C a * C b : Poly) * C ((a+b)/(1+a*b)) = C a + C b := by
    simpa only [C_mul, C_add, map_one] using congrArg (fun c : ℝ => (C c : Poly)) hcancel
  funext i j
  cases i <;> cases j <;>
    simp [interaction, edgeWeight, Matrix.mul_apply,
      Matrix.smul_apply, smul_eq_mul, C_add, C_mul, hc] <;> ring

theorem matrixTotal_zero_left (a : ℝ) (A : ColorMatrix) :
    matrixTotal (interaction 0 * interaction a * A) = C (1+a) * matrixTotal A := by
  simp [matrixTotal, interaction, edgeWeight, Matrix.mul_apply, C_add]
  ring

theorem matrixTotal_zero_right (a : ℝ) (A : ColorMatrix) :
    matrixTotal (A * interaction a * interaction 0) = C (1+a) * matrixTotal A := by
  simp [matrixTotal, interaction, edgeWeight, Matrix.mul_apply, C_add]
  ring

theorem listChain_single_zero : listChain [0] = C 2 * V := by
  simp [listChain, chainMatrix, matrixTotal, interaction, edgeWeight, colorDiag,
    Matrix.mul_apply, color, V]
  ring

theorem listChain_zero_left (b : ℝ) (q : List ℝ) :
    listChain (0 :: b :: q) = C (1+b) * V * listChain q := by
  have h : chainMatrix (0 :: b :: q) =
      (colorDiag * interaction 0 * colorDiag) * interaction b * chainMatrix q := by
    rw [chainMatrix_cons, chainMatrix_cons]
    simp only [Matrix.mul_assoc]
  rw [listChain, h, color_zero_contraction]
  simp only [Matrix.smul_mul, matrixTotal_smul, matrixTotal_zero_left]
  unfold listChain
  ring

theorem listChain_zero_right (a : ℝ) (p : List ℝ) :
    listChain (p ++ [a,0]) = C (1+a) * V * listChain p := by
  have h : chainMatrix (p ++ [a,0]) =
      chainMatrix p * interaction a * (colorDiag * interaction 0 * colorDiag) := by
    rw [chainMatrix_append_edge, chainMatrix_cons, chainMatrix_nil]
  rw [listChain, h, color_zero_contraction]
  simp only [Matrix.mul_smul, matrixTotal_smul, matrixTotal_zero_right]
  unfold listChain
  ring

theorem listChain_zero_middle (a b : ℝ) (p q : List ℝ) (hab : 1+a*b ≠ 0) :
    listChain (p ++ a :: 0 :: b :: q) =
      C (1+a*b) * V * listChain (p ++ ((a+b)/(1+a*b)) :: q) := by
  have h : chainMatrix (p ++ a :: 0 :: b :: q) =
      chainMatrix p * interaction a * (colorDiag * interaction 0 * colorDiag) *
        interaction b * chainMatrix q := by
    rw [chainMatrix_append_edge, chainMatrix_cons, chainMatrix_cons]
    simp only [Matrix.mul_assoc]
  rw [listChain, h, color_zero_contraction]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hgroup : chainMatrix p * interaction a * interaction 0 * interaction b * chainMatrix q =
      chainMatrix p * (interaction a * interaction 0 * interaction b) * chainMatrix q := by
    simp [Matrix.mul_assoc]
  rw [hgroup, interaction_zero_contraction a b hab]
  simp only [Matrix.mul_smul, Matrix.smul_mul, matrixTotal_smul]
  rw [← chainMatrix_append_edge]
  unfold listChain
  ring

theorem contracted_coupling_bounds {a b : ℝ} (ha : 0 ≤ a ∧ a ≤ 2)
    (hb : 0 ≤ b ∧ b ≤ 2) :
    0 ≤ (a+b)/(1+a*b) ∧ (a+b)/(1+a*b) ≤ 2 := by
  have hd : 0 < 1+a*b := by
    have hprod := mul_nonneg ha.1 hb.1
    linarith
  constructor
  · exact div_nonneg (add_nonneg ha.1 hb.1) (le_of_lt hd)
  · apply (div_le_iff₀ hd).2
    by_cases haHalf : a ≤ 1/2
    · have hh : 0 ≤ (1-2*a)*(2-b) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · have hh : 0 ≤ (2*a-1)*b := mul_nonneg (by linarith) hb.1
      nlinarith

private theorem listChain_zero_positive_of_shorter (N : ℕ)
    (ih : ∀ l : List ℝ, l.length < N →
      (∀ x ∈ l, 0 ≤ x ∧ x ≤ 2) → SchurPositive (listChain l))
    (p q : List ℝ) (hlen : (p ++ 0 :: q).length = N)
    (hp : ∀ x ∈ p, 0 ≤ x ∧ x ≤ 2) (hq : ∀ x ∈ q, 0 ≤ x ∧ x ≤ 2) :
    SchurPositive (listChain (p ++ 0 :: q)) := by
  rcases List.eq_nil_or_concat' p with rfl | ⟨p, a, rfl⟩
  · cases q with
    | nil =>
      simp only [List.nil_append]
      rw [listChain_single_zero]
      exact schurPositive_scale 2 (by norm_num) schurPositive_V
    | cons b q =>
      have hb := hq b (by simp)
      have hq' : ∀ x ∈ q, 0 ≤ x ∧ x ≤ 2 := by
        intro x hx
        exact hq x (by simp [hx])
      have hshort : q.length < N := by
        simp only [List.nil_append, List.length_cons] at hlen
        omega
      simp only [List.nil_append]
      rw [listChain_zero_left]
      simpa only [mul_assoc] using schurPositive_scale (1+b) (by linarith [hb.1])
        (schurPositive_mul schurPositive_V (ih q hshort hq'))
  · have ha := hp a (by simp)
    have hp' : ∀ x ∈ p, 0 ≤ x ∧ x ≤ 2 := by
      intro x hx
      exact hp x (by simp [hx])
    cases q with
    | nil =>
      have hshort : p.length < N := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [listChain_zero_right]
      simpa only [mul_assoc] using schurPositive_scale (1+a) (by linarith [ha.1])
        (schurPositive_mul schurPositive_V (ih p hshort hp'))
    | cons b q =>
      have hb := hq b (by simp)
      have hq' : ∀ x ∈ q, 0 ≤ x ∧ x ≤ 2 := by
        intro x hx
        exact hq x (by simp [hx])
      have hd : 0 < 1+a*b := by
        have hprod := mul_nonneg ha.1 hb.1
        linarith
      have hnew : ∀ x ∈ p ++ ((a+b)/(1+a*b)) :: q, 0 ≤ x ∧ x ≤ 2 := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hp' x hx
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact contracted_coupling_bounds ha hb
          · exact hq' x hx
      have hshort : (p ++ ((a+b)/(1+a*b)) :: q).length < N := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
        omega
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [listChain_zero_middle a b p q (ne_of_gt hd)]
      simpa only [mul_assoc] using schurPositive_scale (1+a*b) (le_of_lt hd)
        (schurPositive_mul schurPositive_V (ih _ hshort hnew))

private theorem listChain_positive_scan
    (hUniform : ∀ m : ℕ, SchurPositive (listChain (List.replicate m 2)))
    (N : ℕ)
    (ih : ∀ l : List ℝ, l.length < N →
      (∀ x ∈ l, 0 ≤ x ∧ x ≤ 2) → SchurPositive (listChain l))
    (q : List ℝ) :
    ∀ p : List ℝ, (∀ x ∈ p, x = 2) → (∀ x ∈ q, 0 ≤ x ∧ x ≤ 2) →
      (p ++ q).length = N → SchurPositive (listChain (p ++ q)) := by
  induction q with
  | nil =>
    intro p hp hq hlen
    simp only [List.append_nil]
    have heq : p = List.replicate p.length 2 := List.eq_replicate_of_mem hp
    rw [heq]
    exact hUniform p.length
  | cons a q ihq =>
    intro p hp hq hlen
    have ha := hq a (by simp)
    have hp' : ∀ x ∈ p, 0 ≤ x ∧ x ≤ 2 := by
      intro x hx
      rw [hp x hx]
      norm_num
    have hq' : ∀ x ∈ q, 0 ≤ x ∧ x ≤ 2 := by
      intro x hx
      exact hq x (by simp [hx])
    have hpshort : p.length < N := by
      simp only [List.length_append, List.length_cons] at hlen
      omega
    have hqshort : q.length < N := by
      simp only [List.length_append, List.length_cons] at hlen
      omega
    have hone : SchurPositive (listChain (p ++ 1 :: q)) := by
      rw [listChain_one_split]
      exact schurPositive_mul (ih p hpshort hp') (ih q hqshort hq')
    by_cases hlarge : 1 ≤ a
    · have htwo : SchurPositive (listChain (p ++ 2 :: q)) := by
        have hpTwo : ∀ x ∈ p ++ [2], x = 2 := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hp x hx
          · simpa using hx
        have hlenTwo : ((p ++ [2]) ++ q).length = N := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
          omega
        simpa only [List.append_assoc, List.cons_append, List.nil_append]
          using ihq (p ++ [2]) hpTwo hq' hlenTwo
      rw [listChain_interpolate_two_one]
      exact schurPositive_add
        (schurPositive_scale (a-1) (by linarith) htwo)
        (schurPositive_scale (2-a) (by linarith [ha.2]) hone)
    · have hzero : SchurPositive (listChain (p ++ 0 :: q)) :=
        listChain_zero_positive_of_shorter N ih p q
          (by simpa only [List.length_append, List.length_cons] using hlen) hp' hq'
      rw [listChain_interpolate_one_zero]
      exact schurPositive_add (schurPositive_scale a ha.1 hone)
        (schurPositive_scale (1-a) (by linarith) hzero)

/-- Uniform coupling two controls every path whose couplings lie in `[0,2]`. -/
theorem listChain_schurPositive_of_uniform
    (hUniform : ∀ m : ℕ, SchurPositive (listChain (List.replicate m 2)))
    (l : List ℝ) (hl : ∀ x ∈ l, 0 ≤ x ∧ x ≤ 2) :
    SchurPositive (listChain l) := by
  have hAll : ∀ N : ℕ, ∀ l : List ℝ, l.length = N →
      (∀ x ∈ l, 0 ≤ x ∧ x ≤ 2) → SchurPositive (listChain l) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro l hlen hb
      exact listChain_positive_scan hUniform N
        (fun q hshort hq => ih q.length hshort q rfl hq)
        l [] (by simp) hb (by simpa using hlen)
  exact hAll l.length l rfl hl

end R34



