import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace R34.Transfer

noncomputable section

abbrev Poly := MvPolynomial (Fin 2) ℝ
abbrev Mat := Matrix (Fin 3) (Fin 3) Poly

def S : Poly := MvPolynomial.X 0
def T : Poly := MvPolynomial.X 1
def U : Poly := S + T
def V : Poly := S * T

def unitEntry (a b : Fin 3) : Mat := fun i j => if i = a ∧ j = b then 1 else 0

def compatibility : Mat := ![![1, 1, 1], ![1, 0, 1], ![1, 1, 0]]
def contractedPair : Mat := ![![6, 0, 0], ![0, 0, -1], ![0, -1, 0]]

def normalizedWeight (j : ℕ) : Fin 3 → Poly :=
  if j = 0 then ![0, S, T]
  else ![MvPolynomial.C (j : ℝ) * U ^ (j - 1), T ^ (j - 1), S ^ (j - 1)]

def normalizedMatrix (j : ℕ) : Mat := Matrix.diagonal (normalizedWeight j)

/-- A free-ended transfer product; the empty product has value one. -/
def chain (sites : List Mat) : Mat := (sites.map (fun M => compatibility * M)).prod

def value (sites : List Mat) : Poly := ∑ i, chain sites 0 i

def normalizedModel (word : List ℕ) : Poly := value (word.map normalizedMatrix)

@[simp] theorem chain_nil : chain [] = 1 := rfl
@[simp] theorem value_nil : value [] = 1 := by
  simp [value, chain, Fin.sum_univ_succ]

theorem chain_append (xs ys : List Mat) : chain (xs ++ ys) = chain xs * chain ys := by
  simp [chain, List.map_append, List.prod_append]

theorem chain_singleton (M : Mat) : chain [M] = compatibility * M := by
  simp [chain]

theorem value_add_site (xs ys : List Mat) (M N : Mat) :
    value (xs ++ [M + N] ++ ys) =
      value (xs ++ [M] ++ ys) + value (xs ++ [N] ++ ys) := by
  simp only [value, chain_append, chain_singleton, Matrix.mul_add, Matrix.add_mul,
    Matrix.add_apply, Finset.sum_add_distrib]

theorem value_scale_site (xs ys : List Mat) (r : Poly) (M : Mat) :
    value (xs ++ [r • M] ++ ys) =
      r * value (xs ++ [M] ++ ys) := by
  simp only [value, chain_append, chain_singleton, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]

def separatorMatrix : Mat := fun _ j => if j = 0 then (1 : Poly) else 0
def rowSeparator (M : Mat) : Mat := fun i j => if j = 0 then (∑ k, M i k) else 0

theorem compatibility_separator : compatibility * unitEntry 0 0 = separatorMatrix := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  by_cases hj : j = 0
  · subst j
    simp [unitEntry, separatorMatrix]
    fin_cases i <;> rfl
  · simp [unitEntry, separatorMatrix, hj]

theorem value_separator (xs ys : List Mat) :
    value (xs ++ [unitEntry 0 0] ++ ys) = value xs * value ys := by
  simp only [value, chain_append, chain_singleton]
  rw [compatibility_separator]
  have hm : chain xs * separatorMatrix = rowSeparator (chain xs) := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply]
    by_cases hj : j = 0 <;> simp [rowSeparator, separatorMatrix, hj]
  rw [hm]
  have hs : ∀ i : Fin 3, (rowSeparator (chain xs) * chain ys) 0 i =
      (∑ k, chain xs 0 k) * chain ys 0 i := by
    intro i
    rw [Matrix.mul_apply]
    simp only [rowSeparator]
    rw [Finset.sum_eq_single (0 : Fin 3)]
    · simp
    · intro j hj hne
      simp [hne]
    · simp
  simp_rw [hs]
  rw [Finset.mul_sum]
theorem value_weighted_separator (xs ys : List Mat) (r : Poly) :
    value (xs ++ [r • unitEntry 0 0] ++ ys) = r * value xs * value ys := by
  rw [value_scale_site, value_separator]
  ring

def color (b : Bool) : Poly := if b then S else T

def colorState (b : Bool) : Fin 3 := if b then 1 else 2

def pairSite (a b : Bool) : Mat :=
  (3 : Poly) • unitEntry 0 0 + unitEntry (colorState (!a)) (colorState (!b))

/-- The uncontracted positive site with two charges. -/
def goodThree : Mat := ∑ c : Bool × Bool,
  (color c.1 * color c.2 * (MvPolynomial.C (if c.1 = c.2 then (2 : ℝ) else 1) : Poly)) •
    pairSite c.1 c.2

/-- Splitting a three-leaf site and summing the negatively signed opposite pairs. -/
theorem three_site_contraction :
    normalizedMatrix 3 = (MvPolynomial.C (1 / 2 : ℝ) : Poly) •
      (goodThree + V • contractedPair) := by
  have ht : (MvPolynomial.C (2 : ℝ) : Poly) = 2 := map_ofNat _ 2
  have hth : (MvPolynomial.C (3 : ℝ) : Poly) = 3 := map_ofNat _ 3
  have hn : normalizedMatrix 3 = (fun i j => if i = j then
      if i = 0 then (MvPolynomial.C (3 : ℝ) : Poly) * U ^ 2
      else if i = 1 then T ^ 2 else S ^ 2 else 0) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hb : contractedPair = (fun i j => if i = 0 ∧ j = 0 then (6 : Poly)
      else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then -1 else 0) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hd : goodThree + V • contractedPair = (2 : Poly) • normalizedMatrix 3 := by
    rw [hn, hb]
    apply Matrix.ext
    intro i j
    change goodThree i j + V * (if i = 0 ∧ j = 0 then 6
      else if (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then -1 else 0) =
      2 * (if i = j then if i = 0 then (MvPolynomial.C (3 : ℝ) : Poly) * U ^ 2
        else if i = 1 then T ^ 2 else S ^ 2 else 0)
    simp only [goodThree, Fintype.sum_prod_type, Fintype.sum_bool,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;>
      simp [color, colorState, pairSite, unitEntry, U, V, ht, hth,
        Matrix.smul_apply, smul_eq_mul] <;> ring
  have hh : (MvPolynomial.C (1 / 2 : ℝ) : Poly) * 2 = 1 := by
    calc
      (MvPolynomial.C (1 / 2 : ℝ) : Poly) * 2 =
          MvPolynomial.C ((1 / 2 : ℝ) * 2) := by
        rw [map_mul]
        have ht : (MvPolynomial.C (2 : ℝ) : Poly) = 2 := map_ofNat _ 2
        rw [ht]
      _ = 1 := by norm_num
  rw [hd, smul_smul, hh, one_smul]

end

end R34.Transfer








