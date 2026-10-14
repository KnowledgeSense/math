import MainTheorems.PureOSequences.Triples
import Mathlib.Algebra.BigOperators.Fin

namespace ResearchMain.PureOSequences

noncomputable def blockMonomial {k : ℕ} (a b c d : ℕ) (tail : Fin k → ℕ) :
    Monomial (4 + k) := Finsupp.equivFunOnFinite.symm (Fin.addCases ![a, b, c, d] tail)

@[simp] theorem blockMonomial_left {k : ℕ} (a b c d : ℕ) (tail : Fin k → ℕ)
    (i : Fin 4) : blockMonomial a b c d tail (Fin.castAdd k i) = ![a, b, c, d] i := by
  simp [blockMonomial]

@[simp] theorem blockMonomial_right {k : ℕ} (a b c d : ℕ) (tail : Fin k → ℕ)
    (i : Fin k) : blockMonomial a b c d tail (Fin.natAdd 4 i) = tail i := by
  simp [blockMonomial]

@[simp] theorem degree_blockMonomial {k : ℕ} (a b c d : ℕ) (tail : Fin k → ℕ) :
    totalDeg (blockMonomial a b c d tail) = a + b + c + d + ∑ i, tail i := by
  simp [totalDeg_eq_sum_univ, Fin.sum_univ_add, Fin.sum_univ_four]

theorem blockMonomial_ext {k : ℕ} (m : Monomial (4 + k)) :
    blockMonomial (m (Fin.castAdd k 0)) (m (Fin.castAdd k 1))
      (m (Fin.castAdd k 2)) (m (Fin.castAdd k 3))
      (fun i => m (Fin.natAdd 4 i)) = m := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> simp
  · simp

theorem degree_block_coordinates {k : ℕ} (m : Monomial (4 + k)) :
    totalDeg m = m (Fin.castAdd k 0) + m (Fin.castAdd k 1) + m (Fin.castAdd k 2) +
      m (Fin.castAdd k 3) + ∑ i, m (Fin.natAdd 4 i) := by
  rw [← blockMonomial_ext m, degree_blockMonomial]
  simp

theorem blockMonomial_le {k : ℕ} {a b c d : ℕ} {tail : Fin k → ℕ}
    {m : Monomial (4 + k)} :
    m ≤ blockMonomial a b c d tail ↔
      m (Fin.castAdd k 0) ≤ a ∧ m (Fin.castAdd k 1) ≤ b ∧
      m (Fin.castAdd k 2) ≤ c ∧ m (Fin.castAdd k 3) ≤ d ∧
      ∀ i, m (Fin.natAdd 4 i) ≤ tail i := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa using h (Fin.castAdd k 0)
    · simpa using h (Fin.castAdd k 1)
    · simpa using h (Fin.castAdd k 2)
    · simpa using h (Fin.castAdd k 3)
    · intro i
      simpa using h (Fin.natAdd 4 i)
  · rintro ⟨h0, h1, h2, h3, ht⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · fin_cases j <;> simp_all
    · simpa using ht _

end ResearchMain.PureOSequences
