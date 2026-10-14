import MainTheorems.Hypercomb.ExtensionPolynomials
import MainTheorems.Hypercomb.InitialSets
import MainTheorems.Hypercomb.Continuants

namespace ResearchMain.Hypercomb

open Classical Polynomial

theorem comb_rooted_polynomials (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    (excludedPolynomial (combEdges a n) (combRoot a n), includedPolynomial (combEdges a n) (combRoot a n)) =
      transfer ((1 + C (a : ℝ) * X) * (1 + (C (a : ℝ) - 1) * X)) (1 + C (a : ℝ) * X) X n := by
  induction n with
  | zero =>
    change (excludedPolynomial {Finset.univ} (none : Option (Fin a)),
      includedPolynomial {Finset.univ} (none : Option (Fin a))) = _
    rw [excludedPolynomial_initial, includedPolynomial_initial]
    simp only [Fintype.card_fin, transfer]
  | succ n ih =>
    have h₁ := congrArg Prod.fst ih
    have h₂ := congrArg Prod.snd ih
    dsimp only at h₁ h₂
    have hcast : C ((a - 1 : ℕ) : ℝ) = C (a : ℝ) - (1 : ℝ[X]) := by
      rw [Nat.cast_sub ha, Nat.cast_one, map_sub, map_one]
    apply Prod.ext
    · change excludedPolynomial (extensionEdges (P := Fin (a - 1)) (T := Fin a)
        (combEdges a n) (combRoot a n)) (Sum.inr (Sum.inl none)) = _
      rw [excludedPolynomial_extension]
      simp only [Fintype.card_fin]
      rw [h₁, h₂, hcast]
      rw [transfer]
      ring
    · change includedPolynomial (extensionEdges (P := Fin (a - 1)) (T := Fin a)
        (combEdges a n) (combRoot a n)) (Sum.inr (Sum.inl none)) = _
      rw [includedPolynomial_extension, h₁]
      rfl

theorem strongIndependencePolynomial_eq (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    strongIndependencePolynomial a n = combValue (C (a : ℝ)) X n := by
  rw [strongIndependencePolynomial, strongIndependentSets,
    independentPolynomial_partition (combEdges a n) (combRoot a n)]
  have h := comb_rooted_polynomials a ha n
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp only at h₁ h₂
  rw [h₁, h₂]
  rfl

noncomputable def strongIndependenceCount (a n k : ℕ) : ℕ :=
  ((strongIndependentSets a n).filter fun S => S.card = k).card

theorem strongIndependencePolynomial_coeff (a n k : ℕ) :
    (strongIndependencePolynomial a n).coeff k = (strongIndependenceCount a n k : ℝ) := by
  rw [strongIndependencePolynomial, finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_boole]
  simp only [strongIndependenceCount, eq_comm]

end ResearchMain.Hypercomb
