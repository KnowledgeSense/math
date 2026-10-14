import MainTheorems.Tuza.MedianCuts

namespace ResearchMain.Tuza

def middleEmbedding (n p q : ℕ) (hpq : p ≤ q) (hqn : q ≤ n) :
    Fin (q - p) ↪ Fin n :=
  (suffixEmbedding q p hpq).trans (prefixEmbedding n q hqn)

@[simp]
theorem middleEmbedding_val (n p q : ℕ) (hpq : p ≤ q) (hqn : q ≤ n)
    (i : Fin (q - p)) : (middleEmbedding n p q hpq hqn i).val = p + i.val := rfl

def threeCutColor (p q i : ℕ) : Fin 3 :=
  if i < p then 0 else if i < q then 1 else 2

theorem threeCutColor_first {p q i : ℕ} (hi : i < p) : threeCutColor p q i = 0 := by
  unfold threeCutColor
  exact ite_eq_left hi

theorem threeCutColor_middle {p q i : ℕ} (hpi : p ≤ i) (hiq : i < q) :
    threeCutColor p q i = 1 := by
  unfold threeCutColor
  rw [ite_eq_right (not_lt.mpr hpi), ite_eq_left hiq]

theorem threeCutColor_last {p q i : ℕ} (hpq : p ≤ q) (hqi : q ≤ i) :
    threeCutColor p q i = 2 := by
  unfold threeCutColor
  rw [ite_eq_right (not_lt.mpr (hpq.trans hqi)), ite_eq_right (not_lt.mpr hqi)]

theorem threeCutColor_prefix {p q i : ℕ} (hiq : i < q) :
    threeCutColor p q i ∈ ({0, 1} : Finset (Fin 3)) := by
  by_cases hip : i < p
  · rw [threeCutColor_first hip]
    decide
  · rw [threeCutColor_middle (le_of_not_gt hip) hiq]
    decide

def sixCutColor (a b r t x y : ℕ) : Fin a ⊕ Fin b → Fin 6 :=
  Sum.elim (fun i => Fin.castAdd 3 (threeCutColor x r i.val))
    (fun j => Fin.natAdd 3 (threeCutColor y t j.val))

theorem sixCutColor_left_first {a b r t x y : ℕ} (i : Fin a) (hi : i.val < x) :
    sixCutColor a b r t x y (.inl i) = 0 := by
  change Fin.castAdd 3 (threeCutColor x r i.val) = 0
  rw [threeCutColor_first hi]
  rfl

theorem sixCutColor_left_middle {a b r t x y : ℕ} (i : Fin a)
    (hxi : x ≤ i.val) (hir : i.val < r) :
    sixCutColor a b r t x y (.inl i) = 1 := by
  change Fin.castAdd 3 (threeCutColor x r i.val) = 1
  rw [threeCutColor_middle hxi hir]
  rfl

theorem sixCutColor_left_last {a b r t x y : ℕ} (hxr : x ≤ r)
    (i : Fin a) (hri : r ≤ i.val) :
    sixCutColor a b r t x y (.inl i) = 2 := by
  change Fin.castAdd 3 (threeCutColor x r i.val) = 2
  rw [threeCutColor_last hxr hri]
  rfl

theorem sixCutColor_right_first {a b r t x y : ℕ} (j : Fin b) (hj : j.val < y) :
    sixCutColor a b r t x y (.inr j) = 3 := by
  change Fin.natAdd 3 (threeCutColor y t j.val) = 3
  rw [threeCutColor_first hj]
  rfl

theorem sixCutColor_right_middle {a b r t x y : ℕ} (j : Fin b)
    (hyj : y ≤ j.val) (hjt : j.val < t) :
    sixCutColor a b r t x y (.inr j) = 4 := by
  change Fin.natAdd 3 (threeCutColor y t j.val) = 4
  rw [threeCutColor_middle hyj hjt]
  rfl

theorem sixCutColor_right_last {a b r t x y : ℕ} (hyt : y ≤ t)
    (j : Fin b) (htj : t ≤ j.val) :
    sixCutColor a b r t x y (.inr j) = 5 := by
  change Fin.natAdd 3 (threeCutColor y t j.val) = 5
  rw [threeCutColor_last hyt htj]
  rfl

theorem sixCutColor_left_prefix {a b r t x y : ℕ} (i : Fin a) (hi : i.val < r) :
    sixCutColor a b r t x y (.inl i) ∈ ({0, 1} : Finset (Fin 6)) := by
  by_cases hx : i.val < x
  · rw [sixCutColor_left_first i hx]
    decide
  · rw [sixCutColor_left_middle i (le_of_not_gt hx) hi]
    decide

theorem sixCutColor_right_prefix {a b r t x y : ℕ} (j : Fin b) (hj : j.val < t) :
    sixCutColor a b r t x y (.inr j) ∈ ({3, 4} : Finset (Fin 6)) := by
  by_cases hy : j.val < y
  · rw [sixCutColor_right_first j hy]
    decide
  · rw [sixCutColor_right_middle j (le_of_not_gt hy) hj]
    decide

theorem sixCutColor_left_suffix {a b r t x y : ℕ} (i : Fin a) (hi : x ≤ i.val) :
    sixCutColor a b r t x y (.inl i) ∈ ({1, 2} : Finset (Fin 6)) := by
  change Fin.castAdd 3 (threeCutColor x r i.val) ∈ ({1, 2} : Finset (Fin 6))
  unfold threeCutColor
  rw [ite_eq_right (not_lt.mpr hi)]
  split <;> decide

theorem sixCutColor_right_suffix {a b r t x y : ℕ} (j : Fin b) (hj : y ≤ j.val) :
    sixCutColor a b r t x y (.inr j) ∈ ({4, 5} : Finset (Fin 6)) := by
  change Fin.natAdd 3 (threeCutColor y t j.val) ∈ ({4, 5} : Finset (Fin 6))
  unfold threeCutColor
  rw [ite_eq_right (not_lt.mpr hj)]
  split <;> decide

end ResearchMain.Tuza
