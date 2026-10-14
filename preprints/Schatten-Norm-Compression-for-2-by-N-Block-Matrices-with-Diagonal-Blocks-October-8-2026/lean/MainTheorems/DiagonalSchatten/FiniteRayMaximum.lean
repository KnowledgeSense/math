import MainTheorems.DiagonalSchatten.GramFiber

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def quarterCircle : Set (Fin 2 → ℝ) :=
  {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 ^ 2 + x 1 ^ 2 = 1}

theorem quarterCircle_closed : IsClosed quarterCircle := by
  have h0 : IsClosed {x : Fin 2 → ℝ | 0 ≤ x 0} :=
    isClosed_le continuous_const (by fun_prop)
  have h1 : IsClosed {x : Fin 2 → ℝ | 0 ≤ x 1} :=
    isClosed_le continuous_const (by fun_prop)
  have h2 : IsClosed {x : Fin 2 → ℝ | x 0 ^ 2 + x 1 ^ 2 = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  simpa only [quarterCircle, Set.ofPred_and] using h0.inter (h1.inter h2)

theorem quarterCircle_compact : IsCompact quarterCircle := by
  have hbox : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  apply hbox.of_isClosed_subset quarterCircle_closed
  intro x hx
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
  intro i
  fin_cases i
  · change x 0 ∈ Set.Icc (0 : ℝ) 1
    exact ⟨hx.1, by nlinarith [hx.2.2, sq_nonneg (x 1)]⟩
  · change x 1 ∈ Set.Icc (0 : ℝ) 1
    exact ⟨hx.2.1, by nlinarith [hx.2.2, sq_nonneg (x 0)]⟩

abbrev WeightedRays (J : Type*) := (J → ℝ) × (J → Fin 2 → ℝ)

variable {J : Type*} [Fintype J]

def weightedFirst (P : WeightedRays J) : ℝ := ∑ j, P.1 j * P.2 j 0 ^ 2
def weightedSecond (P : WeightedRays J) : ℝ := ∑ j, P.1 j * P.2 j 1 ^ 2
def weightedCross (P : WeightedRays J) : ℝ := ∑ j, P.1 j * P.2 j 0 * P.2 j 1

def weightedGramFiber (a b c : ℝ) : Set (WeightedRays J) :=
  {P | (∀ j, P.1 j ∈ Set.Icc 0 (a + b)) ∧ (∀ j, P.2 j ∈ quarterCircle) ∧
    weightedFirst P = a ∧ weightedSecond P = b ∧ weightedCross P = c}

theorem weightedGramFiber_closed (a b c : ℝ) :
    IsClosed (weightedGramFiber (J := J) a b c) := by
  have hw : IsClosed {P : WeightedRays J | ∀ j, P.1 j ∈ Set.Icc 0 (a + b)} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_Icc.preimage (by fun_prop)
  have hd : IsClosed {P : WeightedRays J | ∀ j, P.2 j ∈ quarterCircle} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => quarterCircle_closed.preimage (by fun_prop)
  have hA : IsClosed {P : WeightedRays J | weightedFirst P = a} :=
    isClosed_eq (by unfold weightedFirst; fun_prop) continuous_const
  have hB : IsClosed {P : WeightedRays J | weightedSecond P = b} :=
    isClosed_eq (by unfold weightedSecond; fun_prop) continuous_const
  have hC : IsClosed {P : WeightedRays J | weightedCross P = c} :=
    isClosed_eq (by unfold weightedCross; fun_prop) continuous_const
  simpa only [weightedGramFiber, Set.ofPred_and] using
    hw.inter (hd.inter (hA.inter (hB.inter hC)))

theorem weightedGramFiber_compact (a b c : ℝ) :
    IsCompact (weightedGramFiber (J := J) a b c) := by
  have hw : IsCompact (Set.pi Set.univ fun _ : J => Set.Icc (0 : ℝ) (a + b)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hd : IsCompact (Set.pi Set.univ fun _ : J => quarterCircle) :=
    isCompact_univ_pi fun _ => quarterCircle_compact
  apply (hw.prod hd).of_isClosed_subset (weightedGramFiber_closed a b c)
  intro P hP
  constructor
  · simpa only [Set.mem_pi, Set.mem_univ, forall_true_left] using hP.1
  · simpa only [Set.mem_pi, Set.mem_univ, forall_true_left] using hP.2.1

def columnWeight (X : Matrix (Fin 2) J ℝ) (j : J) : ℝ := X 0 j ^ 2 + X 1 j ^ 2

def columnRay (X : Matrix (Fin 2) J ℝ) (j : J) : Fin 2 → ℝ :=
  if columnWeight X j = 0 then ![1, 0]
  else fun i => X i j / Real.sqrt (columnWeight X j)

def rowsToWeights (X : Matrix (Fin 2) J ℝ) : WeightedRays J :=
  (columnWeight X, columnRay X)

def recoverRows (P : WeightedRays J) : Matrix (Fin 2) J ℝ :=
  Matrix.of fun i j => Real.sqrt (P.1 j) * P.2 j i

omit [Fintype J] in
theorem columnWeight_nonneg (X : Matrix (Fin 2) J ℝ) (j : J) :
    0 ≤ columnWeight X j := add_nonneg (sq_nonneg _) (sq_nonneg _)

omit [Fintype J] in
theorem columnWeight_zero {X : Matrix (Fin 2) J ℝ} {j : J}
    (hw : columnWeight X j = 0) : X 0 j = 0 ∧ X 1 j = 0 := by
  unfold columnWeight at hw
  constructor <;> nlinarith [sq_nonneg (X 0 j), sq_nonneg (X 1 j)]

omit [Fintype J] in
theorem columnRay_mem {X : Matrix (Fin 2) J ℝ} {j : J}
    (hX : ∀ i, 0 ≤ X i j) : columnRay X j ∈ quarterCircle := by
  by_cases hw : columnWeight X j = 0
  · simp [columnRay, hw, quarterCircle]
  have hwpos : 0 < columnWeight X j := lt_of_le_of_ne (columnWeight_nonneg X j) (Ne.symm hw)
  have hspos : 0 < Real.sqrt (columnWeight X j) := Real.sqrt_pos.2 hwpos
  have hs : Real.sqrt (columnWeight X j) ^ 2 = columnWeight X j :=
    Real.sq_sqrt hwpos.le
  simp only [columnRay, hw, ite_false, quarterCircle, Set.mem_ofPred_eq]
  refine ⟨div_nonneg (hX 0) hspos.le, div_nonneg (hX 1) hspos.le, ?_⟩
  field_simp [hspos.ne']
  simpa only [columnWeight] using hs.symm

omit [Fintype J] in
theorem recoverRows_rowsToWeights (X : Matrix (Fin 2) J ℝ) :
    recoverRows (rowsToWeights X) = X := by
  ext i j
  by_cases hw : columnWeight X j = 0
  · have h0 := columnWeight_zero hw
    fin_cases i <;> simp [recoverRows, rowsToWeights, columnRay, hw, h0.1, h0.2]
  · have hs : Real.sqrt (columnWeight X j) ≠ 0 :=
      (Real.sqrt_pos.2 (lt_of_le_of_ne (columnWeight_nonneg X j) (Ne.symm hw))).ne'
    simp [recoverRows, rowsToWeights, columnRay, hw, mul_div_cancel₀, hs]

theorem recoverRows_gramFirst {P : WeightedRays J} (hw : ∀ j, 0 ≤ P.1 j) :
    gramFirst (recoverRows P) = weightedFirst P := by
  unfold gramFirst recoverRows weightedFirst
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.of_apply, mul_pow, Real.sq_sqrt (hw j)]

theorem recoverRows_gramSecond {P : WeightedRays J} (hw : ∀ j, 0 ≤ P.1 j) :
    gramSecond (recoverRows P) = weightedSecond P := by
  unfold gramSecond recoverRows weightedSecond
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.of_apply, mul_pow, Real.sq_sqrt (hw j)]

theorem recoverRows_gramCross {P : WeightedRays J} (hw : ∀ j, 0 ≤ P.1 j) :
    gramCross (recoverRows P) = weightedCross P := by
  unfold gramCross recoverRows weightedCross
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.of_apply]
  calc
    _ = Real.sqrt (P.1 j) ^ 2 * P.2 j 0 * P.2 j 1 := by ring
    _ = _ := by rw [Real.sq_sqrt (hw j)]

theorem recoverRows_mem {a b c : ℝ} {P : WeightedRays J}
    (hP : P ∈ weightedGramFiber a b c) : recoverRows P ∈ gramFiber a b c := by
  have hw (j : J) : 0 ≤ P.1 j := (hP.1 j).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    have hd : 0 ≤ P.2 j i := by
      fin_cases i
      · exact (hP.2.1 j).1
      · exact (hP.2.1 j).2.1
    exact mul_nonneg (Real.sqrt_nonneg _) hd
  · rw [recoverRows_gramFirst hw]
    exact hP.2.2.1
  · rw [recoverRows_gramSecond hw]
    exact hP.2.2.2.1
  · rw [recoverRows_gramCross hw]
    exact hP.2.2.2.2

theorem rowsToWeights_mem {a b c : ℝ} {X : Matrix (Fin 2) J ℝ}
    (hX : X ∈ gramFiber a b c) : rowsToWeights X ∈ weightedGramFiber a b c := by
  have hw (j : J) : 0 ≤ (rowsToWeights X).1 j := columnWeight_nonneg X j
  refine ⟨?_, fun j => columnRay_mem (fun i => hX.1 i j), ?_, ?_, ?_⟩
  · intro j
    refine ⟨hw j, ?_⟩
    have h0 := Finset.single_le_sum (fun k _ => sq_nonneg (X 0 k)) (Finset.mem_univ j)
    have h1 := Finset.single_le_sum (fun k _ => sq_nonneg (X 1 k)) (Finset.mem_univ j)
    change X 0 j ^ 2 ≤ gramFirst X at h0
    change X 1 j ^ 2 ≤ gramSecond X at h1
    change columnWeight X j ≤ a + b
    unfold columnWeight
    rw [hX.2.1] at h0
    rw [hX.2.2.1] at h1
    linarith
  · rw [← recoverRows_gramFirst hw, recoverRows_rowsToWeights]
    exact hX.2.1
  · rw [← recoverRows_gramSecond hw, recoverRows_rowsToWeights]
    exact hX.2.2.1
  · rw [← recoverRows_gramCross hw, recoverRows_rowsToWeights]
    exact hX.2.2.2

def weightedObjective (h : (Fin 2 → ℝ) → ℝ) (P : WeightedRays J) : ℝ :=
  ∑ j, P.1 j * h (P.2 j)

def columnObjective (h : (Fin 2 → ℝ) → ℝ) (X : Matrix (Fin 2) J ℝ) : ℝ :=
  ∑ j, h (fun i => X i j)

theorem weightedObjective_continuousOn {a b c : ℝ} {h : (Fin 2 → ℝ) → ℝ}
    (hh : ContinuousOn h quarterCircle) :
    ContinuousOn (weightedObjective h) (weightedGramFiber (J := J) a b c) := by
  apply continuousOn_finsetSum
  intro j _
  apply ContinuousOn.mul (by fun_prop)
  exact hh.comp' (by fun_prop) (fun P hP => hP.2.1 j)

theorem columnObjective_recover {h : (Fin 2 → ℝ) → ℝ}
    (hh : ∀ (x : Fin 2 → ℝ) (t : ℝ), h (t • x) = t ^ 2 * h x)
    {P : WeightedRays J} (hw : ∀ j, 0 ≤ P.1 j) :
    columnObjective h (recoverRows P) = weightedObjective h P := by
  unfold columnObjective weightedObjective
  apply Finset.sum_congr rfl
  intro j _
  change h (Real.sqrt (P.1 j) • P.2 j) = _
  rw [hh, Real.sq_sqrt (hw j)]

theorem exists_columnObjective_max {a b c : ℝ} {h : (Fin 2 → ℝ) → ℝ}
    (hne : (gramFiber (J := J) a b c).Nonempty)
    (hc : ContinuousOn h quarterCircle)
    (hh : ∀ (x : Fin 2 → ℝ) (t : ℝ), h (t • x) = t ^ 2 * h x) :
    ∃ X ∈ gramFiber (J := J) a b c, ∀ Y ∈ gramFiber (J := J) a b c,
      columnObjective h Y ≤ columnObjective h X := by
  obtain ⟨X0, hX0⟩ := hne
  have hne' : (weightedGramFiber (J := J) a b c).Nonempty :=
    ⟨rowsToWeights X0, rowsToWeights_mem hX0⟩
  obtain ⟨P, hP, hmax⟩ := (weightedGramFiber_compact a b c).exists_isMaxOn hne'
    (weightedObjective_continuousOn hc)
  refine ⟨recoverRows P, recoverRows_mem hP, ?_⟩
  intro Y hY
  have hwP (j : J) : 0 ≤ P.1 j := (hP.1 j).1
  have hwY (j : J) : 0 ≤ (rowsToWeights Y).1 j := columnWeight_nonneg Y j
  rw [columnObjective_recover hh hwP]
  have heq := columnObjective_recover hh hwY
  rw [recoverRows_rowsToWeights] at heq
  rw [heq]
  exact hmax (rowsToWeights_mem hY)

end

end ResearchMain.DiagonalSchatten
