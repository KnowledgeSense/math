import MainTheorems.Chollet.RankCoefficients.GramPolynomial
import MainTheorems.Chollet.RankCoefficients.AssignmentSplit
import MainTheorems.Chollet.RankCoefficients.FixedColumns
import MainTheorems.Chollet.RankCoefficients.ComponentGram
import Mathlib.Data.Matrix.ColumnRowPartitioned

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I E : Type*} [Fintype I] [Fintype E] [instI : DecidableEq I]

def splitColumns (U : Matrix I E ℂ) (D : Matrix I I ℂ) (x : I → ℂ) :
    Matrix I (E ⊕ (I ⊕ Unit)) ℂ := fun i =>
  Sum.elim (U i) (Sum.elim (D i) (fun _ => x i))

def splitDegree (f : I → E ⊕ (I ⊕ Unit)) : ℕ :=
  ∑ i, Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1)) (f i)

def patternPolynomial (U : Matrix I E ℂ) (D : Matrix I I ℂ) (x : I → ℂ)
    (s : Finset I) (l : s → E) : Polynomial ℂ :=
  ∑ r : {i : I // i ∉ s} → I ⊕ Unit,
    Polynomial.C (((‖((splitColumns U D x).submatrix id
      (assembleAssignment ⟨s, l, r⟩)).permanent‖ ^ 2 : ℝ) : ℂ)) *
      Polynomial.X ^ assignmentDegree r

omit [Fintype E] instI in
theorem assignmentDegree_sum (f : I → E ⊕ Unit) :
    assignmentDegree f = ∑ i, Sum.elim (fun _ => 0) (fun _ => 1) (f i) := by
  simp only [assignmentDegree, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases f i <;> simp [rankWeight]

omit [Fintype E] in
theorem splitDegree_assemble (s : Finset I) (l : s → E)
    (r : {i : I // i ∉ s} → I ⊕ Unit) :
    splitDegree (assembleAssignment ⟨s, l, r⟩) = assignmentDegree r := by
  classical
  let : DecidableEq I := instI
  rw [splitDegree, assignmentDegree_sum]
  let F : I → ℕ := fun i =>
    Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))
      (assembleAssignment ⟨s, l, r⟩ i)
  have hs : (∑ i ∈ s, F i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [F, assembleAssignment, dite_eq_left hi, Sum.elim_inl]
  have hr : (∑ i ∈ Finset.univ \ s, F i) =
      ∑ i : {i : I // i ∉ s}, Sum.elim (fun _ => 0) (fun _ => 1) (r i) := by
    rw [Finset.sum_subtype (p := fun i : I => i ∉ s)
      (Finset.univ \ s) (fun _ => by simp) F]
    apply Finset.sum_congr rfl
    intro i _
    simp only [F, assembleAssignment, dite_eq_right i.property, Sum.elim_inr]
  change (∑ i, F i) = _
  have hsplit : (∑ i, F i) = (∑ i ∈ s, F i) + ∑ i ∈ Finset.univ \ s, F i := by
    rw [← Finset.sum_union Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset (Finset.subset_univ s)]
  rw [hsplit, hs, zero_add, hr]

theorem gram_assignment_polynomial_split (U : Matrix I E ℂ) (D : Matrix I I ℂ)
    (x : I → ℂ) :
    Polynomial.C (Fintype.card (Equiv.Perm I) : ℂ) *
        rankPolynomial ((Matrix.fromCols U D) * (Matrix.fromCols U D).conjTranspose) x =
      ∑ s : Finset I, ∑ l : s → E, patternPolynomial U D x s l := by
  classical
  let : DecidableEq I := instI
  rw [gram_assignment_polynomial, assignmentPolynomial]
  let e : (I → (E ⊕ I) ⊕ Unit) ≃ (I → E ⊕ (I ⊕ Unit)) :=
    Equiv.piCongrRight (fun _ => Equiv.sumAssoc E I Unit)
  have he : (∑ f : I → (E ⊕ I) ⊕ Unit,
      Polynomial.C (((‖((augmentedColumns (Matrix.fromCols U D) x).submatrix id f).permanent‖ ^
        2 : ℝ) : ℂ)) * Polynomial.X ^ assignmentDegree f) =
      ∑ f : I → E ⊕ (I ⊕ Unit),
        Polynomial.C (((‖((splitColumns U D x).submatrix id f).permanent‖ ^ 2 : ℝ) : ℂ)) *
          Polynomial.X ^ splitDegree f := by
    apply Fintype.sum_equiv e
    intro f
    have hA : (augmentedColumns (Matrix.fromCols U D) x).submatrix id f =
        (splitColumns U D x).submatrix id (e f) := by
      funext i j
      change augmentedColumns (Matrix.fromCols U D) x i (f j) =
        splitColumns U D x i (Equiv.sumAssoc E I Unit (f j))
      cases f j with
      | inl a => cases a <;> rfl
      | inr a => rfl
    have hk : assignmentDegree f = splitDegree (e f) := by
      rw [assignmentDegree_sum, splitDegree]
      apply Finset.sum_congr rfl
      intro i _
      change Sum.elim (fun _ => (0 : ℕ)) (fun _ => 1) (f i) =
        Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))
          (Equiv.sumAssoc E I Unit (f i))
      cases f i with
      | inl a => cases a <;> rfl
      | inr a => rfl
    rw [hA, hk]
  rw [he, sum_assignments_split]
  simp only [splitDegree_assemble, patternPolynomial]

omit [Fintype E] instI in
theorem assignmentDegree_reindex {T : Type*} [Fintype T]
    (e : T ≃ I) (f : I → E ⊕ Unit) : assignmentDegree (fun t => f (e t)) =
      assignmentDegree f := by
  simp only [assignmentDegree_sum]
  exact Fintype.sum_equiv e
    (fun t => Sum.elim (fun _ : E => (0 : ℕ)) (fun _ => 1) (f (e t)))
    (fun i => Sum.elim (fun _ : E => (0 : ℕ)) (fun _ => 1) (f i)) (fun _ => rfl)

omit [Fintype E] in
theorem selected_split_columns (U : Matrix I E ℂ) (D : Matrix I I ℂ)
    (x : I → ℂ) (s : Finset I) (l : s → E)
    (r : {i : I // i ∉ s} → I ⊕ Unit) :
    (∏ j ∈ s, linearForm (fun i => splitColumns U D x i
      (assembleAssignment ⟨s, l, r⟩ j))) =
        ∏ j : s, linearForm (fun i => U i (l j)) := by
  classical
  let : DecidableEq I := instI
  rw [Finset.prod_subtype s (fun _ => Iff.rfl)]
  apply Finset.prod_congr rfl
  intro j _
  apply congrArg linearForm
  funext i
  simp only [assembleAssignment, dite_eq_left j.property, splitColumns, Sum.elim_inl]

omit [Fintype E] in
theorem patternPolynomial_zero (U : Matrix I E ℂ) (D : Matrix I I ℂ)
    (x : I → ℂ) (s : Finset I) (l : s → E)
    (h : (∏ j : s, linearForm (fun i => U i (l j))) = 0) :
    patternPolynomial U D x s l = 0 := by
  rw [patternPolynomial]
  apply Finset.sum_eq_zero
  intro r _
  have hp := permanent_fixed_zero
    ((splitColumns U D x).submatrix id (assembleAssignment ⟨s, l, r⟩)) s
    ((selected_split_columns U D x s l r).trans h)
  rw [hp, norm_zero, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero,
    map_zero, zero_mul]

omit [Fintype E] in
theorem patternPolynomial_contraction (U : Matrix I E ℂ) (D : Matrix I I ℂ)
    (x : I → ℂ) (s : Finset I) (l : s → E) (p : RootedPartition I) (c : ℂ)
    (h : (∏ j : s, linearForm (fun i => U i (l j))) = scalar c * p.polynomial)
    (e : p.parts ≃ {i : I // i ∉ s}) :
    patternPolynomial U D x s l =
      Polynomial.C (((‖c‖ ^ 2 : ℝ) : ℂ)) *
        assignmentPolynomial (fun t j => p.contraction (fun i => D i j) t)
          (p.contraction x) := by
  classical
  let : DecidableEq I := instI
  dsimp only [patternPolynomial, assignmentPolynomial]
  rw [Finset.mul_sum]
  let er : (p.parts → I ⊕ Unit) ≃ ({i : I // i ∉ s} → I ⊕ Unit) :=
    Equiv.arrowCongr e (Equiv.refl _)
  symm
  apply Fintype.sum_equiv er
  intro r
  let f := assembleAssignment ⟨s, l, er r⟩
  let A : Matrix I I ℂ := (splitColumns U D x).submatrix id f
  have hA : (∏ j ∈ s, linearForm (fun i => A i j)) = scalar c * p.polynomial := by
    exact (selected_split_columns U D x s l (er r)).trans h
  have hc := permanent_fixed_columns A s p c hA e
  have hM : p.contractionMatrix (fun i t => A i (e t)) =
      (augmentedColumns (fun t j => p.contraction (fun i => D i j) t)
        (p.contraction x)).submatrix id r := by
    funext t u
    change p.contraction (fun i => A i (e u)) t = _
    simp only [A, Matrix.submatrix_apply, id_eq, f, assembleAssignment,
      dite_eq_right (e u).property, splitColumns, Sum.elim_inr]
    have he : er r (e u) = r u := by simp [er]
    rw [he]
    cases r u <;> rfl
  rw [hM] at hc
  have hk : assignmentDegree (er r) = assignmentDegree r := by
    have hh := assignmentDegree_reindex e (er r)
    simpa [er] using hh.symm
  rw [hk, hc, norm_mul, mul_pow, Complex.ofReal_mul, Polynomial.C_mul]
  ring

end ResearchMain.Chollet.RankCoefficients




