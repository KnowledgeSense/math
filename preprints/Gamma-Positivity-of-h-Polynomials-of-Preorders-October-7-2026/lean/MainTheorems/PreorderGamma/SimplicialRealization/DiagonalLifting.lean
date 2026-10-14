import MainTheorems.PreorderGamma.SimplicialRealization.CanonicalMargins

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def diagonalValue (g : E → ℕ) : Option E → ℕ
  | none => 0
  | some i => g i

def diagonalAddition (g : E → ℕ) (a b : Option E) : ℕ :=
  if a = b then diagonalValue g a else 0

omit [Preorder E] in
theorem diagonalAddition_row (g : E → ℕ) (a : Option E) :
    (∑ b, diagonalAddition g a b) = diagonalValue g a := by
  classical
  calc
    _ = diagonalAddition g a a := by
      apply Finset.sum_eq_single a
      · intro b hb hba
        simp [diagonalAddition, Ne.symm hba]
      · simp
    _ = _ := by simp [diagonalAddition]

omit [Preorder E] in
theorem diagonalAddition_column (g : E → ℕ) (b : Option E) :
    (∑ a, diagonalAddition g a b) = diagonalValue g b := by
  classical
  calc
    _ = diagonalAddition g b b := by
      apply Finset.sum_eq_single b
      · intro a ha hab
        simp [diagonalAddition, hab]
      · simp
    _ = _ := by simp [diagonalAddition]

def appendOriginalDiagonal {d s : Option E → ℕ}
    (p : NaturalTransport augmentedRelation d s) (g : E → ℕ) :
    NaturalTransport augmentedRelation
      (fun a => d a + diagonalValue g a) (fun b => s b + diagonalValue g b) where
  flow := fun a b => p.flow a b + diagonalAddition g a b
  supported := by
    intro a b hab
    have hne : a ≠ b := by
      rintro rfl
      cases a with
      | none => exact hab trivial
      | some i => exact hab le_rfl
    simp [p.supported a b hab, diagonalAddition, hne]
  row_sum := by
    intro a
    rw [Finset.sum_add_distrib, p.row_sum, diagonalAddition_row]
  column_sum := by
    intro b
    rw [Finset.sum_add_distrib, p.column_sum, diagonalAddition_column]

def liftedLeftMargin (z : E → ℤ) (g : E → ℕ) (t : ℕ) : Option E → ℕ :=
  fun a => canonicalLeftMargin z (t - ∑ i, g i) a + diagonalValue g a

def liftedRightMargin (z : E → ℤ) (g : E → ℕ) (t : ℕ) : Option E → ℕ :=
  fun a => canonicalRightMargin z (t - ∑ i, g i) a + diagonalValue g a

theorem liftedMargins_nonempty (z : E → ℤ) (g : E → ℕ) (t : ℕ)
    (hg : quotientLatticeDegree z + (∑ i, g i) ≤ t) :
    Nonempty (NaturalTransport augmentedRelation (liftedLeftMargin z g t)
      (liftedRightMargin z g t)) := by
  have hk : quotientLatticeDegree z ≤ t - ∑ i, g i := by omega
  obtain ⟨p⟩ := ((isCanonicalDegree_iff z (t - ∑ i, g i)).mpr hk).2.2
  exact ⟨appendOriginalDiagonal p g⟩

omit [DecidableEq E] in
theorem liftedLeftMargin_total (z : E → ℤ) (g : E → ℕ) (t : ℕ)
    (hg : quotientLatticeDegree z + (∑ i, g i) ≤ t) :
    (∑ a, liftedLeftMargin z g t a) = t := by
  have hk : quotientLatticeDegree z ≤ t - ∑ i, g i := by omega
  have hp := (quotientLatticeDegree_spec z).1
  have hmass : (∑ i, g i) ≤ t := by omega
  simp only [Fintype.sum_option, liftedLeftMargin, canonicalLeftMargin,
    diagonalValue, Nat.zero_add, Finset.sum_add_distrib]
  change (t - ∑ i, g i - positiveMass z) + positiveMass z + (∑ i, g i) = t
  omega

omit [DecidableEq E] in
theorem liftedRightMargin_total (z : E → ℤ) (g : E → ℕ) (t : ℕ)
    (hg : quotientLatticeDegree z + (∑ i, g i) ≤ t) :
    (∑ a, liftedRightMargin z g t a) = t := by
  have hk : quotientLatticeDegree z ≤ t - ∑ i, g i := by omega
  have hp := (quotientLatticeDegree_spec z).2.1
  have hmass : (∑ i, g i) ≤ t := by omega
  simp only [Fintype.sum_option, liftedRightMargin, canonicalRightMargin,
    diagonalValue, Nat.zero_add, Finset.sum_add_distrib]
  change (t - ∑ i, g i - negativeMass z) + negativeMass z + (∑ i, g i) = t
  omega

omit [DecidableEq E] [Preorder E] in
theorem liftedMargins_projection (z : E → ℤ) (g : E → ℕ) (t : ℕ) :
    marginProjection (liftedLeftMargin z g t) (liftedRightMargin z g t) = z := by
  funext i
  simp only [marginProjection, liftedLeftMargin, liftedRightMargin, canonicalLeftMargin,
    canonicalRightMargin, diagonalValue]
  omega

omit [DecidableEq E] [Preorder E] in
theorem liftedMargins_overlap (z : E → ℤ) (g : E → ℕ) (t : ℕ) :
    originalOverlap (liftedLeftMargin z g t) (liftedRightMargin z g t) = g := by
  funext i
  simp only [originalOverlap, liftedLeftMargin, liftedRightMargin, canonicalLeftMargin,
    canonicalRightMargin, diagonalValue]
  omega

omit [DecidableEq E] [Preorder E] in
theorem lift_original_left (d s : Option E → ℕ) (t : ℕ) (hd : (∑ a, d a) = t) :
    liftedLeftMargin (marginProjection d s) (originalOverlap d s) t = d := by
  funext a
  cases a with
  | none =>
    simp only [liftedLeftMargin, canonicalLeftMargin, diagonalValue, Nat.add_zero]
    change t - overlapMass d s - positiveMass (marginProjection d s) = d none
    have hp := positiveMass_overlap d s
    rw [Fintype.sum_option] at hd
    omega
  | some i =>
    simp only [liftedLeftMargin, canonicalLeftMargin, diagonalValue, marginProjection,
      originalOverlap]
    omega

omit [DecidableEq E] [Preorder E] in
theorem lift_original_right (d s : Option E → ℕ) (t : ℕ) (hs : (∑ a, s a) = t) :
    liftedRightMargin (marginProjection d s) (originalOverlap d s) t = s := by
  funext a
  cases a with
  | none =>
    simp only [liftedRightMargin, canonicalRightMargin, diagonalValue, Nat.add_zero]
    change t - overlapMass d s - negativeMass (marginProjection d s) = s none
    have hp := negativeMass_overlap d s
    rw [Fintype.sum_option] at hs
    omega
  | some i =>
    simp only [liftedRightMargin, canonicalRightMargin, diagonalValue, marginProjection,
      originalOverlap]
    omega

end ResearchMain.PreorderGamma.SimplicialRealization
