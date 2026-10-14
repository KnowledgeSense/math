import MainTheorems.PreorderGamma.SimplicialRealization.DiagonalStripping

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def positiveMass (z : E → ℤ) : ℕ := ∑ i, (z i).toNat

def negativeMass (z : E → ℤ) : ℕ := ∑ i, (-z i).toNat

def canonicalLeftMargin (z : E → ℤ) (k : ℕ) : Option E → ℕ
  | none => k - positiveMass z
  | some i => (z i).toNat

def canonicalRightMargin (z : E → ℤ) (k : ℕ) : Option E → ℕ
  | none => k - negativeMass z
  | some i => (-z i).toNat

def IsCanonicalDegree (z : E → ℤ) (k : ℕ) : Prop :=
  positiveMass z ≤ k ∧ negativeMass z ≤ k ∧
    Nonempty (NaturalTransport augmentedRelation (canonicalLeftMargin z k)
      (canonicalRightMargin z k))

noncomputable def canonicalStarTransport (z : E → ℤ) :
    NaturalTransport augmentedRelation
      (canonicalLeftMargin z (positiveMass z + negativeMass z))
      (canonicalRightMargin z (positiveMass z + negativeMass z)) where
  flow := fun a b => match a, b with
    | none, none => 0
    | some i, none => (z i).toNat
    | none, some j => (-z j).toNat
    | some _, some _ => 0
  supported := by
    intro a b hab
    cases a <;> cases b <;> simp_all [augmentedRelation]
  row_sum := by
    intro a
    cases a <;> simp [Fintype.sum_option, canonicalLeftMargin, negativeMass]
  column_sum := by
    intro b
    cases b <;> simp [Fintype.sum_option, canonicalRightMargin, positiveMass]

omit [DecidableEq E] in
theorem canonicalDegree_exists (z : E → ℤ) : ∃ k, IsCanonicalDegree z k :=
  ⟨positiveMass z + negativeMass z,
    Nat.le_add_right _ _, Nat.le_add_left _ _, ⟨canonicalStarTransport z⟩⟩

noncomputable def quotientLatticeDegree (z : E → ℤ) : ℕ := by
  classical
  exact Nat.find (canonicalDegree_exists z)

omit [DecidableEq E] in
theorem quotientLatticeDegree_spec (z : E → ℤ) :
    IsCanonicalDegree z (quotientLatticeDegree z) := by
  classical
  exact Nat.find_spec (canonicalDegree_exists z)

omit [DecidableEq E] in
theorem quotientLatticeDegree_le (z : E → ℤ) {k : ℕ} (hk : IsCanonicalDegree z k) :
    quotientLatticeDegree z ≤ k := by
  classical
  exact Nat.find_min' (canonicalDegree_exists z) hk

noncomputable def canonicalDegreeExtension (z : E → ℤ) (m k : ℕ)
    (hm : IsCanonicalDegree z m) (hmk : m ≤ k)
    (p : NaturalTransport augmentedRelation (canonicalLeftMargin z m)
      (canonicalRightMargin z m)) :
    NaturalTransport augmentedRelation (canonicalLeftMargin z k)
      (canonicalRightMargin z k) where
  flow := fun a b => p.flow a b + (k - m) * transportUnitEdge none none a b
  supported := by
    intro a b hab
    have h : ¬(a = none ∧ b = none) := by
      rintro ⟨rfl, rfl⟩
      exact hab trivial
    simp [p.supported a b hab, transportUnitEdge, h]
  row_sum := by
    intro a
    rw [Finset.sum_add_distrib, p.row_sum, ← Finset.mul_sum,
      transportUnitEdge_row_sum]
    cases a with
    | none =>
      simp only [canonicalLeftMargin, ite_true, mul_one]
      have hpos := hm.1
      omega
    | some i => simp [canonicalLeftMargin]
  column_sum := by
    intro b
    rw [Finset.sum_add_distrib, p.column_sum, ← Finset.mul_sum,
      transportUnitEdge_column_sum]
    cases b with
    | none =>
      simp only [canonicalRightMargin, ite_true, mul_one]
      have hneg := hm.2.1
      omega
    | some i => simp [canonicalRightMargin]

theorem isCanonicalDegree_mono (z : E → ℤ) {m k : ℕ}
    (hm : IsCanonicalDegree z m) (hmk : m ≤ k) : IsCanonicalDegree z k := by
  obtain ⟨p⟩ := hm.2.2
  exact ⟨hm.1.trans hmk, hm.2.1.trans hmk,
    ⟨canonicalDegreeExtension z m k hm hmk p⟩⟩

theorem isCanonicalDegree_iff (z : E → ℤ) (k : ℕ) :
    IsCanonicalDegree z k ↔ quotientLatticeDegree z ≤ k :=
  ⟨quotientLatticeDegree_le z, fun h =>
    isCanonicalDegree_mono z (quotientLatticeDegree_spec z) h⟩

omit [DecidableEq E] in
theorem quotientLatticeDegree_le_masses (z : E → ℤ) :
    quotientLatticeDegree z ≤ positiveMass z + negativeMass z :=
  quotientLatticeDegree_le z
    ⟨Nat.le_add_right _ _, Nat.le_add_left _ _, ⟨canonicalStarTransport z⟩⟩

omit [DecidableEq E] in
@[simp] theorem quotientLatticeDegree_zero : quotientLatticeDegree (0 : E → ℤ) = 0 := by
  have h := quotientLatticeDegree_le_masses (0 : E → ℤ)
  apply Nat.eq_zero_of_le_zero
  simpa [positiveMass, negativeMass] using h

omit [DecidableEq E] in
theorem quotientLatticeDegree_eq_zero_iff (z : E → ℤ) :
    quotientLatticeDegree z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hs := quotientLatticeDegree_spec z
    rw [h] at hs
    have hp : positiveMass z = 0 := Nat.eq_zero_of_le_zero hs.1
    have hn : negativeMass z = 0 := Nat.eq_zero_of_le_zero hs.2.1
    funext i
    change z i = 0
    have hip : (z i).toNat ≤ positiveMass z :=
      Finset.single_le_sum (f := fun j : E => (z j).toNat)
        (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
    have hin : (-z i).toNat ≤ negativeMass z :=
      Finset.single_le_sum (f := fun j : E => (-z j).toNat)
        (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
    rw [hp] at hip
    rw [hn] at hin
    omega
  · rintro rfl
    exact quotientLatticeDegree_zero

end ResearchMain.PreorderGamma.SimplicialRealization
