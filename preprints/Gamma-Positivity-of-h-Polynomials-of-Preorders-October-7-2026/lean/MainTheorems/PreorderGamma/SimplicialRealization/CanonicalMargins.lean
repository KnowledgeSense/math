import MainTheorems.PreorderGamma.SimplicialRealization.CanonicalDegree

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def marginProjection (d s : Option E → ℕ) : E → ℤ :=
  fun i => (d (some i) : ℤ) - (s (some i) : ℤ)

def originalOverlap (d s : Option E → ℕ) : E → ℕ :=
  fun i => min (d (some i)) (s (some i))

def overlapMass (d s : Option E → ℕ) : ℕ := ∑ i, originalOverlap d s i

omit [DecidableEq E] [Preorder E] in
theorem positiveMass_overlap (d s : Option E → ℕ) :
    positiveMass (marginProjection d s) + overlapMass d s = ∑ i : E, d (some i) := by
  rw [positiveMass, overlapMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [marginProjection, originalOverlap]
  omega

omit [DecidableEq E] [Preorder E] in
theorem negativeMass_overlap (d s : Option E → ℕ) :
    negativeMass (marginProjection d s) + overlapMass d s = ∑ i : E, s (some i) := by
  rw [negativeMass, overlapMass, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [marginProjection, originalOverlap]
  omega

omit [DecidableEq E] [Preorder E] in
theorem overlapMass_le_total (d s : Option E → ℕ) (t : ℕ) (hd : (∑ a, d a) = t) :
    overlapMass d s ≤ t := by
  have hp := positiveMass_overlap d s
  rw [Fintype.sum_option] at hd
  omega

omit [DecidableEq E] in
theorem normalForm_canonical_left (d s : Option E → ℕ) (t : ℕ)
    (hd : (∑ a, d a) = t) (p : NaturalTransport augmentedRelation d s)
    (hp : ∀ i : E, p.flow (some i) (some i) = originalOverlap d s i) :
    (fun a => d a - originalDiagonalValue p a) =
      canonicalLeftMargin (marginProjection d s) (t - overlapMass d s) := by
  funext a
  cases a with
  | none =>
    simp only [originalDiagonalValue, Nat.sub_zero, canonicalLeftMargin]
    have h := positiveMass_overlap d s
    rw [Fintype.sum_option] at hd
    omega
  | some i =>
    simp only [originalDiagonalValue, hp i, canonicalLeftMargin, marginProjection,
      originalOverlap]
    omega

omit [DecidableEq E] in
theorem normalForm_canonical_right (d s : Option E → ℕ) (t : ℕ)
    (hs : (∑ a, s a) = t) (p : NaturalTransport augmentedRelation d s)
    (hp : ∀ i : E, p.flow (some i) (some i) = originalOverlap d s i) :
    (fun a => s a - originalDiagonalValue p a) =
      canonicalRightMargin (marginProjection d s) (t - overlapMass d s) := by
  funext a
  cases a with
  | none =>
    simp only [originalDiagonalValue, Nat.sub_zero, canonicalRightMargin]
    have h := negativeMass_overlap d s
    rw [Fintype.sum_option] at hs
    omega
  | some i =>
    simp only [originalDiagonalValue, hp i, canonicalRightMargin, marginProjection,
      originalOverlap]
    omega

theorem margins_canonical_degree (d s : Option E → ℕ) (t : ℕ)
    (hd : (∑ a, d a) = t) (hs : (∑ b, s b) = t)
    (p : NaturalTransport augmentedRelation d s) :
    IsCanonicalDegree (marginProjection d s) (t - overlapMass d s) := by
  obtain ⟨q, hq⟩ := exists_originalDiagonal_normalForm p
  have hq' : ∀ i : E, q.flow (some i) (some i) = originalOverlap d s i := hq
  have hp := positiveMass_overlap d s
  have hn := negativeMass_overlap d s
  have hd' := hd
  have hs' := hs
  rw [Fintype.sum_option] at hd' hs'
  refine ⟨by omega, by omega, ?_⟩
  have hl := normalForm_canonical_left d s t hd q hq'
  have hr := normalForm_canonical_right d s t hs q hq'
  rw [← hl, ← hr]
  exact ⟨stripOriginalDiagonal q⟩

theorem quotientLatticeDegree_projection_bound (d s : Option E → ℕ) (t : ℕ)
    (hd : (∑ a, d a) = t) (hs : (∑ b, s b) = t)
    (p : NaturalTransport augmentedRelation d s) :
    overlapMass d s + quotientLatticeDegree (marginProjection d s) ≤ t := by
  have hk := quotientLatticeDegree_le (marginProjection d s)
    (margins_canonical_degree d s t hd hs p)
  have ho := overlapMass_le_total d s t hd
  omega

end ResearchMain.PreorderGamma.SimplicialRealization
