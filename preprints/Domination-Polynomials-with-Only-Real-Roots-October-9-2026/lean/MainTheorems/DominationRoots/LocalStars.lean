import MainTheorems.DominationRoots.SubsetFibers
import Mathlib.Data.Finset.Option

namespace ResearchMain.DominationRoots

open Classical Polynomial

variable {W : Type} [Fintype W]

noncomputable def optionSubset (b : Bool) (T : Finset W) : Finset (Option W) :=
  if b then T.insertNone else T.map Function.Embedding.some

omit [Fintype W] in
theorem optionSubset_card (b : Bool) (T : Finset W) :
    (optionSubset b T).card = T.card + if b then 1 else 0 := by
  cases b <;> simp [optionSubset]

noncomputable def optionSubsetEquiv : Finset (Option W) ≃ Bool × Finset W where
  toFun S := (decide (none ∈ S), S.eraseNone)
  invFun p := optionSubset p.1 p.2
  left_inv S := by
    by_cases hn : none ∈ S
    · simp [optionSubset, hn, Finset.insert_eq_of_mem hn]
    · simp [optionSubset, hn]
  right_inv p := by
    rcases p with ⟨b, T⟩
    cases b <;> simp [optionSubset]

def CoversStar (S : Finset (Option W)) : Prop :=
  none ∈ S ∨ ∀ w, some w ∈ S

theorem coversStar_optionSubset (b : Bool) (T : Finset W) :
    CoversStar (optionSubset b T) ↔ b = true ∨ T = Finset.univ := by
  cases b <;> simp [optionSubset, CoversStar, Finset.eq_univ_iff_forall]

theorem subset_monomial_sum :
    (∑ T : Finset W, (X : ℤ[X]) ^ T.card) = (1 + X) ^ Fintype.card W := by
  have h := Fintype.prod_add (fun _ : W => (X : ℤ[X])) (fun _ : W => (1 : ℤ[X]))
  simp only [Finset.prod_const, Finset.card_univ, one_pow, mul_one] at h
  simpa only [add_comm X 1] using h.symm

theorem star_subset_polynomial :
    (∑ S : Finset (Option W), if CoversStar S then (X : ℤ[X]) ^ S.card else 0) =
      starFactor (Fintype.card W) := by
  calc
    _ = ∑ p : Bool × Finset W,
        if p.1 = true ∨ p.2 = Finset.univ then
          (X : ℤ[X]) ^ (p.2.card + if p.1 then 1 else 0) else 0 := by
      apply Fintype.sum_equiv (optionSubsetEquiv (W := W))
      intro S
      have hinv := (optionSubsetEquiv (W := W)).left_inv S
      change optionSubset (decide (none ∈ S)) S.eraseNone = S at hinv
      change _ = if decide (none ∈ S) = true ∨ S.eraseNone = Finset.univ then _ else _
      conv_lhs => rw [← hinv, coversStar_optionSubset, optionSubset_card]
      by_cases hn : none ∈ S <;> simp [optionSubsetEquiv, hn]
    _ = (∑ T : Finset W, if T = Finset.univ then (X : ℤ[X]) ^ T.card else 0) +
        ∑ T : Finset W, (X : ℤ[X]) ^ (T.card + 1) := by
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp [add_comm]
    _ = (X : ℤ[X]) ^ Fintype.card W + X * (1 + X) ^ Fintype.card W := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left, Finset.card_univ]
      simp_rw [pow_succ, mul_comm _ X]
      rw [← Finset.mul_sum, subset_monomial_sum]
    _ = _ := by rw [starFactor, add_comm]

end ResearchMain.DominationRoots
