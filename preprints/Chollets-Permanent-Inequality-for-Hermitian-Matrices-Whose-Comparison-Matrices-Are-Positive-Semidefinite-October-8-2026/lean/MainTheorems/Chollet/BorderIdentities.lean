import MainTheorems.Chollet.BorderExpansion
import MainTheorems.Chollet.RankPolynomial
import MainTheorems.Chollet.PermanentEquivalence

noncomputable section

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [DecidableEq I]

def borderEquivalence : Option I ≃ Unit ⊕ I where
  toFun
    | none => Sum.inl ()
    | some i => Sum.inr i
  invFun
    | Sum.inl _ => none
    | Sum.inr i => some i
  left_inv i := by cases i <;> rfl
  right_inv i := by cases i with
    | inl u => cases u; rfl
    | inr i => rfl

theorem border_permanent (a : ℝ) (z : I → ℂ) (B : Matrix I I ℂ) :
    (border a z B).permanent = (a : ℂ) * B.permanent +
      ∑ π : Equiv.Perm I, ∑ i, z (π i) * star (z i) *
        ∏ j ∈ Finset.univ.erase i, B (π j) j := by
  have he : (border a z B).submatrix borderEquivalence borderEquivalence =
      optionBorder (a : ℂ) (fun i => star (z i)) z B := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [← permanent_reindex borderEquivalence (border a z B), he,
    permanent_optionBorder]

omit [Fintype I] [DecidableEq I] in
theorem normalizedBorder_outer (a : ℝ) (z : I → ℂ) (ha : 0 < a) (i j : I) :
    (a : ℂ) * (normalizedBorder a z i * star (normalizedBorder a z j)) =
      z i * star (z j) := by
  have hs : (Real.sqrt a : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ha).ne'
  have he : (a : ℂ) = (Real.sqrt a : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ha.le]
  rw [he]
  simp only [normalizedBorder, Complex.star_def, map_div₀, Complex.conj_ofReal]
  field_simp [hs]

theorem border_permanent_normalized (a : ℝ) (z : I → ℂ) (B : Matrix I I ℂ)
    (ha : 0 < a) :
    (border a z B).permanent =
      (a : ℂ) * (B.permanent + rankFirst B (normalizedBorder a z)) := by
  rw [border_permanent, mul_add]
  apply congrArg (fun c => (a : ℂ) * B.permanent + c)
  simp only [rankFirst, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro i _
  rw [← normalizedBorder_outer a z ha (π i) i]
  ring

end ResearchMain.Chollet
