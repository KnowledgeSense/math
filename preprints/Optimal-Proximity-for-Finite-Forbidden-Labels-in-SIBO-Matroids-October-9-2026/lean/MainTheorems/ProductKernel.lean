import MainTheorems.SIBOKernel
import MainTheorems.FiniteInterpolation

namespace ResearchMain.SIBO

open scoped BigOperators

/-- The product bound for interval differences meeting at least one forbidden set. -/
theorem multi_forbidden_interval_bound {m : ℕ} {ι : Type*} [Fintype ι]
    {A : ι → Type*} [∀ t, AddCommGroup (A t)]
    (T : ∀ t, Finset (A t)) (hzero : ∀ t, 0 ∉ T t)
    (s : Fin (m + 1) → ∀ t, A t)
    (hupper : ∀ i j, i < j → ∃ t, s j t - s i t ∈ T t) :
    m ≤ (∏ t, ((T t).card + 1)) - 1 := by
  classical
  choose χ c hc hz using fun t => finite_forbidden_annihilator (T t) (hzero t)
  let J := ∀ t, Fin ((T t).card + 1)
  let ψ (j : J) : AddChar (∀ t, A t) ℂ := {
    toFun := fun x => ∏ t, χ t (j t) (x t)
    map_zero_eq_one' := by simp
    map_add_eq_mul' := by
      intro x y
      simp only [Pi.add_apply, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]
  }
  let C (j : J) : ℂ := ∏ t, c t (j t)
  have heval (x : ∀ t, A t) :
      (∑ j : J, C j * ψ j x) = ∏ t, ∑ a, c t a * χ t a (x t) := by
    simp only [C, ψ, AddChar.coe_mk]
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun t a => c t a * χ t a (x t))).symm
  have hcoeff : (∑ j : J, C j) = 1 := by
    rw [show (∑ j : J, C j) = ∏ t, ∑ a, c t a from (Fintype.prod_sum c).symm]
    simp [hc]
  have hbound := character_interval_bound ψ C s (by
    intro i j hij
    obtain ⟨t, ht⟩ := hupper i j hij
    rw [characterKernel, heval]
    exact Finset.prod_eq_zero (Finset.mem_univ t) (hz t _ ht))
    (by rw [hcoeff]; exact one_ne_zero)
  simpa only [J, Fintype.card_pi, Fintype.card_fin] using hbound

end ResearchMain.SIBO
