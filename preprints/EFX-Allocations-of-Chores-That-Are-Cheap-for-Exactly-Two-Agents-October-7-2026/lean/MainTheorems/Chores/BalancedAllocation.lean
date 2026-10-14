import MainTheorems.Chores.SeparatedHall

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

omit [DecidableEq A] [DecidableEq E] in
theorem average_floor_bounds {μ : ℝ} (hn : 0 < Fintype.card A)
    (hμ : μ * Fintype.card A = Fintype.card E) :
    (Fintype.card E / Fintype.card A : ℕ) ≤ μ ∧
      μ < (Fintype.card E / Fintype.card A : ℕ) + 1 := by
  have hdecomp := Nat.mod_add_div (Fintype.card E) (Fintype.card A)
  have hmod := Nat.mod_lt (Fintype.card E) hn
  have hd : ((Fintype.card E % Fintype.card A : ℕ) : ℝ) +
      Fintype.card A * (Fintype.card E / Fintype.card A : ℕ) = Fintype.card E :=
    by exact_mod_cast hdecomp
  have hm : ((Fintype.card E % Fintype.card A : ℕ) : ℝ) < Fintype.card A :=
    by exact_mod_cast hmod
  have hn' : (0 : ℝ) < Fintype.card A := by exact_mod_cast hn
  have hnon : (0 : ℝ) ≤ (Fintype.card E % Fintype.card A : ℕ) := by positivity
  constructor <;> nlinarith

theorem separated_balanced_allocation (M : TwoCheapModel A E) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : μ * Fintype.card A = Fintype.card E) (hn : 0 < Fintype.card A)
    {S : Finset A} (hS : MaxDeficient M μ S) :
    ∃ f : E → A, (∀ e, f e ∈ separatedAllowed M S e) ∧ ∀ a,
      Fintype.card E / Fintype.card A ≤ (bundle f a).card ∧
      (bundle f a).card ≤ Fintype.card E / Fintype.card A + 1 := by
  let q := Fintype.card E / Fintype.card A
  obtain ⟨hql, hqu⟩ := average_floor_bounds hn hμ
  apply bounded_allocation (separatedAllowed M S) (fun _ => q) (fun _ => q + 1)
    (fun _ => Nat.le_succ _)
  · intro U
    have hc := separated_incident_bound M hμ0 hμ hS U
    have hcard : (0 : ℝ) ≤ U.card := by positivity
    have hle : (q : ℝ) * U.card ≤ (incidentAllowed (separatedAllowed M S) U).card := by
      nlinarith
    simpa [Finset.sum_const, mul_comm] using (by exact_mod_cast hle :
      q * U.card ≤ (incidentAllowed (separatedAllowed M S) U).card)
  · intro U
    have hc := separated_confined_bound M hμ0 hμ hS U
    have hcard : (0 : ℝ) ≤ U.card := by positivity
    have hle : ((confinedAllowed (separatedAllowed M S) U).card : ℝ) ≤ (q + 1) * U.card := by
      nlinarith
    simpa [Finset.sum_const, mul_comm] using (by exact_mod_cast hle :
      (confinedAllowed (separatedAllowed M S) U).card ≤ (q + 1) * U.card)

omit [Fintype A] [DecidableEq E] in
theorem all_cheap_bundleCost (M : TwoCheapModel A E) (r : ℝ) (f : E → A)
    (hf : ∀ e, M.Cheap (f e) e) (a : A) :
    bundleCost M r a (bundle f a) = (bundle f a).card := by
  unfold bundleCost
  calc
    _ = ∑ e ∈ bundle f a, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      have hc := hf e
      rw [(mem_bundle f a e).mp he] at hc
      simp [itemCost, hc]
    _ = _ := by simp

omit [Fintype A] in
theorem balanced_cheap_efx (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r) (q : ℕ)
    (f : E → A) (hc : ∀ e, M.Cheap (f e) e)
    (hs : ∀ a, q ≤ (bundle f a).card ∧ (bundle f a).card ≤ q + 1) : EFX M r f := by
  intro a b _ e he
  have hec := hc e
  rw [(mem_bundle f a e).mp he] at hec
  rw [bundleCost_erase M r a he, all_cheap_bundleCost M r f hc, itemCost,
    ite_eq_left hec, bundleCost_eq_size]
  have ha : ((bundle f a).card : ℝ) ≤ q + 1 := by exact_mod_cast (hs a).2
  have hb : (q : ℝ) ≤ (bundle f b).card := by exact_mod_cast (hs b).1
  have hexp : (0 : ℝ) ≤ expensiveCount M f a b := by positivity
  nlinarith

theorem no_deficiency_efx (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r) {μ : ℝ}
    (hμ0 : 0 ≤ μ) (hμ : μ * Fintype.card A = Fintype.card E)
    (hn : 0 < Fintype.card A) (h : ∀ U : Finset A, deficiency M μ U ≤ 0) :
    ∃ f : E → A, EFX M r f := by
  have hm : MaxDeficient M μ ∅ := by
    intro U
    simpa only [deficiency_empty] using h U
  obtain ⟨f, hf, hs⟩ := separated_balanced_allocation M hμ0 hμ hn hm
  refine ⟨f, balanced_cheap_efx M hr _ f ?_ hs⟩
  intro e
  simpa [separatedAllowed, mem_endpointAllowed] using hf e

end ResearchMain.Chores
