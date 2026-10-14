import MainTheorems.Chores.FrozenComparisons
import MainTheorems.Chores.DirectBuffer

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

omit [Fintype A] [DecidableEq E] in
theorem one_filler_expensive (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    (hf : Feasible M S f₀ f) {t : E} (ht : f₀ t ∈ S)
    (hfill : ∀ e, f₀ e ∈ S → (Filler M S e ↔ e = t)) {v : A} (hv : v ∈ S) :
    expensiveCount M f v v = if f t = v then 1 else 0 := by
  have htoken : Filler M S t := (hfill t ht).mpr rfl
  have hset : (bundle f v).filter (fun e => ¬M.Cheap v e) = ({t} : Finset E).filter (fun e => f e = v) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton, mem_bundle]
    constructor
    · intro he
      have hin : f e ∈ S := he.1 ▸ hv
      have hfi : Filler M S e := separated_expensive_filler M hf.1 (by rw [he.1]; exact he.2)
      have heq : e = t := (hfill e (feasible_original_inside M hf hin)).mp hfi
      exact ⟨heq, he.1⟩
    · intro he
      obtain ⟨heq, ho⟩ := he
      subst e
      exact ⟨ho, filler_not_cheap M hv htoken⟩
  unfold expensiveCount
  rw [hset]
  simp only [Finset.filter_singleton]
  split_ifs <;> simp

omit [Fintype A] in
theorem one_filler_bad_pair (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {t : E} (ht : f₀ t ∈ S) (hfill : ∀ e, f₀ e ∈ S → (Filler M S e ↔ e = t))
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) :
    UniqueBad M S f a b ∧ expensiveCount M f a a = 1 ∧ expensiveCount M f b b = 0 := by
  have hsource {c d : A} (hc : c ∈ S) (hbad : Bad M f c d) : f t = c := by
    have he := one_filler_expensive M hf.1 ht hfill hc
    have hp := bad_expensive_positive M hbad
    by_contra hn
    rw [ite_eq_right hn] at he
    omega
  have hta := hsource ha hbad
  have he : expensiveCount M f a a = 1 := by
    rw [one_filler_expensive M hf.1 ht hfill ha, ite_eq_left hta]
  have hbzero : expensiveCount M f b b = 0 := by
    have hc := (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hbad).1
    omega
  refine ⟨⟨hbad, ?_⟩, he, hbzero⟩
  intro c hc d hd hcd
  have hca : c = a := (hsource hc hcd).symm.trans hta
  subst c
  have hdb : d = b := by
    by_contra hn
    exact optimal_pair_no_other_outgoing M hf hs ha hb hd hbad hn hcd
  exact ⟨rfl, hdb⟩

theorem one_filler_optimal (M : TwoCheapModel A E) (S : Finset A) (f₀ : E → A)
    (hf₀ : Separated M S f₀) {q : ℕ}
    (hs₀ : ∀ c, q ≤ (bundle f₀ c).card ∧ (bundle f₀ c).card ≤ q + 1)
    {t : E} (ht : f₀ t ∈ S) (hfill : ∀ e, f₀ e ∈ S → (Filler M S e ↔ e = t)) :
    ∃ f : E → A, Optimal M S f₀ f ∧
      (∀ v ∈ S, expensiveCount M f v v ≤ 1) ∧
      ((∀ a ∈ S, ∀ b ∈ S, ¬Bad M f a b) ∨
        ∃ a b, a ∈ S ∧ b ∈ S ∧ UniqueBad M S f a b ∧
          expensiveCount M f a a = 1 ∧ expensiveCount M f b b = 0) := by
  obtain ⟨f, hf⟩ := exists_optimal M S f₀ hf₀
  have hs (c : A) : q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1 := by
    simpa only [hf.1.2.1 c] using hs₀ c
  refine ⟨f, hf, ?_, ?_⟩
  · intro v hv
    rw [one_filler_expensive M hf.1 ht hfill hv]
    split_ifs <;> omega
  · by_cases hnone : ∀ a ∈ S, ∀ b ∈ S, ¬Bad M f a b
    · exact Or.inl hnone
    · push Not at hnone
      obtain ⟨a, ha, b, hb, hbad⟩ := hnone
      obtain ⟨hunique, he, hl⟩ := one_filler_bad_pair M hf hs ht hfill ha hb hbad
      exact Or.inr ⟨a, b, ha, hb, hunique, he, hl⟩

end ResearchMain.Chores
