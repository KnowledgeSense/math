import MainTheorems.Chores.NonpureExchange

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

def BadSubset (M : TwoCheapModel A E) (S : Finset A) (f g : E → A) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, Bad M f a b → Bad M g a b

private theorem walk_aux (M : TwoCheapModel A E) (S : Finset A) (f₀ : E → A) (q n : ℕ) :
    ∀ f : E → A, nonMixedCount M S f = n → ∀ a b : A,
      EnergyMinimum M S f₀ f →
      (∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) →
      a ∈ S → b ∈ S → ¬Mixed M f a → Bad M f a b → ¬Pure M f a b →
      ∃ g : E → A, EnergyMinimum M S f₀ g ∧ energy M S g = energy M S f ∧
        BadSubset M S g f ∧ ∀ c ∈ S, ¬Bad M g a c := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hn a b hf hs ha hb hm hbad hnp
    obtain ⟨B⟩ := exists_basic_exchange M hf.1.1 hs ha hb hbad
    have hfnew := B.minimum hf hs hbad
    have hsnew := B.balanced hs
    have henergy := B.energy_same (minimum_bad_counts M hf hs ha hb hbad).1
    by_cases hmore : ∃ c ∈ S, Bad M B.allocation b c
    · obtain ⟨c, hc, hbc⟩ := hmore
      have hsmall : nonMixedCount M S B.allocation < n := by
        rw [← hn]
        exact B.nonMixed_decreases hf hs hbad hnp hm
      obtain ⟨g, hg, hge, hsub, hstop⟩ := ih (nonMixedCount M S B.allocation) hsmall
        B.allocation rfl b c hfnew hsnew hb hc (B.target_not_mixed hf hs hbad) hbc
        (B.target_nonpure hf hs hbad hnp hc hbc)
      refine ⟨g, hg, hge.trans henergy, ?_, ?_⟩
      · intro v hv w hw hvw
        have hnew := hsub v hv w hw hvw
        have hvb : v ≠ b := by
          intro heq
          subst v
          exact hstop w hw hvw
        exact B.bad_outside_target hf hs hbad hnp hv hw hvb hnew
      · intro w hw haw
        exact B.no_outgoing_source hf hs hbad hw (hsub a ha w hw haw)
    · refine ⟨B.allocation, hfnew, henergy, ?_, ?_⟩
      · intro v hv w hw hvw
        have hvb : v ≠ b := by
          intro heq
          subst v
          exact hmore ⟨w, hw, hvw⟩
        exact B.bad_outside_target hf hs hbad hnp hv hw hvb hvw
      · intro c hc
        exact B.no_outgoing_source hf hs hbad hc

theorem nonpure_walk (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A} {q : ℕ}
    (hf : EnergyMinimum M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) (hnp : ¬Pure M f a b) :
    ∃ g : E → A, EnergyMinimum M S f₀ g ∧ energy M S g = energy M S f ∧
      BadSubset M S g f ∧ ∀ c ∈ S, ¬Bad M g a c := by
  classical
  obtain ⟨B⟩ := exists_basic_exchange M hf.1.1 hs ha hb hbad
  have hfnew := B.minimum hf hs hbad
  have hsnew := B.balanced hs
  have henergy := B.energy_same (minimum_bad_counts M hf hs ha hb hbad).1
  by_cases hmore : ∃ c ∈ S, Bad M B.allocation b c
  · obtain ⟨c, hc, hbc⟩ := hmore
    obtain ⟨g, hg, hge, hsub, hstop⟩ := walk_aux M S f₀ q
      (nonMixedCount M S B.allocation) B.allocation rfl b c hfnew hsnew hb hc
      (B.target_not_mixed hf hs hbad) hbc (B.target_nonpure hf hs hbad hnp hc hbc)
    refine ⟨g, hg, hge.trans henergy, ?_, ?_⟩
    · intro v hv w hw hvw
      have hnew := hsub v hv w hw hvw
      have hvb : v ≠ b := by
        intro heq
        subst v
        exact hstop w hw hvw
      exact B.bad_outside_target hf hs hbad hnp hv hw hvb hnew
    · intro w hw haw
      exact B.no_outgoing_source hf hs hbad hw (hsub a ha w hw haw)
  · refine ⟨B.allocation, hfnew, henergy, ?_, ?_⟩
    · intro v hv w hw hvw
      have hvb : v ≠ b := by
        intro heq
        subst v
        exact hmore ⟨w, hw, hvw⟩
      exact B.bad_outside_target hf hs hbad hnp hv hw hvb hvw
    · intro c hc
      exact B.no_outgoing_source hf hs hbad hc

omit [DecidableEq E] in
theorem badCount_strict (M : TwoCheapModel A E) {S : Finset A} {f g : E → A}
    (hsub : BadSubset M S g f) {a b : A} (ha : a ∈ S) (hb : b ∈ S)
    (hbad : Bad M f a b) (hstop : ¬Bad M g a b) : badCount M S g < badCount M S f := by
  have hs : ((S ×ˢ S).filter (fun p => Bad M g p.1 p.2)) ⊆
      ((S ×ˢ S).filter (fun p => Bad M f p.1 p.2)) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hm := Finset.mem_product.mp hp'.1
    exact Finset.mem_filter.mpr ⟨hp'.1, hsub p.1 hm.1 p.2 hm.2 hp'.2⟩
  have hneq : ((S ×ˢ S).filter (fun p => Bad M g p.1 p.2)) ≠
      ((S ×ˢ S).filter (fun p => Bad M f p.1 p.2)) := by
    intro heq
    have hm : (a, b) ∈ ((S ×ˢ S).filter (fun p => Bad M f p.1 p.2)) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hbad⟩
    rw [← heq] at hm
    exact hstop (Finset.mem_filter.mp hm).2
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs, hneq⟩)

theorem optimal_bad_source_pure (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A} {q : ℕ}
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) : Pure M f a b := by
  by_contra hnp
  obtain ⟨g, hg, hge, hsub, hstop⟩ := nonpure_walk M (hf.energyMinimum M) hs ha hb hbad hnp
  have hlt := badCount_strict M hsub ha hb hbad (hstop b hb)
  have hle := hf.2.2 g hg.1 hge
  omega

end ResearchMain.Chores
