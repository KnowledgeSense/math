import MainTheorems.Chores.TokenSwap
import MainTheorems.Chores.EqualCounts

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

omit [DecidableEq E] in
theorem nonshared_cheap_count (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {v w : A} (hv : v ∈ S) :
    ((bundle f w).filter (fun e => M.Cheap w e ∧ ¬M.Cheap v e)).card +
      expensiveCount M f w w = expensiveCount M f v w := by
  let X := (bundle f w).filter (fun e => ¬M.Cheap v e)
  have h₁ : X.filter (M.Cheap w) =
      (bundle f w).filter (fun e => M.Cheap w e ∧ ¬M.Cheap v e) := by
    ext e
    simp only [X, Finset.mem_filter]
    tauto
  have h₂ : X.filter (fun e => ¬M.Cheap w e) =
      (bundle f w).filter (fun e => ¬M.Cheap w e) := by
    ext e
    simp only [X, Finset.mem_filter]
    constructor
    · tauto
    · rintro ⟨he, hn⟩
      refine ⟨⟨he, ?_⟩, hn⟩
      intro hc
      have ho := separated_owner_cheap M hf hv hc
      rw [(mem_bundle f w e).mp he] at ho
      exact hn ho
  have ht := Finset.card_filter_add_card_filter_not (s := X) (M.Cheap w)
  rw [h₁, h₂] at ht
  exact ht

omit [DecidableEq E] in
theorem third_cheap_count_le (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {v w p : A} (hv : v ∈ S) (hpS : p ∈ S)
    (hvw : v ≠ w) (hpv : p ≠ v) (hpw : p ≠ w)
    (hcount : expensiveCount M f v w ≤ expensiveCount M f w w + 1) :
    cheapCount M f p w ≤ 1 := by
  have hs : (bundle f w).filter (M.Cheap p) ⊆
      (bundle f w).filter (fun e => M.Cheap w e ∧ ¬M.Cheap v e) := by
    intro e he
    obtain ⟨he, hp⟩ := Finset.mem_filter.mp he
    have hw : M.Cheap w e := by
      have ho := separated_owner_cheap M hf hpS hp
      rwa [(mem_bundle f w e).mp he] at ho
    refine Finset.mem_filter.mpr ⟨he, hw, ?_⟩
    exact two_cheap_third M hpw hp hw hpv.symm hvw
  have hc := Finset.card_le_card hs
  have ht := nonshared_cheap_count M hf (w := w) hv
  change cheapCount M f p w ≤ _ at hc
  omega

namespace TokenSwap

variable {M : TwoCheapModel A E} {T : Finset A} {f : E → A} {v w : A}

theorem target_pure (B : TokenSwap M T f v w) (hp : Pure M f w v) :
    Pure M B.allocation w v := by
  intro e he hc
  rw [B.target_bundle] at he
  rcases Finset.mem_insert.mp he with he | he
  · subst e
    exact False.elim (filler_not_cheap M B.target_mem B.token_uniform hc)
  · exact hp e (Finset.mem_of_mem_erase he) hc

theorem target_own_cheap (B : TokenSwap M T f v w) (hc : 2 ≤ cheapCount M f w w) :
    OwnCheap M B.allocation w := by
  rw [ownCheap_iff_count]
  have h₁ := cheap_add_expensive M f w w
  have h₂ := cheap_add_expensive M B.allocation w w
  rw [B.card, B.target_count] at h₂
  omega

theorem target_mixed (B : TokenSwap M T f v w)
    (hshared : 2 ≤ cheapCount M f v w)
    (howner : ∀ e ∈ bundle f w, M.Cheap v e → M.Cheap w e)
    (hnp : ¬Pure M f w v) : Mixed M B.allocation w := by
  have hex : ∃ e ∈ bundle f w, M.Cheap w e ∧ ¬M.Cheap v e := by
    by_contra hn
    apply hnp
    intro e he hc
    by_contra hv
    exact hn ⟨e, he, hc, hv⟩
  obtain ⟨e, he, hew, hev⟩ := hex
  have hec : e ≠ B.chore := by
    intro ht
    subst e
    exact hev B.sourceCheap
  have hdmem : B.chore ∈ (bundle f w).filter (M.Cheap v) :=
    Finset.mem_filter.mpr ⟨(mem_bundle f w B.chore).mpr B.choreOwner, B.sourceCheap⟩
  have hcard := Finset.card_erase_add_one hdmem
  have hpos : 0 < (((bundle f w).filter (M.Cheap v)).erase B.chore).card := by
    change 2 ≤ ((bundle f w).filter (M.Cheap v)).card at hshared
    omega
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hpos
  obtain ⟨hdc, hd⟩ := Finset.mem_erase.mp hd
  obtain ⟨hd, hdv⟩ := Finset.mem_filter.mp hd
  have hdw := howner d hd hdv
  have heNew : e ∈ bundle B.allocation w := by
    rw [B.target_bundle]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hec, he⟩)
  have hdNew : d ∈ bundle B.allocation w := by
    rw [B.target_bundle]
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hdc, hd⟩)
  refine ⟨e, heNew, d, hdNew, hew, hdw, ?_⟩
  rw [otherEndpoint_eq M B.distinct.symm hdw hdv]
  intro ht
  have hc := (cheap_otherEndpoint M hew).1
  rw [ht] at hc
  exact hev hc

end TokenSwap

end ResearchMain.Chores
