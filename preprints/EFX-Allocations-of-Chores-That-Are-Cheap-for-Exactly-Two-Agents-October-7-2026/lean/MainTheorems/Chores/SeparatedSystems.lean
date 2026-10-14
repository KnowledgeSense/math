import MainTheorems.Chores.Exchange

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

def Separated (M : TwoCheapModel A E) (S : Finset A) (f : E → A) : Prop :=
  ∀ e, f e ∈ separatedAllowed M S e

def Filler (M : TwoCheapModel A E) (S : Finset A) (e : E) : Prop :=
  M.first e ∉ S ∧ M.second e ∉ S

def otherEndpoint (M : TwoCheapModel A E) (a : A) (e : E) : A :=
  if a = M.first e then M.second e else M.first e

def Pure (M : TwoCheapModel A E) (f : E → A) (a b : A) : Prop :=
  ∀ e ∈ bundle f a, M.Cheap a e → M.Cheap b e

def Mixed (M : TwoCheapModel A E) (f : E → A) (a : A) : Prop :=
  ∃ e ∈ bundle f a, ∃ d ∈ bundle f a,
    M.Cheap a e ∧ M.Cheap a d ∧ otherEndpoint M a e ≠ otherEndpoint M a d

instance (M : TwoCheapModel A E) (f : E → A) (a : A) : Decidable (Mixed M f a) :=
  inferInstanceAs (Decidable (∃ e ∈ bundle f a, ∃ d ∈ bundle f a,
    M.Cheap a e ∧ M.Cheap a d ∧ otherEndpoint M a e ≠ otherEndpoint M a d))

omit [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem two_cheap_third (M : TwoCheapModel A E) {a b c : A} {e : E} (hab : a ≠ b)
    (ha : M.Cheap a e) (hb : M.Cheap b e) (hca : c ≠ a) (hcb : c ≠ b) : ¬M.Cheap c e := by
  unfold TwoCheapModel.Cheap at *
  aesop

omit [Fintype A] [Fintype E] [DecidableEq E] in
theorem otherEndpoint_eq (M : TwoCheapModel A E) {a b : A} {e : E} (hab : a ≠ b)
    (ha : M.Cheap a e) (hb : M.Cheap b e) : otherEndpoint M a e = b := by
  unfold otherEndpoint TwoCheapModel.Cheap at *
  split_ifs <;> aesop

omit [Fintype A] [Fintype E] [DecidableEq E] in
theorem cheap_otherEndpoint (M : TwoCheapModel A E) {a : A} {e : E} (ha : M.Cheap a e) :
    M.Cheap (otherEndpoint M a e) e ∧ otherEndpoint M a e ≠ a := by
  unfold otherEndpoint
  split_ifs with h
  · subst a
    exact ⟨Or.inr rfl, (M.distinct e).symm⟩
  · have hs : a = M.second e := ha.resolve_left h
    exact ⟨Or.inl rfl, (M.distinct e).trans_eq hs.symm⟩

omit [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E] in
theorem filler_not_cheap (M : TwoCheapModel A E) {S : Finset A} {a : A} {e : E}
    (ha : a ∈ S) (he : Filler M S e) : ¬M.Cheap a e := by
  intro hc
  rcases hc with h | h
  · exact he.1 (h ▸ ha)
  · exact he.2 (h ▸ ha)

omit [Fintype A] [Fintype E] [DecidableEq E] in
theorem separated_owner_cheap (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {a : A} {e : E} (ha : a ∈ S) (hc : M.Cheap a e) :
    M.Cheap (f e) e := by
  have ht : M.first e ∈ S ∨ M.second e ∈ S := by
    rcases hc with h | h
    · exact Or.inl (h ▸ ha)
    · exact Or.inr (h ▸ ha)
  have h := hf e
  rw [separatedAllowed, ite_eq_left ht, Finset.mem_inter] at h
  exact (mem_endpointAllowed M _ e).mp h.1

omit [Fintype A] [Fintype E] [DecidableEq E] in
theorem separated_expensive_filler (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {e : E} (hc : ¬M.Cheap (f e) e) : Filler M S e := by
  by_contra hn
  have ht : M.first e ∈ S ∨ M.second e ∈ S := by
    unfold Filler at hn
    tauto
  have h := hf e
  rw [separatedAllowed, ite_eq_left ht, Finset.mem_inter] at h
  exact hc ((mem_endpointAllowed M _ e).mp h.1)

omit [Fintype A] [DecidableEq E] in
theorem pure_not_mixed (M : TwoCheapModel A E) {f : E → A} {a b : A} (hab : a ≠ b)
    (hp : Pure M f a b) : ¬Mixed M f a := by
  rintro ⟨e, he, d, hd, hae, had, hne⟩
  exact hne ((otherEndpoint_eq M hab hae (hp e he hae)).trans
    (otherEndpoint_eq M hab had (hp d hd had)).symm)

omit [Fintype A] [DecidableEq E] in
theorem separated_observer_expensive_ge (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {a b : A} (ha : a ∈ S) :
    expensiveCount M f b b ≤ expensiveCount M f a b := by
  apply Finset.card_le_card
  intro e he
  have he' := Finset.mem_filter.mp he
  refine Finset.mem_filter.mpr ⟨he'.1, ?_⟩
  intro hc
  have hown := separated_owner_cheap M hf ha hc
  rw [(mem_bundle f b e).mp he'.1] at hown
  exact he'.2 hown

omit [Fintype A] [DecidableEq E] in
theorem pure_unique (M : TwoCheapModel A E) {f : E → A} {a b c : A}
    (hc : OwnCheap M f a) (hab : a ≠ b) (hac : a ≠ c)
    (hp : Pure M f a b) (hq : Pure M f a c) : b = c := by
  obtain ⟨e, he, hae⟩ := hc
  exact (otherEndpoint_eq M hab hae (hp e he hae)).symm.trans
    (otherEndpoint_eq M hac hae (hq e he hae))

omit [Fintype A] [DecidableEq E] in
theorem pure_observer_expensive (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) {a b : A} (ha : a ∈ S) (hp : Pure M f b a) :
    expensiveCount M f a b = expensiveCount M f b b := by
  unfold expensiveCount
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · intro h
    refine ⟨h.1, fun hc => h.2 (hp e h.1 hc)⟩
  · intro h
    refine ⟨h.1, ?_⟩
    intro hc
    have ho := separated_owner_cheap M hf ha hc
    rw [(mem_bundle f b e).mp h.1] at ho
    exact h.2 ho

def Feasible (M : TwoCheapModel A E) (S : Finset A) (f₀ f : E → A) : Prop :=
  Separated M S f ∧ (∀ a, (bundle f a).card = (bundle f₀ a).card) ∧
    ∀ e, f₀ e ∉ S → f e = f₀ e

omit [Fintype A] [DecidableEq E] in
theorem feasible_self (M : TwoCheapModel A E) (S : Finset A) (f : E → A)
    (hf : Separated M S f) : Feasible M S f f := ⟨hf, fun _ => rfl, fun _ _ => rfl⟩

omit [Fintype A] in
theorem feasible_exchange (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    (hf : Feasible M S f₀ f) {e d : E} (heS : f e ∈ S) (hdS : f d ∈ S)
    (he : Filler M S e) (hd : M.Cheap (f e) d) : Feasible M S f₀ (exchange f e d) := by
  refine ⟨?_, fun a => (exchange_bundle_card f e d a).trans (hf.2.1 a), ?_⟩
  · intro c
    by_cases hc : c = e
    · subst c
      rw [exchange_left, separatedAllowed, ite_eq_right (by simpa [Filler] using he)]
      exact Finset.mem_union_right _ hdS
    · by_cases hc' : c = d
      · subst c
        rw [exchange_right]
        by_cases ht : M.first d ∈ S ∨ M.second d ∈ S
        · rw [separatedAllowed, ite_eq_left ht]
          exact Finset.mem_inter.mpr ⟨(mem_endpointAllowed M _ d).mpr hd, heS⟩
        · rw [separatedAllowed, ite_eq_right ht]
          exact Finset.mem_union_right _ heS
      · rw [exchange_other f hc hc']
        exact hf.1 c
  · intro c hc
    have hce : c ≠ e := by
      intro h
      subst c
      rw [hf.2.2 e hc] at heS
      exact hc heS
    have hcd : c ≠ d := by
      intro h
      subst c
      rw [hf.2.2 d hc] at hdS
      exact hc hdS
    rw [exchange_other f hce hcd]
    exact hf.2.2 c hc

end ResearchMain.Chores
