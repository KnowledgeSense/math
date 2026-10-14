import MainTheorems.Chores.TokenWalkEFX

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

structure TokenWalkStep {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {P : TokenReady M S f₀ q k} {B : TokenSeed P} {r : ℝ} (W : TokenWalkState B r) where
  target : A
  target_mem : target ∈ P.walkAgents
  distinct : W.current ≠ target
  failing : expensiveCount M W.allocation W.current target <
    expensiveCount M P.allocation W.current W.current + 1
  swap : TokenSwap M P.walkAgents W.allocation W.current target
  token_eq : swap.token = B.cycle.lowChore

namespace TokenWalkState

theorem exists_step {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {P : TokenReady M S f₀ q k} {B : TokenSeed P} {r : ℝ} (W : TokenWalkState B r) {w : A}
    (hw : w ∈ P.walkAgents) (hvw : W.current ≠ w)
    (hfail : expensiveCount M W.allocation W.current w <
      expensiveCount M P.allocation W.current W.current + 1) : Nonempty (TokenWalkStep W) := by
  obtain ⟨e, he, hc, ho⟩ := W.failing_target_chore hw hvw hfail
  have hf : Filler M P.walkAgents B.cycle.lowChore := by
    constructor <;> intro hm
    · have hv := P.mem_walkAgents.mp hm
      exact two_cheap_third M P.unique_bad.1.1 B.low_highCheap B.low_ownCheap
        hv.2.1 hv.2.2 (Or.inl rfl)
    · have hv := P.mem_walkAgents.mp hm
      exact two_cheap_third M P.unique_bad.1.1 B.low_highCheap B.low_ownCheap
        hv.2.1 hv.2.2 (Or.inr rfl)
  exact ⟨⟨w, hw, hvw, hfail,
    ⟨B.cycle.lowChore, e, W.token_owner, (mem_bundle W.allocation w e).mp he,
      W.current_mem, hw, hvw, hf, hc, ho⟩, rfl⟩⟩

end TokenWalkState

namespace TokenWalkStep

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {P : TokenReady M S f₀ q k} {B : TokenSeed P} {r : ℝ} {W : TokenWalkState B r}

theorem target_new (D : TokenWalkStep W) : D.target ∉ W.passed :=
  W.failing_target_new D.target_mem D.distinct D.failing

theorem target_original (D : TokenWalkStep W) :
    bundle W.allocation D.target = bundle P.allocation D.target :=
  W.untouched D.target D.target_mem D.target_new D.distinct.symm

theorem level (D : TokenWalkStep W) :
    expensiveCount M P.allocation D.target D.target ≤ expensiveCount M P.allocation W.current W.current ∧
      expensiveCount M P.allocation W.current W.current ≤ expensiveCount M P.allocation D.target D.target + 1 :=
  W.failing_target_level D.target_mem D.distinct D.failing

theorem source_count (D : TokenWalkStep W) :
    expensiveCount M D.swap.allocation W.current W.current =
      expensiveCount M P.allocation W.current W.current := by
  have ht := D.swap.source_count
  rw [W.current_count] at ht
  omega

theorem target_count (D : TokenWalkStep W) :
    expensiveCount M D.swap.allocation D.target D.target =
      expensiveCount M P.allocation D.target D.target + 1 := by
  rw [D.swap.target_count, expensiveCount, D.target_original]
  rfl

theorem target_shared (D : TokenWalkStep W) : 2 ≤ cheapCount M W.allocation W.current D.target := by
  have ht := cheap_add_expensive M P.allocation W.current D.target
  have he := W.failing_target_count D.target_mem D.distinct D.failing
  have hq := (P.size D.target).1
  have hd := W.current_bound
  have hL := P.low_bound
  rw [cheapCount, D.target_original]
  change 2 ≤ cheapCount M P.allocation W.current D.target
  omega

theorem target_cheap (D : TokenWalkStep W) : OwnCheap M D.swap.allocation D.target := by
  apply D.swap.target_own_cheap
  have ht := cheap_add_expensive M P.allocation D.target D.target
  have hq := (P.size D.target).1
  have hd := D.level.1
  have hc := W.current_bound
  have hL := P.low_bound
  rw [cheapCount, D.target_original]
  change 2 ≤ cheapCount M P.allocation D.target D.target
  omega

theorem target_anchor (D : TokenWalkStep W) :
    Mixed M D.swap.allocation D.target ∨ Pure M D.swap.allocation D.target W.current := by
  have hvS := (P.mem_walkAgents.mp W.current_mem).1
  have he := W.failing_target_count D.target_mem D.distinct D.failing
  by_cases heq : expensiveCount M P.allocation D.target D.target =
      expensiveCount M P.allocation W.current W.current
  · right
    apply D.swap.target_pure
    have hp := pure_of_equal_expensive M P.optimal.1.1 hvS (he.trans heq.symm)
    intro e hem hc
    rw [D.target_original] at hem
    exact hp e hem hc
  · left
    apply D.swap.target_mixed D.target_shared
    · intro e hem hc
      rw [D.target_original] at hem
      have ho := separated_owner_cheap M P.optimal.1.1 hvS hc
      rwa [(mem_bundle P.allocation D.target e).mp hem] at ho
    · intro hp
      have hp₀ : Pure M P.allocation D.target W.current := by
        intro e hem hc
        exact hp e (D.target_original.symm ▸ hem) hc
      have ht := pure_observer_expensive M P.optimal.1.1 hvS hp₀
      exact heq (ht.symm.trans he)

theorem source_mixed (D : TokenWalkStep W) : Mixed M D.swap.allocation W.current := by
  rcases W.current_anchor with hm | hp
  · exact D.swap.source_mixed_preserved hm
  · apply D.swap.source_mixed_of_pure W.predecessor_ne _ hp W.current_cheap
    intro ht
    rcases W.predecessor_mem with ha | hv
    · have hh := (P.mem_walkAgents.mp D.target_mem).2.1
      exact hh (ht.symm.trans ha)
    · exact D.target_new (ht ▸ hv)

theorem uniform (D : TokenWalkStep W) : ∀ t ∈ P.walkAgents, ∀ u ∈ P.walkAgents,
    ∀ e ∈ bundle D.swap.allocation t, ¬M.Cheap t e → ¬M.Cheap u e := by
  intro t ht u hu e he hn
  by_cases htv : t = W.current
  · subst t
    rw [D.swap.source_bundle] at he
    rcases Finset.mem_insert.mp he with he | he
    · subst e
      exact False.elim (hn D.swap.sourceCheap)
    · exact W.uniform W.current W.current_mem u hu e (Finset.mem_of_mem_erase he) hn
  · by_cases htw : t = D.target
    · subst t
      rw [D.swap.target_bundle] at he
      rcases Finset.mem_insert.mp he with he | he
      · subst e
        exact filler_not_cheap M hu D.swap.token_uniform
      · exact W.uniform D.target D.target_mem u hu e (Finset.mem_of_mem_erase he) hn
    · rw [D.swap.other_bundle htv htw] at he
      exact W.uniform t ht u hu e he hn

theorem pair_source_margin (D : TokenWalkStep W) {p : A} (hp : p = P.high ∨ p = P.low) :
    expensiveCount M W.allocation p W.current ≤ expensiveCount M D.swap.allocation p W.current := by
  have hpc : M.Cheap p D.swap.token := by
    rw [D.token_eq]
    exact hp.elim (fun ht => ht ▸ B.low_highCheap) (fun ht => ht ▸ B.low_ownCheap)
  have hpn : ¬M.Cheap p D.swap.chore := by
    have hpv : p ≠ W.current := hp.elim
      (fun ht => ht ▸ (P.mem_walkAgents.mp W.current_mem).2.1.symm)
      (fun ht => ht ▸ (P.mem_walkAgents.mp W.current_mem).2.2.symm)
    have hpw : p ≠ D.target := hp.elim
      (fun ht => ht ▸ (P.mem_walkAgents.mp D.target_mem).2.1.symm)
      (fun ht => ht ▸ (P.mem_walkAgents.mp D.target_mem).2.2.symm)
    exact two_cheap_third M D.distinct D.swap.sourceCheap D.swap.targetCheap hpv hpw
  have ht := exchange_expensive_left M W.allocation D.swap.chore_distinct D.swap.owner_distinct p
  rw [D.swap.tokenOwner, ite_eq_left hpc, ite_eq_right hpn] at ht
  change (expensiveCount M D.swap.allocation p W.current : ℤ) =
    expensiveCount M W.allocation p W.current - 0 + 1 at ht
  omega

theorem pair_target_margin (D : TokenWalkStep W) {p : A} (hp : p = P.high ∨ p = P.low) :
    expensiveCount M P.allocation P.low P.low + 1 ≤ expensiveCount M D.swap.allocation p D.target := by
  have hpS : p ∈ S := hp.elim (fun ht => ht ▸ P.high_mem) (fun ht => ht ▸ P.low_mem)
  have hpv : p ≠ W.current := hp.elim
    (fun ht => ht ▸ (P.mem_walkAgents.mp W.current_mem).2.1.symm)
    (fun ht => ht ▸ (P.mem_walkAgents.mp W.current_mem).2.2.symm)
  have hpw : p ≠ D.target := hp.elim
    (fun ht => ht ▸ (P.mem_walkAgents.mp D.target_mem).2.1.symm)
    (fun ht => ht ▸ (P.mem_walkAgents.mp D.target_mem).2.2.symm)
  have hsmall := third_cheap_count_le M P.optimal.1.1
    (P.mem_walkAgents.mp W.current_mem).1 hpS D.distinct hpv hpw
    (by rw [W.failing_target_count D.target_mem D.distinct D.failing]; exact D.level.2)
  have hsum := cheap_add_expensive M P.allocation p D.target
  have hpc : M.Cheap p D.swap.token := by
    rw [D.token_eq]
    exact hp.elim (fun ht => ht ▸ B.low_highCheap) (fun ht => ht ▸ B.low_ownCheap)
  have hpn := two_cheap_third M D.distinct D.swap.sourceCheap D.swap.targetCheap hpv hpw
  have ht := exchange_expensive_right M W.allocation D.swap.chore_distinct D.swap.owner_distinct p
  rw [D.swap.choreOwner, ite_eq_right hpn, ite_eq_left hpc] at ht
  have heq : expensiveCount M W.allocation p D.target = expensiveCount M P.allocation p D.target := by
    rw [expensiveCount, D.target_original]
    rfl
  change (expensiveCount M D.swap.allocation p D.target : ℤ) =
    expensiveCount M W.allocation p D.target - 1 + 0 at ht
  have hq := (P.size D.target).1
  have hL := P.low_bound
  omega

end TokenWalkStep

end ResearchMain.Chores
