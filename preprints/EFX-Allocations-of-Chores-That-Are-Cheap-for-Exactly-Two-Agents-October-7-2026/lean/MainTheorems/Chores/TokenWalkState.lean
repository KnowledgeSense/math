import MainTheorems.Chores.TokenTargets
import MainTheorems.Chores.TokenSeedBounds

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace TokenReady

def walkAgents {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    (P : TokenReady M S f₀ q k) : Finset A := (S.erase P.high).erase P.low

omit [DecidableEq E] in
theorem mem_walkAgents {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    (P : TokenReady M S f₀ q k) {v : A} :
    v ∈ P.walkAgents ↔ v ∈ S ∧ v ≠ P.high ∧ v ≠ P.low := by
  simp only [walkAgents, Finset.mem_erase]
  tauto

end TokenReady

structure TokenWalkState {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {P : TokenReady M S f₀ q k} (B : TokenSeed P) (r : ℝ) where
  allocation : E → A
  passed : Finset A
  current : A
  predecessor : A
  passed_subset : passed ⊆ P.walkAgents
  current_mem : current ∈ P.walkAgents
  current_new : current ∉ passed
  predecessor_mem : predecessor = P.high ∨ predecessor ∈ passed
  predecessor_ne : current ≠ predecessor
  card : ∀ u, (bundle allocation u).card = (bundle P.allocation u).card
  fixed : ∀ u, u ∉ P.walkAgents → bundle allocation u = bundle B.cycle.allocation u
  token_owner : allocation B.cycle.lowChore = current
  uniform : ∀ t ∈ P.walkAgents, ∀ u ∈ P.walkAgents,
    ∀ e ∈ bundle allocation t, ¬M.Cheap t e → ¬M.Cheap u e
  current_count : expensiveCount M allocation current current =
    expensiveCount M P.allocation current current + 1
  current_bound : expensiveCount M P.allocation current current ≤
    expensiveCount M P.allocation P.low P.low + 1
  current_cheap : OwnCheap M allocation current
  current_anchor : Mixed M allocation current ∨ Pure M allocation current predecessor
  passed_count : ∀ u ∈ passed, expensiveCount M allocation u u = expensiveCount M P.allocation u u
  passed_mixed : ∀ u ∈ passed, Mixed M allocation u
  passed_level : ∀ u ∈ passed,
    expensiveCount M P.allocation current current ≤ expensiveCount M P.allocation u u
  passed_bound : ∀ u ∈ passed, expensiveCount M P.allocation u u ≤
    expensiveCount M P.allocation P.low P.low + 1
  untouched : ∀ u ∈ P.walkAgents, u ∉ passed → u ≠ current →
    bundle allocation u = bundle P.allocation u
  donor_visited : k ∈ passed ∨ k = current
  internal : ∀ u ∈ P.walkAgents, u ≠ current → ∀ w ∈ P.walkAgents, u ≠ w →
    threshold M r allocation u ≤ bundleCost M r u (bundle allocation w)
  pair_margin : ∀ p, p = P.high ∨ p = P.low → ∀ u ∈ P.walkAgents,
    expensiveCount M P.allocation P.low P.low + 1 ≤ expensiveCount M allocation p u

namespace TokenWalkState

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {P : TokenReady M S f₀ q k} {B : TokenSeed P} {r : ℝ}

theorem balanced (W : TokenWalkState B r) (u : A) :
    q ≤ (bundle W.allocation u).card ∧ (bundle W.allocation u).card ≤ q + 1 := by
  rw [W.card]
  exact P.size u

theorem original_current_cheap (W : TokenWalkState B r) : OwnCheap M P.allocation W.current := by
  rw [ownCheap_iff_count]
  have ht := cheap_add_expensive M P.allocation W.current W.current
  have hq := (P.size W.current).1
  have hd := W.current_bound
  have hL := P.low_bound
  omega

theorem original_no_bad (W : TokenWalkState B r) {w : A} (hw : w ∈ P.walkAgents) :
    ¬Bad M P.allocation W.current w := by
  have hv := P.mem_walkAgents.mp W.current_mem
  have hwS := (P.mem_walkAgents.mp hw).1
  intro hb
  exact hv.2.1 (P.unique_bad.2 W.current hv.1 w hwS hb).1

theorem failing_target_new (W : TokenWalkState B r) {w : A}
    (hw : w ∈ P.walkAgents) (hvw : W.current ≠ w)
    (hfail : expensiveCount M W.allocation W.current w <
      expensiveCount M P.allocation W.current W.current + 1) : w ∉ W.passed := by
  intro hp
  have ht := passed_vertex_margin M hvw.symm (W.passed_mixed w hp) (W.passed_count w hp)
    (W.passed_level w hp) (W.uniform w hw W.current W.current_mem)
  omega

theorem failing_target_count (W : TokenWalkState B r) {w : A}
    (hw : w ∈ P.walkAgents) (hvw : W.current ≠ w)
    (hfail : expensiveCount M W.allocation W.current w <
      expensiveCount M P.allocation W.current W.current + 1) :
    expensiveCount M P.allocation W.current w = expensiveCount M P.allocation W.current W.current := by
  have hb := W.untouched w hw (W.failing_target_new hw hvw hfail) hvw.symm
  have heq : expensiveCount M W.allocation W.current w = expensiveCount M P.allocation W.current w := by
    rw [expensiveCount, hb]
    rfl
  have hge : expensiveCount M P.allocation W.current W.current ≤
      expensiveCount M P.allocation W.current w := by
    by_contra hn
    apply W.original_no_bad hw
    exact ⟨hvw, W.original_current_cheap, by omega⟩
  omega

theorem failing_target_chore (W : TokenWalkState B r) {w : A}
    (hw : w ∈ P.walkAgents) (hvw : W.current ≠ w)
    (hfail : expensiveCount M W.allocation W.current w <
      expensiveCount M P.allocation W.current W.current + 1) :
    ∃ e ∈ bundle W.allocation w, M.Cheap W.current e ∧ M.Cheap w e := by
  have hb := W.untouched w hw (W.failing_target_new hw hvw hfail) hvw.symm
  have ht := W.failing_target_count hw hvw hfail
  have hsum := cheap_add_expensive M P.allocation W.current w
  have hq := (P.size w).1
  have hd := W.current_bound
  have hL := P.low_bound
  have hpos : 0 < cheapCount M P.allocation W.current w := by omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  obtain ⟨he, hc⟩ := Finset.mem_filter.mp he
  have ho := separated_owner_cheap M P.optimal.1.1
    (P.mem_walkAgents.mp W.current_mem).1 hc
  rw [(mem_bundle P.allocation w e).mp he] at ho
  exact ⟨e, hb.symm ▸ he, hc, ho⟩

theorem failing_target_level (W : TokenWalkState B r) {w : A}
    (hw : w ∈ P.walkAgents) (hvw : W.current ≠ w)
    (hfail : expensiveCount M W.allocation W.current w <
      expensiveCount M P.allocation W.current W.current + 1) :
    expensiveCount M P.allocation w w ≤ expensiveCount M P.allocation W.current W.current ∧
      expensiveCount M P.allocation W.current W.current ≤ expensiveCount M P.allocation w w + 1 := by
  obtain ⟨e, he, hc, _⟩ := W.failing_target_chore hw hvw hfail
  have hb := W.untouched w hw (W.failing_target_new hw hvw hfail) hvw.symm
  rw [hb] at he
  have hmin := minimum_exchange_bound M (P.optimal.energyMinimum M)
    (P.mem_walkAgents.mp W.current_mem).1 (P.mem_walkAgents.mp hw).1 hvw he hc
  have hge := separated_observer_expensive_ge M P.optimal.1.1
    (P.mem_walkAgents.mp W.current_mem).1 (b := w)
  rw [W.failing_target_count hw hvw hfail] at hge
  exact ⟨hge, hmin⟩

end TokenWalkState

end ResearchMain.Chores
