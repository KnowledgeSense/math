import MainTheorems.Chores.TokenWalkStep

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace TokenWalkStep

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ : E → A} {q : ℕ} {k : A}
    {P : TokenReady M S f₀ q k} {B : TokenSeed P} {r : ℝ} {W : TokenWalkState B r}

theorem source_comparison (D : TokenWalkStep W) (hr : 2 < r) {c : A}
    (hc : c ∈ P.walkAgents) (hvc : W.current ≠ c) :
    threshold M r D.swap.allocation W.current ≤ bundleCost M r W.current (bundle D.swap.allocation c) := by
  have hown : OwnCheap M D.swap.allocation W.current := by
    obtain ⟨e, he, _, _, hc, _, _⟩ := D.source_mixed
    exact ⟨e, he, hc⟩
  have hsize : (bundle D.swap.allocation W.current).card ≤ (bundle D.swap.allocation c).card + 1 := by
    rw [D.swap.card, D.swap.card]
    have h₁ := (W.balanced W.current).2
    have h₂ := (W.balanced c).1
    omega
  by_cases hcw : c = D.target
  · subst c
    apply positive_comparison M (by linarith : 1 ≤ r) hown hsize
    rw [D.source_count, D.swap.source_to_target]
    have heq : expensiveCount M W.allocation W.current D.target =
        expensiveCount M P.allocation W.current D.target := by
      rw [expensiveCount, D.target_original]
      rfl
    rw [heq, W.failing_target_count D.target_mem D.distinct D.failing]
    omega
  · by_cases hcp : c ∈ W.passed
    · apply positive_comparison M (by linarith : 1 ≤ r) hown hsize
      rw [D.source_count]
      have hcnt : expensiveCount M D.swap.allocation c c = expensiveCount M P.allocation c c := by
        rw [expensiveCount, D.swap.other_bundle hvc.symm hcw]
        exact W.passed_count c hcp
      have hm : Mixed M D.swap.allocation c := by
        unfold Mixed
        rw [D.swap.other_bundle hvc.symm hcw]
        exact W.passed_mixed c hcp
      have ht := passed_vertex_margin M hvc.symm hm hcnt (W.passed_level c hcp)
        (D.uniform c hc W.current W.current_mem)
      omega
    · have hθ : threshold M r D.swap.allocation W.current = threshold M r P.allocation W.current :=
        threshold_eq_of_counts M r ((D.swap.card W.current).trans (W.card W.current)) D.source_count
      have hbundle : bundle D.swap.allocation c = bundle P.allocation c := by
        rw [D.swap.other_bundle hvc.symm hcw, W.untouched c hc hcp hvc.symm]
      rw [hθ, hbundle]
      exact separated_comparison M hr (P.optimal.energyMinimum M) P.size hvc
        (fun _ _ => W.original_no_bad hc)

theorem internal (D : TokenWalkStep W) (hr : 2 < r) :
    ∀ u ∈ P.walkAgents, u ≠ D.target → ∀ c ∈ P.walkAgents, u ≠ c →
      threshold M r D.swap.allocation u ≤ bundleCost M r u (bundle D.swap.allocation c) := by
  intro u hu huw c hc huc
  by_cases huv : u = W.current
  · subst u
    exact D.source_comparison hr hc huc
  · have heq (t : A) := D.swap.outsider_expensive hu huv huw t
    rw [threshold_eq_of_counts M r (D.swap.card u) (heq u),
      cost_eq_of_counts M r (D.swap.card c) (heq c)]
    exact W.internal u hu huv c hc huc

def advance (D : TokenWalkStep W) (hr : 2 < r) : TokenWalkState B r where
  allocation := D.swap.allocation
  passed := insert W.current W.passed
  current := D.target
  predecessor := W.current
  passed_subset := by
    intro u hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · exact hu ▸ W.current_mem
    · exact W.passed_subset hu
  current_mem := D.target_mem
  current_new := by
    intro ht
    rcases Finset.mem_insert.mp ht with ht | ht
    · exact D.distinct ht.symm
    · exact D.target_new ht
  predecessor_mem := Or.inr (Finset.mem_insert_self _ _)
  predecessor_ne := D.distinct.symm
  card := fun u => (D.swap.card u).trans (W.card u)
  fixed := by
    intro u hu
    have huv : u ≠ W.current := fun ht => hu (ht ▸ W.current_mem)
    have huw : u ≠ D.target := fun ht => hu (ht ▸ D.target_mem)
    rw [D.swap.other_bundle huv huw]
    exact W.fixed u hu
  token_owner := by
    rw [← D.token_eq]
    exact D.swap.token_owner
  uniform := D.uniform
  current_count := D.target_count
  current_bound := D.level.1.trans W.current_bound
  current_cheap := D.target_cheap
  current_anchor := D.target_anchor
  passed_count := by
    intro u hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · subst u
      exact D.source_count
    · have huv : u ≠ W.current := fun ht => W.current_new (ht ▸ hu)
      have huw : u ≠ D.target := fun ht => D.target_new (ht ▸ hu)
      rw [expensiveCount, D.swap.other_bundle huv huw]
      exact W.passed_count u hu
  passed_mixed := by
    intro u hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · subst u
      exact D.source_mixed
    · have huv : u ≠ W.current := fun ht => W.current_new (ht ▸ hu)
      have huw : u ≠ D.target := fun ht => D.target_new (ht ▸ hu)
      unfold Mixed
      rw [D.swap.other_bundle huv huw]
      exact W.passed_mixed u hu
  passed_level := by
    intro u hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · subst u
      exact D.level.1
    · exact D.level.1.trans (W.passed_level u hu)
  passed_bound := by
    intro u hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · subst u
      exact W.current_bound
    · exact W.passed_bound u hu
  untouched := by
    intro u hu hup huw
    have huv : u ≠ W.current := fun ht => hup (Finset.mem_insert.mpr (Or.inl ht))
    have hup₀ : u ∉ W.passed := fun ht => hup (Finset.mem_insert_of_mem ht)
    rw [D.swap.other_bundle huv huw]
    exact W.untouched u hu hup₀ huv
  donor_visited := by
    rcases W.donor_visited with hk | hk
    · exact Or.inl (Finset.mem_insert_of_mem hk)
    · exact Or.inl (Finset.mem_insert.mpr (Or.inl hk))
  internal := D.internal hr
  pair_margin := by
    intro p hp u hu
    by_cases huv : u = W.current
    · subst u
      exact (W.pair_margin p hp W.current W.current_mem).trans (D.pair_source_margin hp)
    · by_cases huw : u = D.target
      · subst u
        exact D.pair_target_margin hp
      · have heq : expensiveCount M D.swap.allocation p u = expensiveCount M W.allocation p u := by
          rw [expensiveCount, D.swap.other_bundle huv huw]
          rfl
        rw [heq]
        exact W.pair_margin p hp u hu

theorem advance_passed_card (D : TokenWalkStep W) (hr : 2 < r) :
    (D.advance hr).passed.card = W.passed.card + 1 :=
  Finset.card_insert_of_notMem W.current_new

end TokenWalkStep

end ResearchMain.Chores
