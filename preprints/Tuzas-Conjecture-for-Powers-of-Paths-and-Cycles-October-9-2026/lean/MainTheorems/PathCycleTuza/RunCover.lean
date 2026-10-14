import MainTheorems.PathCycleTuza.RunEdges

namespace ResearchMain.PathCycleTuza

open Tuza

namespace CircularRuns

variable {n k : ℕ} (D : CircularRuns n k)

theorem skip_budget (p q : D.Position) (y : ℕ)
    (he : y = D.runStart (p.1.val + 2) + q.2.val)
    (hs : y ≤ (D.vertexEquiv p).val + k) :
    D.length p.1 - p.2.val - 1 + q.2.val < k - D.length (D.next p.1) := by
  have h₁ := D.runStart_succ p.1.val
  rw [extendedLength, D.index_lt _ p.1.isLt] at h₁
  change D.runStart (p.1.val + 1) = D.runStart p.1.val + D.length p.1 at h₁
  have h₂ : D.runStart (p.1.val + 2) = D.runStart (p.1.val + 1) + D.length (D.next p.1) := by
    simpa [extendedLength, next, Nat.add_assoc] using D.runStart_succ (p.1.val + 1)
  have hv := D.vertex_val p
  have hp := p.2.isLt
  have hu := D.upper (D.next p.1)
  omega

theorem forwardEdge_mem (p q : D.Position)
    (hxy : (D.vertexEquiv p).val < (D.vertexEquiv q).val)
    (hs : (D.vertexEquiv q).val ≤ (D.vertexEquiv p).val + k)
    (hc : D.color (D.vertexEquiv p) = D.color (D.vertexEquiv q)) :
    s(D.vertexEquiv p, D.vertexEquiv q) ∈ D.edges := by
  rcases D.short_positions p q hxy hs hc with h | h
  · exact D.withinEdge_mem p q (Fin.ext h.symm) (by intro he; have := congrArg Fin.val he; omega)
  · apply D.skippedEdge_mem p q (D.index_pair _ _ (Or.inl h))
    apply D.skip_budget p q (D.vertexEquiv q).val ?_ hs
    rw [D.vertex_val q, h]

theorem wrapEdge_mem (p q : D.Position)
    (hxy : (D.vertexEquiv q).val < (D.vertexEquiv p).val)
    (hs : (D.vertexEquiv q).val + n ≤ (D.vertexEquiv p).val + k)
    (hc : D.color (D.vertexEquiv p) = D.color (D.vertexEquiv q)) :
    s(D.vertexEquiv p, D.vertexEquiv q) ∈ D.edges := by
  have h := D.short_wrap_positions p q hxy hs hc
  apply D.skippedEdge_mem p q (D.index_pair _ _ (Or.inr h))
  apply D.skip_budget p q ((D.vertexEquiv q).val + n) ?_ hs
  rw [D.vertex_val q, ← h, D.runStart_period]
  omega

theorem coloredCover_subset : coloredCover (cyclePower n k) D.color ⊆ D.edges := by
  intro e he
  induction e using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨hadj, hc⟩ := (mem_coloredCover _ _ x y).mp he
    obtain ⟨p, rfl⟩ := D.vertexEquiv.surjective x
    obtain ⟨q, rfl⟩ := D.vertexEquiv.surjective y
    have hne : (D.vertexEquiv p).val ≠ (D.vertexEquiv q).val :=
      fun h => hadj.1 (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · rcases hadj.2 with h | h
      · exact D.forwardEdge_mem p q hxy (by unfold Nat.dist at h; omega) hc
      · have hmem := D.wrapEdge_mem q p hxy (by unfold Nat.dist at h; omega) hc.symm
        rwa [show s(D.vertexEquiv q, D.vertexEquiv p) = s(D.vertexEquiv p, D.vertexEquiv q)
          from Sym2.eq_swap] at hmem
    · rcases hadj.2 with h | h
      · have hmem := D.forwardEdge_mem q p hyx (by unfold Nat.dist at h; omega) hc.symm
        rwa [show s(D.vertexEquiv q, D.vertexEquiv p) = s(D.vertexEquiv p, D.vertexEquiv q)
          from Sym2.eq_swap] at hmem
      · exact D.wrapEdge_mem p q hyx (by unfold Nat.dist at h; omega) hc

theorem cover_bound : coverNumber (cyclePower n k) ≤ ∑ i : Fin D.count, runCost k (D.length i) := by
  let C := D.edges ∩ (cyclePower n k).edgeFinset
  have hC : Cover (cyclePower n k) C := by
    apply (coloredCover_covers (cyclePower n k) D.color).of_subset
    · intro e he
      exact Finset.mem_inter.mpr ⟨D.coloredCover_subset he,
        SimpleGraph.mem_edgeFinset.mpr ((coloredCover_covers _ _).1 e he)⟩
    · intro e he
      exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_inter.mp he).2
  exact (number_le_cover hC).trans ((Finset.card_le_card Finset.inter_subset_left).trans D.edges_card)

end CircularRuns

theorem cycle_run_cover (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 2 ≤ n) :
    coverNumber (cyclePower n k) ≤ k / 2 * n :=
  (canonicalRuns n k hk hn).cover_bound.trans (runCost_sum n k hk hn)

theorem cycle_run_cover_even_odd (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 2 ≤ n)
    (hp : k % 2 = 0) (ho : n % 2 = 1) : coverNumber (cyclePower n k) + k / 2 ≤ k / 2 * n := by
  have hc := (canonicalRuns n k hk hn).cover_bound
  have hs := runCost_sum_even_odd n k hk hn hp ho
  exact (Nat.add_le_add_right hc _).trans hs

end ResearchMain.PathCycleTuza
