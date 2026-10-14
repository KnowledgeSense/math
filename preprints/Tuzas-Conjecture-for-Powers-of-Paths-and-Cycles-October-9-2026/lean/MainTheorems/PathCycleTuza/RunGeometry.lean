import MainTheorems.PathCycleTuza.CircularRuns
import MainTheorems.PathCycleTuza.CyclicEdges

namespace ResearchMain.PathCycleTuza.CircularRuns

variable {n k : ℕ} (D : CircularRuns n k)

theorem short_interval_indices (i j x y : ℕ)
    (hx : D.runStart i ≤ x ∧ x < D.runStart (i + 1))
    (hy : D.runStart j ≤ y ∧ y < D.runStart (j + 1))
    (hxy : x < y) (hs : y ≤ x + k) (hp : i % 2 = j % 2) :
    j = i ∨ j = i + 2 := by
  have hij : i ≤ j := by
    by_contra h
    have hm := D.runStart_mono (by omega : j + 1 ≤ i)
    omega
  have hji : j ≤ i + 2 := by
    by_contra h
    have hm := D.runStart_mono (by omega : i + 3 ≤ j)
    have hb := D.runStart_lower (i + 1) 2
    have hb' : D.runStart (i + 1) + Tuza.halfUp k * 2 ≤ D.runStart (i + 3) := by
      simpa using hb
    have hL : k ≤ 2 * Tuza.halfUp k := by unfold Tuza.halfUp; omega
    omega
  omega

theorem short_positions (p q : D.Position)
    (hxy : (D.vertexEquiv p).val < (D.vertexEquiv q).val)
    (hs : (D.vertexEquiv q).val ≤ (D.vertexEquiv p).val + k)
    (hp : D.color (D.vertexEquiv p) = D.color (D.vertexEquiv q)) :
    q.1.val = p.1.val ∨ q.1.val = p.1.val + 2 :=
  D.short_interval_indices _ _ _ _ (D.position_bounds p) (D.position_bounds q)
    hxy hs (D.sameColor_positions p q hp)

theorem short_wrap_positions (p q : D.Position)
    (_hxy : (D.vertexEquiv q).val < (D.vertexEquiv p).val)
    (hs : (D.vertexEquiv q).val + n ≤ (D.vertexEquiv p).val + k)
    (hp : D.color (D.vertexEquiv p) = D.color (D.vertexEquiv q)) :
    q.1.val + D.count = p.1.val + 2 := by
  have hy := D.position_bounds q
  have hy' : D.runStart (q.1.val + D.count) ≤ (D.vertexEquiv q).val + n ∧
      (D.vertexEquiv q).val + n < D.runStart (q.1.val + D.count + 1) := by
    rw [D.runStart_period]
    rw [show q.1.val + D.count + 1 = (q.1.val + 1) + D.count by omega, D.runStart_period]
    omega
  have hn := (D.vertexEquiv p).isLt
  have hc := D.count_even
  have hp' := D.sameColor_positions p q hp
  have h := D.short_interval_indices p.1.val (q.1.val + D.count)
    (D.vertexEquiv p).val ((D.vertexEquiv q).val + n)
    (D.position_bounds p) hy' (by omega) hs (by omega)
  have hi := p.1.isLt
  omega

theorem short_skip_offsets (i x y : ℕ)
    (hx : D.runStart i ≤ x ∧ x < D.runStart (i + 1))
    (hy : D.runStart (i + 2) ≤ y)
    (hs : y ≤ x + k) :
    (D.runStart (i + 1) - x - 1) + (y - D.runStart (i + 2)) <
      k - D.extendedLength (i + 1) := by
  have hstep := D.runStart_succ (i + 1)
  have hstep' : D.runStart (i + 2) = D.runStart (i + 1) + D.extendedLength (i + 1) := by
    simpa using hstep
  have hu := D.upper (D.index (i + 1))
  change D.extendedLength (i + 1) ≤ k at hu
  omega

end ResearchMain.PathCycleTuza.CircularRuns
