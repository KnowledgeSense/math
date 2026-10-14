import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section
open Filter
open scoped Topology
namespace CircleKernel

/-- A vanishing error is bounded by any vanishing telescoping barrier for its increments. -/
theorem discrete_tail_barrier (e b : ℕ → ℝ) (N : ℕ)
    (he : Tendsto e atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hd : ∀ n, N ≤ n → |e (n+1)-e n| ≤ b n-b (n+1))
    (n : ℕ) (hn : N ≤ n) : |e n| ≤ b n := by
  have hfinite : ∀ k, |e (n+k)-e n| ≤ b n-b (n+k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep := hd (n+k) (by omega)
      calc
        |e (n+(k+1))-e n| = |(e (n+k+1)-e (n+k))+(e (n+k)-e n)| := by
          congr 1
          ring_nf
        _ ≤ |e (n+k+1)-e (n+k)| + |e (n+k)-e n| := abs_add_le _ _
        _ ≤ (b (n+k)-b (n+k+1)) + (b n-b (n+k)) := add_le_add hstep ih
        _ = b n-b (n+(k+1)) := by simp only [Nat.add_assoc]; ring
  have ht : Tendsto (fun k => n+k) atTop atTop := tendsto_atTop_mono (fun k => Nat.le_add_left k n) tendsto_id
  have hel := ((he.comp ht).sub_const (e n)).abs
  have hbl := (tendsto_const_nhds (x := b n) (f := atTop)).sub (hb.comp ht)
  have h := le_of_tendsto_of_tendsto hel hbl (Filter.Eventually.of_forall hfinite)
  simpa using h

end CircleKernel
