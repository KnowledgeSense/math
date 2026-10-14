import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith

namespace SumsetRanges

/-- Consecutive integer intervals with no gap fill the interval between their endpoints. -/
theorem integer_interval_chain {α : Type*} (f : ℕ → α → ℤ)
    (valid : ℕ → α → Prop) (lo hi : ℕ → ℤ) (n : ℕ)
    (cover : ∀ j≤n, ∀ z, lo j≤z → z≤hi j → ∃x, valid j x ∧ f j x=z)
    (hlo : ∀ j<n, lo (j+1)≤lo j)
    (hoverlap : ∀ j<n, lo j≤hi (j+1)+1) :
    ∀ z, lo n≤z → z≤hi 0 → ∃j≤n, ∃x, valid j x ∧ f j x=z := by
  induction n with
  | zero =>
      intro z hz hz'
      obtain ⟨x,hx,he⟩ := cover 0 (by omega) z hz hz'
      exact ⟨0,by omega,x,hx,he⟩
  | succ n ih =>
      intro z hz hz'
      by_cases hn : lo n≤z
      · obtain ⟨j,hj,x,hx,he⟩ := ih
          (fun j hj => cover j (by omega))
          (fun j hj => hlo j (by omega))
          (fun j hj => hoverlap j (by omega)) z hn hz'
        exact ⟨j,by omega,x,hx,he⟩
      · have hov := hoverlap n (by omega)
        obtain ⟨x,hx,he⟩ := cover (n+1) (by omega) z hz (by omega)
        exact ⟨n+1,by omega,x,hx,he⟩

/-- A nonincreasing integer sequence with drops at most one takes every intermediate value. -/
theorem integer_sequence_intermediate (f : ℕ → ℤ) (n : ℕ)
    (step : ∀ j<n, f (j+1)≤f j ∧ f j≤f (j+1)+1)
    (z : ℤ) (hz : f n≤z) (hz' : z≤f 0) : ∃j≤n, f j=z := by
  obtain ⟨j,hj,x,_,he⟩ := integer_interval_chain (fun j (_ : Unit) => f j)
    (fun _ _ => True) f f n
    (fun j _ z h1 h2 => ⟨(),trivial,by omega⟩)
    (fun j hj => (step j hj).1) (fun j hj => (step j hj).2) z hz hz'
  exact ⟨j,hj,he⟩

end SumsetRanges
