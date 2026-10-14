import HonestEmbeddingDimension.MinimumCoordinate

namespace HonestEmbeddingDimension

def subalgebraValues (B : Subalgebra ℂ (PowerSeries ℂ)) : Set ℕ :=
  {n | ∃ f ∈ B, PowerSeries.order f=n}

def ReducedBelow (B : Subalgebra ℂ (PowerSeries ℂ)) (N : ℕ) (f : PowerSeries ℂ) : Prop :=
  (N : ℕ∞) ≤ f.order ∨ ∃ n < N, f.order=n ∧ n ∉ subalgebraValues B

/-- Matching leading coefficients strictly raises the order of a difference. -/
theorem order_sub_leading_cancellation (f g : PowerSeries ℂ) (n : ℕ)
    (hf : f.order=n) (hg : g.order=n) :
    ((n+1 : ℕ) : ℕ∞) ≤
      (f-(PowerSeries.coeff n f / PowerSeries.coeff n g) • g).order := by
  apply PowerSeries.nat_le_order
  intro k hk
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h | rfl
  · have hfk := (PowerSeries.order_eq_nat.mp hf).2 k h
    have hgk := (PowerSeries.order_eq_nat.mp hg).2 k h
    simp [hfk, hgk]
  · have hgn := (PowerSeries.order_eq_nat.mp hg).1
    simp [div_mul_cancel₀ _ hgn]

/-- Finite cancellation against an actual subalgebra terminates, without any convergence premise. -/
theorem exists_reduced_mod_subalgebra (B : Subalgebra ℂ (PowerSeries ℂ)) (N : ℕ)
    (f : PowerSeries ℂ) : ∃ h ∈ B, ReducedBelow B N (f-h) := by
  classical
  have step : ∀ n, n ≤ N → ∀ f : PowerSeries ℂ, (n : ℕ∞) ≤ f.order →
      ∃ h ∈ B, ReducedBelow B N (f-h) := by
    intro n hn
    refine Nat.decreasingInduction (motive := fun n _ =>
      ∀ f : PowerSeries ℂ, (n : ℕ∞) ≤ f.order → ∃ h ∈ B, ReducedBelow B N (f-h))
      ?_ ?_ hn
    · intro k hk ih f hf
      by_cases hhigh : ((k+1 : ℕ) : ℕ∞) ≤ f.order
      · exact ih f hhigh
      · have hlt : f.order < (k : ℕ∞)+1 := by
          simpa only [Nat.cast_add, Nat.cast_one] using lt_of_not_ge hhigh
        have he : f.order=k := le_antisymm (ENat.lt_natCast_add_one_iff.mp hlt) hf
        by_cases hv : k ∈ subalgebraValues B
        · obtain ⟨g,hg,hgo⟩ := hv
          let c := PowerSeries.coeff k f / PowerSeries.coeff k g
          have hrem := order_sub_leading_cancellation f g k he hgo
          obtain ⟨h,hh,hr⟩ := ih (f-c • g) hrem
          refine ⟨c • g+h, B.add_mem (B.smul_mem hg c) hh, ?_⟩
          have hform : f-(c • g+h)=(f-c • g)-h := by abel
          rwa [hform]
        · exact ⟨0, B.zero_mem, by simpa only [sub_zero] using (show ReducedBelow B N f from Or.inr ⟨k,hk,he,hv⟩)⟩
    · intro f hf
      exact ⟨0,B.zero_mem,by simpa only [sub_zero] using (show ReducedBelow B N f from Or.inl hf)⟩
  exact step 0 (Nat.zero_le N) f (by simp)

end HonestEmbeddingDimension
