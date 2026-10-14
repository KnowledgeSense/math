import WeakClergyman

open WeakClergyman

example {k : ℕ} {a : Fin k → ℕ} (S : AntiRecurrence k a)
    (hk : 2 ≤ k) (ha : ∀ j, 0 < a j) (n : ℕ) (hn : 1 ≤ n) :
    |(S.A (n-1) : ℤ) - ((k*(∑ j : Fin k, a j)+1)*n : ℕ)| ≤
      (2*(k*(∑ j : Fin k, a j)+1) : ℕ) :=
  uniform_discrepancy S hk ha n hn

example (S : AntiRecurrence 2 (fun _ => 1)) (n : ℕ) (hn : 1 ≤ n) :
    |(S.A (n-1) : ℤ) - (5*n : ℕ)| ≤ (10 : ℤ) := by
  simpa using uniform_discrepancy S (by decide) (by intro j; decide) n hn
