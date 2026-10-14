import WeakClergyman.Induction

namespace WeakClergyman

/-- The uniform weak Clergyman bound, in natural-number two-sided form. -/
theorem discrepancy_bounds {k : ℕ} {a : Fin k → ℕ}
    (S : AntiRecurrence k a) (hk : 2 ≤ k) (ha : ∀ j, 0 < a j) (n : ℕ) :
    let κ := k * (∑ j : Fin k, a j) + 1
    κ * (n+1) ≤ S.A n + 2*κ ∧ S.A n ≤ κ*(n+1) + 2*κ := by
  classical
  let τ := ∑ j : Fin k, a j
  let κ := k*τ+1
  change κ*(n+1) ≤ S.A n+2*κ ∧ S.A n ≤ κ*(n+1)+2*κ
  have hτ : k ≤ τ := WeakClergyman.AntiRecurrence.tau_lower ha
  have hκ : κ = k*τ+1 := rfl
  have hi := S.initial_bounds hk ha
  change τ ≤ S.A 0 ∧ S.A 0 ≤ k*τ at hi
  have hv : S.A 0 = (∑ j : Fin k, a j*j.val) + τ := by
    simpa [Nat.mul_add, Finset.sum_add_distrib, τ] using S.initial_value hk ha
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn0 : n=0
    · subst n
      constructor <;> nlinarith
    by_cases hn1 : n=1
    · subst n
      have hr := S.complementary_rank k
      have hf := S.forward_position hk ha 1
      have hb : S.B k ≤ S.A 1 := by
        apply le_trans (S.B_strictMono.monotone ?_) hf.le
        omega
      have hc := card_valuesBelow_le S.A_strictMono hb
      have hB : S.B k ≤ k+2 := by omega
      have hBt := Nat.mul_le_mul_left τ hB
      have hw := (S.weighted_block_bounds hk ha 1).2
      simp only [Nat.mul_one] at hw
      change S.A 1 ≤ τ*S.B k + (∑ j : Fin k, a j*j.val)+τ at hw
      constructor
      · omega
      · nlinarith
    have hn : 2 ≤ n := by omega
    let h := (valuesBelow S.A (S.B (k*n))).card
    have hh : h < n := S.earlier_anchor hk ha n hn
    have hr : S.B (k*n) = k*n+h+1 := S.complementary_rank (k*n)
    have hbr := rank_bracket S.A_strictMono (S.B (k*n))
    have hstrict : S.B (k*n) < S.A h :=
      lt_of_le_of_ne hbr.1 (S.disjoint_values h (k*n)).symm
    have huA := (ih h hh).2
    have hu : S.B (k*n)+1 ≤ κ*(h+1)+2*κ := by omega
    have hl : κ*h+1 ≤ S.B (k*n)+2*κ := by
      by_cases hh0 : h=0
      · rw [hh0]
        simp only [Nat.mul_zero, Nat.zero_add]
        have := S.B_pos (k*n)
        omega
      · have hprev : h-1 < n := by omega
        have hlA := (ih (h-1) hprev).1
        have hbprev := hbr.2 (h-1) (by omega)
        have hs : h-1+1=h := by omega
        rw [hs] at hlA
        omega
    have hw := S.weighted_block_bounds hk ha n
    change τ*S.B (k*n)+(∑ j : Fin k, a j*j.val) ≤ S.A n ∧
      S.A n ≤ τ*S.B (k*n)+(∑ j : Fin k, a j*j.val)+τ at hw
    have hwu : S.A n ≤ τ*S.B (k*n)+S.A 0 := by omega
    have hwl : τ*S.B (k*n)+S.A 0 ≤ S.A n+τ := by omega
    rw [hr] at hwu hwl hu hl
    have hmul : 2*κ ≤ k*κ := Nat.mul_le_mul_right κ hk
    have hku := Nat.mul_le_mul_left k hwu
    have hkl := Nat.mul_le_mul_left k hwl
    have hki0 := Nat.mul_le_mul_left k hi.1
    have hki1 := Nat.mul_le_mul_left k hi.2
    constructor <;> nlinarith

/-- Absolute discrepancy for the original one-based index convention. -/
theorem uniform_discrepancy {k : ℕ} {a : Fin k → ℕ}
    (S : AntiRecurrence k a) (hk : 2 ≤ k) (ha : ∀ j, 0 < a j)
    (n : ℕ) (hn : 1 ≤ n) :
    |(S.A (n-1) : ℤ) - ((k*(∑ j : Fin k, a j)+1)*n : ℕ)| ≤
      (2*(k*(∑ j : Fin k, a j)+1) : ℕ) := by
  have hb := discrepancy_bounds S hk ha (n-1)
  dsimp at hb
  rw [Nat.sub_add_cancel hn] at hb
  rw [abs_le]
  constructor <;> omega

end WeakClergyman
