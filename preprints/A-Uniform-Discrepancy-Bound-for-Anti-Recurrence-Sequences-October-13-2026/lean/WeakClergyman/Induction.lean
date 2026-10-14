import WeakClergyman.Blocks

namespace WeakClergyman.AntiRecurrence

variable {k : ℕ} {a : Fin k → ℕ} (S : AntiRecurrence k a)
variable (hk : 2 ≤ k) (ha : ∀ j, 0 < a j)
include hk ha

 theorem initial_large : k + 1 ≤ S.A 0 := by
  classical
  let last : Fin k := ⟨k-1, by omega⟩
  have hs : a last * last.val ≤ ∑ j : Fin k, a j * j.val :=
    Finset.single_le_sum (f := fun j : Fin k => a j * j.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ last)
  have hp : k-1 ≤ a last * last.val := by
    dsimp [last]
    exact Nat.le_mul_of_pos_left _ (ha last)
  have ht := WeakClergyman.AntiRecurrence.tau_lower ha
  have hv := S.initial_value hk ha
  simp only [Nat.mul_add, Nat.mul_one, Finset.sum_add_distrib] at hv
  omega

omit hk ha in
 theorem iterated_separation (n : ℕ) :
    S.A 0 + n * (k * ∑ j : Fin k, a j) ≤ S.A n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := S.separation n
    nlinarith

 theorem earlier_anchor (n : ℕ) (hn : 2 ≤ n) :
    (valuesBelow S.A (S.B (k*n))).card < n := by
  let h := (valuesBelow S.A (S.B (k*n))).card
  have hf := S.forward_position hk ha n
  have hm : S.B (k*n) ≤ S.B (k*n+(k-1)) := S.B_strictMono.monotone (by omega)
  have hc : h ≤ n := card_valuesBelow_le S.A_strictMono (le_trans hm hf.le)
  have hr := S.complementary_rank (k*n)
  have hs := S.iterated_separation (n-1)
  have hi := S.initial_large hk ha
  have ht := WeakClergyman.AntiRecurrence.tau_lower ha
  have hτ : 2 ≤ ∑ j : Fin k, a j := le_trans hk ht
  have hmul : 2*k ≤ k * ∑ j : Fin k, a j := by nlinarith
  have hbound : S.B (k*n) ≤ S.A (n-1) := by
    dsimp [h] at hc
    have hn' : n-1+1=n := by omega
    have hprod := Nat.mul_le_mul_left (n-1) hmul
    have hpoly : 0 ≤ (k-2)*(n-2) := Nat.zero_le _
    nlinarith
  have hstrict : S.B (k*n) < S.A (n-1) :=
    lt_of_le_of_ne hbound (S.disjoint_values (n-1) (k*n)).symm
  have hx := card_valuesBelow_le S.A_strictMono hstrict.le
  omega

end WeakClergyman.AntiRecurrence
