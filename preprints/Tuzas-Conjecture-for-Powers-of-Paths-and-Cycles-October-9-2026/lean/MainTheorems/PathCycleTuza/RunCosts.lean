import MainTheorems.PathCycleTuza.RunLengths
import MainTheorems.Tuza.CompletePacking

namespace ResearchMain.PathCycleTuza

def runCost (k ℓ : ℕ) : ℕ := ℓ.choose 2 + (k - ℓ + 1).choose 2

theorem runCost_le (k ℓ : ℕ) (hl : Tuza.halfUp k ≤ ℓ) (hu : ℓ ≤ k) :
    runCost k ℓ ≤ k / 2 * ℓ := by
  have h₁ := Tuza.choose_two_integer ℓ
  have h₂ := Tuza.choose_two_integer (k - ℓ + 1)
  rw [Nat.cast_add, Nat.cast_sub hu, Nat.cast_one] at h₂
  have hs := halfUp_split k
  have hb := Tuza.halfUp_balanced k
  have he : (runCost k ℓ : ℤ) ≤ (k / 2 : ℕ) * (ℓ : ℤ) := by
    unfold runCost
    rw [Nat.cast_add]
    by_cases hp : k % 2 = 0
    · have hk : (k : ℤ) = 2 * (k / 2 : ℕ) := by omega
      have hlow : (k / 2 : ℕ) ≤ (ℓ : ℤ) := by omega
      have hprod := mul_nonpos_of_nonneg_of_nonpos
        (by omega : 0 ≤ (ℓ : ℤ) - (k / 2 : ℕ))
        (by omega : (ℓ : ℤ) - k - 1 ≤ 0)
      nlinarith
    · have hk : (k : ℤ) = 2 * (k / 2 : ℕ) + 1 := by omega
      have hlow : (k / 2 : ℕ) + 1 ≤ (ℓ : ℤ) := by omega
      have hprod := mul_nonpos_of_nonneg_of_nonpos
        (by omega : 0 ≤ (ℓ : ℤ) - (k / 2 : ℕ) - 1)
        (by omega : (ℓ : ℤ) - k ≤ 0)
      nlinarith
  exact_mod_cast he

theorem runCost_even_gain (k ℓ : ℕ) (hp : k % 2 = 0)
    (hl : k / 2 < ℓ) (hu : ℓ ≤ k) : runCost k ℓ + k / 2 ≤ k / 2 * ℓ := by
  have h₁ := Tuza.choose_two_integer ℓ
  have h₂ := Tuza.choose_two_integer (k - ℓ + 1)
  rw [Nat.cast_add, Nat.cast_sub hu, Nat.cast_one] at h₂
  have hk : (k : ℤ) = 2 * (k / 2 : ℕ) := by omega
  have hprod := mul_nonneg
    (by omega : 0 ≤ (ℓ : ℤ) - (k / 2 : ℕ) - 1)
    (by omega : 0 ≤ 2 * (k / 2 : ℕ) - (ℓ : ℤ))
  have he : (runCost k ℓ : ℤ) + (k / 2 : ℕ) ≤ (k / 2 : ℕ) * (ℓ : ℤ) := by
    unfold runCost
    rw [Nat.cast_add]
    nlinarith
  exact_mod_cast he

theorem sum_le_with_gain {I : Type*} [Fintype I] [DecidableEq I]
    (f g : I → ℕ) (a : ℕ) (hfg : ∀ i, f i ≤ g i)
    (i : I) (hi : f i + a ≤ g i) : (∑ j, f j) + a ≤ ∑ j, g j := by
  have hf := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hg := Finset.sum_erase_add Finset.univ g (Finset.mem_univ i)
  have hs : ∑ j ∈ Finset.univ.erase i, f j ≤ ∑ j ∈ Finset.univ.erase i, g j :=
    Finset.sum_le_sum (fun j _ => hfg j)
  omega

theorem runCost_sum (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 2 ≤ n) :
    (∑ i : Fin (runCount n k), runCost k (runLength n k i)) ≤ k / 2 * n := by
  calc
    _ ≤ ∑ i : Fin (runCount n k), k / 2 * runLength n k i :=
      Finset.sum_le_sum (fun i _ => runCost_le k _
        (runLength_bounds n k i).1 (runLength_bounds n k i).2)
    _ = _ := by rw [← Finset.mul_sum, runLength_sum n k hk hn]

theorem runLength_large (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 2 ≤ n)
    (hp : k % 2 = 0) (ho : n % 2 = 1) :
    ∃ i : Fin (runCount n k), k / 2 < runLength n k i := by
  by_contra h
  push Not at h
  have hs := halfUp_split k
  have hb := Tuza.halfUp_balanced k
  have he : ∀ i : Fin (runCount n k), runLength n k i = k / 2 := by
    intro i
    have hl := (runLength_bounds n k i).1
    have hu := h i
    omega
  have hm := runLength_sum n k hk hn
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hm
  norm_cast at hm
  have hr := runCount_even n k
  have hv : (runCount n k * (k / 2)) % 2 = 0 := by rw [Nat.mul_mod, hr]; simp
  omega

theorem runCost_sum_even_odd (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k + 2 ≤ n)
    (hp : k % 2 = 0) (ho : n % 2 = 1) :
    (∑ i : Fin (runCount n k), runCost k (runLength n k i)) + k / 2 ≤ k / 2 * n := by
  obtain ⟨i, hi⟩ := runLength_large n k hk hn hp ho
  have h := sum_le_with_gain (fun i => runCost k (runLength n k i))
    (fun i => k / 2 * runLength n k i) (k / 2)
    (fun i => runCost_le k _ (runLength_bounds n k i).1 (runLength_bounds n k i).2)
    i (runCost_even_gain k _ hp hi (runLength_bounds n k i).2)
  rwa [← Finset.mul_sum, runLength_sum n k hk hn] at h

end ResearchMain.PathCycleTuza
