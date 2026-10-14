import Paving.SeparatedRatios

noncomputable section
namespace Paving

theorem strict_turan_of_lower_half (f : ℕ→ℝ) (k : ℕ)
    (hs : ∀i, i ≤ k → f (k-i)=f i)
    (hl : ∀i, 1 ≤ i → 2*i ≤ k → f (i-1)*f (i+1) < f i^2) :
    ∀i, 1 ≤ i → i < k → f (i-1)*f (i+1) < f i^2 := by
  intro i hi hik
  by_cases hh : 2*i ≤ k
  · exact hl i hi hh
  · have hj : 1 ≤ k-i := by omega
    have hjk : 2*(k-i) ≤ k := by omega
    have h := hl (k-i) hj hjk
    have h0 := hs i (by omega)
    have h1 := hs (i+1) (by omega)
    have h2 := hs (i-1) (by omega)
    rw [show k-i-1=k-(i+1) by omega,
      show k-i+1=k-(i-1) by omega,h1,h2,h0] at h
    nlinarith [h]

theorem odd_row_strict (f : ℕ→ℝ) (m n : ℕ) (hm : 1 ≤ m) (hn : 2*m+1 ≤ n)
    (hp : ∀i, i ≤ 2*m+1 → 0 < f i)
    (hs : ∀i, i ≤ 2*m+1 → f (2*m+1-i)=f i)
    (hb : ∀i, 1 ≤ i → i ≤ m →
      lowerRatio (2*m+1) n i*f (i-1) ≤ f i ∧
        f i ≤ upperRatio (2*m+1) n i*f (i-1)) :
    ∀i, 1 ≤ i → i < 2*m+1 → f (i-1)*f (i+1) < f i^2 := by
  apply strict_turan_of_lower_half f (2*m+1) hs
  intro i hi hh
  have him : i ≤ m := by omega
  have hiR : (0:ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hnR : (2:ℝ)*m+1 ≤ n := by exact_mod_cast hn
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hiR' : (i:ℝ) ≤ m := by exact_mod_cast him
  by_cases he : i=m
  · subst i
    have hlow := (hb m hm le_rfl).1
    have hmid := odd_middle_lowerRatio (m:=(m:ℝ)) (n:=(n:ℝ)) (by linarith) (by linarith)
    have hprev := hp (m-1) (by omega)
    have hinc : f (m-1) < f m := by nlinarith [mul_lt_mul_of_pos_right hmid hprev]
    have heq : f (m+1)=f m := by
      simpa only [show 2*m+1-m=m+1 by omega] using hs m (by omega)
    rw [heq]
    exact middle_pair_strict (hp m (by omega)) hinc
  · have hip : i+1 ≤ m := by omega
    have hlo := (hb i hi him).1
    have hup := (hb (i+1) (by omega) hip).2
    rw [Nat.add_sub_cancel] at hup
    apply strict_turan_of_separated_bounds (hp (i-1) (by omega)) (hp i (by omega)) hlo hup
    have hsep := ratio_intervals_separated (k:=2*(m:ℝ)+1) (n:=(n:ℝ)) (i:=(i:ℝ))
      hiR (by linarith) (by linarith)
    simpa only [Nat.cast_add,Nat.cast_one] using hsep

theorem even_row_strict (f : ℕ→ℝ) (m n : ℕ) (hm : 2 ≤ m) (hn : 2*m ≤ n)
    (hp : ∀i, i ≤ 2*m → 0 < f i)
    (hs : ∀i, i ≤ 2*m → f (2*m-i)=f i)
    (hb : ∀i, 1 ≤ i → i < m →
      lowerRatio (2*m) n i*f (i-1) ≤ f i ∧
        f i ≤ upperRatio (2*m) n i*f (i-1))
    (hpen : f (m-2)*f m < f (m-1)^2) (hmid : f (m-1) < f m) :
    ∀i, 1 ≤ i → i < 2*m → f (i-1)*f (i+1) < f i^2 := by
  apply strict_turan_of_lower_half f (2*m) hs
  intro i hi hh
  have him : i ≤ m := by omega
  by_cases he : i=m
  · subst i
    have heq : f (m+1)=f (m-1) := by
      have h := hs (m+1) (by omega)
      rw [show 2*m-(m+1)=m-1 by omega] at h
      exact h.symm
    rw [heq]
    nlinarith [hp (m-1) (by omega),hp m (by omega)]
  · by_cases he1 : i=m-1
    · subst i
      simpa only [show m-1-1=m-2 by omega,show m-1+1=m by omega] using hpen
    · have him' : i+1 < m := by omega
      have hlo := (hb i hi (by omega)).1
      have hup := (hb (i+1) (by omega) him').2
      rw [Nat.add_sub_cancel] at hup
      apply strict_turan_of_separated_bounds (hp (i-1) (by omega)) (hp i (by omega)) hlo hup
      have hiR : (0:ℝ) < i := by exact_mod_cast (show 0 < i by omega)
      have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
      have hiR' : (i:ℝ)+1 < m := by exact_mod_cast him'
      have hnR : (2:ℝ)*m ≤ n := by exact_mod_cast hn
      simpa only [Nat.cast_add,Nat.cast_one] using
        ratio_intervals_separated (k:=2*(m:ℝ)) (n:=(n:ℝ)) hiR (by linarith) (by linarith)

end Paving
