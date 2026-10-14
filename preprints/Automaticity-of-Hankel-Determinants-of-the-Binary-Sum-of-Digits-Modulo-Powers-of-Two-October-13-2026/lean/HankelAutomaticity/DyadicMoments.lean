import HankelAutomaticity.Definitions

noncomputable section
namespace HankelAutomaticity

 theorem weightedMoment_below {L n : ℕ} (x : ℚ) (hn : n<2^(L+1)) :
    weightedMoment L x n=(digitSum n : ℚ) := by
  simp [weightedMoment, Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn]

 theorem weightedMoment_add_period {L n : ℕ} (x : ℚ) (hn : n<2^(L+1)) :
    weightedMoment L x (n+2^(L+1))=(digitSum n : ℚ)+x := by
  simp [weightedMoment, Nat.mod_eq_of_lt hn, Nat.div_eq_of_lt hn]

 theorem weightedMoment_first_difference {L n : ℕ} (x : ℚ) (hn : n<2*2^L) :
    weightedMoment L x (n+2^L)-weightedMoment L x n=
      1+(x-2)*(if 2^L≤n then 1 else 0) := by
  have hp : 2^(L+1)=2*2^L := by rw [pow_succ]; ring
  have hnb : n<2^(L+1) := by omega
  rw [weightedMoment_below x hnb]
  by_cases h : n<2^L
  · have hn' : n+2^L<2^(L+1) := by omega
    rw [weightedMoment_below x hn', digitSum_add_pow h]
    simp [show ¬2^L≤n by omega]
  · have ht : n-2^L<2^L := by omega
    have he : n=(n-2^L)+2^L := by omega
    have he' : n+2^L=(n-2^L)+2^(L+1) := by omega
    rw [he', weightedMoment_add_period x (by omega), he, digitSum_add_pow ht]
    simp [show 2^L≤n-2^L+2^L by omega]
    ring

 theorem weightedMoment_second_difference {L n : ℕ} (x : ℚ) (hn : n<2*2^L) :
    weightedMoment L x (n+2*2^L)-2*weightedMoment L x (n+2^L)+
      weightedMoment L x n = (x-2)-2*(x-2)*(if 2^L≤n then 1 else 0) := by
  have hp : 2^(L+1)=2*2^L := by rw [pow_succ]; ring
  have h1 := weightedMoment_first_difference x hn
  have h2 : weightedMoment L x (n+2*2^L)=weightedMoment L x n+x := by
    rw [← hp, weightedMoment_add_period x (by omega), weightedMoment_below x (by omega)]
  rw [h2]
  linear_combination -2*h1

 theorem weightedMoment_lower_top {L n : ℕ} (hL : 0<L) (x : ℚ)
    (hn : n<2^(L+1)) :
    weightedMoment (L-1) x n=(digitSum n : ℚ)+
      (x-1)*(if 2^L≤n then 1 else 0) := by
  have he : L-1+1=L := by omega
  unfold weightedMoment
  rw [he]
  have hs := digitSum_split (L:=L) hn
  have hp : 0<2^L := by positivity
  have hq : n/2^L<2 := by
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    simpa [pow_succ, Nat.mul_comm] using hn
  have hq01 := Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hq)
  rcases hq01 with hq | hq
  · have hlt : n<2^L := (Nat.div_eq_zero_iff.mp hq).resolve_left hp.ne'
    simp [Nat.mod_eq_of_lt hlt, hq, show ¬2^L≤n by omega]
  · have hge : 2^L≤n := by
      by_contra h
      have := Nat.div_eq_of_lt (show n<2^L by omega)
      omega
    rw [hs]
    simp [hq, hge]

end HankelAutomaticity
