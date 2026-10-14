import PenneyDensity.FiniteProbability

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

 theorem card_pair_overlap {n k : ℕ} (hk : 0<k) (hkn : k<n) (b c : Bool) :
    Fintype.card {f : Fin (n+n) → Bool //
      properOverlap (pairWords f b) (pairWords f c) k}=2^(n+n-k) := by
  have he : ∀ f : Fin (n+n) → Bool,
      properOverlap (pairWords f b) (pairWords f c) k ↔
      ((pairWords f b).drop (n-k)).take k=((pairWords f c).drop 0).take k := by
    intro f
    have hh : (((pairWords f b).drop (n-k))).length=k := by
      simp only [List.length_drop,pairWords_length]
      omega
    have ht : (((pairWords f b).drop (n-k))).take k=(pairWords f b).drop (n-k) := by
      simpa only [hh] using (List.take_length (l := (pairWords f b).drop (n-k)))
    simp only [properOverlap,pairWords_length,hk,hkn,true_and,List.drop_zero,ht]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  exact card_pair_block_collision b c (by omega) (by omega) (by omega) (by omega)
    (Or.inr (by omega))

 theorem power_ratio {N k : ℕ} (hk : k≤N) :
    (2 : ℝ)^(N-k)/2^N=(1/2 : ℝ)^k := by
  have he : N=N-k+k := (Nat.sub_add_cancel hk).symm
  conv_lhs => arg 2; rw [he,pow_add]
  rw [div_mul_eq_div_div,div_self (pow_ne_zero _ (by norm_num))]
  rw [one_div,one_div,inv_pow]

 theorem probability_pair_overlap {n k : ℕ} (hk : 0<k) (hkn : k<n) (b c : Bool) :
    probability (fun f : Fin (n+n) → Bool =>
      properOverlap (pairWords f b) (pairWords f c) k)=(1/2 : ℝ)^k := by
  rw [probability_card_formula]
  rw [card_pair_overlap hk hkn b c]
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  exact power_ratio (by omega)

 theorem probability_pair_block_collision {n i j m : ℕ} (b c : Bool)
    (hi : i+m≤n) (hj : j+m≤n) (hiN : i<n) (hjN : j<n) (hneq : b≠c ∨ i≠j) :
    probability (fun f : Fin (n+n) → Bool =>
      ((pairWords f b).drop i).take m=((pairWords f c).drop j).take m)=(1/2 : ℝ)^m := by
  rw [probability_card_formula]
  rw [card_pair_block_collision b c hi hj hiN hjN hneq]
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  exact power_ratio (by omega)

end PenneyDensity
