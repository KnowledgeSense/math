import HankelAutomaticity.Normalization
import HankelAutomaticity.PolynomialPair

noncomputable section
namespace HankelAutomaticity

 theorem normalized_binary_word (v : List Bool) (q : ℚ) (hq : q≠0) :
    normalizedPair v.length (binaryValue (true::v)+1) q=polynomialPair (true::v) q := by
  induction v using (measure List.length).wf.induction generalizing q with
  | h v ih =>
    rcases v with _ | ⟨b, _ | ⟨c, w⟩⟩
    · simpa [binaryValue, polynomialPair] using normalized_two q hq
    · cases b
      · simpa [binaryValue, polynomialPair] using normalized_three q hq
      · simpa [binaryValue, polynomialPair] using normalized_four q hq
    · let k := (c::w).length
      let s := binaryValue (c::w)
      have hk : 1 ≤ k := by simp [k]
      have hs : s<2^k := binaryValue_lt (c::w)
      have hpow : 2^(k+1)=2*2^k := by rw [pow_succ]; ring
      have htail : (c::w).length<(b::c::w).length := by simp
      have hcomp : (complement (c::w)).length<(b::c::w).length := by simp
      cases b
      · have hc := ih (complement (c::w)) hcomp 1 (by norm_num)
        have hcindex : binaryValue (true::complement (c::w))+1=2^(k+1)-s := by
          have hv := binaryValue_complement (c::w)
          change 2^(complement (c::w)).length+binaryValue (complement (c::w))+1=_
          rw [complement_length]
          change 2^k+binaryValue (complement (c::w))+1=_
          change s+binaryValue (complement (c::w))+1=2^k at hv
          omega
        have hcn : (complement (c::w)).length=k := by simp [k]
        rw [hcindex, hcn] at hc
        have hn := normalized_lower (k+1) (2^(k+1)-s) s (by omega)
          (by omega) (by omega) q hq
        simp only [Nat.add_sub_cancel] at hn
        rw [hc] at hn
        rw [polynomialPair]
        simpa only [k, s, List.length_cons, binaryValue, Bool.false_eq_true, ↓reduceIte,
          zero_add, complement_cons, Bool.not_false, Nat.add_assoc] using hn
      · have hc := ih (c::w) htail (2*q) (mul_ne_zero (by norm_num) hq)
        have hM : (2^k-s-1)+(2*s+1)+1+(2^k-s-1)=2^(k+1) := by omega
        have hd : (2^k-s-1)+(2*s+1)+1=2^k+s+1 := by omega
        have hn := normalized_upper (k+1) (2^k-s-1) (2*s+1) (by omega) hM q hq
        simp only [Nat.add_sub_cancel] at hn
        rw [hd] at hn
        have hci : binaryValue (true::c::w)+1=2^k+s+1 := rfl
        rw [hci] at hc
        rw [hc] at hn
        rw [polynomialPair]
        simpa only [k, s, List.length_cons, binaryValue, ↓reduceIte, Nat.add_assoc] using hn

 theorem determinant_eq_polynomialPair (v : List Bool) :
    determinant (binaryValue (true::v)+1)=(polynomialPair (true::v) (1 : ℤ)).1 := by
  have h := congrArg Prod.fst (normalized_binary_word v 1 (by norm_num))
  simp only [normalizedPair, one_pow, one_div_one, one_mul] at h
  have hn : binaryValue (true::v)+1 ≤ 2^(v.length+1) := by
    have hv := binaryValue_lt v
    simp only [binaryValue, ↓reduceIte]
    rw [pow_succ]
    omega
  rw [hankel_one hn] at h
  have hm := polynomialPair_map (Int.castRingHom ℚ) (true::v) 1
  simp only [map_one] at hm
  have hm' := congrArg Prod.fst hm
  exact Int.cast_injective (α:=ℚ) (h.trans hm')

end HankelAutomaticity
