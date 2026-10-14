import SumsetRanges.SmallRangeParameters

open Finset
namespace SumsetRanges

/-- Every cardinality in the complete small range is attained by an actual bounded integer set. -/
theorem restricted_small_range (h k M t : ℕ) (hh : 2≤h)
    (hk : 64*(2*h-1)*h+1≤k) (hM : k-2≤M)
    (hmax : (64*(2*h-1)*h)^h*M≤(2*h-1)*(k-1)^h)
    (ht : h*(k-h)+1≤t) (htM : t≤h*M+h-(h-1)^2+1) :
    ∃A : Finset ℤ,A.card=k ∧ A⊆Icc 0 ((h+M:ℕ):ℤ) ∧
      (restrictedSums A h).card=t := by
  have hl : 1≤2*h-1 := by omega
  have hkh : h+2≤k := by nlinarith
  have hs : 64*(2*h-1)*h≤k-1 := by omega
  have hsmall : h<(k-1)/2 := by
    have hb : 2*(h+1)≤k-1 := by nlinarith
    have hd := (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr (by simpa [mul_comm] using hb)
    omega
  obtain ⟨d,i,hd,hdM,hi,hih,he⟩ := small_range_parameters h k M t hh hkh hM ht htM
  have hmaxd : (64*(2*h-1)*h)^h*d≤(2*h-1)*(k-1)^h :=
    (Nat.mul_le_mul_left _ hdM).trans hmax
  obtain ⟨B,hBc,hBb,_,hBi,hBf⟩ := restricted_filling h (k-1) d hh hs (by omega) hmaxd
  have hprefix : Icc 0 (h:ℤ)⊆B := by
    intro x hx
    obtain ⟨hx0,hxh⟩ := Finset.mem_Icc.mp hx
    have hc : (x.toNat:ℤ)=x := Int.toNat_of_nonneg hx0
    have hhx : x.toNat<(k-1)/2 := by
      have hxnh : x.toNat≤h := Int.toNat_le.mpr hxh
      omega
    simpa [hc] using hBi x.toNat hhx
  refine ⟨smallFamily B i,?_,?_,?_⟩
  · rw [card_smallFamily B i hi (fun b hb => (Finset.mem_Icc.mp (hBb hb)).1),hBc]
    omega
  · intro x hx
    have hb := Finset.mem_Icc.mp (smallFamily_bounds B d i hBb hx)
    apply Finset.mem_Icc.mpr
    refine ⟨hb.1,?_⟩
    have hdi : i+d≤h+M := Nat.add_le_add hih hdM
    exact hb.2.trans (by exact_mod_cast hdi)
  · have hq : h-1+1=h := by omega
    have hc := card_smallFamily_sums B (h-1) d i (by omega) hi (by omega) (by omega)
      hBb (by simpa [hq] using hprefix) (by simpa [hq] using hBf)
    rw [hq] at hc
    simpa [pow_two] using hc.trans (by simpa [pow_two] using he)

end SumsetRanges
