import SumsetRanges.OrdinarySmallParameters

open Finset
namespace SumsetRanges

/-- Actual bounded witnesses for every nonexcluded value in the ordinary small range. -/
theorem ordinary_small_range (h k M t : ℕ) (hh : 2≤h) (hk : h≤k)
    (hkn : 8*h≤k-1) (hprefix : h^2+1≤(k-1)/2) (hM : k+h-3≤M)
    (hmax : (8*h)^h*M≤(k-1)^h)
    (ht : ordinaryMinimum h k≤t) (htM : t≤h*M+1) (hex : t∉excludedValues h k) :
    ∃A : Finset ℤ,A.card=k ∧ A⊆Icc 0 ((h+M:ℕ):ℤ) ∧
      (ordinarySums A h).card=t := by
  have hM' : k-2≤M := by omega
  obtain ⟨d,i,hd,hdM,hi,hih,he⟩ := ordinary_small_parameters h k M t hh hk hM' ht htM hex
  have hmaxd : (8*h)^h*d≤(k-1)^h := (Nat.mul_le_mul_left _ hdM).trans hmax
  obtain ⟨B,hBc,hBb,hBi,hBf⟩ := positional_filling h (k-1) d hh hkn (by omega) hmaxd
  have hBprefix : Icc 0 ((h^2:ℕ):ℤ)⊆B := by
    intro x hx
    obtain ⟨hx0,hxh⟩ := Finset.mem_Icc.mp hx
    have hc : (x.toNat:ℤ)=x := Int.toNat_of_nonneg hx0
    have hhx : x.toNat<(k-1)/2 := by
      have hxx : x.toNat≤h^2 := Int.toNat_le.mpr hxh
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
  · rw [card_ordinary_smallFamily_sums B h d i (by omega) hi hih hBb hBprefix hBf,he]

end SumsetRanges
