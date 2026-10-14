import SumsetRanges.RestrictedFilling

open Finset
namespace SumsetRanges

def smallFamily (B : Finset ℤ) (i : ℕ) : Finset ℤ := insert 0 (B.image (fun b => (i:ℤ)+b))

theorem card_smallFamily (B : Finset ℤ) (i : ℕ) (hi : 1 ≤ i)
    (hB : ∀b∈B,0≤b) : (smallFamily B i).card=B.card+1 := by
  unfold smallFamily
  rw [Finset.card_insert_of_notMem,Finset.card_image_of_injective]
  · exact fun _ _ h => add_left_cancel h
  · intro hz
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hz
    have hp := hB b hb
    omega

theorem smallFamily_bounds (B : Finset ℤ) (d i : ℕ)
    (hB : B⊆Icc 0 (d:ℤ)) : smallFamily B i⊆Icc 0 ((i+d:ℕ):ℤ) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · simp only [Finset.mem_Icc]; constructor <;> positivity
  · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    have hh := Finset.mem_Icc.mp (hB hb)
    apply Finset.mem_Icc.mpr
    push_cast
    constructor <;> omega

theorem smallFamily_sums (B : Finset ℤ) (q d i : ℕ) (hq : 1≤q)
    (hi : 1 ≤ i) (hiq : i≤q+1) (hd : q+1≤d)
    (hB : B⊆Icc 0 (d:ℤ)) (hprefix : Icc 0 ((q+1:ℕ):ℤ)⊆B)
    (hf : restrictedSums B (q+1)=Icc ((q+1).choose 2:ℤ)
      (((q+1:ℕ):ℤ)*d-(q+1).choose 2)) :
    restrictedSums (smallFamily B i) (q+1)=
      Icc ((q:ℤ)*i+q.choose 2) (((q+1:ℕ):ℤ)*(i+d)-(q+1).choose 2) := by
  have hz : (0:ℤ)∉B.image (fun b => (i:ℤ)+b) := by
    intro hz
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hz
    have hp := (Finset.mem_Icc.mp (hB hb)).1
    omega
  have hc : ((q+1).choose 2:ℤ)=(q:ℤ)+q.choose 2 := by
    exact_mod_cast (show (q+1).choose 2=q+q.choose 2 by
      rw [Nat.choose_succ_succ' q 1,Nat.choose_one_right])
  have hc2 : 2*(q.choose 2:ℤ)=(q:ℤ)*((q:ℤ)-1) := by
    have ht : (2:ℤ)*(q.choose 2:ℤ)=(q:ℤ)*((q-1:ℕ):ℤ) := by exact_mod_cast choose_two_double q
    simpa [Int.ofNat_sub hq] using ht
  unfold smallFamily
  rw [restrictedSums_insert_succ _ 0 hz,restrictedSums_translate,restrictedSums_translate]
  simp only [zero_add,Finset.image_id',nsmul_eq_mul]
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      rw [hf] at hy
      have hh := Finset.mem_Icc.mp hy
      apply Finset.mem_Icc.mpr
      constructor <;> push_cast at hh ⊢ <;> nlinarith
    · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      have hh := restrictedSums_int_bounds B 0 d (fun _ hb => Finset.mem_Icc.mp (hB hb)) q hy
      simp only [mul_zero,zero_add] at hh
      apply Finset.mem_Icc.mpr
      constructor <;> push_cast at hh ⊢ <;> nlinarith
  · intro hx
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hx
    by_cases hm : ((q+1:ℕ):ℤ)*i+(q+1).choose 2≤x
    · apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨x-((q+1:ℕ):ℤ)*i,?_,by ring⟩
      rw [hf]
      apply Finset.mem_Icc.mpr
      constructor <;> push_cast at * <;> nlinarith
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨x-(q:ℤ)*i,restrictedSums_mono hprefix q ?_,by ring⟩
      rw [restrictedSums_int_Icc 0 ((q+1:ℕ):ℤ) q (by omega) (by omega)]
      simp only [mul_zero,zero_add]
      apply Finset.mem_Icc.mpr
      constructor <;> push_cast at * <;> nlinarith

theorem card_smallFamily_sums (B : Finset ℤ) (q d i : ℕ) (hq : 1≤q)
    (hi : 1 ≤ i) (hiq : i≤q+1) (hd : q+1≤d)
    (hB : B⊆Icc 0 (d:ℤ)) (hprefix : Icc 0 ((q+1:ℕ):ℤ)⊆B)
    (hf : restrictedSums B (q+1)=Icc ((q+1).choose 2:ℤ)
      (((q+1:ℕ):ℤ)*d-(q+1).choose 2)) :
    (restrictedSums (smallFamily B i) (q+1)).card=(q+1)*d+i-q*q+1 := by
  rw [smallFamily_sums B q d i hq hi hiq hd hB hprefix hf,Int.card_Icc]
  have hc : ((q+1).choose 2:ℤ)=(q:ℤ)+q.choose 2 := by
    exact_mod_cast (show (q+1).choose 2=q+q.choose 2 by
      rw [Nat.choose_succ_succ' q 1,Nat.choose_one_right])
  have hc2 : 2*(q.choose 2:ℤ)=(q:ℤ)*((q:ℤ)-1) := by
    have ht : (2:ℤ)*(q.choose 2:ℤ)=(q:ℤ)*((q-1:ℕ):ℤ) := by exact_mod_cast choose_two_double q
    simpa [Int.ofNat_sub hq] using ht
  have hb : q*q≤(q+1)*d+i := by nlinarith
  have he : (((q+1:ℕ):ℤ)*(i+d)-(q+1).choose 2)+1-
      ((q:ℤ)*i+q.choose 2)=(((q+1)*d+i-q*q+1:ℕ):ℤ) := by
    simp only [Nat.cast_add,Int.ofNat_sub hb,Nat.cast_one,Nat.cast_mul]
    nlinarith
  rw [he,Int.toNat_natCast]

end SumsetRanges
