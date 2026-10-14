import SumsetRanges.OrdinarySetOperations
import SumsetRanges.SmallFamily

open Finset
namespace SumsetRanges

@[simp] theorem ordinarySums_one {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) : ordinarySums A 1=A := by
  ext x
  rw [mem_ordinarySums]
  constructor
  · rintro ⟨v,hv,he⟩
    have he' : v 0=x := by simpa using he
    simpa [he'] using hv 0
  · intro hx
    exact ⟨fun _ => x,fun _ => hx,by simp⟩

theorem ordinary_smallFamily_sums (B : Finset ℤ) (h d i : ℕ) (hh : 1≤h)
    (hi : 1 ≤ i) (hih : i≤h) (hB : B⊆Icc 0 (d:ℤ))
    (hprefix : Icc 0 ((h^2:ℕ):ℤ)⊆B)
    (hf : ordinarySums B h=Icc 0 ((h*d:ℕ):ℤ)) :
    ordinarySums (smallFamily B i) h=insert 0 (Icc (i:ℤ) ((h*(i+d):ℕ):ℤ)) := by
  have h0 : (0:ℤ)∈smallFamily B i := Finset.mem_insert_self _ _
  have hnonneg : ∀a∈smallFamily B i,0≤a :=
    fun a ha => (Finset.mem_Icc.mp (smallFamily_bounds B d i hB ha)).1
  ext x
  constructor
  · intro hx
    by_cases hx0 : x=0
    · exact Finset.mem_insert.mpr (Or.inl hx0)
    apply Finset.mem_insert.mpr
    apply Or.inr
    have hb := ordinarySums_int_bounds (smallFamily B i) 0 ((i+d:ℕ):ℤ)
      (fun a ha => Finset.mem_Icc.mp (smallFamily_bounds B d i hB ha)) h hx
    obtain ⟨v,hv,he⟩ := (mem_ordinarySums _ _ _).mp hx
    have hex : ∃j,v j≠0 := by
      by_contra hn
      push Not at hn
      have hz : (∑j,v j)=0 := by simp [hn]
      exact hx0 (he.symm.trans hz)
    obtain ⟨j,hj⟩ := hex
    have hjm : v j∈(B.image (fun b => (i:ℤ)+b)) :=
      (Finset.mem_insert.mp (hv j)).resolve_left hj
    obtain ⟨b,hbm,hbe⟩ := Finset.mem_image.mp hjm
    have hb0 := (Finset.mem_Icc.mp (hB hbm)).1
    have hle : v j≤∑a,v a := Finset.single_le_sum (fun a _ => hnonneg _ (hv a)) (Finset.mem_univ j)
    apply Finset.mem_Icc.mpr
    refine ⟨by omega,?_⟩
    simpa using hb.2
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact zero_mem_ordinarySums _ h0 h
    obtain ⟨hxi,hxhi⟩ := Finset.mem_Icc.mp hx
    by_cases hxm : x≤((h*i:ℕ):ℤ)
    · have hp : x-(i:ℤ)∈B := by
        apply hprefix
        apply Finset.mem_Icc.mpr
        refine ⟨by omega,?_⟩
        have hib : h*i≤h*h := Nat.mul_le_mul_left _ hih
        have hibz : ((h*i:ℕ):ℤ)≤((h^2:ℕ):ℤ) := by exact_mod_cast (by simpa [pow_two] using hib)
        omega
      have hxin : x∈smallFamily B i := by
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨x-i,hp,by ring⟩
      apply ordinarySums_order_mono _ h0 1 h hh
      simpa using hxin
    · apply ordinarySums_mono (B:=smallFamily B i) (Finset.subset_insert 0 _) h
      rw [ordinarySums_translate]
      apply Finset.mem_image.mpr
      refine ⟨x-h • (i:ℤ),?_,by ring⟩
      rw [hf]
      apply Finset.mem_Icc.mpr
      simp only [nsmul_eq_mul]
      push_cast at hxm hxhi ⊢
      constructor <;> nlinarith

theorem card_ordinary_smallFamily_sums (B : Finset ℤ) (h d i : ℕ) (hh : 1≤h)
    (hi : 1 ≤ i) (hih : i≤h) (hB : B⊆Icc 0 (d:ℤ))
    (hprefix : Icc 0 ((h^2:ℕ):ℤ)⊆B)
    (hf : ordinarySums B h=Icc 0 ((h*d:ℕ):ℤ)) :
    (ordinarySums (smallFamily B i) h).card=h*(i+d)-i+2 := by
  rw [ordinary_smallFamily_sums B h d i hh hi hih hB hprefix hf,
    Finset.card_insert_of_notMem (by simp; omega),Int.card_Icc]
  have hb : i≤h*(i+d) := by nlinarith
  have he : ((h*(i+d):ℕ):ℤ)+1-i=((h*(i+d)-i+1:ℕ):ℤ) := by
    simp only [Nat.cast_add,Nat.cast_one,Int.ofNat_sub hb]
    omega
  rw [he,Int.toNat_natCast]

end SumsetRanges
