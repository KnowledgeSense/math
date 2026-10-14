import SumsetRanges.OrdinaryTwoParameters

open Finset
namespace SumsetRanges

theorem ordinaryValue_two_baseline (c b x : ℕ) :
    ordinaryValue 2 c b (fun _ => 0) (fun _ => 1) x=ordinaryBaselineValue 2 c b x := by
  simp [ordinaryValue,ordinaryBaselineValue,ordinarySparseSeries,ordinaryNonfreeSize]

theorem dense_two_card (m s : ℕ) (hm : 3≤m) (hs : s≤m-3) :
    (ordinarySums (denseSet (m-1) (m-1+s)) 2).card=2*m-1+s := by
  have he : m-1=m-2+1 := by omega
  rw [he,card_dense_ordinary (m-2) _ 2 (by omega)]
  norm_num [Finset.sum_range_succ]
  omega

theorem ordinary_two_realized (k t : ℕ) (hk : 10≤k) (ht : 2*k-1≤t)
    (htop : t≤(k+1).choose 2) :
    ∃A : Finset ℤ,A.card=k ∧ (∀a∈A,0≤a ∧ a≤(k^(ordinaryExponent 2):ℕ)) ∧
      (ordinarySums A 2).card=t := by
  by_cases heq : t=(k+1).choose 2
  · obtain ⟨A,hAc,hA,hAs⟩ := ordinary_large_value_realized 2 (k-2) 2 1
      (fun _ => 0) (fun _ => 1) (by omega) (by omega) (by omega)
      (by simp [ordinaryNonfreeSize]) (by omega) (by omega)
    have he : k-2+2=k := by omega
    rw [he] at hAc hA
    rw [ordinaryValue_two_baseline] at hAs
    have hv := ordinary_baseline_top 2 k (by omega)
    norm_num [denseMaximum] at hv
    rw [hv] at hAs
    refine ⟨A,hAc,hA,?_⟩
    rw [heq]
    have hAs' : ((ordinarySums A 2).card:ℤ)=((k+1).choose 2:ℤ) := by simpa [Nat.add_comm] using hAs
    exact_mod_cast hAs'
  · obtain ⟨m,s,hm,hmk,hs,hdef⟩ := ordinary_two_parameters k t (by omega) ht (by omega)
    obtain ⟨A,hAc,hA,hAs⟩ := ordinary_large_value_realized 2 (k-m) m (m-1+s)
      (fun _ => 0) (fun _ => 1) (by omega) (by omega) (by omega)
      (by simp [ordinaryNonfreeSize]) (by omega) (by omega)
    have he : k-m+m=k := by omega
    rw [he] at hAc hA
    rw [ordinaryValue_two_baseline] at hAs
    have hv := ordinary_baseline_two (k-m) m (m-1+s) (by omega) (by omega)
    rw [dense_two_card m s hm hs,←hAs] at hv
    have hsplit := choose_two_split m (by omega)
    have hk2 := twice_choose_two (k+1)
    have hm2 := twice_choose_two (m+1)
    have hsub : (k+1).choose 2-t+t=(k+1).choose 2 := Nat.sub_add_cancel htop
    have hsle : s≤(m-1).choose 2 := by
      have hd := Nat.choose_succ_succ (m-2) 1
      have he' : m-2+1=m-1 := by omega
      simp only [Nat.choose_one_right] at hd
      omega
    have hdef' : (k+1).choose 2+s=t+(m-1).choose 2 := by omega
    simp only [Nat.add_sub_cancel,Nat.mul_comm] at hk2 hm2
    have hk2' : (k:ℤ)*((k:ℤ)+1)=2*((k+1).choose 2:ℤ) := by exact_mod_cast hk2.symm
    have hm2' : (m:ℤ)*((m:ℤ)+1)=2*((m+1).choose 2:ℤ) := by exact_mod_cast hm2.symm
    have hdefZ : ((k+1).choose 2:ℤ)+s=t+((m-1).choose 2:ℤ) := by exact_mod_cast hdef'
    have hsplitZ : ((m+1).choose 2:ℤ)=((m-1).choose 2:ℤ)+((2*m-1:ℕ):ℤ) := by exact_mod_cast hsplit
    have hkm : ((k-m:ℕ):ℤ)=k-m := by omega
    have hms : ((2*m-1+s:ℕ):ℤ)=2*(m:ℤ)-1+s := by omega
    have hms' : ((2*m-1:ℕ):ℤ)=2*(m:ℤ)-1 := by omega
    rw [hkm,hms] at hv
    rw [hms'] at hsplitZ
    refine ⟨A,hAc,hA,?_⟩
    have hres : ((ordinarySums A 2).card:ℤ)=(t:ℤ) := by nlinarith
    exact_mod_cast hres

end SumsetRanges
