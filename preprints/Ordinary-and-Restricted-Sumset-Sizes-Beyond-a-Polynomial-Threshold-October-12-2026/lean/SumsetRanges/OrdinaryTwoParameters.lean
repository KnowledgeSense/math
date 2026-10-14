import SumsetRanges.OrdinaryTwoCoefficients

namespace SumsetRanges

theorem twice_choose_two (n : ℕ) : 2*n.choose 2=n*(n-1) := by
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · simp
  have he := ordinaryBeta_recurrence (n+1) 1 (by omega)
  simpa [ordinaryBeta,Nat.mul_comm] using he.symm

theorem choose_two_split (m : ℕ) (hm : 1≤m) :
    (m+1).choose 2=(m-1).choose 2+(2*m-1) := by
  have h0 := twice_choose_two (m+1)
  have h1 := twice_choose_two (m-1)
  rcases Nat.eq_or_lt_of_le hm with hm | hm
  · subst m; norm_num
  · have he : m-1-1=m-2 := by omega
    have hm1 : m-1+1=m := by omega
    have hm2 : m-2+2=m := by omega
    rw [he] at h1
    have hz : m+1-1=m := by omega
    rw [hz] at h0
    have ht : 2*m-1+1=2*m := by omega
    nlinarith

theorem ordinary_two_parameters (k t : ℕ) (hk : 3≤k) (ht : 2*k-1≤t)
    (htop : t<(k+1).choose 2) :
    ∃m s,3≤m ∧ m≤k ∧ s≤m-3 ∧
      (k+1).choose 2-t=(m-1).choose 2-s := by
  let D := (k+1).choose 2-t
  have hD : 1≤D := by dsimp [D]; omega
  have hDk : D≤(k-1).choose 2 := by
    have he := choose_two_split k (by omega)
    dsimp [D]
    omega
  have hex : ∃m,3≤m ∧ D≤(m-1).choose 2 := ⟨k,hk,hDk⟩
  let m := Nat.find hex
  have hm : 3≤m ∧ D≤(m-1).choose 2 := Nat.find_spec hex
  have hmk : m≤k := Nat.find_min' hex ⟨hk,hDk⟩
  have hprev : (m-2).choose 2<D := by
    by_cases he : m=3
    · rw [he]
      norm_num
      omega
    · have hn : ¬(3≤m-1 ∧ D≤(m-1-1).choose 2) := Nat.find_min hex (by dsimp [m]; omega)
      have hsub : m-1-1=m-2 := by omega
      rw [hsub] at hn
      omega
  have hdelta : (m-1).choose 2=(m-2).choose 2+(m-2) := by
    have he := Nat.choose_succ_succ (m-2) 1
    have he' : m-2+1=m-1 := by omega
    simpa [he',Nat.add_comm] using he
  refine ⟨m,(m-1).choose 2-D,hm.1,hmk,?_,?_⟩
  · omega
  · change D=_
    exact (Nat.sub_sub_self hm.2).symm

end SumsetRanges
