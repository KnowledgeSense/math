import SumsetRanges.OrdinarySmallFamily

open Finset
namespace SumsetRanges
set_option maxHeartbeats 1000000

/-- The triangular deleted intervals are exactly the holes left by the small-family parameters. -/
theorem ordinary_small_parameters (h k M t : ℕ) (hh : 2≤h) (hk : h≤k)
    (hM : k-2≤M) (ht : ordinaryMinimum h k≤t) (htM : t≤h*M+1)
    (hex : t∉excludedValues h k) :
    ∃d i : ℕ,k-2≤d ∧ d≤M ∧ 1 ≤ i ∧ i≤h ∧ h*(i+d)-i+2=t := by
  have hk1 : 1≤k := by omega
  have hkh : h≤h*k := Nat.le_mul_of_pos_right h (by omega)
  have hsub : h*k-h+h=h*k := Nat.sub_add_cancel hkh
  have hk2 : k-2+2=k := Nat.sub_add_cancel (by omega)
  have hmin : ordinaryMinimum h k=h*k-h+1 := rfl
  by_cases heq : t=ordinaryMinimum h k
  · refine ⟨k-2,1,le_rfl,hM,by omega,by omega,?_⟩
    rw [heq,hmin]
    have hp : 1≤h*(1+(k-2)) := by nlinarith
    have hp' := Nat.sub_add_cancel hp
    nlinarith only [hp',hsub,hk2]
  let z := t-ordinaryMinimum h k-1
  let l := z/h
  let a := z%h+1
  have ha : 1≤a ∧ a≤h := by
    have hm := Nat.mod_lt z (by omega : 0<h)
    dsimp [a]
    omega
  have hz : z+ordinaryMinimum h k+1=t := by dsimp [z]; omega
  have hza : h*l+a=z+1 := by
    have he := Nat.div_add_mod z h
    dsimp [l,a]
    omega
  have htform : ordinaryMinimum h k+h*l+a=t := by omega
  have hlM : k+l≤M := by
    rw [hmin] at htform
    nlinarith
  have hallow : h-1≤l+a := by
    by_contra hbad
    have hl : l<h-2 := by omega
    have ha' : a≤h-2-l := by omega
    apply hex
    unfold excludedValues
    apply Finset.mem_biUnion.mpr
    refine ⟨l,?_,?_⟩
    · simp only [Finset.mem_range,min_eq_left hk]
      exact hl
    · apply Finset.mem_Icc.mpr
      constructor <;> nlinarith
  let i := h+1-a
  have hi : 1 ≤ i ∧ i≤h := by dsimp [i]; omega
  have hia : i+a=h+1 := by dsimp [i]; omega
  have hil : i≤l+2 := by omega
  let d := k+l-i
  have hdi : d+i=k+l := by dsimp [d]; omega
  have hd : k-2≤d := by omega
  have hdM : d≤M := by omega
  refine ⟨d,i,hd,hdM,hi.1,hi.2,?_⟩
  have hsubi : i≤h*(i+d) := by nlinarith
  have hs : h*(i+d)-i+i=h*(i+d) := Nat.sub_add_cancel hsubi
  rw [hmin] at htform
  nlinarith

end SumsetRanges
