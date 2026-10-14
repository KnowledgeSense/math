import SumsetRanges.SmallFamily

namespace SumsetRanges

theorem small_range_parameters (h k M t : ℕ) (hh : 2≤h) (hk : h+2≤k)
    (hM : k-2≤M) (ht : h*(k-h)+1≤t)
    (htM : t≤h*M+h-(h-1)^2+1) :
    ∃d i : ℕ,k-2≤d ∧ d≤M ∧ 1 ≤ i ∧ i≤h ∧ h*d+i-(h-1)^2+1=t := by
  let q := h-1
  have hq : q+1=h := by dsimp [q]; omega
  have hkh : k-h+h=k := Nat.sub_add_cancel (by omega)
  have hk2 : k-2+2=k := Nat.sub_add_cancel (by omega)
  have hlow : h*(k-h)+1+q^2=h*(k-2)+2 := by nlinarith
  have htop : q^2≤h*M+h := by nlinarith
  have htop' : h*M+h-q^2+q^2=h*M+h := Nat.sub_add_cancel htop
  change t≤h*M+h-q^2+1 at htM
  have ht2 : 2≤t+q^2 := by nlinarith
  have ht1 : 1≤t := by omega
  let m := t+q^2-2
  have hm : m+2=t+q^2 := Nat.sub_add_cancel ht2
  have hml : h*(k-2)≤m := by omega
  have hmu : m<h*(M+1) := by nlinarith
  let d := m/h
  let i := m%h+1
  have hd : k-2≤d := (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
  have hdM : d≤M := by
    have hh' : m/h<M+1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith)
    exact Nat.le_of_lt_succ hh'
  have hi : i≤h := by
    have hm' := Nat.mod_lt m (by omega : 0<h)
    dsimp [i]
    omega
  refine ⟨d,i,hd,hdM,by dsimp [i]; omega,hi,?_⟩
  have he := Nat.div_add_mod m h
  change h*d+(i-1)=m at he
  change h*d+i-q^2+1=t
  have hi0 : 1 ≤ i := by dsimp [i]; omega
  omega

end SumsetRanges
