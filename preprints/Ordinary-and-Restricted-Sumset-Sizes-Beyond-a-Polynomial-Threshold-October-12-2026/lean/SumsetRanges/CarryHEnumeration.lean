import SumsetRanges.CarryEnumeration

open Finset Polynomial
namespace SumsetRanges

abbrev CarryRows (m r q : ℕ) := Fin r → Fin (q+1) × Fin m

def carryRowQuotient {m r q : ℕ} (a : CarryRows m r q) : ℕ := ∑i,(a i).1.val

def carryRowWeight {m r q : ℕ} (a : CarryRows m r q) : ℕ := ∑i,((a i).1.val+(a i).2.val)

def carryRowVector {m r q : ℕ} (a : CarryRows m r q) : Fin r → ℕ :=
  fun i => m*(a i).1.val+(a i).2.val

abbrev CarryHNormal (m r q : ℕ) := Σa : CarryRows m r q,Fin (carryRowQuotient a+1)

def carryHDegree {m r q : ℕ} (a : CarryHNormal m r q) : ℕ :=
  carryRowWeight a.1+(m-1)*a.2.val

theorem carryRowVector_injective (m r q : ℕ) (hm : 0<m) :
    Function.Injective (@carryRowVector m r q) := by
  intro a b he
  funext i
  apply Prod.ext <;> apply Fin.ext
  · have hh := congrArg (fun n => n/m) (congrFun he i)
    dsimp [carryRowVector] at hh
    simpa only [Nat.add_comm (m*_) _,Nat.add_mul_div_left _ _ hm,
      Nat.div_eq_of_lt (a i).2.isLt,Nat.div_eq_of_lt (b i).2.isLt,Nat.zero_add] using hh
  · have hh := congrArg (fun n => n%m) (congrFun he i)
    dsimp [carryRowVector] at hh
    simpa only [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt (a i).2.isLt,
      Nat.mod_eq_of_lt (b i).2.isLt] using hh

theorem carryRowWeight_vector {m r q : ℕ} (a : CarryRows m r q) :
    carryWeight m (carryRowVector a)=carryRowWeight a :=
  carryWeight_normal (0,a)

theorem carryRowQuotient_vector {m r q : ℕ} (hm : 0<m) (a : CarryRows m r q) :
    carryQuotient m (carryRowVector a)=carryRowQuotient a := by
  apply Finset.sum_congr rfl
  intro i _
  change (m*(a i).1.val+(a i).2.val)/m=(a i).1.val
  rw [Nat.add_comm,Nat.add_mul_div_left _ _ hm,Nat.div_eq_of_lt (a i).2.isLt,Nat.zero_add]

theorem card_carryH_normal_bound (m r n q : ℕ) (hm : 2≤m) (hqn : q≤n) :
    ((univ : Finset (CarryHNormal m r n)).filter (fun a => carryHDegree a=q)).card =
      (ordinarySums (carryH m r) q).card := by
  apply Finset.card_bij (fun a _ => carryRowVector a.1)
  · intro a ha
    rw [mem_ordinarySums_carryH m r q hm,carryRowWeight_vector,
      carryRowQuotient_vector (by omega)]
    refine ⟨a.2.val,by have := a.2.isLt; omega,?_⟩
    exact (Finset.mem_filter.mp ha).2.symm
  · intro a ha b hb he
    have hr := carryRowVector_injective m r n (by omega) he
    cases a with
    | mk a ta =>
      cases b with
      | mk b tb =>
        dsimp at hr
        subst b
        have hta := (Finset.mem_filter.mp ha).2
        have htb := (Finset.mem_filter.mp hb).2
        dsimp [carryHDegree] at hta htb
        have ht : ta=tb := by
          apply Fin.ext
          have hp : 0<m-1 := by omega
          nlinarith
        subst tb
        rfl
  · intro v hv
    obtain ⟨t,ht,hq⟩ := (mem_ordinarySums_carryH m r q hm v).mp hv
    have hw : carryWeight m v≤q := by omega
    have hd (i : Fin r) : v i/m≤q := by
      calc
        _ ≤ carryLength m (v i) := Nat.le_add_right _ _
        _ ≤ carryWeight m v := Finset.single_le_sum (f := fun j => carryLength m (v j)) (fun j _ => Nat.zero_le _) (mem_univ i)
        _ ≤ q := hw
    let a : CarryRows m r n := fun i => (⟨v i/m,by have := hd i; omega⟩,⟨v i%m,Nat.mod_lt _ (by omega)⟩)
    have ha : carryRowQuotient a=carryQuotient m v := rfl
    refine ⟨⟨a,⟨t,by rw [ha]; omega⟩⟩,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨mem_univ _,hq.symm⟩
    · funext i
      exact Nat.div_add_mod (v i) m

theorem card_carryH_normal (m r q : ℕ) (hm : 2≤m) :
    ((univ : Finset (CarryHNormal m r q)).filter (fun a => carryHDegree a=q)).card =
      (ordinarySums (carryH m r) q).card :=
  card_carryH_normal_bound m r q q hm (le_refl _)

end SumsetRanges
