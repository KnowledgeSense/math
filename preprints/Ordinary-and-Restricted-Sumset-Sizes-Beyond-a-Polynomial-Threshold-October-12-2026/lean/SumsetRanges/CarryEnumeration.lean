import SumsetRanges.CarrySharedNormalForms
import SumsetRanges.WeightedEnumeration

open Finset Polynomial
namespace SumsetRanges

abbrev CarryNormal (m r q : ℕ) := Fin (q+1) × (Fin r → Fin (q+1) × Fin m)

def carryNormalDegree {m r q : ℕ} (a : CarryNormal m r q) : ℕ :=
  a.1.val + ∑i,((a.2 i).1.val+(a.2 i).2.val)

def carryNormalVector {m r q : ℕ} (a : CarryNormal m r q) : Fin r → ℕ :=
  fun i => m*(a.2 i).1.val+(a.2 i).2.val

theorem carryWeight_normal {m r q : ℕ} (a : CarryNormal m r q) :
    carryWeight m (carryNormalVector a)=∑i,((a.2 i).1.val+(a.2 i).2.val) := by
  unfold carryWeight carryNormalVector carryLength
  apply Finset.sum_congr rfl
  intro i _
  have he := (a.2 i).2.isLt
  have hm : 0<m := by omega
  rw [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt he]
  congr 1
  rw [Nat.add_comm,Nat.add_mul_div_left _ _ hm,Nat.div_eq_of_lt he,Nat.zero_add]

theorem card_carryG_normal (m r q : ℕ) (hm : 2≤m) :
    ((univ : Finset (CarryNormal m r q)).filter (fun a => carryNormalDegree a=q)).card =
      (ordinarySums (carryG m r) q).card := by
  apply Finset.card_bij (fun a _ => carryNormalVector a)
  · intro a ha
    rw [mem_ordinarySums_carryG m r q hm,carryWeight_normal]
    have hh := (Finset.mem_filter.mp ha).2
    dsimp [carryNormalDegree] at hh
    omega
  · intro a ha b hb he
    have hv : a.2=b.2 := by
      funext i
      apply Prod.ext
      · apply Fin.ext
        have hh := congrFun he i
        have ha' := (a.2 i).2.isLt
        have hb' := (b.2 i).2.isLt
        dsimp [carryNormalVector] at hh
        have hh' := congrArg (fun n => n/m) hh
        simpa only [Nat.add_comm (m*_ ) _,Nat.add_mul_div_left _ _ (show 0<m by omega),
          Nat.div_eq_of_lt ha',Nat.div_eq_of_lt hb',Nat.zero_add] using hh'
      · apply Fin.ext
        have hh := congrFun he i
        have ha' := (a.2 i).2.isLt
        have hb' := (b.2 i).2.isLt
        dsimp [carryNormalVector] at hh
        have hh' := congrArg (fun n => n%m) hh
        simpa only [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt ha',Nat.mod_eq_of_lt hb'] using hh'
    apply Prod.ext _ hv
    apply Fin.ext
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    dsimp [carryNormalDegree] at ha' hb'
    rw [hv] at ha'
    omega
  · intro v hv
    have hw := (mem_ordinarySums_carryG m r q hm v).mp hv
    have hdi (i : Fin r) : v i/m≤q := by
      calc
        v i/m ≤ carryLength m (v i) := Nat.le_add_right _ _
        _ ≤ carryWeight m v := by
          exact Finset.single_le_sum (f := fun j => carryLength m (v j)) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        _ ≤ q := hw
    let a : CarryNormal m r q := (⟨q-carryWeight m v,by omega⟩,
      fun i => (⟨v i/m,by have := hdi i; omega⟩,⟨v i%m,Nat.mod_lt _ (by omega)⟩))
    refine ⟨a,?_,?_⟩
    · apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      change q-carryWeight m v + (∑i,(v i/m+v i%m))=q
      exact Nat.sub_add_cancel hw
    · funext i
      exact Nat.div_add_mod (v i) m

noncomputable def geometricPolynomial (n : ℕ) : Polynomial ℤ :=
  ∑i∈range n,X^i

theorem weightPolynomial_fin (n : ℕ) :
    weightPolynomial (fun i : Fin n => i.val)=geometricPolynomial n := by
  simp only [weightPolynomial,geometricPolynomial]
  exact Fin.sum_univ_eq_sum_range _ _

theorem carryNormal_polynomial (m r q : ℕ) :
    weightPolynomial (@carryNormalDegree m r q)=
      geometricPolynomial (q+1)*(geometricPolynomial (q+1)*geometricPolynomial m)^r := by
  unfold carryNormalDegree
  rw [weightPolynomial_prod (fun i : Fin (q+1) => i.val)
    (fun a : Fin r → Fin (q+1) × Fin m => ∑i,((a i).1.val+(a i).2.val)),
    weightPolynomial_pi (fun _ (a : Fin (q+1) × Fin m) => a.1.val+a.2.val)]
  simp only [weightPolynomial_prod,weightPolynomial_fin,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem coeff_carryG_geometric (m r q : ℕ) (hm : 2≤m) :
    (geometricPolynomial (q+1)*(geometricPolynomial (q+1)*geometricPolynomial m)^r).coeff q =
      ((ordinarySums (carryG m r) q).card : ℤ) := by
  rw [←carryNormal_polynomial,coeff_weightPolynomial,card_carryG_normal m r q hm]

end SumsetRanges
