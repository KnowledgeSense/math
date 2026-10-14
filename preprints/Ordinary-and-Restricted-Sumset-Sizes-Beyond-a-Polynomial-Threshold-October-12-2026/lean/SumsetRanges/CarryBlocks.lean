import SumsetRanges.CarryLength
import Mathlib.Data.Fintype.Prod

open Finset
namespace SumsetRanges

def carryPoint (m r : ℕ) (p : Fin r×Bool) : Fin r→ℕ :=
  Pi.single p.1 (if p.2 then m else 1)

def carryH (m r : ℕ) : Finset (Fin r→ℕ) := univ.image (carryPoint m r)
def carryG (m r : ℕ) : Finset (Fin r→ℕ) := insert 0 (carryH m r)

theorem carryPoint_injective (m r : ℕ) (hm : 2≤m) : Function.Injective (carryPoint m r) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ he
  have hij : i=j := by
    by_contra hn
    have hh := congrFun he i
    cases b <;> cases c <;> simp [carryPoint,hn] at hh <;> omega
  subst j
  have hbc : b=c := by
    have hh := congrFun he i
    cases b <;> cases c <;> simp_all [carryPoint]
    omega
  subst c
  rfl

theorem carryPoint_ne_zero (m r : ℕ) (hm : 1≤m) (p : Fin r×Bool) : carryPoint m r p≠0 := by
  intro he
  have hh := congrFun he p.1
  rcases p with ⟨i,b⟩
  cases b <;> simp [carryPoint] at hh
  omega

theorem card_carryH (m r : ℕ) (hm : 2≤m) : (carryH m r).card=2*r := by
  rw [carryH,Finset.card_image_of_injective _ (carryPoint_injective m r hm)]
  simp [mul_comm]

theorem zero_not_mem_carryH (m r : ℕ) (hm : 1≤m) : 0∉carryH m r := by
  intro hz
  obtain ⟨p,_,he⟩ := Finset.mem_image.mp hz
  exact carryPoint_ne_zero m r hm p he

theorem card_carryG (m r : ℕ) (hm : 2≤m) : (carryG m r).card=2*r+1 := by
  rw [carryG,Finset.card_insert_of_notMem (zero_not_mem_carryH m r (by omega)),card_carryH m r hm]

theorem carryPoint_mem_H (m r : ℕ) (p : Fin r×Bool) : carryPoint m r p∈carryH m r :=
  Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩

theorem carryPoint_mem_G (m r : ℕ) (p : Fin r×Bool) : carryPoint m r p∈carryG m r :=
  Finset.mem_insert_of_mem (carryPoint_mem_H m r p)

theorem carryWeight_point (m r : ℕ) (hm : 2≤m) (p : Fin r×Bool) :
    carryWeight m (carryPoint m r p)=1 := by
  rcases p with ⟨i,b⟩
  unfold carryWeight
  rw [Finset.sum_eq_single i]
  · cases b
    · simp [carryPoint,carryLength,Nat.div_eq_of_lt (show 1<m by omega),
        Nat.mod_eq_of_lt (show 1<m by omega)]
    · simp [carryPoint,carryLength,Nat.div_self (show 0<m by omega)]
  · intro j _ hji
    simp [carryPoint,hji]
  · simp

theorem carryWeight_G_le (m r : ℕ) (hm : 2≤m) :
    ∀v∈carryG m r,carryWeight m v≤1 := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · simp
  · obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hv
    rw [carryWeight_point m r hm p]

theorem sum_minimal_carry_representation (m r : ℕ) (v : Fin r→ℕ) :
    (∑i : Fin r,(v i/m) • carryPoint m r (i,true))+
      (∑i : Fin r,(v i%m) • carryPoint m r (i,false))=v := by
  funext j
  change (∑i : Fin r,(v i/m) • carryPoint m r (i,true)) j+
    (∑i : Fin r,(v i%m) • carryPoint m r (i,false)) j=v j
  have hd : (∑i : Fin r,(v i/m) • carryPoint m r (i,true)) j=(v j/m)*m := by
    simp [Finset.sum_apply,carryPoint,Pi.single_apply,nsmul_eq_mul,mul_ite]
  have hr : (∑i : Fin r,(v i%m) • carryPoint m r (i,false)) j=v j%m := by
    simp [Finset.sum_apply,carryPoint,Pi.single_apply,nsmul_eq_mul,mul_ite]
  rw [hd,hr]
  simpa [mul_comm] using Nat.div_add_mod (v j) m

/-- Complete ordinary-sum membership criterion for the actual carry block G. -/
theorem mem_ordinarySums_carryG (m r q : ℕ) (hm : 2≤m) (v : Fin r→ℕ) :
    v∈ordinarySums (carryG m r) q ↔ carryWeight m v≤q := by
  constructor
  · intro hv
    obtain ⟨w,hw,rfl⟩ := (mem_ordinarySums _ _ _).mp hv
    calc
      _ ≤ ∑i : Fin q,carryWeight m (w i) := carryWeight_sum_le univ m r (by omega) w
      _ ≤ ∑_i : Fin q,1 := Finset.sum_le_sum (fun i _ => carryWeight_G_le m r hm (w i) (hw i))
      _ = q := by simp
  · intro hq
    have hd := weighted_sum_mem_ordinarySums univ (carryG m r)
      (fun i : Fin r => carryPoint m r (i,true)) (fun i => v i/m)
      (fun i _ => carryPoint_mem_G m r (i,true))
    have hr := weighted_sum_mem_ordinarySums univ (carryG m r)
      (fun i : Fin r => carryPoint m r (i,false)) (fun i => v i%m)
      (fun i _ => carryPoint_mem_G m r (i,false))
    have hl : (∑i : Fin r,v i/m)+(∑i : Fin r,v i%m)=carryWeight m v := by
      simp [carryWeight,carryLength,Finset.sum_add_distrib]
    have hv : v∈ordinarySums (carryG m r) (carryWeight m v) := by
      rw [←hl,ordinarySums_add]
      exact Finset.mem_add.mpr ⟨_,hd,_,hr,sum_minimal_carry_representation m r v⟩
    exact ordinarySums_order_mono _ (Finset.mem_insert_self _ _) _ _ hq hv

end SumsetRanges
