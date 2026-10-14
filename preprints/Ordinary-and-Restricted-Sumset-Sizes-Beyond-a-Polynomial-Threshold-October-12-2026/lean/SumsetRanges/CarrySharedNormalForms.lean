import SumsetRanges.CarryBlocks
import SumsetRanges.BoundedAllocation

open Finset
namespace SumsetRanges

def carryQuotient {r : ℕ} (m : ℕ) (v : Fin r→ℕ) : ℕ := ∑i,v i/m

def coordinateMass (r : ℕ) : (Fin r→ℕ) →+ ℕ where
  toFun v := ∑i,v i
  map_zero' := by simp
  map_add' v w := by simp [Finset.sum_add_distrib]

theorem coordinateMass_carry (m r : ℕ) (hm : 1≤m) (v : Fin r→ℕ) :
    coordinateMass r v=carryWeight m v+(m-1)*carryQuotient m v := by
  change (∑i,v i)=(∑i,carryLength m (v i))+(m-1)*(∑i,v i/m)
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he := Nat.div_add_mod (v i) m
  have hm' : m-1+1=m := by omega
  unfold carryLength
  calc
    v i = m*(v i/m)+v i%m := he.symm
    _ = ((m-1)+1)*(v i/m)+v i%m := by rw [hm']
    _ = _ := by ring

theorem coordinateMass_point (m r : ℕ) (hm : 1≤m) (p : Fin r×Bool) :
    coordinateMass r (carryPoint m r p)=1+(m-1)*(if p.2 then 1 else 0) := by
  rcases p with ⟨i,b⟩
  cases b <;> simp [coordinateMass,carryPoint]
  omega

theorem sum_carry_representation (m r : ℕ) (a b : Fin r→ℕ) :
    (∑i : Fin r,b i • carryPoint m r (i,true))+
      (∑i : Fin r,a i • carryPoint m r (i,false))=(fun i => b i*m+a i) := by
  funext j
  simp [Finset.sum_apply,carryPoint,Pi.single_apply,nsmul_eq_mul,mul_ite]

/-- Exhaustive length normal form for H: the parameter records how many large coins are split. -/
theorem mem_ordinarySums_carryH (m r q : ℕ) (hm : 2≤m) (v : Fin r→ℕ) :
    v∈ordinarySums (carryH m r) q ↔
      ∃t≤carryQuotient m v,q=carryWeight m v+(m-1)*t := by
  constructor
  · intro hv
    have hG : v∈ordinarySums (carryG m r) q := ordinarySums_mono (Finset.subset_insert _ _) q hv
    have hweight := (mem_ordinarySums_carryG m r q hm v).mp hG
    obtain ⟨w,hw,he⟩ := (mem_ordinarySums _ _ _).mp hv
    have hex (i : Fin q) : ∃p : Fin r×Bool,carryPoint m r p=w i := by
      obtain ⟨p,_,hp⟩ := Finset.mem_image.mp (hw i)
      exact ⟨p,hp⟩
    let p (i : Fin q) := Classical.choose (hex i)
    have hp (i : Fin q) : carryPoint m r (p i)=w i := Classical.choose_spec (hex i)
    let b := ∑i : Fin q,if (p i).2 then 1 else 0
    have hmass : coordinateMass r v=q+(m-1)*b := by
      rw [←he,map_sum]
      calc
        (∑i,coordinateMass r (w i))=∑i : Fin q,(1+(m-1)*(if (p i).2 then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [←hp i,coordinateMass_point m r (by omega)]
        _ = _ := by
          rw [Finset.sum_add_distrib,←Finset.mul_sum]
          simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
          rfl
    have hmc := coordinateMass_carry m r (by omega) v
    have hb : b≤carryQuotient m v := by
      by_contra hn
      have hp' : (m-1)*(carryQuotient m v+1)≤(m-1)*b := Nat.mul_le_mul_left _ (by omega)
      have hmp : 1 ≤ m-1 := by omega
      nlinarith only [hmass,hmc,hweight,hp',hmp]
    refine ⟨carryQuotient m v-b,Nat.sub_le _ _,?_⟩
    have hs := Nat.sub_add_cancel hb
    nlinarith
  · rintro ⟨t,ht,hq⟩
    obtain ⟨a,ha,hs⟩ := bounded_allocation r (fun i => v i/m) t ht
    let b (i : Fin r) := v i/m-a i
    let c (i : Fin r) := v i%m+m*a i
    have hlen (i : Fin r) : b i+c i=carryLength m (v i)+(m-1)*a i := by
      have hb := Nat.sub_add_cancel (ha i)
      have hm' : m-1+1=m := by omega
      dsimp [b,c,carryLength]
      nlinarith
    have hval (i : Fin r) : b i*m+c i=v i := by
      have hb := Nat.sub_add_cancel (ha i)
      have hd := Nat.div_add_mod (v i) m
      dsimp [b,c]
      nlinarith
    have hlenSum : (∑i,b i)+(∑i,c i)=q := by
      rw [←Finset.sum_add_distrib]
      simp_rw [hlen]
      rw [Finset.sum_add_distrib,←Finset.mul_sum,hs]
      exact hq.symm
    have hbmem := weighted_sum_mem_ordinarySums univ (carryH m r)
      (fun i : Fin r => carryPoint m r (i,true)) b (fun i _ => carryPoint_mem_H m r (i,true))
    have hcmem := weighted_sum_mem_ordinarySums univ (carryH m r)
      (fun i : Fin r => carryPoint m r (i,false)) c (fun i _ => carryPoint_mem_H m r (i,false))
    rw [←hlenSum,ordinarySums_add]
    refine Finset.mem_add.mpr ⟨_,hbmem,_,hcmem,?_⟩
    rw [sum_carry_representation]
    funext i
    exact hval i

end SumsetRanges
