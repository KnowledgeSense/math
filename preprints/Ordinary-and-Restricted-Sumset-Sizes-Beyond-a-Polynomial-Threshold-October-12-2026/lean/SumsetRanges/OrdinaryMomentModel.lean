import SumsetRanges.NonnegativeMoments
import SumsetRanges.OrdinaryLargeConstruction

open Finset
namespace SumsetRanges

def natMomentMap (n L : ℕ) : (Fin n → ℕ) →+ (Fin (L+1) → ℤ) where
  toFun v := momentMap n L (fun i => (v i : ℤ))
  map_zero' := (momentMap n L).map_zero
  map_add' v w := by
    change momentMap n L (fun i => ((v+w) i : ℤ)) = _
    simp only [Pi.add_apply,Nat.cast_add]
    exact (momentMap n L).map_add _ _

def ordinaryMomentHom (n L : ℕ) (τ : Type*) :
    OrdinaryLargeSpace (Fin n) τ →+ ((Fin (L+1) → ℤ) × ℤ × (τ⊕Fin 1 → ℤ)) where
  toFun a := (natMomentMap n L a.1,(a.2.1 : ℤ),a.2.2)
  map_zero' := by simp
  map_add' a b := by simp

theorem ordinary_atom_mass_bound {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (A : Finset (OrdinaryLargeSpace (Fin n) τ)) (h q : ℕ)
    (hA : ∀a∈A,(∑i,a.1 i)≤h) {v : OrdinaryLargeSpace (Fin n) τ}
    (hv : v∈ordinarySums A q) : (∑i,v.1 i)≤q*h := by
  obtain ⟨a,ha,rfl⟩ := (mem_ordinarySums A q v).mp hv
  simp only [Prod.fst_sum,Finset.sum_apply]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑_j : Fin q,h := Finset.sum_le_sum (fun j _ => hA _ (ha j))
    _ = q*h := by simp

theorem ordinaryMomentHom_injOn {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (A : Finset (OrdinaryLargeSpace (Fin n) τ)) (h q : ℕ)
    (hA : ∀a∈A,(∑i,a.1 i)≤h) (hq : q≤h) :
    Set.InjOn (ordinaryMomentHom n (h*h) τ) (ordinarySums A q) := by
  intro v hv w hw he
  have hvb := (ordinary_atom_mass_bound A h q hA hv).trans (Nat.mul_le_mul_right h hq)
  have hwb := (ordinary_atom_mass_bound A h q hA hw).trans (Nat.mul_le_mul_right h hq)
  have hatoms : v.1=w.1 := momentMap_nonnegative_injective n (h*h) v.1 w.1 hvb hwb
    (congrArg Prod.fst he)
  apply Prod.ext hatoms
  apply Prod.ext
  · exact Int.ofNat_inj.mp (congrArg (fun a => a.2.1) he)
  · exact congrArg (fun a => a.2.2) he

theorem natMomentMap_bounds (n L H K : ℕ) (hn : n≤K) (hK : 1≤K)
    (v : Fin n → ℕ) (hv : (∑i,v i)≤H) (j : Fin (L+1)) :
    0≤natMomentMap n L v j ∧ natMomentMap n L v j≤(H*K^L:ℕ) := by
  change 0≤∑i,(v i:ℤ)*(i.val:ℤ)^j.val ∧ (∑i,(v i:ℤ)*(i.val:ℤ)^j.val)≤_
  constructor
  · positivity
  · have hp (i : Fin n) : i.val^j.val≤K^L := by
      exact (Nat.pow_le_pow_left (le_trans (Nat.le_of_lt i.isLt) hn) j.val).trans
        (Nat.pow_le_pow_right hK (by omega))
    calc
      _ ≤ ∑i : Fin n,(v i:ℤ)*(K^L:ℕ) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hp i
      _ = ((∑i,v i)*K^L:ℕ) := by simp [Finset.sum_mul]
      _ ≤ (H*K^L:ℕ) := by exact_mod_cast Nat.mul_le_mul_right (K^L) hv

end SumsetRanges
