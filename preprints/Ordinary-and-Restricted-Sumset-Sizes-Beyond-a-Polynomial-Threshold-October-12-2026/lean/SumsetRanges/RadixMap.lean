import SumsetRanges.LatticeNorm

open Finset
namespace SumsetRanges

def radixMap (D Q : ℕ) : (Fin D → ℤ) →+ ℤ where
  toFun v := ∑ i, v i*(Q:ℤ)^i.val
  map_zero' := by simp
  map_add' v w := by simp [add_mul,Finset.sum_add_distrib]

theorem radixMap_succ (D Q : ℕ) (v : Fin (D+1) → ℤ) :
    radixMap (D+1) Q v = v 0+(Q:ℤ)*radixMap D Q (fun i => v i.succ) := by
  change (∑ i : Fin (D+1),v i*(Q:ℤ)^i.val)=_
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ]
  change _ = _+(Q:ℤ)*(∑ i : Fin D,v i.succ*(Q:ℤ)^i.val)
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Uniqueness of bounded radix digits, including the base-one degenerate box. -/
theorem radixMap_injOn_box (D Q : ℕ) (hQ : 0<Q) (v w : Fin D → ℤ)
    (hv : ∀ i,0≤v i ∧ v i<(Q:ℤ)) (hw : ∀ i,0≤w i ∧ w i<(Q:ℤ))
    (he : radixMap D Q v=radixMap D Q w) : v=w := by
  induction D with
  | zero => exact Subsingleton.elim _ _
  | succ D ih =>
    rw [radixMap_succ,radixMap_succ] at he
    have h0 : v 0=w 0 := by
      have hh := congrArg (fun x : ℤ => x%(Q:ℤ)) he
      simpa [Int.add_emod,Int.mul_emod,Int.emod_eq_of_lt (hv 0).1 (hv 0).2,
        Int.emod_eq_of_lt (hw 0).1 (hw 0).2] using hh
    have hmul : (Q:ℤ)*radixMap D Q (fun i => v i.succ) =
        (Q:ℤ)*radixMap D Q (fun i => w i.succ) := by omega
    have hQz : (Q:ℤ)≠0 := by exact_mod_cast (Nat.ne_of_gt hQ)
    have htail := ih (fun i => v i.succ) (fun i => w i.succ)
      (fun i => hv i.succ) (fun i => hw i.succ) (mul_left_cancel₀ hQz hmul)
    funext i
    exact Fin.cases h0 (fun j => congrFun htail j) i

theorem radixMap_bounds (D Q M : ℕ) (hD : 1≤D) (hQ : 1≤Q) (v : Fin D → ℤ)
    (hv : ∀ i,0≤v i ∧ v i≤(M:ℤ)) :
    0≤radixMap D Q v ∧ radixMap D Q v≤(D*M*Q^(D-1):ℕ) := by
  change 0 ≤ (∑ i : Fin D, v i*(Q:ℤ)^i.val) ∧
    (∑ i : Fin D, v i*(Q:ℤ)^i.val) ≤ (D*M*Q^(D-1):ℕ)
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hv i).1 (by positivity))
  · calc
      _ ≤ ∑ _i : Fin D, (M:ℤ)*(Q:ℤ)^(D-1) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul (hv i).2
        · exact_mod_cast Nat.pow_le_pow_right hQ (show i.val≤D-1 by omega)
        · positivity
        · positivity
      _ = (D*M*Q^(D-1):ℕ) := by simp; ring

end SumsetRanges
