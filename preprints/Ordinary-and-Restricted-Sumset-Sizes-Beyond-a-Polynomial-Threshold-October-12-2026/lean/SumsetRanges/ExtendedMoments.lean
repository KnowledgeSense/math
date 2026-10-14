import SumsetRanges.RadixEmbedding

open Finset
namespace SumsetRanges

abbrev ModelSpace (n s : ℕ) := (Fin n → ℤ) × ℤ × (Fin s → ℤ)
abbrev ModelCoordinate (L s : ℕ) := Fin (L+1) ⊕ Option (Fin s)

def sparsePart (n s : ℕ) : ModelSpace n s →+ (Fin n → ℤ) where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

def extendedMomentMap (n L s : ℕ) : ModelSpace n s →+ (ModelCoordinate L s → ℤ) where
  toFun x a := match a with
    | Sum.inl j => momentMap n L x.1 j
    | Sum.inr none => x.2.1
    | Sum.inr (some j) => x.2.2 j
  map_zero' := by funext a; rcases a with j | (_ | j) <;> simp
  map_add' x y := by funext a; rcases a with j | (_ | j) <;> simp [map_add]

theorem latticeNorm_restricted_sum_map {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (n M q : ℕ) (A : Finset α) (φ : α →+ (Fin n → ℤ))
    (hA : ∀ a∈A,latticeNorm (φ a)≤M) (x : α) (hx : x∈restrictedSums A q) :
    latticeNorm (φ x)≤q*M := by
  obtain ⟨S,hS,hSc,rfl⟩ := mem_restrictedSums.mp hx
  rw [map_sum]
  calc
    _ ≤ ∑ a∈S,latticeNorm (φ a) := latticeNorm_sum S φ
    _ ≤ ∑ _a∈S,M := Finset.sum_le_sum (fun a ha => hA a (hS ha))
    _ = q*M := by simp [hSc]

theorem extendedMomentMap_injOn_restrictedSums (n L s M q : ℕ)
    (A : Finset (ModelSpace n s)) (hA : ∀ a∈A,latticeNorm a.1≤M) (hL : 2*q*M≤L+1) :
    Set.InjOn (extendedMomentMap n L s) (restrictedSums A q) := by
  intro x hx y hy he
  have hnx := latticeNorm_restricted_sum_map n M q A (sparsePart n s) hA x hx
  have hny := latticeNorm_restricted_sum_map n M q A (sparsePart n s) hA y hy
  change latticeNorm x.1≤q*M at hnx
  change latticeNorm y.1≤q*M at hny
  have hns := latticeNorm_sub x.1 y.1
  have hsupport := support_card_le_latticeNorm (x.1-y.1)
  have hs : (coordinateSupport (x.1-y.1)).card≤L+1 := by nlinarith
  have hmoment : momentMap n L x.1=momentMap n L y.1 := by
    funext j
    exact congrFun he (Sum.inl j)
  have hm : momentMap n L (x.1-y.1)=0 := by rw [map_sub,hmoment,sub_self]
  have hxy := sub_eq_zero.mp (momentMap_sparse_zero n L (x.1-y.1) hs hm)
  apply Prod.ext hxy
  apply Prod.ext
  · exact congrFun he (Sum.inr none)
  · funext j
    exact congrFun he (Sum.inr (some j))

theorem moment_coordinate_bound_by (n L M k : ℕ) (hnk : n≤k)
    (v : Fin n → ℤ) (hv : latticeNorm v≤M) (j : Fin (L+1)) :
    ((momentMap n L v) j).natAbs≤M*k^L := by
  cases n with
  | zero => simp [momentMap]
  | succ n =>
    exact (moment_coordinate_bound (n+1) L M (by omega) v hv j).trans
      (Nat.mul_le_mul_left M (Nat.pow_le_pow_left hnk L))

end SumsetRanges
