import SumsetRanges.SeparatedConvolution
import SumsetRanges.RadixMap

open Finset
namespace SumsetRanges

theorem restricted_sum_coordinate_bounds (D M q : ℕ) (A : Finset (Fin D → ℤ))
    (hA : ∀ a∈A,∀ i,0≤a i ∧ a i≤(M:ℤ)) (x : Fin D → ℤ)
    (hx : x∈restrictedSums A q) (i : Fin D) : 0≤x i ∧ x i≤(q*M:ℕ) := by
  obtain ⟨S,hS,hSc,rfl⟩ := mem_restrictedSums.mp hx
  rw [Finset.sum_apply]
  constructor
  · exact Finset.sum_nonneg (fun a ha => (hA a (hS ha) i).1)
  · calc
      _ ≤ ∑ _a∈S,(M:ℤ) := Finset.sum_le_sum (fun a ha => (hA a (hS ha) i).2)
      _ = (q*M:ℕ) := by simp [hSc]

theorem radixMap_injOn_restrictedSums (D M h Q q : ℕ) (A : Finset (Fin D → ℤ))
    (hA : ∀ a∈A,∀ i,0≤a i ∧ a i≤(M:ℤ)) (hQ : h*M<Q) (hq : q≤h) :
    Set.InjOn (radixMap D Q) (restrictedSums A q) := by
  intro x hx y hy he
  have hQ0 : 0<Q := by omega
  apply radixMap_injOn_box D Q hQ0 x y _ _ he
  · intro i
    have hb := restricted_sum_coordinate_bounds D M q A hA x hx i
    have hnat : q*M<Q := lt_of_le_of_lt (Nat.mul_le_mul_right M hq) hQ
    exact ⟨hb.1,lt_of_le_of_lt hb.2 (by exact_mod_cast hnat)⟩
  · intro i
    have hb := restricted_sum_coordinate_bounds D M q A hA y hy i
    have hnat : q*M<Q := lt_of_le_of_lt (Nat.mul_le_mul_right M hq) hQ
    exact ⟨hb.1,lt_of_le_of_lt hb.2 (by exact_mod_cast hnat)⟩

theorem radixMap_injOn_points (D M h Q : ℕ) (A : Finset (Fin D → ℤ))
    (hA : ∀ a∈A,∀ i,0≤a i ∧ a i≤(M:ℤ)) (hh : 1≤h) (hQ : h*M<Q) :
    Set.InjOn (radixMap D Q) A := by
  have hi := radixMap_injOn_restrictedSums D M h Q 1 A hA hQ hh
  simpa using hi

/-- A bounded integer model with explicit diameter, preserving every restricted
 sumset through order h. The map and all cardinalities are actual finite objects. -/
theorem bounded_integer_model (D M h Q : ℕ) (A : Finset (Fin D → ℤ))
    (hD : 1≤D) (hh : 1≤h) (hQ : h*M<Q)
    (hA : ∀ a∈A,∀ i,0≤a i ∧ a i≤(M:ℤ)) :
    ∃ B : Finset ℤ, B.card=A.card ∧
      (∀ b∈B,0≤b ∧ b≤(D*M*Q^(D-1):ℕ)) ∧
      ∀ q≤h,(restrictedSums B q).card=(restrictedSums A q).card := by
  refine ⟨A.image (radixMap D Q),?_,?_,?_⟩
  · exact Finset.card_image_of_injOn (radixMap_injOn_points D M h Q A hA hh hQ)
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact radixMap_bounds D Q M hD (by omega) a (hA a ha)
  · intro q hq
    exact card_restrictedSums_image A (radixMap D Q) (radixMap_injOn_points D M h Q A hA hh hQ)
      q (radixMap_injOn_restrictedSums D M h Q q A hA hQ hq)

end SumsetRanges
