import SumsetRanges.RadixEmbedding
import SumsetRanges.OrdinaryImages

open Finset
namespace SumsetRanges

theorem ordinary_sum_coordinate_bounds (D M q : ℕ) (A : Finset (Fin D → ℤ))
    (hA : ∀ a∈A,∀ i,0≤a i ∧ a i≤(M:ℤ)) (x : Fin D → ℤ)
    (hx : x∈ordinarySums A q) (i : Fin D) : 0≤x i ∧ x i≤(q*M:ℕ) := by
  obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums A q x).mp hx
  rw [Finset.sum_apply]
  constructor
  · exact Finset.sum_nonneg (fun j _ => (hA _ (hv j) i).1)
  · calc
      _ ≤ ∑ _j : Fin q,(M:ℤ) := Finset.sum_le_sum (fun j _ => (hA _ (hv j) i).2)
      _ = (q*M:ℕ) := by simp

theorem radixMap_injOn_ordinarySums (D M h Q q : ℕ) (A : Finset (Fin D → ℤ))
    (hA : ∀ a∈A,∀ i,0≤a i ∧ a i≤(M:ℤ)) (hQ : h*M<Q) (hq : q≤h) :
    Set.InjOn (radixMap D Q) (ordinarySums A q) := by
  intro x hx y hy he
  apply radixMap_injOn_box D Q (by omega) x y _ _ he
  · intro i
    have hb := ordinary_sum_coordinate_bounds D M q A hA x hx i
    have hnat : q*M<Q := lt_of_le_of_lt (Nat.mul_le_mul_right M hq) hQ
    exact ⟨hb.1,lt_of_le_of_lt hb.2 (by exact_mod_cast hnat)⟩
  · intro i
    have hb := ordinary_sum_coordinate_bounds D M q A hA y hy i
    have hnat : q*M<Q := lt_of_le_of_lt (Nat.mul_le_mul_right M hq) hQ
    exact ⟨hb.1,lt_of_le_of_lt hb.2 (by exact_mod_cast hnat)⟩

/-- An actual integer image preserving every ordinary sumset through order h. -/
theorem bounded_ordinary_integer_model (D M h Q : ℕ) (A : Finset (Fin D → ℤ))
    (hD : 1≤D) (hh : 1≤h) (hQ : h*M<Q)
    (hA : ∀ a∈A,∀ i,0≤a i ∧ a i≤(M:ℤ)) :
    ∃ B : Finset ℤ, B.card=A.card ∧
      (∀ b∈B,0≤b ∧ b≤(D*M*Q^(D-1):ℕ)) ∧
      ∀ q≤h,(ordinarySums B q).card=(ordinarySums A q).card := by
  refine ⟨A.image (radixMap D Q),?_,?_,?_⟩
  · exact Finset.card_image_of_injOn (radixMap_injOn_points D M h Q A hA hh hQ)
  · intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact radixMap_bounds D Q M hD (by omega) a (hA a ha)
  · intro q hq
    rw [ordinarySums_image]
    exact Finset.card_image_of_injOn (radixMap_injOn_ordinarySums D M h Q q A hA hQ hq)

end SumsetRanges
