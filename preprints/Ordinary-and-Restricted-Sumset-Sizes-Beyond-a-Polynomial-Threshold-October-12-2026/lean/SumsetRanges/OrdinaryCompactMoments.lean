import SumsetRanges.OrdinaryMomentModel

open Finset
namespace SumsetRanges

abbrev OrdinaryCoordinate (L : ℕ) (τ : Type*) := Fin (L+1) ⊕ Option (τ⊕Fin 1)

def ordinaryCompactMoment (n L : ℕ) (τ : Type*) :
    OrdinaryLargeSpace (Fin n) τ →+ (OrdinaryCoordinate L τ → ℤ) where
  toFun a i := match i with
    | Sum.inl j => natMomentMap n L a.1 j
    | Sum.inr none => (a.2.1 : ℤ)
    | Sum.inr (some t) => a.2.2 t
  map_zero' := by funext i; rcases i with j | (_ | t) <;> simp
  map_add' a b := by funext i; rcases i with j | (_ | t) <;> simp

theorem ordinaryCompactMoment_injOn {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (A : Finset (OrdinaryLargeSpace (Fin n) τ)) (h q : ℕ)
    (hA : ∀a∈A,(∑i,a.1 i)≤h) (hq : q≤h) :
    Set.InjOn (ordinaryCompactMoment n (h*h) τ) (ordinarySums A q) := by
  intro v hv w hw he
  apply ordinaryMomentHom_injOn A h q hA hq hv hw
  apply Prod.ext
  · funext j; exact congrFun he (Sum.inl j)
  · apply Prod.ext
    · exact congrFun he (Sum.inr none)
    · funext t; exact congrFun he (Sum.inr (some t))

theorem ordinaryCompactMoment_bounds {n : ℕ} {τ : Type*} [Fintype τ]
    (h k : ℕ) (hh : 1≤h) (hk : 1≤k) (hn : n≤k)
    (a : OrdinaryLargeSpace (Fin n) τ)
    (ha : (∑i,a.1 i)≤h ∧ a.2.1≤h*k ∧ ∀t,a.2.2 t=0 ∨ a.2.2 t=1) :
    ∀i,0≤ordinaryCompactMoment n (h*h) τ a i ∧
      ordinaryCompactMoment n (h*h) τ a i≤(h*k^(h*h):ℕ) := by
  have hL : 1≤h*h := by nlinarith
  have hp : k≤k^(h*h) := by simpa using Nat.pow_le_pow_right hk hL
  have hM : 1≤h*k^(h*h) := by have hp := Nat.one_le_pow (h*h) k hk; nlinarith
  intro i
  rcases i with j | (_ | t)
  · exact natMomentMap_bounds n (h*h) h k hn hk a.1 ha.1 j
  · change 0≤(a.2.1:ℤ) ∧ (a.2.1:ℤ)≤_
    constructor
    · positivity
    · exact_mod_cast ha.2.1.trans (Nat.mul_le_mul_left h hp)
  · change 0≤a.2.2 t ∧ a.2.2 t≤_
    rcases ha.2.2 t with he | he <;> rw [he]
    · constructor <;> positivity
    · exact ⟨by norm_num,by exact_mod_cast hM⟩

end SumsetRanges
