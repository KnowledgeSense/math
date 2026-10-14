import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

noncomputable section
namespace HankelAutomaticity

 theorem odd_base_unit (K : ℕ) (q : ZMod (2^K)) : IsUnit (1-2*q) := by
  apply IsNilpotent.isUnit_one_sub
  refine ⟨K, ?_⟩
  rw [mul_pow]
  have h : (2 : ZMod (2^K))^K=0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (ZMod.natCast_self (2^K))
  rw [h, zero_mul]

 theorem odd_base_period (K : ℕ) (hK : 1 ≤ K) (q : ZMod (2^K)) :
    (1-2*q)^(2^K)=1 := by
  let : NeZero (2^K) := ⟨by positivity⟩
  obtain ⟨u, hu⟩ := odd_base_unit K q
  have h : u^Fintype.card ((ZMod (2^K))ˣ)=1 := pow_card_eq_one
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)] at h
  norm_num at h
  have hp : u^(2^K)=1 := by
    calc
      u^(2^K)=u^(2^(K-1)*2) := congrArg (fun n : ℕ => u^n) (by
        rw [show K=K-1+1 by omega, pow_succ]
        simp)
      _=1 := by rw [pow_mul, h, one_pow]
  have hv := congrArg Units.val hp
  simpa [hu] using hv

 theorem odd_base_reduce_power (K : ℕ) (hK : 1 ≤ K) (q : ZMod (2^K)) (n : ℕ) :
    (1-2*q)^n=(1-2*q)^((n : ZMod (2^K)).val) := by
  let : NeZero (2^K) := ⟨by positivity⟩
  rw [ZMod.val_natCast]
  exact pow_eq_pow_mod n (odd_base_period K hK q)

end HankelAutomaticity
