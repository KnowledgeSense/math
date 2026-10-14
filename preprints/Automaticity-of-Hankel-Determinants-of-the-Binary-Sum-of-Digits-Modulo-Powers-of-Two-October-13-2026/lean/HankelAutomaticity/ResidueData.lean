import HankelAutomaticity.BinaryWords
import HankelAutomaticity.PowerPeriod

noncomputable section
namespace HankelAutomaticity

 theorem cast_binaryValue_complement {R : Type*} [CommRing R] (w : List Bool) :
    (binaryValue (complement w) : R)=(2 : R)^w.length-1-(binaryValue w : R) := by
  have h := congrArg (Nat.cast : ℕ → R) (binaryValue_complement w)
  push_cast at h
  linear_combination h

 theorem cast_binaryValue_twist {R : Type*} [CommRing R] (o : Bool) (w : List Bool) :
    (binaryValue (twist o w) : R)=
      if o then (2 : R)^w.length-1-(binaryValue w : R) else (binaryValue w : R) := by
  cases o <;> simp [cast_binaryValue_complement]

 theorem parity_two_power {w : List Bool} (hw : w≠[]) : (2 : ZMod 2)^w.length=0 := by
  have hl : 0<w.length := List.length_pos_iff.mpr hw
  simp [show (2 : ZMod 2)=0 by decide, hl.ne']

 theorem parity_twist (o : Bool) (w : List Bool) (hw : w≠[]) :
    (binaryValue (twist o w) : ZMod 2)=
      if o then 1-(binaryValue w : ZMod 2) else (binaryValue w : ZMod 2) := by
  rw [cast_binaryValue_twist]
  cases o
  · rfl
  · simp only [↓reduceIte, parity_two_power hw, zero_sub]
    have h : (-1 : ZMod 2)=1 := by decide
    rw [h]

 theorem sign_reduce {R : Type*} [CommRing R] (n : ℕ) :
    (-1 : R)^n=(-1 : R)^((n : ZMod 2).val) := by
  rw [ZMod.val_natCast]
  exact pow_eq_pow_mod n (by ring : (-1 : R)^2=1)

end HankelAutomaticity
