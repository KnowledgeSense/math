import R34.ReducedCorners

noncomputable section

namespace R34.ReducedCharge

open MvPolynomial ChargeSites
open scoped BigOperators

def localEqualZ (c : ChargedSite) (χ : Fin c.size → Bool) (e : Fin (c.size-1)) : ℝ :=
  if (internalChargeEndpoints c.size χ e).1 = (internalChargeEndpoints c.size χ e).2
    then 1 else 0

def siteExtraWeight (c : ChargedSite) (χ : Fin c.size → Bool) : ℝ :=
  match c with
  | .point => 1
  | .group a => if a=1 then if χ 0=χ (Fin.last a) then 2 else 1 else 1

def weightedSiteTensor (c : ChargedSite) (χ : Fin c.size → Bool) : RealMat :=
  siteExtraWeight c χ • c.tensor χ

def realTensor : (ch : Chain) → ChargeColorings ch.sizes → RealMat
  | .last c, χ => weightedSiteTensor c χ.1
  | .cons c K tail, χ => weightedSiteTensor c χ.1 * K.entry * realTensor tail χ.2

def realValue (ch : Chain) (left right : ℝ × ℝ) (χ : ChargeColorings ch.sizes) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    Kernel.embed left i * realTensor ch χ i j * Kernel.embed right j

def siteLeftState (c : ChargedSite) (χ : Fin c.size → Bool) (o : Bool) : Fin 3 :=
  if o then match c with
    | .point => Transfer.colorState (χ 0)
    | .group _ => Transfer.colorState (!χ 0)
  else 0

def siteRightState (c : ChargedSite) (χ : Fin c.size → Bool) (o : Bool) : Fin 3 :=
  if o then match c with
    | .point => Transfer.colorState (χ 0)
    | .group a => Transfer.colorState (!χ (Fin.last a))
  else 0

def siteAmplitude (c : ChargedSite) (χ : Fin c.size → Bool) (o : Bool) : ℝ :=
  siteCoefficient c o * (∏ e : Fin (c.size-1),
    ((internalAffine c o e).1 + (internalAffine c o e).2 * localEqualZ c χ e))

def optionFirstState : (ch : Chain) → ChargeColorings ch.sizes → Options ch → Fin 3
  | .last c, χ, o => siteLeftState c χ.1 o
  | .cons c _ _, χ, o => siteLeftState c χ.1 o.1

def optionLastState : (ch : Chain) → ChargeColorings ch.sizes → Options ch → Fin 3
  | .last c, χ, o => siteRightState c χ.1 o
  | .cons _ _ tail, χ, o => optionLastState tail χ.2 o.2

def optionAmplitude (ch : Chain) (χ : ChargeColorings ch.sizes) (o : Options ch) : ℝ :=
  siteCoefficients ch o * affineEdgeProduct ch o (equalZ ch χ)

theorem colorWeight_eq_extra (c : ChargedSite) (χ : Fin c.size → Bool) :
    c.colorWeight χ = ChargeSites.chargeWeight χ * C (siteExtraWeight c χ) := by
  cases c with
  | point => simp [ChargedSite.colorWeight, siteExtraWeight]
  | group a =>
    by_cases ha : a=1 <;> simp [ChargedSite.colorWeight, siteExtraWeight, ha]

end R34.ReducedCharge
