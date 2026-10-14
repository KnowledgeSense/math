import HankelAutomaticity.BinaryWords

namespace HankelAutomaticity
variable {R : Type*} [CommRing R]

/-- Integral recurrences arising from the actual determinant normalization.
Their link to the Hankel matrices is proved separately. -/
 def polynomialPair (w : List Bool) (q : R) : R × R :=
  match w with
  | [] => (0, 0)
  | [_] => (-q, 1-2*q)
  | [_, b] => if b then (q*(1-2*q)*(3-8*q), -(1-2*q)^2*(1-4*q))
      else (3*q-1, 2*q-1)
  | _::b::c::v =>
    let tail := b::c::v
    let u := 1-2*q
    if b then
      let p := polynomialPair tail (2*q)
      (u^(2^tail.length)*p.1-q*u^(2^tail.length-1)*p.2,
        u^(2^tail.length)*p.2)
    else
      let p := polynomialPair (complement tail) 1
      let r := binaryValue tail
      ((-1)^r*(u^(2*r+1)*p.1-q*u^(2*r)*p.2), (-1)^r*u^(2*r+1)*p.2)
 termination_by w.length
 decreasing_by all_goals simp [complement]

 theorem polynomialPair_map {S : Type*} [CommRing S] (f : R →+* S)
    (w : List Bool) (q : R) :
    polynomialPair w (f q)=((f (polynomialPair w q).1), f (polynomialPair w q).2) := by
  induction w using (measure List.length).wf.induction generalizing q with
  | h w ih =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, v⟩⟩⟩
    · simp [polynomialPair]
    · simp [polynomialPair, map_ofNat]
    · cases b <;> simp [polynomialPair, map_ofNat]
    · have htail : (b::c::v).length<(a::b::c::v).length := by simp
      have hc : (complement (b::c::v)).length<(a::b::c::v).length := by simp
      rw [polynomialPair, polynomialPair]
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [show (1 : S)=f 1 by simp, ih _ hc]
        simp [map_ofNat]
      · simp only [↓reduceIte]
        rw [show 2*f q=f (2*q) by simp [map_ofNat], ih _ htail]
        simp [map_ofNat]

end HankelAutomaticity
