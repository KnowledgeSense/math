import ASR312.RectanglePivotCounting

namespace ASR312

theorem pureAtRectangle_card {r k d : ℕ} (p : Fin r) (hpd : p.val < d) (hpk : p.val < k+1) :
    Nat.card (PureAtRectangle (k := k) (d := d) p) =
      squareASMCount p.val * S (r-(p.val+1)) ((k+1)-(p.val+1)) (d-(p.val+1)) := by
  have transport (a R K D rt kt dt : ℕ) (hr : (a+1)+R = rt) (hk : (a+1)+K = kt)
      (hd : (a+1)+D = dt) (hp : a < rt) (hk0 : 0 < kt) :
      Nat.card {A : AvoidingRectangle rt kt dt //
        A.val ⟨a,hp⟩ ⟨0,hk0⟩ = .plus ∧ ∀ j, j ≠ ⟨0,hk0⟩ → A.val ⟨a,hp⟩ j = .zero} =
        squareASMCount a * S R K D := by
    subst rt; subst kt; subst dt
    exact rectanglePure_card a R K D
  exact transport p.val (r-(p.val+1)) ((k+1)-(p.val+1)) (d-(p.val+1)) r (k+1) d
    (by omega) (by omega) (by omega) p.isLt (by omega)

theorem negativeAtRectangle_card_zero {r k d : ℕ} (p : Fin r) (hp0 : p.val = 0)
    (hk : p.val < k+1) : Nat.card (NegativeAtRectangle (d := d) p hk) = 0 := by
  have hj : (⟨p.val,hk⟩ : Fin (k+1)) = 0 := Fin.ext hp0
  let : IsEmpty (NegativeAtRectangle (d := d) p hk) := ⟨fun A => by
    have hm : A.val.val p 0 = .minus :=
      (congrArg (fun j => A.val.val p j) hj).symm.trans A.property.2
    have hf := A.property.1.symm.trans hm
    cases hf⟩
  simp

theorem negativeAtRectangle_card {r k d : ℕ} (p : Fin r) (hp0 : 0 < p.val)
    (hpd : p.val < d) (hpk : p.val < k+1) :
    Nat.card (NegativeAtRectangle (d := d) p hpk) =
      squareASMCount p.val * Nat.card (NonemptyCornerZeroRectangle (r-p.val-1) (k-p.val) (d-p.val)) := by
  have transport (a R K D rt kt dt : ℕ) (hr : (a+1)+(R+1) = rt) (hk : (a+1)+(K+1) = kt)
      (hd : (a+1)+D = dt) (hp : a+1 < rt) (hkp : a+1 < kt) (hk0 : 0 < kt) :
      Nat.card {A : AvoidingRectangle rt kt dt //
        A.val ⟨a+1,hp⟩ ⟨0,hk0⟩ = .plus ∧ A.val ⟨a+1,hp⟩ ⟨a+1,hkp⟩ = .minus} =
        squareASMCount (a+1) * Nat.card (NonemptyCornerZeroRectangle R K D) := by
    subst rt; subst kt; subst dt
    exact rectangleNegative_card a R K D
  have hp : p.val-1+1 = p.val := by omega
  have hh := transport (p.val-1) (r-p.val-1) (k-p.val) (d-p.val) r (k+1) d
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hi : (⟨p.val-1+1,by omega⟩ : Fin r) = p := Fin.ext hp
  have hj : (⟨p.val-1+1,by omega⟩ : Fin (k+1)) = ⟨p.val,hpk⟩ := Fin.ext hp
  have hz : (⟨0,by omega⟩ : Fin (k+1)) = 0 := Fin.ext rfl
  simpa only [hp,hi,hj,Fin.eta,hz] using hh

theorem rectangle_pivot_pair_card {r k d : ℕ} (p : Fin r) (hp0 : 0 < p.val)
    (hpd : p.val < d) (hdk : d ≤ k+1) :
    Nat.card (PureAtRectangle (k := k) (d := d) p) +
      Nat.card (NegativeAtRectangle (d := d) p (lt_of_lt_of_le hpd hdk)) =
      squareASMCount p.val * (S (r-p.val) (k+1-p.val) (d-p.val) -
        (r-p.val-1).choose (d-p.val)) := by
  have hpk : p.val < k+1 := lt_of_lt_of_le hpd hdk
  rw [pureAtRectangle_card p hpd hpk,negativeAtRectangle_card p hp0 hpd hpk,← Nat.mul_add]
  congr 1
  have hh := rectangleCorner_card_add (r-p.val-1) (k-p.val) (d-p.val-1) (by omega)
  have hr : r-p.val-1+1 = r-p.val := by omega
  have hk : k-p.val+1 = k+1-p.val := by omega
  have hd : d-p.val-1+1 = d-p.val := by omega
  have hr' : r-(p.val+1) = r-p.val-1 := by omega
  have hk' : k+1-(p.val+1) = k-p.val := by omega
  have hd' : d-(p.val+1) = d-p.val-1 := by omega
  rw [hr,hk,hd] at hh
  rw [hr',hk',hd']
  omega

end ASR312
