import SumsetRanges.FiniteCoordinateModel

namespace SumsetRanges

theorem momentOrder_pos (h : ℕ) (hh : 2≤h) : 1≤momentOrder h := by
  unfold momentOrder
  nlinarith

theorem restrictedScale_ge (h : ℕ) : 4*h≤restrictedScale h := by
  have hp : 1≤(2*h+2)^(momentOrder h) := Nat.one_le_pow _ _ (by omega)
  unfold restrictedScale
  nlinarith

theorem restrictedDimension_pos (h : ℕ) : 1≤restrictedDimension h := by
  unfold restrictedDimension
  omega

/-- The explicit logarithmic exponent in the release bounds the actual radix diameter. -/
theorem restricted_model_diameter_bound (h k D : ℕ) (hk : 2≤k)
    (hD : D≤restrictedDimension h) :
    D*(restrictedScale h*k^(momentOrder h)) *
      (h*(restrictedScale h*k^(momentOrder h))+1)^(D-1) ≤ k^(restrictedExponent h) := by
  let L := momentOrder h
  let σ := restrictedScale h
  let D0 := restrictedDimension h
  have hD0 : 1≤D0 := restrictedDimension_pos h
  have hkpow : 1≤k^L := Nat.one_le_pow _ _ (by omega)
  have hQ : h*(σ*k^L)+1 ≤ (h*σ+1)*k^L := by nlinarith
  have hQ1 : 1≤h*(σ*k^L)+1 := by omega
  have hdim : D-1≤D0-1 := by omega
  change D*(σ*k^L)*(h*(σ*k^L)+1)^(D-1)≤_
  calc
    _ ≤ D0*(σ*k^L)*(h*(σ*k^L)+1)^(D0-1) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ hD) (Nat.pow_le_pow_right hQ1 hdim)
    _ ≤ D0*(σ*k^L)*((h*σ+1)*k^L)^(D0-1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _)
    _ = restrictedConstant h*k^(L*D0) := by
      rw [mul_pow,← pow_mul]
      have he : L*D0=L+L*(D0-1) := by have := Nat.sub_add_cancel hD0; nlinarith
      rw [he,pow_add]
      change D0*(σ*k^L)*((h*σ+1)^(D0-1)*k^(L*(D0-1))) =
        (D0*σ*(h*σ+1)^(D0-1))*(k^L*k^(L*(D0-1)))
      ring
    _ ≤ k^(Nat.clog 2 (restrictedConstant h))*k^(L*D0) := by
      apply Nat.mul_le_mul_right
      calc
        restrictedConstant h ≤ 2^(Nat.clog 2 (restrictedConstant h)) := Nat.le_pow_clog (by decide) _
        _ ≤ k^(Nat.clog 2 (restrictedConstant h)) := Nat.pow_le_pow_left hk _
    _ = k^(restrictedExponent h) := by
      rw [← pow_add]
      unfold restrictedExponent
      congr 1
      change Nat.clog 2 (restrictedConstant h)+L*D0=L*D0+Nat.clog 2 (restrictedConstant h)
      omega

end SumsetRanges
