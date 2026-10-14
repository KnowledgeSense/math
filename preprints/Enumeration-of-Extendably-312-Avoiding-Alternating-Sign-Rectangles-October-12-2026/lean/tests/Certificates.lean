import ASR312

open ASR312 PowerSeries

example (r k : ℕ) : S r k 0 = 1 := S_zero r k

example (n : ℕ) : S (n+1) (n+1) (n+1) = Nat.largeSchroder n :=
  S_square_schroder n

example (r k : ℕ) (h : k < r) :
    S r k k = ∑ q : Fin (k+1), S q.val k q.val * (r-q.val-1).choose (k-q.val) :=
  S_balanced_recurrence r k h

example (r k d : ℕ) (hdr : d ≤ r) (hdk : d ≤ k) :
    (S r k d : ℚ) = coeff d
      (P*(((1-X : PowerSeries ℚ)⁻¹)^(r-d)+
        R^(k-d)*((1-X*R : PowerSeries ℚ)⁻¹)^(r-d))) :=
  S_coefficient_closed_form r k d hdr hdk

example (a b : ℕ) :
    T a b = P*(((1-X : PowerSeries ℚ)⁻¹)^a+
      R^b*((1-X*R : PowerSeries ℚ)⁻¹)^a) :=
  T_closed_form_inverses a b

example (r k d : ℕ) (hdr : d ≤ r) (hdk : d ≤ k) :
    (S r k d : ℤ) = F r k d := full_enumeration r k d hdr hdk

example : FullEnumeration := fullEnumeration

example (r k : ℕ) : (S r k 0 : ℤ) = F r k 0 :=
  full_enumeration r k 0 (Nat.zero_le r) (Nat.zero_le k)

example (d : ℕ) : (S d d d : ℤ) = F d d d :=
  full_enumeration d d d (Nat.le_refl d) (Nat.le_refl d)
