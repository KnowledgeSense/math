import SumsetRanges.LargeWeights

namespace SumsetRanges

theorem telescoping_linear_lower (f : ℕ → ℤ) (N : ℕ) (w : ℤ)
    (hs : ∀j<N,w≤2*(f j-f (j+1))) :
    (N : ℤ)*w≤2*(f 0-f N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := ih (fun j hj => hs j (by omega))
    have hn := hs N (by omega)
    push_cast
    linarith

theorem telescoping_triangular_lower (f : ℕ → ℤ) (N : ℕ) (w : ℤ)
    (hs : ∀j<N,((j : ℤ)+1)*w≤2*(f j-f (j+1))) :
    (N : ℤ)*((N : ℤ)+1)*w≤4*(f 0-f N) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hi := ih (fun j hj => hs j (by omega))
    have hn := hs N (by omega)
    push_cast
    nlinarith

theorem linear_width_covers_shared (f : ℕ → ℤ) (R S : ℕ) (w : ℤ)
    (hw : 0≤w) (hRS : 4*(S-1)≤R)
    (hs : ∀j<R,w≤2*(f j-f (j+1))) :
    2*((S-1 : ℕ) : ℤ)*w≤f 0-f R := by
  have ht := telescoping_linear_lower f R w hs
  have hr : 4*((S-1 : ℕ) : ℤ)≤R := by exact_mod_cast hRS
  have hm := mul_le_mul_of_nonneg_right hr hw
  linarith

theorem shared_width_covers_linear (f : ℕ → ℤ) (S k : ℕ) (w : ℤ)
    (hw : 0≤w) (hS : 1≤S) (hk : 8*k≤S*(S-1))
    (hs : ∀j<S-1,((j : ℤ)+1)*w≤2*(f j-f (j+1))) :
    2*(k : ℤ)*w≤f 0-f (S-1) := by
  have ht := telescoping_triangular_lower f (S-1) w hs
  have he : ((S-1 : ℕ) : ℤ)+1=S := by omega
  rw [he] at ht
  have hk' : 8*(k : ℤ)≤(S : ℤ)*((S-1 : ℕ) : ℤ) := by exact_mod_cast hk
  have hm := mul_le_mul_of_nonneg_right hk' hw
  nlinarith

end SumsetRanges
