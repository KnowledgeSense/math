import Dowling.DowlingMixtureWeights
import Dowling.DiscreteMidpointStrict

noncomputable section
namespace Dowling

def dowlingMixtureTerm (c p : ℝ) (n k j : ℕ) : ℝ :=
  if j≤k ∧ k+j≤n then dowlingQuadraticWeight c j*
    dowlingBinomialWeight p (k-j)*dowlingBinomialWeight p (n-k-j) else 0

def dowlingMixtureFunction (c p : ℝ) (n k : ℕ) (j : ℤ) : ℝ :=
  if j<0 then 0 else dowlingMixtureTerm c p n k j.toNat

theorem dowlingMixtureTerm_pos {c p : ℝ} (n k j : ℕ) (hc : (n : ℝ)/2<c) (hp : 1<p) (hj : j≤k ∧ k+j≤n) : 0<dowlingMixtureTerm c p n k j := by
  rw [dowlingMixtureTerm,ite_eq_left hj]
  have hc0 : 0<c := lt_of_le_of_lt (by positivity) hc
  have hjc : (j : ℝ)<c := by
    have hbound : (2 : ℝ)*j≤n := by exact_mod_cast (show 2*j≤n by omega)
    linarith
  exact mul_pos (mul_pos (dowlingQuadraticWeight_pos hc0 hjc)
    (dowlingBinomialWeight_pos (by linarith) _)) (dowlingBinomialWeight_pos (by linarith) _)

theorem dowlingMixtureTerm_nonneg {c p : ℝ} (n k j : ℕ) (hc : (n : ℝ)/2<c) (hp : 1<p) :
    0≤dowlingMixtureTerm c p n k j := by
  by_cases hj : j≤k ∧ k+j≤n
  · exact le_of_lt (dowlingMixtureTerm_pos n k j hc hp hj)
  · simp [dowlingMixtureTerm,hj]

theorem dowlingMixtureTerm_midpoint_strict {c p : ℝ} (n k i j : ℕ)
    (hc : (n : ℝ)/2<c) (hp : 1<p) (hk : 1≤k) (_hkn : k<n)
    (hi : i≤k-1 ∧ k-1+i≤n) (hj : j≤k+1 ∧ k+1+j≤n) :
    dowlingMixtureTerm c p n (k-1) i*dowlingMixtureTerm c p n (k+1) j <
      dowlingMixtureTerm c p n k ((i+j)/2)*dowlingMixtureTerm c p n k ((i+j+1)/2) := by
  let u := (i+j)/2
  let v := (i+j+1)/2
  have hu : u≤k ∧ k+u≤n := by dsimp [u]; omega
  have hv : v≤k ∧ k+v≤n := by dsimp [v]; omega
  change dowlingMixtureTerm c p n (k-1) i*dowlingMixtureTerm c p n (k+1) j <
      dowlingMixtureTerm c p n k u*dowlingMixtureTerm c p n k v
  rw [dowlingMixtureTerm,dowlingMixtureTerm,dowlingMixtureTerm,dowlingMixtureTerm,
    ite_eq_left hi,ite_eq_left hj,ite_eq_left hu,ite_eq_left hv]
  have hc0 : 0<c := lt_of_le_of_lt (by positivity) hc
  have hic : (i : ℝ)<c := by
    have : (2 : ℝ)*i≤n := by exact_mod_cast (show 2*i≤n by omega)
    linarith
  have hjc : (j : ℝ)<c := by
    have : (2 : ℝ)*j≤n := by exact_mod_cast (show 2*j≤n by omega)
    linarith
  have huc : (u : ℝ)<c := by
    have : (2 : ℝ)*u≤n := by exact_mod_cast (show 2*u≤n by omega)
    linarith
  have hvc : (v : ℝ)<c := by
    have : (2 : ℝ)*v≤n := by exact_mod_cast (show 2*v≤n by omega)
    linarith
  have hw := dowlingQuadraticWeight_midpoint hc0 i j hic hjc
  have hA := dowlingBinomialWeight_midpoint hp (k-1-i) (k+1-j)
  have hB := dowlingBinomialWeight_midpoint hp (n-(k-1)-i) (n-(k+1)-j)
  have ha1 : (k-1-i+(k+1-j))/2=k-v := by dsimp [v]; omega
  have ha2 : (k-1-i+(k+1-j)+1)/2=k-u := by dsimp [u]; omega
  have hb1 : (n-(k-1)-i+(n-(k+1)-j))/2=n-k-v := by dsimp [v]; omega
  have hb2 : (n-(k-1)-i+(n-(k+1)-j)+1)/2=n-k-u := by dsimp [u]; omega
  rw [ha1,ha2,mul_comm (dowlingBinomialWeight p (k-v))] at hA
  rw [hb1,hb2,mul_comm (dowlingBinomialWeight p (n-k-v))] at hB
  have hpos (r : ℕ) : 0<dowlingBinomialWeight p r := dowlingBinomialWeight_pos (by linarith) r
  have hAB :
      (dowlingBinomialWeight p (k-1-i)*dowlingBinomialWeight p (k+1-j))*
        (dowlingBinomialWeight p (n-(k-1)-i)*dowlingBinomialWeight p (n-(k+1)-j)) <
      (dowlingBinomialWeight p (k-u)*dowlingBinomialWeight p (k-v))*
        (dowlingBinomialWeight p (n-k-u)*dowlingBinomialWeight p (n-k-v)) := by
    by_cases hs : k-1-i+1<k+1-j ∨ k+1-j+1<k-1-i
    · have hAs := dowlingBinomialWeight_midpoint_strict hp (k-1-i) (k+1-j) hs
      rw [ha1,ha2,mul_comm (dowlingBinomialWeight p (k-v))] at hAs
      exact (mul_lt_mul_of_pos_right hAs (mul_pos (hpos _) (hpos _))).trans_le
        (mul_le_mul_of_nonneg_left hB (le_of_lt (mul_pos (hpos _) (hpos _))))
    · have hs' : n-(k-1)-i+1<n-(k+1)-j ∨ n-(k+1)-j+1<n-(k-1)-i := by omega
      have hBs := dowlingBinomialWeight_midpoint_strict hp (n-(k-1)-i) (n-(k+1)-j) hs'
      rw [hb1,hb2,mul_comm (dowlingBinomialWeight p (n-k-v))] at hBs
      exact (mul_le_mul_of_nonneg_right hA (le_of_lt (mul_pos (hpos _) (hpos _)))).trans_lt
        (mul_lt_mul_of_pos_left hBs (mul_pos (hpos _) (hpos _)))
  have hwpos : 0<dowlingQuadraticWeight c u*dowlingQuadraticWeight c v :=
    mul_pos (dowlingQuadraticWeight_pos hc0 huc) (dowlingQuadraticWeight_pos hc0 hvc)
  have hmul := (mul_le_mul_of_nonneg_right hw
    (le_of_lt (mul_pos (mul_pos (hpos (k-1-i)) (hpos (k+1-j)))
      (mul_pos (hpos (n-(k-1)-i)) (hpos (n-(k+1)-j)))))).trans_lt
        (mul_lt_mul_of_pos_left hAB hwpos)
  nlinarith [hmul]

end Dowling
