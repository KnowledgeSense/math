import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Elementary finite midpoint inequalities, following the support-removal proof
of Halikias–Klartag–Slomka, Proposition 2.2, DOI 10.5802/afst.1674. -/
noncomputable section
namespace Dowling

 theorem midpoint_two_sum {a b c d : ℝ} (ha : 0≤a) (hb : 0≤b)
    (hc : 0≤c) (hd : 0≤d) (hab : a≤b) (hp : a*b≤c*d)
    (hm : b≤max c d) : a+b≤c+d := by
  by_cases hsmall : b≤min c d
  · have hbc : b≤c := hsmall.trans (min_le_left _ _)
    have hbd : b≤d := hsmall.trans (min_le_right _ _)
    linarith
  · have hpos : 0<b := lt_of_le_of_lt (le_min hc hd) (lt_of_not_ge hsmall)
    have hp' : 0≤(b-min c d)*(max c d-b) := mul_nonneg (by linarith) (by linarith)
    have hsum : min c d+max c d=c+d := min_add_max _ _
    have hprod : min c d*max c d=c*d := min_mul_max _ _
    nlinarith

 theorem midpoint_small_endpoint {a b c d : ℝ} (_ha : 0≤a)
    (hc : 0≤c) (hd : 0≤d) (hp : a*b≤c*d) (hb : max c d<b) :
    a≤min c d := by
  have hbc : c<b := lt_of_le_of_lt (le_max_left _ _) hb
  have hbd : d<b := lt_of_le_of_lt (le_max_right _ _) hb
  apply le_min
  · by_contra h
    have hprod : 0<(a-c)*b := mul_pos (by linarith) (lt_of_le_of_lt hc hbc)
    nlinarith
  · by_contra h
    have hprod : 0<(a-d)*b := mul_pos (by linarith) (lt_of_le_of_lt hd hbd)
    nlinarith

/-- The finite integer band produced by midpointing a diagonal interval. -/
def midpointBand (H : ℤ→ℝ) (z : ℤ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n+1), H ((z-(n : ℤ))/2+i)

@[simp] theorem midpointBand_zero (H : ℤ→ℝ) (z : ℤ) : midpointBand H z 0=H (z/2) := by
  simp [midpointBand]

 theorem midpointBand_two_step (H : ℤ→ℝ) (z : ℤ) (n : ℕ) :
    midpointBand H z (n+2)=H ((z-(n+2 : ℕ))/2)+midpointBand H z n+
      H ((z+(n+2 : ℕ))/2) := by
  have hlo : (z-(n : ℤ))/2=(z-(n+2 : ℕ))/2+1 := by omega
  have hhi : (z-(n+2 : ℕ))/2+(n+2 : ℕ)=(z+(n+2 : ℕ))/2 := by omega
  rw [midpointBand,Finset.sum_range_succ,Finset.sum_range_succ']
  rw [← hhi]
  dsimp only [midpointBand]
  rw [hlo]
  have he : (∑ i ∈ Finset.range (n+1),H ((z-(n+2 : ℕ))/2+(i+1)))=
      ∑ i ∈ Finset.range (n+1),H ((z-(n+2 : ℕ))/2+1+i) := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    omega
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_zero,add_zero] at *
  rw [he]
  ring

 theorem midpointBand_one_step (H : ℤ→ℝ) (z : ℤ) (n : ℕ) :
    min (H ((z-(n+1 : ℕ))/2)) (H ((z+(n+1 : ℕ))/2))+midpointBand H z n ≤
      midpointBand H z (n+1) := by
  have hhi : (z-(n+1 : ℕ))/2+(n+1 : ℕ)=(z+(n+1 : ℕ))/2 := by omega
  by_cases he : (z-(n : ℤ))/2=(z-(n+1 : ℕ))/2
  · have hb : midpointBand H z (n+1)=midpointBand H z n+H ((z+(n+1 : ℕ))/2) := by
      rw [midpointBand,Finset.sum_range_succ,midpointBand,he,hhi]
    rw [hb]
    linarith [min_le_right (H ((z-(n+1 : ℕ))/2)) (H ((z+(n+1 : ℕ))/2))]
  · have he' : (z-(n : ℤ))/2=(z-(n+1 : ℕ))/2+1 := by omega
    have hb : midpointBand H z (n+1)=H ((z-(n+1 : ℕ))/2)+midpointBand H z n := by
      rw [midpointBand,Finset.sum_range_succ',midpointBand,he']
      simp only [Nat.cast_zero,add_zero,Nat.cast_add,Nat.cast_one]
      have hh : (∑ i ∈ Finset.range (n+1),H ((z-(n+1 : ℕ))/2+(i+1)))=
          ∑ i ∈ Finset.range (n+1),H ((z-(n+1 : ℕ))/2+1+i) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        omega
      simp only [Nat.cast_add,Nat.cast_one] at hh
      rw [hh]
      ring
    rw [hb]
    linarith [min_le_left (H ((z-(n+1 : ℕ))/2)) (H ((z+(n+1 : ℕ))/2))]

end Dowling
