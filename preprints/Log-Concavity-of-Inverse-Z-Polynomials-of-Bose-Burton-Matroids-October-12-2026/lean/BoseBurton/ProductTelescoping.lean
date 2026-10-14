import BoseBurton.TelescopingDefinitions
import BoseBurton.PairedConcavity

noncomputable section
namespace BoseBurton

theorem pairedProduct_telescoping (z : ℝ) (r h k : ℕ)
    (hh : 1≤h) (hk : 1≤k) (hkr : k<r) :
    pairedProduct z r (h-1) k*cancellationBracket z r h k=
      (1-z^h)^2*pairedProduct z r (h-1) k-z^(2*h)*pairedProduct z r h k := by
  by_cases hl : h≤k
  · by_cases hr : h≤r-k
    · have he : h=(h-1)+1 := by omega
      have hQ : pairedProduct z r h k=pairedProduct z r (h-1) k*
          (1-z^(k-h))*(1-z^(r-k-h)) := by
        unfold pairedProduct
        conv_lhs => lhs; rw [he,fallingProduct_succ,← he]
        conv_lhs => rhs; rw [he,fallingProduct_succ,← he]
        ring
      rw [hQ,cancellationBracket]
      have h1 : z^h*z^(k-h)=z^k := by rw [← pow_add]; congr 1; omega
      have h2 : z^h*z^(r-k-h)=z^(r-k) := by rw [← pow_add]; congr 1; omega
      have h3 : z^k*z^(r-k)=z^r := by rw [← pow_add]; congr 1; omega
      rw [show 2*h=h+h by omega,pow_add]
      linear_combination pairedProduct z r (h-1) k*(z^h*z^(r-k-h)-z^h)*h1 +
        pairedProduct z r (h-1) k*(z^k-z^h)*h2 + pairedProduct z r (h-1) k*h3
    · rw [pairedProduct_eq_zero_right z r (h-1) k hkr (by omega),
        pairedProduct_eq_zero_right z r h k hkr (by omega)]
      ring
  · rw [pairedProduct_eq_zero_left z r (h-1) k hk (by omega),
      pairedProduct_eq_zero_left z r h k hk (by omega)]
    ring

end BoseBurton
