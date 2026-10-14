import BoseBurton.KernelPartials
import BoseBurton.PairedConcavity
import BoseBurton.GaussianFalling
import BoseBurton.TelescopingDefinitions

noncomputable section
namespace BoseBurton

theorem cancellationBracket_identity (z : ℝ) (r h k : ℕ) (hl : h≤k) (hkr : k≤r) :
    z^h*(1-z^(k-h))*(1-z^(r-k))-(1-z^h)*(1-z^k)=
      -cancellationBracket z r h k := by
  have h1 : z^h*z^(k-h)=z^k := by rw [← pow_add]; congr 1; omega
  have h2 : z^k*z^(r-k)=z^r := by rw [← pow_add]; congr 1; omega
  unfold cancellationBracket
  linear_combination (z^(r-k)-1)*h1+h2

theorem partial_difference_normalized (z : ℝ) (hz0 : 0≤z) (hz1 : z<1)
    (r s h k : ℕ) (hsr : s<r) (hh : 1≤h) (hk : 1≤k) (hkr : k<r) :
    (upperPartialTerm z r s h k-lowerPartialTerm z r s h k)/gaussian z r k=
      -cancellationWeight z r s h*pairedProduct z r (h-1) k*cancellationBracket z r h k := by
  by_cases hl : h≤k
  · by_cases hr : h≤r-k
    · have hu : upperPartialTerm z r s h k=z^(h*(r-s+h))*gaussian z s h*
          gaussian z (r-h) k*gaussian z (k-1) h := by
        by_cases hlt : h<k
        · simp [upperPartialTerm,hlt,show k≤r-h by omega]
        · have he : h=k := by omega
          subst h
          simp [upperPartialTerm,gaussian_outside z (k-1) k (by omega)]
      rw [hu,lowerPartialTerm,ite_eq_left ⟨hl,hr⟩,sub_div]
      have htu : (z^(h*(r-s+h))*gaussian z s h*gaussian z (r-h) k*gaussian z (k-1) h)/gaussian z r k=
          z^(h*(r-s+h))*gaussian z s h*(gaussian z (r-h) k*gaussian z (k-1) h/gaussian z r k) := by ring
      have htl : (z^(h*(r-s+h-1))*gaussian z s h*gaussian z (r-h) (k-h)*gaussian z (r-k-1) (h-1))/gaussian z r k=
          z^(h*(r-s+h-1))*gaussian z s h*(gaussian z (r-h) (k-h)*gaussian z (r-k-1) (h-1)/gaussian z r k) := by ring
      rw [htu,htl,gaussian_upper_falling z hz0 hz1 r h k hh hl hr,
        gaussian_lower_falling z hz0 hz1 r h k hh hl hr]
      have he : z^(h*(r-s+h))=z^(h*(r-s+h-1))*z^h := by
        rw [← pow_add]
        congr 1
        have hE : r-s+h=(r-s+h-1)+1 := by omega
        calc
          _ = h*((r-s+h-1)+1) := congrArg (fun t=>h*t) hE
          _ = _ := by ring
      rw [he,cancellationWeight]
      have hb := cancellationBracket_identity z r h k hl hkr.le
      linear_combination
        (z^(h*(r-s+h-1))*gaussian z s h*qFactorial z (r-h)/
          (qFactorial z r*qFactorial z h)*pairedProduct z r (h-1) k)*hb
    · rw [pairedProduct_eq_zero_right z r (h-1) k hkr (by omega)]
      simp [upperPartialTerm,lowerPartialTerm,hr,show ¬k≤r-h by omega]
  · rw [pairedProduct_eq_zero_left z r (h-1) k hk (by omega)]
    simp [upperPartialTerm,lowerPartialTerm,hl,show ¬h<k by omega]

end BoseBurton
