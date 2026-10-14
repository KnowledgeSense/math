import SumsetRanges.BaselineGluing

open Finset
namespace SumsetRanges
open scoped Classical

theorem restricted_large_chain (h k K : ℕ) (hh : 2≤h) (hK : (32*h^3)^10≤K)
    (hKk : K+2≤k) (hkK : sparseThreshold k≤K) (z : ℤ)
    (hz : baselineValue h K (k-K) (k-K-1)≤z) (hzt : z≤(k.choose h : ℤ)) :
    ∃B : Finset ℤ,B.card=k ∧ (∀a∈B,0≤a ∧ a≤(k^(restrictedExponent h):ℕ)) ∧
      ((restrictedSums B h).card : ℤ)=z := by
  let N := k-K-2
  let lo := fun j => baselineValue h (k-(j+2)) (j+2) (j+1)
  let hi := fun j => baselineValue h (k-(j+2)) (j+2) (denseMaximum h (j+2))
  have hpar (j : ℕ) (hj : j≤N) : K≤k-(j+2) ∧ k-(j+2)+(j+2)=k := by
    dsimp [N] at hj
    omega
  have hc (j : ℕ) (hj : j≤N) : (32*h^3)^10≤k-(j+2) := hK.trans (hpar j hj).1
  have hjoint (j : ℕ) (hj : j<N) : hi (j+1)=lo j := by
    dsimp [hi,lo]
    rw [baseline_adjacent h (k-(j+1+2)) (j+1+2) (by omega)]
    have h1 : k-(j+1+2)+1=k-(j+2) := by have := hpar (j+1) (by omega); omega
    have h2 : j+1+2-1=j+2 := by omega
    have h3 : j+1+2-2=j+1 := by omega
    rw [h1,h2,h3]
  have cover : ∀j≤N,∀w,lo j≤w → w≤hi j →
      ∃B : Finset ℤ,(B.card=k ∧ ∀a∈B,0≤a ∧ a≤(k^(restrictedExponent h):ℕ)) ∧
        ((restrictedSums B h).card : ℤ)=w := by
    intro j hj w hw hw'
    have hkc : sparseThreshold (k-(j+2)+(j+2))≤k-(j+2) := by
      rw [(hpar j hj).2]
      exact hkK.trans (hpar j hj).1
    obtain ⟨B,hB,hBd,hBe⟩ := baseline_interval_realized h (k-(j+2)) (j+2) hh (hc j hj)
      (by omega) hkc w (by simpa [lo] using hw) hw'
    rw [(hpar j hj).2] at hB hBd
    exact ⟨B,⟨hB,hBd⟩,hBe⟩
  have hlo : ∀j<N,lo (j+1)≤lo j := by
    intro j hj
    have hb := baseline_ordered h (k-(j+1+2)) (j+1+2) hh (hc (j+1) (by omega)) (by omega)
    have hb' : lo (j+1)≤hi (j+1) := by simpa [lo,hi] using hb
    rwa [hjoint j hj] at hb'
  have hover : ∀j<N,lo j≤hi (j+1)+1 := by
    intro j hj
    rw [hjoint j hj]
    omega
  have hzlo : lo N≤z := by
    have h1 : k-(N+2)=K := by dsimp [N]; omega
    have h2 : N+2=k-K := by dsimp [N]; omega
    have h3 : N+1=k-K-1 := by dsimp [N]; omega
    simpa only [lo,h2,h3,show k-(k-K)=K by omega] using hz
  have hzhi : z≤hi 0 := by
    simpa [hi,baseline_top h k (by omega)] using hzt
  obtain ⟨j,_,B,hB,hBe⟩ := integer_interval_chain
    (fun _ (B : Finset ℤ) => ((restrictedSums B h).card : ℤ))
    (fun _ B => B.card=k ∧ ∀a∈B,0≤a ∧ a≤(k^(restrictedExponent h):ℕ))
    lo hi N cover hlo hover z hzlo hzhi
  exact ⟨B,hB.1,hB.2,hBe⟩

end SumsetRanges
