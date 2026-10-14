import Fan.KernelTuranCoefficients
import Fan.KernelTuranPayment
import Fan.DelannoyRatio

noncomputable section
open scoped BigOperators
namespace Fan

theorem positive_cross_of_adjacent (A B : ℕ → ℝ) (hB : ∀ i,0<B i)
    (h : ∀ i,A i*B (i+2)<A (i+1)*B (i+1)) :
    ∀ i j,j < i → A j*B (i+1)<A i*B (j+1) := by
  have hm : StrictMono (fun i => A i/B (i+1)) := by
    apply strictMono_nat_of_lt_succ
    intro i
    apply (div_lt_div_iff₀ (hB _) (hB _)).mpr
    exact h i
  intro i j hji
  exact (div_lt_div_iff₀ (hB _) (hB _)).mp (hm hji)

theorem kernelTuran_coeff_positive (A B C rho : ℕ → ℝ)
    (hA : ∀ n,A n=∑ j∈Finset.range (n+1),B j*rho (n-j))
    (hC : ∀ n,C n=∑ j∈Finset.range (n+1),A j*rho (n-j))
    (hAp : ∀ i,0<A i) (hBp : ∀ i,0<B i) (hrhop : ∀ i,0<rho i)
    (hcross : ∀ i j,j < i → A j*B (i+1)<A i*B (j+1))
    (k r : ℕ) (hr : r≤k+1) : 0<(kernelTuran A B C k).coeff r := by
  rw [kernelTuran_coeff A B C rho hA hC]
  have hp := boundaryExtended_payment A B rho hAp hBp hrhop hcross (k+1) (k+1-r) (by omega)
  have h1 : ((k+1-r:ℕ):ℤ)=(k:ℤ)+1-r := by omega
  have h2 : ((k+1-r:ℕ):ℤ)-1=(k:ℤ)-r := by omega
  rw [h2,h1] at hp
  simpa only [Nat.cast_add,Nat.cast_one,show (1:ℤ)+1=2 from rfl,add_assoc] using hp

theorem kernelTuran_coeff_above (A B C rho : ℕ → ℝ)
    (hA : ∀ n,A n=∑ j∈Finset.range (n+1),B j*rho (n-j))
    (hC : ∀ n,C n=∑ j∈Finset.range (n+1),A j*rho (n-j))
    (k r : ℕ) (hr : k+1<r) : (kernelTuran A B C k).coeff r=0 := by
  rw [kernelTuran_coeff A B C rho hA hC]
  have h1 : ¬0≤(k:ℤ)+1-r := by omega
  have h2 : ¬0≤(k:ℤ)-r := by omega
  simp only [boundaryExtended,h1,h2,and_false,false_and,ite_false,sub_self]

theorem delannoy_convolution_right (z : ℝ) (e m : ℕ) :
    delannoy z m (m+e+2)=∑ j∈Finset.range (m+1),
      delannoy z j (j+e)*convolutionRho z (m-j) := by
  have h := congrArg (PowerSeries.coeff m) (imbalanceSeries_step_two z e)
  rw [mul_comm,PowerSeries.coeff_mul] at h
  simp only [imbalanceSeries_coeff] at h
  change delannoy z m (m+(e+2)) = ∑ x∈Finset.antidiagonal m,
    delannoy z x.1 (x.1+e)*convolutionRho z x.2 at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => delannoy z j (j+e)*convolutionRho z k) m] at h
  simpa only [Nat.add_assoc] using h

def delannoyTuran (z : ℝ) (e k : ℕ) : Polynomial ℝ :=
  kernelTuran (fun m => delannoy z m (m+e+2)) (fun m => delannoy z m (m+e))
    (fun m => delannoy z m (m+e+4)) k

theorem delannoyTuran_coeff_positive_of_ratio (z : ℝ) (hz : 0<z) (e k r : ℕ)
    (h : ∀ m,delannoy z m (m+e+2)*delannoy z (m+2) (m+e+2)<
      delannoy z (m+1) (m+e+3)*delannoy z (m+1) (m+e+1)) (hr : r≤k+1) :
    0<(delannoyTuran z e k).coeff r := by
  apply kernelTuran_coeff_positive _ _ _ (convolutionRho z)
    (delannoy_convolution_right z e)
  · intro m
    simpa only [Nat.add_assoc] using delannoy_convolution_right z (e+2) m
  · exact fun _ => delannoy_pos hz.le _ _
  · exact fun _ => delannoy_pos hz.le _ _
  · exact convolutionRho_pos hz
  · apply positive_cross_of_adjacent (fun m => delannoy z m (m+e+2))
      (fun m => delannoy z m (m+e))
    · exact fun _ => delannoy_pos hz.le _ _
    · intro m
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h m
  · exact hr

theorem delannoyTuran_coeff_above (z : ℝ) (e k r : ℕ) (hr : k+1<r) :
    (delannoyTuran z e k).coeff r=0 := by
  apply kernelTuran_coeff_above _ _ _ (convolutionRho z)
    (delannoy_convolution_right z e)
  · intro m
    simpa only [Nat.add_assoc] using delannoy_convolution_right z (e+2) m
  · exact hr

theorem delannoyTuran_coeff_positive (z : ℝ) (hz : 0<z) (e k r : ℕ) (hr : r≤k+1) :
    0<(delannoyTuran z e k).coeff r := by
  apply delannoyTuran_coeff_positive_of_ratio z hz e k r
  · intro m
    exact delannoy_adjacent_ratio z hz e m
  · exact hr

end Fan
