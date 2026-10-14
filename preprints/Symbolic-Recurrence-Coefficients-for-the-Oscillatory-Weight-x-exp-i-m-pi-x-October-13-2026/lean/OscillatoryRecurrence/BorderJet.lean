import OscillatoryRecurrence.BorderBasis
import OscillatoryRecurrence.EndpointBlocks

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

theorem endpointEntry_coeff_one (i j : ℕ) :
    (endpointEntry i j).coeff 1 =
      -((i/2+j/2+1).factorial:ℚ)*((i%2+j%2+1:ℕ)+(i/2+j/2:ℕ)/2:ℚ)*
        ((-2)^(i/2+j/2)+2^(i/2+j/2)*(-1)^(i%2+j%2+1)) := by
  simp only [endpointEntry,coeff_sub,factorialTransform_coeff,
    endpointTail_one_coeff_one,endpointTail_neg_one_coeff_one]
  rw [Nat.add_comm 1 (i/2+j/2)]
  ring

def indexedEndpointEntry (r s c e f : ℕ) : ℚ[X] :=
  C (((-2:ℚ)^(r+s))⁻¹)*endpointEntry (2*r+(c+r+e)%2) (2*s+(c+s+f)%2)

theorem indexedEndpointEntry_coeff_zero (r s c e f : ℕ) :
    (indexedEndpointEntry r s c e f).coeff 0=
      (1+(-1:ℚ)^(e+f))*((r+s).factorial:ℚ) := by
  rw [indexedEndpointEntry,coeff_C_mul,coeff_zero_eq_eval_zero,
    endpointEntry_index_eval_zero]
  rw [← pow_add]
  field_simp

theorem indexedEndpointEntry_coeff_one (r s c e f : ℕ) :
    (indexedEndpointEntry r s c e f).coeff 1=
      -((r+s+1).factorial:ℚ)*(((c+r+e)%2+(c+s+f)%2+1:ℕ)+(r+s:ℕ)/2:ℚ)*
        (1-(-1:ℚ)^(e+f)) := by
  have hr : (2*r+(c+r+e)%2)/2=r := by omega
  have hs : (2*s+(c+s+f)%2)/2=s := by omega
  have hrm : (2*r+(c+r+e)%2)%2=(c+r+e)%2 := by omega
  have hsm : (2*s+(c+s+f)%2)%2=(c+s+f)%2 := by omega
  rw [indexedEndpointEntry,coeff_C_mul,endpointEntry_coeff_one,hr,hs,hrm,hsm]
  have hsign := endpoint_pair_sign r s c e f
  have hsq : ((-1:ℚ)^(r+s))^2=1 := by
    rw [← pow_mul,Nat.mul_comm _ 2,pow_mul]
    norm_num
  have he : (-2:ℚ)^(r+s)+2^(r+s)*(-1)^((c+r+e)%2+(c+s+f)%2+1)=
      (-2)^(r+s)*(1-(-1)^(e+f)) := by
    rw [← hsign,neg_pow]
    simp only [pow_add,pow_succ] at hsq ⊢
    linear_combination (2:ℚ)^(r+s)*(-1)^((c+r+e)%2)*(-1)^((c+s+f)%2)*hsq
  rw [he]
  field_simp

end OscillatoryRecurrence
