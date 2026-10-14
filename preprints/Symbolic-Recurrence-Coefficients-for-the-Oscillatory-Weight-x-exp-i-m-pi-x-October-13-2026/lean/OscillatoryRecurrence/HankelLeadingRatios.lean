import OscillatoryRecurrence.EndpointHankelLeading

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

theorem polynomialHankel_even_leadingCoeff (k : ℕ) :
    (polynomialHankel (2*k)).leadingCoeff =
      (-1:ℚ)^k * 4^(k^2) * laguerreConstant k^2 := by
  rw [polynomialHankel_leadingCoeff,hankelDegree_even,endpointConstantMatrix_even_det]
  have he : (-1:ℚ)^(k^2)=(-1:ℚ)^k := by
    rw [neg_one_pow_eq_pow_mod_two (k^2),neg_one_pow_eq_pow_mod_two k]
    congr 1
    rw [Nat.pow_mod]
    have h : k%2=0 ∨ k%2=1 := by omega
    rcases h with h|h <;> simp [h]
  rw [he]
  ring

theorem polynomialHankel_odd_leadingCoeff (k : ℕ) :
    (polynomialHankel (2*k+1)).leadingCoeff =
      2 * 4^(k*(k+1)) * laguerreConstant k * laguerreConstant (k+1) := by
  rw [polynomialHankel_leadingCoeff,hankelDegree_odd,endpointConstantMatrix_odd_det]
  have he : Even (k*(k+1)) := by
    obtain ⟨r,rfl|rfl⟩ := Nat.even_or_odd' k
    · exact ⟨r*(2*r+1),by ring⟩
    · exact ⟨(2*r+1)*(r+1),by ring⟩
  rw [he.neg_one_pow,one_mul]

/-- The leading constants in consecutive odd recurrence positions cancel exactly. -/
theorem polynomialHankel_leading_odd_recurrence (k : ℕ) :
    (polynomialHankel (2*k+2)).leadingCoeff *
      (polynomialHankel (2*k)).leadingCoeff =
      -(polynomialHankel (2*k+1)).leadingCoeff^2 := by
  rw [show 2*k+2=2*(k+1) by omega,polynomialHankel_even_leadingCoeff,
    polynomialHankel_even_leadingCoeff,polynomialHankel_odd_leadingCoeff]
  have hs : (-1:ℚ)^(k+1)*(-1)^k = -1 := by
    rw [← pow_add,show k+1+k=2*k+1 by omega,pow_add,pow_mul]
    norm_num
  have he : (k+1)^2+k^2=2*(k*(k+1))+1 := by ring
  have hp : (4:ℚ)^((k+1)^2)*4^(k^2)=4*(4^(k*(k+1)))^2 := by
    rw [← pow_add,he,pow_add,Nat.mul_comm 2 _,pow_mul,pow_one]
    ring
  calc
    _ = ((-1:ℚ)^(k+1)*(-1)^k)*
      (4^((k+1)^2)*4^(k^2))*laguerreConstant (k+1)^2*laguerreConstant k^2 := by ring
    _ = _ := by rw [hs,hp]; ring

/-- The leading constants in consecutive even recurrence positions yield the square factor. -/
theorem polynomialHankel_leading_even_recurrence (k : ℕ) :
    (polynomialHankel (2*k+3)).leadingCoeff *
      (polynomialHankel (2*k+1)).leadingCoeff =
      (2*(k+1):ℚ)^2 * (polynomialHankel (2*k+2)).leadingCoeff^2 := by
  rw [show 2*k+3=2*(k+1)+1 by omega,show 2*k+2=2*(k+1) by omega,
    polynomialHankel_odd_leadingCoeff,polynomialHankel_odd_leadingCoeff,
    polynomialHankel_even_leadingCoeff]
  have hs : ((-1:ℚ)^(k+1))^2=1 := by rw [← pow_mul,Nat.mul_comm _ 2,pow_mul]; norm_num
  have he : (k+1)*(k+1+1)+k*(k+1)=2*(k+1)^2 := by ring
  have hp : (4:ℚ)^((k+1)*(k+1+1))*4^(k*(k+1))=(4^((k+1)^2))^2 := by
    rw [← pow_add,he,Nat.mul_comm 2 _,pow_mul]
  have hl : laguerreConstant (k+2)*laguerreConstant k =
      (k+1:ℚ)^2*laguerreConstant (k+1)^2 := by
    rw [show k+2=(k+1)+1 by omega,laguerreConstant_succ,laguerreConstant_succ]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring
  calc
    _ = 4*(4^((k+1)*(k+1+1))*4^(k*(k+1)))*
      laguerreConstant (k+1)^2*(laguerreConstant (k+2)*laguerreConstant k) := by ring
    _ = _ := by rw [hp,hl]; simp only [mul_pow,hs]; ring

end OscillatoryRecurrence
