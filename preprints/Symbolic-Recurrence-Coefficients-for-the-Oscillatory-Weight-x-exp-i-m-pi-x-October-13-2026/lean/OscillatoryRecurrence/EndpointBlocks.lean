import OscillatoryRecurrence.EndpointBasis
import OscillatoryRecurrence.EndpointDeterminants

noncomputable section
open Polynomial Finset
open scoped BigOperators Matrix
namespace OscillatoryRecurrence

 def evenEndpointIndex (k c : ℕ) : Fin k ⊕ Fin k → Fin (2*k)
  | Sum.inl r => ⟨2*r.val+(c+r.val)%2,by have := r.isLt; omega⟩
  | Sum.inr r => ⟨2*r.val+(c+r.val+1)%2,by have := r.isLt; omega⟩

 theorem evenEndpointIndex_bijective (k c : ℕ) : Function.Bijective (evenEndpointIndex k c) := by
  constructor
  · intro x y h
    have he := congrArg Fin.val h
    rcases x with x|x <;> rcases y with y|y <;> simp only [evenEndpointIndex] at he
    · congr 1
      apply Fin.ext
      omega
    · exfalso
      omega
    · exfalso
      omega
    · congr 1
      apply Fin.ext
      omega
  · intro i
    let r : Fin k := ⟨i.val/2,by have := i.isLt; omega⟩
    by_cases h : i.val%2=(c+r.val)%2
    · refine ⟨Sum.inl r,?_⟩
      apply Fin.ext
      dsimp [evenEndpointIndex,r] at *
      omega
    · refine ⟨Sum.inr r,?_⟩
      apply Fin.ext
      dsimp [evenEndpointIndex,r] at *
      omega

 def evenEndpointEquiv (k c : ℕ) : Fin k ⊕ Fin k ≃ Fin (2*k) :=
  Equiv.ofBijective (evenEndpointIndex k c) (evenEndpointIndex_bijective k c)

 def oddEndpointIndex (k : ℕ) : Fin (k+1) ⊕ Fin k → Fin (2*k+1)
  | Sum.inl r => ⟨2*r.val+(k+r.val)%2,by have := r.isLt; omega⟩
  | Sum.inr r => ⟨2*r.val+(k+r.val+1)%2,by have := r.isLt; omega⟩

 theorem oddEndpointIndex_bijective (k : ℕ) : Function.Bijective (oddEndpointIndex k) := by
  constructor
  · intro x y h
    have he := congrArg Fin.val h
    rcases x with x|x <;> rcases y with y|y <;> simp only [oddEndpointIndex] at he
    · congr 1
      apply Fin.ext
      omega
    · exfalso
      omega
    · exfalso
      omega
    · congr 1
      apply Fin.ext
      omega
  · intro i
    by_cases h : i.val%2=(k+i.val/2)%2
    · let r : Fin (k+1) := ⟨i.val/2,by have := i.isLt; omega⟩
      refine ⟨Sum.inl r,?_⟩
      apply Fin.ext
      dsimp [oddEndpointIndex,r]
      omega
    · let r : Fin k := ⟨i.val/2,by have := i.isLt; omega⟩
      refine ⟨Sum.inr r,?_⟩
      apply Fin.ext
      dsimp [oddEndpointIndex,r]
      omega

 def oddEndpointEquiv (k : ℕ) : Fin (k+1) ⊕ Fin k ≃ Fin (2*k+1) :=
  Equiv.ofBijective (oddEndpointIndex k) (oddEndpointIndex_bijective k)

 theorem endpointEntry_eval_zero_factored (i j : ℕ) :
    (endpointEntry i j).eval 0=(-2:ℚ)^(i/2)*(-2)^(j/2)*
      (1+(-1)^(i/2+j/2+i%2+j%2))*((i/2+j/2).factorial:ℚ) := by
  rw [endpointEntry_eval_zero]
  have hs : ((-1:ℚ)^(i/2+j/2))^2=1 := by
    rw [← pow_mul,Nat.mul_comm _ 2,pow_mul]
    norm_num
  rw [neg_pow (2:ℚ) (i/2+j/2),neg_pow (2:ℚ) (i/2),neg_pow (2:ℚ) (j/2)]
  simp only [pow_add,pow_succ] at hs ⊢
  linear_combination -((2:ℚ)^(i/2)*(2:ℚ)^(j/2)*(-1)^(i%2)*(-1)^(j%2)*
    ((i/2+j/2).factorial:ℚ))*hs

 theorem endpoint_pair_sign (r s c e f : ℕ) :
    (-1:ℚ)^(r+s+(c+r+e)%2+(c+s+f)%2)=(-1)^(e+f) := by
  rw [neg_one_pow_eq_pow_mod_two,neg_one_pow_eq_pow_mod_two (R := ℚ) (e+f)]
  congr 1
  omega

 theorem endpointEntry_index_eval_zero (r s c e f : ℕ) :
    (endpointEntry (2*r+(c+r+e)%2) (2*s+(c+s+f)%2)).eval 0=
      (-2:ℚ)^r*(-2)^s*(1+(-1)^(e+f))*((r+s).factorial:ℚ) := by
  have hr : (2*r+(c+r+e)%2)/2=r := by omega
  have hs : (2*s+(c+s+f)%2)/2=s := by omega
  have hrm : (2*r+(c+r+e)%2)%2=(c+r+e)%2 := by omega
  have hsm : (2*s+(c+s+f)%2)%2=(c+s+f)%2 := by omega
  rw [endpointEntry_eval_zero_factored,hr,hs,hrm,hsm,endpoint_pair_sign]

 def laguerreConstant (n : ℕ) : ℚ := ∏ j : Fin n, (j.val.factorial:ℚ)^2

 theorem vandermonde_successive_det (n : ℕ) :
    (Matrix.vandermonde (fun i : Fin n => (i.val:ℚ)+1)).det=
      ∏ i : Fin n,(i.val.factorial:ℚ) := by
  rw [Matrix.det_vandermonde_add (fun i : Fin n => (i.val:ℚ)) 1]
  cases n with
  | zero => simp [Matrix.det_isEmpty]
  | succ n =>
    rw [Matrix.det_vandermonde_id_eq_superFactorial,
      Fin.prod_univ_eq_prod_range (fun i : ℕ => (i.factorial:ℚ)) (n+1)]
    norm_cast
    exact (Nat.prod_range_succ_factorial n).symm

 theorem factorialMoment_det (n : ℕ) :
    Matrix.det (Matrix.of (fun i j : Fin n => ((i.val+j.val).factorial:ℚ)))=
      laguerreConstant n := by
  let v : Fin n → ℚ := fun i => (i.val:ℚ)+1
  let p : Fin n → ℚ[X] := fun j => ascPochhammer ℚ j.val
  let E : Matrix (Fin n) (Fin n) ℚ := Matrix.of (fun i j => (p j).eval (v i))
  have hE : E.det=(Matrix.vandermonde v).det :=
    (Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v p
      (fun j => ascPochhammer_natDegree ℚ j.val) (fun j => monic_ascPochhammer ℚ j.val)).symm
  have he : Matrix.of (fun i j : Fin n => ((i.val+j.val).factorial:ℚ))=
      Matrix.of (fun i j : Fin n => (i.val.factorial:ℚ)*E i j) := by
    apply Matrix.ext
    intro i j
    dsimp [E,p,v]
    rw [show (i.val:ℚ)+1=((i.val+1:ℕ):ℚ) by norm_cast,
      ascPochhammer_nat_eq_natCast_ascFactorial]
    exact_mod_cast (Nat.factorial_mul_ascFactorial i.val j.val).symm
  rw [he,Matrix.det_mul_column,hE,vandermonde_successive_det]
  unfold laguerreConstant
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  ring

 theorem laguerreConstant_pos (n : ℕ) : 0<laguerreConstant n := by
  apply Finset.prod_pos
  intro i hi
  positivity

@[simp] theorem laguerreConstant_zero : laguerreConstant 0=1 := by simp [laguerreConstant]

 theorem laguerreConstant_succ (n : ℕ) :
    laguerreConstant (n+1)=laguerreConstant n*(n.factorial:ℚ)^2 := by
  simp [laguerreConstant,Fin.prod_univ_castSucc]

end OscillatoryRecurrence
