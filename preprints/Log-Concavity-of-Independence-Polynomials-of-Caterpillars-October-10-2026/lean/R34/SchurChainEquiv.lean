import R34.SchurUniform
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

namespace R34

open MvPolynomial
open scoped BigOperators

def chainWeight (n : ℕ) (coupling : Fin n → ℝ) (χ : Fin (n+1) → Bool) : Poly :=
  (∏ i : Fin (n+1), color (χ i)) *
    C (∏ e : Fin n, edgeWeight (coupling e) (χ e.castSucc) (χ e.succ))

theorem isingChain_eq_sum_weight (n : ℕ) (coupling : Fin n → ℝ) :
    isingChain (n+1) coupling = ∑ χ : Fin (n+1) → Bool, chainWeight n coupling χ := by
  rfl

theorem sum_colors_succ (n : ℕ) (F : (Fin (n+1) → Bool) → Poly) :
    (∑ χ, F χ) = ∑ a : Bool, ∑ χ : Fin n → Bool, F (Fin.cons a χ) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp F]
  simp [Fintype.sum_prod_type, Fin.consEquiv]

theorem chainWeight_cons (n : ℕ) (coupling : Fin (n+1) → ℝ)
    (a : Bool) (χ : Fin (n+1) → Bool) :
    chainWeight (n+1) coupling (Fin.cons a χ) =
      color a*C (edgeWeight (coupling 0) a (χ 0))*
        chainWeight n (fun e => coupling e.succ) χ := by
  simp only [chainWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero,
    Fin.cons_succ, Fin.castSucc_succ, C_mul]
  ring

def fixedChainSum (n : ℕ) (coupling : Fin n → ℝ) (a : Bool) : Poly :=
  ∑ χ : Fin n → Bool, chainWeight n coupling (Fin.cons a χ)

theorem fixedChainSum_zero (coupling : Fin 0 → ℝ) (a : Bool) :
    fixedChainSum 0 coupling a=color a := by simp [fixedChainSum, chainWeight]

theorem fixedChainSum_succ (n : ℕ) (coupling : Fin (n+1) → ℝ) (a : Bool) :
    fixedChainSum (n+1) coupling a=
      color a*(∑ b : Bool, C (edgeWeight (coupling 0) a b)*
        fixedChainSum n (fun e => coupling e.succ) b) := by
  unfold fixedChainSum
  rw [sum_colors_succ]
  simp only [chainWeight_cons, Fin.cons_zero]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro χ hχ
  ring

theorem colorDiag_mul_apply (A : ColorMatrix) (a b : Bool) :
    (colorDiag*A) a b=color a*A a b := by
  cases a <;> cases b <;> simp [Matrix.mul_apply, colorDiag]

theorem chainMatrix_cons_apply (couplingScalar : ℝ) (l : List ℝ) (a b : Bool) :
    chainMatrix (couplingScalar::l) a b =
      color a*(∑ c : Bool, C (edgeWeight couplingScalar a c)*chainMatrix l c b) := by
  rw [chainMatrix_cons, Matrix.mul_assoc, colorDiag_mul_apply, Matrix.mul_apply]
  rfl

theorem chainMatrix_rowSum (n : ℕ) (coupling : Fin n → ℝ) (a : Bool) :
    (∑ b : Bool, chainMatrix (List.ofFn coupling) a b)=fixedChainSum n coupling a := by
  induction n generalizing a with
  | zero => simp [List.ofFn_zero, chainMatrix_nil, colorDiag, fixedChainSum_zero]
  | succ n ih =>
    rw [List.ofFn_succ, fixedChainSum_succ]
    simp only [chainMatrix_cons_apply]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ih]

def endpointChainSum (n : ℕ) (coupling : Fin n → ℝ) (a b : Bool) : Poly :=
  ∑ χ : Fin n → Bool, chainWeight n coupling (Fin.cons a χ)*
    (if (Fin.cons a χ : Fin (n+1) → Bool) (Fin.last n)=b then 1 else 0)

theorem endpointChainSum_zero (coupling : Fin 0 → ℝ) (a b : Bool) :
    endpointChainSum 0 coupling a b=colorDiag a b := by
  simp [endpointChainSum, chainWeight, colorDiag, mul_ite]

theorem endpointChainSum_succ (n : ℕ) (coupling : Fin (n+1) → ℝ) (a b : Bool) :
    endpointChainSum (n+1) coupling a b =
      color a*(∑ c : Bool, C (edgeWeight (coupling 0) a c)*
        endpointChainSum n (fun e => coupling e.succ) c b) := by
  unfold endpointChainSum
  rw [sum_colors_succ]
  simp only [chainWeight_cons, Fin.cons_zero, Fin.cons_last, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro χ hχ
  ring

theorem chainMatrix_endpointSum (n : ℕ) (coupling : Fin n → ℝ) (a b : Bool) :
    chainMatrix (List.ofFn coupling) a b=endpointChainSum n coupling a b := by
  induction n generalizing a b with
  | zero => simp [endpointChainSum_zero]
  | succ n ih =>
    rw [List.ofFn_succ, chainMatrix_cons_apply, endpointChainSum_succ]
    simp only [ih]

theorem chainMatrix_terminal_sum (n : ℕ) (coupling : Fin n → ℝ) (g : Bool → Poly) :
    (∑ χ : Fin (n+1) → Bool, chainWeight n coupling χ*g (χ (Fin.last n))) =
      ∑ a : Bool, ∑ b : Bool, chainMatrix (List.ofFn coupling) a b*g b := by
  rw [sum_colors_succ]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [chainMatrix_endpointSum, endpointChainSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  cases hl : (Fin.cons a χ : Fin (n+1) → Bool) (Fin.last n) <;> simp

theorem isingChain_eq_listChain (n : ℕ) (coupling : Fin n → ℝ) :
    isingChain (n+1) coupling=listChain (List.ofFn coupling) := by
  rw [isingChain_eq_sum_weight, sum_colors_succ]
  simp only [listChain, matrixTotal, chainMatrix_rowSum, fixedChainSum]

theorem isingChain_schurPositive (n : ℕ) (coupling : Fin (n-1) → ℝ)
    (hcoupling : ∀ e, 0 ≤ coupling e ∧ coupling e ≤ 2) :
    SchurPositive (isingChain n coupling) := by
  cases n with
  | zero => simpa using schurPositive_one
  | succ n =>
    rw [isingChain_eq_listChain]
    apply listChain_schurPositive_of_uniform uniform_chain_schurPositive
    intro x hx
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hx
    exact hcoupling e

end R34







