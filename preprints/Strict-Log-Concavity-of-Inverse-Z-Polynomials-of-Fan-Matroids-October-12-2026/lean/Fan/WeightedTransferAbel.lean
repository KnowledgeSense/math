import Fan.KernelTuranRows

noncomputable section
open scoped BigOperators
namespace Fan

def weightIncrement (x : ℕ → ℝ) (R : ℕ) : ℕ → ℝ
  | 0 => x 0*x R
  | h+1 => x (h+1)*x (R-(h+1))-x h*x (R-h)

theorem weightIncrement_sum (x : ℕ → ℝ) (R M : ℕ) :
    ∑ h∈Finset.range (M+1),weightIncrement x R h=x M*x (R-M) := by
  induction M with
  | zero => simp [weightIncrement]
  | succ M ih =>
    rw [Finset.sum_range_succ,ih,weightIncrement]
    ring

theorem weightIncrement_nonneg (x : ℕ → ℝ) (hx : ∀ i,0 ≤ x i)
    (hp : ∀ R r,2*r+2 ≤ R → x r*x (R-r) ≤ x (r+1)*x (R-r-1))
    (R h : ℕ) (hh : 2*h ≤ R) : 0 ≤ weightIncrement x R h := by
  cases h with
  | zero => exact mul_nonneg (hx 0) (hx R)
  | succ h =>
    rw [weightIncrement]
    apply sub_nonneg.mpr
    simpa only [Nat.sub_sub] using hp R h (by omega)

theorem weightPair_expansion (x : ℕ → ℝ) (N i j : ℕ) (hi : i ≤ N) (_hj : j ≤ N) :
    (∑ h∈Finset.range (N+1),if h ≤ i ∧ h ≤ j then weightIncrement x (i+j) h else 0)=x i*x j := by
  have hm : min i j ≤ N := (min_le_left _ _).trans hi
  have he : (∑ h∈Finset.range (N+1),if h ≤ i ∧ h ≤ j then weightIncrement x (i+j) h else 0)=
      ∑ h∈Finset.range (min i j+1),if h ≤ i ∧ h ≤ j then weightIncrement x (i+j) h else 0 := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro h hh hn
    have hnot : ¬(h ≤ i ∧ h ≤ j) := by
      have := Finset.mem_range.mp hh
      simp only [Finset.mem_range,not_lt] at hn
      omega
    exact ite_eq_right hnot
  rw [he]
  have hf : (∑ h∈Finset.range (min i j+1),if h ≤ i ∧ h ≤ j then weightIncrement x (i+j) h else 0)=
      ∑ h∈Finset.range (min i j+1),weightIncrement x (i+j) h := by
    apply Finset.sum_congr rfl
    intro h hh
    have := Finset.mem_range.mp hh
    exact ite_eq_left (by omega)
  rw [hf,weightIncrement_sum]
  by_cases hij : i ≤ j
  · rw [min_eq_left hij,show i+j-i=j by omega]
  · rw [min_eq_right (by omega),show i+j-j=i by omega,mul_comm]

def quadraticTail {N : ℕ} (M : Fin (N+1) → Fin (N+1) → ℝ) (R h : ℕ) : ℝ :=
  ∑ i,∑ j,if i.val+j.val=R ∧ h ≤ i.val ∧ h ≤ j.val then M i j else 0

theorem quadraticTail_empty {N : ℕ} (M : Fin (N+1) → Fin (N+1) → ℝ)
    (R h : ℕ) (hh : R < 2*h) : quadraticTail M R h=0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  exact ite_eq_right (by omega)

theorem quadraticTail_zero {N : ℕ} (M : Fin (N+1) → Fin (N+1) → ℝ) :
    quadraticTail M 0 0=M 0 0 := by
  unfold quadraticTail
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    have hn : i.val+j.val≠0 := by
      intro h
      apply hi
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    simp only [ite_eq_right (by omega : ¬(i.val+j.val=0 ∧ 0 ≤ i.val ∧ 0 ≤ j.val))]
  · simp

/-- Finite Abel decomposition by total index and simultaneous lower truncation. -/
theorem weighted_quadratic_decomposition {N : ℕ}
    (M : Fin (N+1) → Fin (N+1) → ℝ) (x : ℕ → ℝ) :
    (∑ i,∑ j,M i j*x i*x j) =
      ∑ R∈Finset.range (2*N+1),∑ h∈Finset.range (N+1),weightIncrement x R h*quadraticTail M R h := by
  symm
  simp only [quadraticTail,Finset.mul_sum]
  conv_lhs => arg 2; ext R; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; arg 2; ext R; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (i.val+j.val)]
  · have he (h : ℕ) : weightIncrement x (i.val+j.val) h*
        (if i.val+j.val=i.val+j.val ∧ h ≤ i.val ∧ h ≤ j.val then M i j else 0) =
        M i j*(if h ≤ i.val ∧ h ≤ j.val then weightIncrement x (i.val+j.val) h else 0) := by
      split_ifs  <;> simp_all [mul_comm]
    rw [Finset.sum_congr rfl (fun h _ => he h),← Finset.mul_sum]
    rw [weightPair_expansion x N i j (by have := i.isLt; omega) (by have := j.isLt; omega)]
    ring
  · intro R _ hR
    apply Finset.sum_eq_zero
    intro h _
    have hn : i.val+j.val≠R := Ne.symm hR
    simp [hn]
  · have hm : i.val+j.val∈Finset.range (2*N+1) := by
      have := i.isLt
      have := j.isLt
      simp only [Finset.mem_range]
      omega
    simp [hm]

theorem weighted_quadratic_pos {N : ℕ}
    (M : Fin (N+1) → Fin (N+1) → ℝ) (x : ℕ → ℝ)
    (hx : ∀ i,0 ≤ x i) (hx0 : 0 < x 0)
    (hp : ∀ R r,2*r+2 ≤ R → x r*x (R-r) ≤ x (r+1)*x (R-r-1))
    (hM : ∀ R h,0 ≤ quadraticTail M R h) (hM0 : 0 < M 0 0) :
    0 < ∑ i,∑ j,M i j*x i*x j := by
  rw [weighted_quadratic_decomposition]
  have hnonneg (R h : ℕ) : 0 ≤ weightIncrement x R h*quadraticTail M R h := by
    by_cases hh : 2*h ≤ R
    · exact mul_nonneg (weightIncrement_nonneg x hx hp R h hh) (hM R h)
    · rw [quadraticTail_empty M R h (by omega),mul_zero]
  apply Finset.sum_pos'
  · intro R _
    exact Finset.sum_nonneg fun h _ => hnonneg R h
  · refine ⟨0,by simp,?_⟩
    apply Finset.sum_pos'
    · intro h _; exact hnonneg 0 h
    · refine ⟨0,by simp,?_⟩
      rw [weightIncrement,quadraticTail_zero]
      exact mul_pos (mul_pos hx0 hx0) hM0

end Fan
