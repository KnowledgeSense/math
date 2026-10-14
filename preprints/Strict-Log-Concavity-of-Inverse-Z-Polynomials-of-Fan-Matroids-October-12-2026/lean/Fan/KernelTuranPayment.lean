import Fan.KernelTuranBoundary

noncomputable section
open scoped BigOperators Classical
namespace Fan

private def paymentEmbedding (U V : ℕ) (hUV : V+1≤U) :
    Fin (V+1) × Fin (U+2) ↪ Fin (U+1) × Fin (V+2) where
  toFun x := if h : x.2.val≤V+1 then
    (⟨x.1.val,by have := x.1.isLt; omega⟩,⟨x.2.val,by omega⟩)
    else (⟨x.2.val-1,by have := x.2.isLt; omega⟩,⟨x.1.val+1,by have := x.1.isLt; omega⟩)
  inj' := by
    intro x y he
    dsimp only at he
    split_ifs at he with hx hy
    all_goals
      have h1 := congrArg (fun t : Fin (U+1) × Fin (V+2) => t.1.val) he
      have h2 := congrArg (fun t : Fin (U+1) × Fin (V+2) => t.2.val) he
      have hx1 := x.1.isLt
      have hx2 := x.2.isLt
      have hy1 := y.1.isLt
      have hy2 := y.2.isLt
      dsimp only at h1 h2
      apply Prod.ext <;> apply Fin.ext <;> omega

private theorem paymentEmbedding_omit (U V : ℕ) (hUV : V+1≤U) :
    (⟨U,by omega⟩,0) ∉ Finset.univ.map (paymentEmbedding U V hUV) := by
  simp only [Finset.mem_map,Finset.mem_univ,true_and,not_exists]
  intro x he
  change (paymentEmbedding U V hUV).toFun x = _ at he
  dsimp only [paymentEmbedding] at he
  split_ifs at he
  all_goals
    have h1 := congrArg (fun t : Fin (U+1) × Fin (V+2) => t.1.val) he
    have h2 := congrArg (fun t : Fin (U+1) × Fin (V+2) => t.2.val) he
    have := x.1.isLt
    simp only [Fin.val_zero] at *
    omega

theorem boundaryArray_fin_sum (A B rho : ℕ → ℝ) (a b : ℕ) :
    boundaryArray A B rho a b=
      ∑ x : Fin (a+1) × Fin (b+1),A x.1*B x.2*rho (a+b-x.1-x.2) := by
  rw [Fintype.sum_prod_type]
  simp only [boundaryArray,Finset.sum_range]

/-- The subtraction is paid by an injective matching of the rectangle terms,
leaving a strictly positive boundary term unmatched. -/
theorem boundaryArray_payment (A B rho : ℕ → ℝ)
    (hA : ∀ i,0<A i) (hB : ∀ i,0<B i) (hrho : ∀ i,0<rho i)
    (hcross : ∀ i j,j < i → A j*B (i+1)<A i*B (j+1))
    (U V : ℕ) (hUV : V+1≤U) :
    boundaryArray A B rho V (U+1)<boundaryArray A B rho U (V+1) := by
  let L : Fin (U+1) × Fin (V+2) → ℝ :=
    fun x => A x.1*B x.2*rho (U+V+1-x.1-x.2)
  let R : Fin (V+1) × Fin (U+2) → ℝ :=
    fun x => A x.1*B x.2*rho (U+V+1-x.1-x.2)
  have hle (x : Fin (V+1) × Fin (U+2)) : R x≤L (paymentEmbedding U V hUV x) := by
    change R x ≤ L ((paymentEmbedding U V hUV).toFun x)
    dsimp only [R,L,paymentEmbedding]
    split_ifs with h
    · exact le_rfl
    · have hx1 := x.1.isLt
      have hx2 := x.2.isLt
      have hc := hcross (x.2.val-1) x.1.val (by omega)
      have he : x.2.val-1+1=x.2.val := by omega
      rw [he] at hc
      have hi : U+V+1-(x.2.val-1)-(x.1.val+1)=U+V+1-x.1.val-x.2.val := by omega
      rw [hi]
      exact (mul_lt_mul_of_pos_right hc (hrho _)).le
  have hpos (x : Fin (U+1) × Fin (V+2)) : 0<L x :=
    mul_pos (mul_pos (hA _) (hB _)) (hrho _)
  have hs : (∑ x,R x)<∑ x,L x := calc
    (∑ x,R x) ≤ ∑ x,L (paymentEmbedding U V hUV x) := Finset.sum_le_sum fun x _ => hle x
    _ = ∑ x∈Finset.univ.map (paymentEmbedding U V hUV),L x := by rw [Finset.sum_map]
    _ < ∑ x,L x := by
      apply Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ (⟨U,by omega⟩,0))
        (paymentEmbedding_omit U V hUV) (hpos _) (fun x _ _ => (hpos x).le)
  simpa only [boundaryArray_fin_sum,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,L,R] using hs

theorem boundaryExtended_payment (A B rho : ℕ → ℝ)
    (hA : ∀ i,0<A i) (hB : ∀ i,0<B i) (hrho : ∀ i,0<rho i)
    (hcross : ∀ i j,j < i → A j*B (i+1)<A i*B (j+1))
    (U V : ℕ) (hUV : V≤U) :
    0<boundaryExtended A B rho U V-boundaryExtended A B rho ((V:ℤ)-1) (U+1) := by
  cases V with
  | zero =>
    simp only [Nat.cast_zero,zero_sub]
    have hz : boundaryExtended A B rho (-1) (U+1)=0 := by simp [boundaryExtended]
    rw [hz,sub_zero]
    change 0<boundaryExtended A B rho (U:ℤ) ((0:ℕ):ℤ)
    rw [boundaryExtended_nat,boundaryArray_zero_right]
    apply mul_pos (hB 0)
    apply Finset.sum_pos'
    · intro i _; exact (mul_pos (hA i) (hrho _)).le
    · exact ⟨0,by simp,by exact mul_pos (hA 0) (hrho _)⟩
  | succ V =>
    have hv : ((V+1:ℕ):ℤ)-1=V := by omega
    have hu : (U:ℤ)+1=(U+1:ℕ) := by omega
    rw [hv,hu,boundaryExtended_nat,boundaryExtended_nat]
    exact sub_pos.mpr (boundaryArray_payment A B rho hA hB hrho hcross U V hUV)

end Fan
