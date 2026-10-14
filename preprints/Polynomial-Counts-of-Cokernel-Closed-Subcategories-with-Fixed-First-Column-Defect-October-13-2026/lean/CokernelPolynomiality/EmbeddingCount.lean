import CokernelPolynomiality.CodeCounting

namespace CokernelPolynomiality
noncomputable section

variable {q m : ℕ}

 def addZeroEmbedding (f : Fin q ↪o Fin m) : ZeroEmbedding q m := by
  let g : Fin (q+1) → Fin (m+1) := Fin.cases 0 (fun j => (f j).succ)
  have hg : StrictMono g := by
    intro a b hab
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact False.elim ((lt_irrefl _) hab)
      | succ b => exact Fin.succ_pos _
    | succ a =>
      cases b using Fin.cases with
      | zero => exact False.elim (Fin.not_lt_zero _ hab)
      | succ b => exact Fin.succ_lt_succ_iff.mpr (f.strictMono (Fin.succ_lt_succ_iff.mp hab))
  exact ⟨OrderEmbedding.ofStrictMono g hg,rfl⟩

 def dropZeroEmbedding (e : ZeroEmbedding q m) : Fin q ↪o Fin m :=
  OrderEmbedding.ofStrictMono
    (fun j => ⟨(e.val j.succ).val-1,by
      have hp : (0 : Fin (m+1)) < e.val j.succ := by
        simpa only [e.property] using e.val.strictMono (Fin.succ_pos j)
      have hb := (e.val j.succ).isLt
      omega⟩)
    (by
      intro j k hjk
      have hh := e.val.strictMono (Fin.succ_lt_succ_iff.mpr hjk)
      have hp : (0 : Fin (m+1)) < e.val j.succ := by
        simpa only [e.property] using e.val.strictMono (Fin.succ_pos j)
      change (e.val j.succ).val-1 < (e.val k.succ).val-1
      omega)

 theorem drop_add_zero (f : Fin q ↪o Fin m) : dropZeroEmbedding (addZeroEmbedding f) = f := by
  ext j
  rfl

 theorem add_drop_zero (e : ZeroEmbedding q m) : addZeroEmbedding (dropZeroEmbedding e) = e := by
  apply Subtype.ext
  ext j
  cases j using Fin.cases with
  | zero => exact congrArg Fin.val e.property.symm
  | succ j =>
    change (e.val j.succ).val-1+1 = (e.val j.succ).val
    have hp : (0 : Fin (m+1)) < e.val j.succ := by
      simpa only [e.property] using e.val.strictMono (Fin.succ_pos j)
    omega

 def zeroEmbeddingEquiv : ZeroEmbedding q m ≃ (Fin q ↪o Fin m) where
  toFun := dropZeroEmbedding
  invFun := addZeroEmbedding
  left_inv := add_drop_zero
  right_inv := drop_add_zero

 theorem card_zeroEmbedding (q m : ℕ) : Nat.card (ZeroEmbedding q m) = m.choose q := by
  rw [Nat.card_congr zeroEmbeddingEquiv,
    Nat.card_congr (Set.powersetCard.ofFinEmbEquiv (n := q) (I := Fin m)),
    Set.powersetCard.card]
  simp

 theorem codeCount_binomial_formula (i m : ℕ) :
    codeCount i m = ∑ q : Fin (2*i+1), templateCount i q * m.choose q := by
  rw [codeCount_sum_embeddings]
  apply Finset.sum_congr rfl
  intro q _
  rw [card_zeroEmbedding,mul_comm]

end
end CokernelPolynomiality
