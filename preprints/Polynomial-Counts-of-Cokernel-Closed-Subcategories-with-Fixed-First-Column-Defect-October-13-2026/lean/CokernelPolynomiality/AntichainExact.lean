import CokernelPolynomiality.AntichainQuotient

noncomputable section
namespace CokernelPolynomiality

def antichainSource {m : ℕ} (a b : ℕ) (c d : Fin (m+1) → ℕ) (i : ℕ) :
    intervalSpace a b i →ₗ[ℂ] (∀ j, intervalSpace (c j) (d j) i) :=
  LinearMap.pi (fun j => intervalComponent a b (c j) (d j) i)

@[simp] theorem antichainSource_val {m : ℕ} (a b : ℕ) (c d : Fin (m+1) → ℕ)
    (i : ℕ) (x : intervalSpace a b i) (j : Fin (m+1)) :
    (antichainSource a b c d i x j).val=if intervalActive (c j) (d j) i then x.val else 0 :=
  intervalComponent_val a b (c j) (d j) i x

theorem antichainQuotient_exact {m : ℕ} (a b : ℕ) (c d : Fin (m+1) → ℕ) (i : ℕ)
    (hc : Monotone c) (hac : ∀ j, a ≤ c j) (hcb : ∀ j, c j ≤ b) (hbd : ∀ j, b ≤ d j) :
    Function.Exact (antichainSource a b c d i) (antichainQuotient b c d i) := by
  intro y
  constructor
  · intro hy
    have hzero (j : Fin (m+1)) : (antichainQuotient b c d i y j).val=0 :=
      congrArg (fun z => (z j).val) hy
    by_cases hib : i ≤ b
    · have heq : ∀ j, intervalActive (c j) (d j) i → (y j).val=(y 0).val := by
        intro j
        induction j using Fin.induction with
        | zero => intro _; rfl
        | succ j ih =>
          intro hj
          have hp : intervalActive (c j.castSucc) (d j.castSucc) i :=
            ⟨(hc (by change j.val ≤ j.val+1; omega)).trans hj.1,hib.trans (hbd _)⟩
          have ho : intervalActive (c j.succ) (d j.castSucc) i := ⟨hj.1,hib.trans (hbd _)⟩
          have hh := hzero j.castSucc
          rw [antichainQuotient_castSucc,ite_eq_left ho] at hh
          exact (sub_eq_zero.mp hh).symm.trans (ih hp)
      by_cases h0 : c 0 ≤ i
      · have hs : intervalActive a b i := ⟨(hac 0).trans h0,hib⟩
        refine ⟨⟨(y 0).val,by simp [intervalSpace,hs]⟩,?_⟩
        funext j
        apply Subtype.ext
        rw [antichainSource_val]
        by_cases hj : intervalActive (c j) (d j) i
        · rw [ite_eq_left hj]
          exact (heq j hj).symm
        · rw [ite_eq_right hj]
          exact (intervalSpace_val_zero hj (y j)).symm
      · refine ⟨0,?_⟩
        rw [map_zero]
        funext j
        apply Subtype.ext
        apply Eq.symm
        apply intervalSpace_val_zero
        intro hj
        exact h0 ((hc (Fin.zero_le j)).trans hj.1)
    · have hall : ∀ j, (y j).val=0 := by
        intro j
        induction j using Fin.reverseInduction with
        | last =>
          by_cases hj : intervalActive (c (Fin.last m)) (d (Fin.last m)) i
          · have ht : intervalActive (b+1) (d (Fin.last m)) i := ⟨by omega,hj.2⟩
            have hh := hzero (Fin.last m)
            rwa [antichainQuotient_last,ite_eq_left ht] at hh
          · exact intervalSpace_val_zero hj (y (Fin.last m))
        | cast j ih =>
          by_cases hj : intervalActive (c j.castSucc) (d j.castSucc) i
          · have ho : intervalActive (c j.succ) (d j.castSucc) i :=
              ⟨le_trans (hcb j.succ) (by omega),hj.2⟩
            have hh := hzero j.castSucc
            rwa [antichainQuotient_castSucc,ite_eq_left ho,ih,sub_zero] at hh
          · exact intervalSpace_val_zero hj (y j.castSucc)
      refine ⟨0,?_⟩
      rw [map_zero]
      funext j
      exact Subtype.ext (hall j).symm
  · rintro ⟨x,rfl⟩
    by_cases hib : i ≤ b
    · funext j
      apply Subtype.ext
      induction j using Fin.lastCases with
      | last =>
        rw [antichainQuotient_last,ite_eq_right (by unfold intervalActive; omega)]
        rfl
      | cast j =>
        rw [antichainQuotient_castSucc]
        by_cases ho : intervalActive (c j.succ) (d j.castSucc) i
        · have hp : intervalActive (c j.castSucc) (d j.castSucc) i :=
            ⟨(hc (by change j.val ≤ j.val+1; omega)).trans ho.1,ho.2⟩
          have hn : intervalActive (c j.succ) (d j.succ) i := ⟨ho.1,hib.trans (hbd _)⟩
          rw [ite_eq_left ho,antichainSource_val,antichainSource_val,
            ite_eq_left hp,ite_eq_left hn,sub_self]
          rfl
        · rw [ite_eq_right ho]
          rfl
    · have hs : ¬intervalActive a b i := by unfold intervalActive; omega
      have hx : x=0 := Subtype.ext (intervalSpace_val_zero hs x)
      rw [hx,map_zero,map_zero]

end CokernelPolynomiality
