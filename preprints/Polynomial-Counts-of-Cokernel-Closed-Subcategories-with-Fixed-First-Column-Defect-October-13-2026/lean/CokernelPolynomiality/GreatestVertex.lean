import CokernelPolynomiality.OrderRestriction

namespace CokernelPolynomiality

variable {V : Type*} [LinearOrder V]

 theorem admissible_of_delete_greatest (G : SimpleGraph V) (a : V)
    (hmax : ∀ v, v ≤ a) (ha : ∀ v, v ≠ a → G.Adj v a)
    (hG : Admissible (G.comap (Subtype.val : {v : V // v ≠ a} → V))) :
    Admissible G := by
  constructor
  · intro s t x y hst hxy hsx hxt hty
    by_cases hya : y = a
    · subst y
      exact ha t (ne_of_lt hty)
    · have hya' : y < a := lt_of_le_of_ne (hmax y) hya
      let s' : {v : V // v ≠ a} := ⟨s,by order⟩
      let t' : {v : V // v ≠ a} := ⟨t,by order⟩
      let x' : {v : V // v ≠ a} := ⟨x,by order⟩
      let y' : {v : V // v ≠ a} := ⟨y,hya⟩
      exact hG.1 s' t' x' y' hst hxy hsx hxt hty
  · intro s t x y z w hst hxy hzw hsx hxt hty hsz hzt htw
    have hsep : max x z < max y w := lt_of_lt_of_le (max_lt hxt hzt)
      (le_trans hty (le_max_left y w))
    by_cases hya : max y w = a
    · rw [hya] at hsep ⊢
      exact ha (max x z) (ne_of_lt hsep)
    · have hywa : max y w < a := lt_of_le_of_ne (hmax _) hya
      have hya' : y < a := lt_of_le_of_lt (le_max_left y w) hywa
      have hwa' : w < a := lt_of_le_of_lt (le_max_right y w) hywa
      let s' : {v : V // v ≠ a} := ⟨s,by order⟩
      let t' : {v : V // v ≠ a} := ⟨t,by order⟩
      let x' : {v : V // v ≠ a} := ⟨x,by order⟩
      let y' : {v : V // v ≠ a} := ⟨y,ne_of_lt hya'⟩
      let z' : {v : V // v ≠ a} := ⟨z,by order⟩
      let w' : {v : V // v ≠ a} := ⟨w,ne_of_lt hwa'⟩
      exact hG.2 s' t' x' y' z' w' hst hxy hzw hsx hxt hty hsz hzt htw

 theorem admissible_iff_delete_greatest (G : SimpleGraph V) (a : V)
    (hmax : ∀ v, v ≤ a) (ha : ∀ v, v ≠ a → G.Adj v a) :
    Admissible G ↔ Admissible (G.comap (Subtype.val : {v : V // v ≠ a} → V)) := by
  constructor
  · intro hG
    exact admissible_comap G hG _ (fun _ _ h => h)
  · exact admissible_of_delete_greatest G a hmax ha

end CokernelPolynomiality
