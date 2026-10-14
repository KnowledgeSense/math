import Fan.TrailingCut

namespace Fan
open scoped Classical

theorem trailing_left_endsNonhub {m r : ℕ} (p : Configuration (m+r))
    (hcut : trailingCut p=m) :
    EndsNonhub (⟨leftPair p.val,p.property.left_valid⟩ : Configuration m) := by
  intro i hi hs
  apply trailingCut_endpoint p (i.castAdd r) (by simpa only [Fin.val_castAdd,hcut] using hi)
  exact (mem_leftSet p.val.1 i).mp hs

theorem trailing_right_spokes {m r : ℕ} (p : Configuration (m+r))
    (hcut : trailingCut p=m) (j : Fin r) : j.natAdd m∈p.val.1 := by
  apply spoke_of_trailingCut_le
  rw [hcut]
  change m ≤ m+j.val
  omega

theorem trailing_gap {m r : ℕ} (p : Configuration (m+r)) (hcut : trailingCut p=m) :
    ∀ j : Fin r, j.val=0 → j.natAdd m∉p.val.2 := by
  intro j hj hr
  by_cases hm : m=0
  · have hpos := p.property.1 (j.natAdd m) hr
    simp only [Fin.val_natAdd,hm,hj] at hpos
    omega
  · let i : Fin (m+r) := ⟨m-1,by have := j.isLt; omega⟩
    have hij : i.val+1=(j.natAdd m).val := by dsimp [i]; omega
    have hi : i.val+1=trailingCut p := by dsimp [i]; omega
    exact trailingCut_endpoint p i hi
      (((p.property.2 i (j.natAdd m) hij).1 hr).mpr (trailing_right_spokes p hcut j))

theorem trailing_right_top {m r : ℕ} (p : Configuration (m+r)) (hcut : trailingCut p=m) :
    (⟨rightPair p.val,p.property.right_valid (trailing_gap p hcut)⟩ : Configuration r)=⊤ := by
  apply configuration_eq_top_of_spokes
  intro j
  exact (mem_rightSet p.val.1 j).mpr (trailing_right_spokes p hcut j)

noncomputable def trailingPrefix {m r : ℕ} (p : Configuration (m+r)) : Configuration m :=
  ⟨leftPair p.val,p.property.left_valid⟩

theorem trailing_split {m r : ℕ} (p : Configuration (m+r)) (hcut : trailingCut p=m) :
    joinedConfiguration (trailingPrefix p) (⊤ : Configuration r)
      ((trailing_left_endsNonhub p hcut).compatible ⊤)=p := by
  apply Subtype.ext
  change joinPair (leftPair p.val) (⊤ : Configuration r).val=p.val
  have he := congrArg Subtype.val (trailing_right_top p hcut)
  change rightPair p.val=(⊤ : Configuration r).val at he
  rw [← he,joinPair_left_right]

theorem trailingCut_join_top {m r : ℕ} (p : Configuration m) (hp : EndsNonhub p) :
    trailingCut (joinedConfiguration p (⊤ : Configuration r) (hp.compatible ⊤))=m := by
  let z := joinedConfiguration p (⊤ : Configuration r) (hp.compatible ⊤)
  have hle : trailingCut z ≤ m := by
    apply Finset.sup_le
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j _
      change j.val+1 ≤ m
      have := j.isLt
      omega
    · intro j hj
      have hnot := (mem_nonhubVertices z (j.natAdd m)).mp hj
      exact False.elim (hnot ((mem_join_right p.val.1 (⊤ : Configuration r).val.1 j).mpr (top_spoke j)))
  apply Nat.le_antisymm hle
  cases m with
  | zero => exact Nat.zero_le _
  | succ m =>
    apply nonhub_le_trailingCut z (i:=(Fin.last m).castAdd r)
    intro h
    exact hp (Fin.last m) rfl ((mem_join_left p.val.1 (⊤ : Configuration r).val.1 (Fin.last m)).mp h)

theorem configuration_zero_eq (p : Configuration 0) : p=⊥ := by
  apply Subtype.ext
  rw [configuration_bot_val]
  apply Prod.ext <;> apply Finset.eq_empty_iff_forall_notMem.mpr <;> intro i <;> exact Fin.elim0 i

@[simp] theorem Q_zero : Q 0=1 := by
  unfold Q
  rw [configuration_zero_eq (⊤ : Configuration 0),MatroidInverseZ.inverseKL_self]

@[simp] theorem inverseZ_zero : inverseZ 0=1 := by
  rw [inverseZ_configuration]
  change MatroidInverseZ.inverseZ configurationRank (⊥ : Configuration 0) ⊤=1
  rw [configuration_zero_eq (⊤ : Configuration 0),MatroidInverseZ.inverseZ_self]

@[simp] theorem joinedConfiguration_zero (p : Configuration m) (q : Configuration 0)
    (hc : Compatible p.val q.val) : joinedConfiguration p q hc=p := by
  apply Subtype.ext
  apply Prod.ext
  · ext i
    exact mem_join_left p.val.1 q.val.1 i
  · ext i
    exact mem_join_left p.val.2 q.val.2 i

end Fan
