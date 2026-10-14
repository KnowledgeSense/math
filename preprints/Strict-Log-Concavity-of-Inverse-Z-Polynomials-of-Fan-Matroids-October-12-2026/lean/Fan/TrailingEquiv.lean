import Fan.TrailingSplit

namespace Fan
open scoped Classical

abbrev NonhubConfiguration (n : ℕ) := {p : Configuration n // EndsNonhub p}
abbrev Trailing (n : ℕ) := Σ m : Fin (n+1), NonhubConfiguration m.val

noncomputable def trailingAssemble (n : ℕ) (x : Trailing n) : Configuration n :=
  configurationCast (Nat.add_sub_of_le (Nat.lt_succ_iff.mp x.1.isLt))
    (joinedConfiguration x.2.val (⊤ : Configuration (n-x.1.val)) (x.2.property.compatible ⊤))

theorem trailingAssemble_cut (n : ℕ) (x : Trailing n) : trailingCut (trailingAssemble n x)=x.1.val := by
  unfold trailingAssemble
  rw [trailingCut_cast,trailingCut_join_top x.2.val x.2.property]

/-- Every actual fan flat has a unique ending-nonhub prefix followed by a
(possibly empty) full hub suffix. The zero-length prefix is retained. -/
noncomputable def trailingEquiv (n : ℕ) : Trailing n ≃ Configuration n :=
  Equiv.ofBijective (trailingAssemble n) (by
    constructor
    · rintro ⟨m,p⟩ ⟨k,q⟩ he
      have hm := congrArg trailingCut he
      rw [trailingAssemble_cut,trailingAssemble_cut] at hm
      have hmk : m=k := Fin.ext hm
      subst k
      have hj : joinedConfiguration p.val (⊤ : Configuration (n-m.val)) (p.property.compatible ⊤)=
          joinedConfiguration q.val (⊤ : Configuration (n-m.val)) (q.property.compatible ⊤) :=
        (configurationCast (Nat.add_sub_of_le (Nat.lt_succ_iff.mp m.isLt))).injective he
      have hpq : p=q := by
        apply Subtype.ext
        apply Subtype.ext
        have hl := congrArg (fun z : Configuration (m.val+(n-m.val)) =>
          leftPair (m:=m.val) (n:=n-m.val) z.val) hj
        change leftPair (joinPair p.val.val (⊤ : Configuration (n-m.val)).val)=
          leftPair (joinPair q.val.val (⊤ : Configuration (n-m.val)).val) at hl
        simpa only [leftPair_join] using hl
      subst q
      rfl
    · intro p
      let m := trailingCut p
      have hm : m≤n := trailingCut_le p
      let i : Fin (n+1) := ⟨m,by omega⟩
      have he : m+(n-m)=n := Nat.add_sub_of_le hm
      let z : Configuration (m+(n-m)) := configurationCast he.symm p
      have hz : trailingCut z=m := by
        dsimp [z,m]
        rw [trailingCut_cast]
      let q : Configuration m := trailingPrefix (m:=m) (r:=n-m) z
      have hq : EndsNonhub q := trailing_left_endsNonhub z hz
      refine ⟨⟨i,⟨q,hq⟩⟩,?_⟩
      change configurationCast he (joinedConfiguration q (⊤ : Configuration (n-m)) (hq.compatible ⊤))=p
      rw [trailing_split z hz]
      exact configurationCast_cancel he p)

theorem sum_trailing {R : Type*} [AddCommMonoid R] (n : ℕ) (f : Configuration n → R) :
    (∑ p, f p)=∑ m : Fin (n+1), ∑ p : NonhubConfiguration m.val,
      f (trailingAssemble n ⟨m,p⟩) := by
  classical
  rw [← (trailingEquiv n).sum_comp f,Fintype.sum_sigma]
  rfl

end Fan
