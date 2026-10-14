import MainTheorems.Tuza.SkolemShuffle

namespace ResearchMain.Tuza

theorem halfLabel_double (m : ℕ) [NeZero (2 * m)] (x : Fin m × Bool) :
    ((halfLabelEquiv m x) + (halfLabelEquiv m x)).val = 2 * x.1.val := by
  obtain ⟨i, b⟩ := x
  have hi : 2 * i.val < 2 * m := by have ht := i.isLt; omega
  rw [Fin.val_add]
  cases b
  · change (i.val + 0 + (i.val + 0)) % (2 * m) = 2 * i.val
    rw [show i.val + 0 + (i.val + 0) = 2 * i.val by omega, Nat.mod_eq_of_lt hi]
  · change (i.val + m + (i.val + m)) % (2 * m) = 2 * i.val
    rw [show i.val + m + (i.val + m) = 2 * m + 2 * i.val by ring]
    simp [Nat.mod_eq_of_lt hi]

def skolemQuasigroup (m : ℕ) [NeZero (2 * m)] : HalfQuasigroup (Fin m) where
  mul x y := parityEquiv m ((halfLabelEquiv m x) + (halfLabelEquiv m y))
  comm x y := congrArg (parityEquiv m) (add_comm _ _)
  bijective x := (parityEquiv m).bijective.comp
    ((Equiv.addLeft (halfLabelEquiv m x)).bijective.comp (halfLabelEquiv m).bijective)
  diagonal x := by
    apply Prod.ext
    · apply Fin.ext
      change ((halfLabelEquiv m x + halfLabelEquiv m x).val / 2) = x.1.val
      rw [halfLabel_double]
      omega
    · change decide ((halfLabelEquiv m x + halfLabelEquiv m x).val % 2 = 1) = false
      rw [halfLabel_double]
      simp

end ResearchMain.Tuza
