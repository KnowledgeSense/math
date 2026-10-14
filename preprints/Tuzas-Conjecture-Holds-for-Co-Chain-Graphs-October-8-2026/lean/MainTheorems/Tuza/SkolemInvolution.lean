import MainTheorems.Tuza.SkolemThird

namespace ResearchMain.Tuza

theorem zmod_three_sub_twice (i : ZMod 3) : i - 1 - 1 = i + 1 := by revert i; decide

theorem zmod_three_successor_twice (i : ZMod 3) : (i + 1) + 1 = i - 1 := by revert i; decide

variable {L : Type*} [DecidableEq L]

theorem skolem_same_involutive (H : HalfQuasigroup L) (x y : L × Bool) (i : ZMod 3) :
    skolemThird H (some (x, i)) (skolemFinite H x y i i) = some (y, i) := by
  rw [skolemFinite_same]
  by_cases hxy : x = y
  · subst y
    simp [skolemThird, skolemFinite]
  · rw [ite_eq_right hxy]
    change skolemFinite H x (H.mul x y) i (i + 1) = _
    rw [skolemFinite_up, skolemUp, ite_eq_right (H.mul_ne_diagonal hxy), H.div_mul]

theorem skolem_up_involutive (H : HalfQuasigroup L) (x y : L × Bool) (i : ZMod 3) :
    skolemThird H (some (x, i)) (skolemUp H x y i) = some (y, i + 1) := by
  by_cases hd : y = H.mul x x
  · subst y
    obtain ⟨l, b⟩ := x
    cases b
    · rw [skolemUp, ite_eq_left rfl]
      change skolemFinite H (l, false) (l, false) i (i - 1) = some (H.mul (l, false) (l, false), i + 1)
      have hf := skolemFinite_down H (l, false) (l, false) (i - 1)
      rw [sub_add_cancel] at hf
      rw [hf, skolemUp, H.diagonal]
      simp only [ite_true, Bool.false_eq_true, ite_false, zmod_three_sub_twice]
    · simp [skolemUp, skolemThird, skolemPartner, H.diagonal]
  · rw [skolemUp, ite_eq_right hd]
    change skolemFinite H x (H.div x y) i i = _
    rw [skolemFinite_same, ite_eq_right (Ne.symm (H.div_ne hd)), H.mul_div]

theorem skolem_down_involutive (H : HalfQuasigroup L) (x y : L × Bool) (i : ZMod 3) :
    skolemThird H (some (x, i + 1)) (skolemUp H y x i) = some (y, i) := by
  by_cases hd : x = H.mul y y
  · subst x
    obtain ⟨l, b⟩ := y
    cases b
    · rw [skolemUp, ite_eq_left rfl]
      rw [H.diagonal]
      change skolemFinite H (l, false) (l, false) (i + 1) (i - 1) = _
      rw [← zmod_three_successor_twice, skolemFinite_up, skolemUp, H.diagonal]
      simp
    · simp [skolemUp, skolemThird, skolemPartner, H.diagonal]
  · rw [skolemUp, ite_eq_right hd]
    change skolemFinite H x (H.div y x) (i + 1) i = _
    rw [skolemFinite_down, skolemUp, ite_eq_right (H.div_diagonal_ne hd), H.div_reverse]

theorem skolemThird_partner (H : HalfQuasigroup L) (x : (L × Bool) × ZMod 3) :
    skolemThird H (some x) (some (skolemPartner x)) = none := by
  obtain ⟨⟨l, b⟩, i⟩ := x
  cases b
  · change skolemFinite H (l, false) (l, true) i (i - 1) = none
    have hf := skolemFinite_down H (l, false) (l, true) (i - 1)
    rw [sub_add_cancel] at hf
    rw [hf]
    simp [skolemUp, H.diagonal]
  · change skolemFinite H (l, true) (l, false) i (i + 1) = none
    rw [skolemFinite_up]
    simp [skolemUp, H.diagonal]

theorem skolemThird_involutive (H : HalfQuasigroup L) (x y : SkolemPoint L) :
    skolemThird H x (skolemThird H x y) = y := by
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => exact congrArg some (skolemPartner_involutive y)
  | some x =>
    cases y with
    | none => exact skolemThird_partner H x
    | some y =>
      obtain ⟨x, i⟩ := x
      obtain ⟨y, j⟩ := y
      by_cases hij : i = j
      · subst j
        exact skolem_same_involutive H x y i
      · rcases zmod_three_ne_cases hij with hji | hij
        · subst j
          change skolemThird H (some (x, i)) (skolemFinite H x y i (i + 1)) = _
          rw [skolemFinite_up]
          exact skolem_up_involutive H x y i
        · subst i
          change skolemThird H (some (x, j + 1)) (skolemFinite H x y (j + 1) j) = _
          rw [skolemFinite_down]
          exact skolem_down_involutive H x y j

noncomputable def skolemOperation (H : HalfQuasigroup L) : SteinerOperation (SkolemPoint L) where
  third := skolemThird H
  comm := skolemThird_comm H
  involutive := skolemThird_involutive H
  idempotent := by intro x; cases x <;> simp [skolemThird, skolemFinite]

end ResearchMain.Tuza
