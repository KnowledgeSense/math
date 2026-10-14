import MainTheorems.Tuza.HalfQuasigroup

namespace ResearchMain.Tuza

abbrev SkolemPoint (L : Type*) := Option ((L × Bool) × ZMod 3)

def skolemPartner {L : Type*} (x : (L × Bool) × ZMod 3) : (L × Bool) × ZMod 3 :=
  ((x.1.1, !x.1.2), if x.1.2 then x.2 + 1 else x.2 - 1)

theorem skolemPartner_involutive {L : Type*} (x : (L × Bool) × ZMod 3) :
    skolemPartner (skolemPartner x) = x := by
  obtain ⟨⟨l, b⟩, i⟩ := x
  cases b <;> simp [skolemPartner]

variable {L : Type*} [DecidableEq L]

noncomputable def skolemUp (H : HalfQuasigroup L) (x y : L × Bool) (i : ZMod 3) : SkolemPoint L :=
  if y = H.mul x x then if x.2 then none else some (x, i - 1)
  else some (H.div x y, i)

noncomputable def skolemFinite (H : HalfQuasigroup L) (x y : L × Bool) (i j : ZMod 3) :
    SkolemPoint L :=
  if i = j then if x = y then some (x, i) else some (H.mul x y, i + 1)
  else if j = i + 1 then skolemUp H x y i else skolemUp H y x j

noncomputable def skolemThird (H : HalfQuasigroup L) (x y : SkolemPoint L) : SkolemPoint L :=
  match x, y with
  | none, none => none
  | none, some y => some (skolemPartner y)
  | some x, none => some (skolemPartner x)
  | some x, some y => skolemFinite H x.1 y.1 x.2 y.2

theorem skolemFinite_same (H : HalfQuasigroup L) (x y : L × Bool) (i : ZMod 3) :
    skolemFinite H x y i i = if x = y then some (x, i) else some (H.mul x y, i + 1) := by
  simp [skolemFinite]

theorem skolemFinite_up (H : HalfQuasigroup L) (x y : L × Bool) (i : ZMod 3) :
    skolemFinite H x y i (i + 1) = skolemUp H x y i := by
  have hi : i ≠ i + 1 := by revert i; decide
  simp [skolemFinite, hi]

theorem skolemFinite_down (H : HalfQuasigroup L) (x y : L × Bool) (i : ZMod 3) :
    skolemFinite H x y (i + 1) i = skolemUp H y x i := by
  have hi : i + 1 ≠ i := by revert i; decide
  simp [skolemFinite, hi, zmod_three_no_reverse]

theorem skolemFinite_comm (H : HalfQuasigroup L) (x y : L × Bool) (i j : ZMod 3) :
    skolemFinite H x y i j = skolemFinite H y x j i := by
  by_cases hij : i = j
  · subst j
    rw [skolemFinite_same, skolemFinite_same]
    by_cases hxy : x = y
    · subst y
      simp
    · simp [hxy, Ne.symm hxy, H.comm]
  · rcases zmod_three_ne_cases hij with hji | hij
    · subst j
      rw [skolemFinite_up, skolemFinite_down]
    · subst i
      rw [skolemFinite_down, skolemFinite_up]

theorem skolemThird_comm (H : HalfQuasigroup L) (x y : SkolemPoint L) :
    skolemThird H x y = skolemThird H y x := by
  cases x with
  | none => cases y <;> rfl
  | some x =>
    cases y with
    | none => rfl
    | some y => exact skolemFinite_comm H _ _ _ _

end ResearchMain.Tuza
