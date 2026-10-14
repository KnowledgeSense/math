import MainTheorems.Tuza.BoseArithmetic

namespace ResearchMain.Tuza

variable {K : Type*} [AddCommGroup K] [DecidableEq K]

def boseThird (D : K ≃+ K) (x y : K × ZMod 3) : K × ZMod 3 :=
  if x.1 = y.1 then (x.1, -x.2 - y.2)
  else if x.2 = y.2 then (midpoint D x.1 y.1, x.2 + 1)
  else if y.2 = x.2 + 1 then (D y.1 - x.1, x.2)
  else (D x.1 - y.1, y.2)

theorem boseThird_vertical (D : K ≃+ K) (x : K) (i j : ZMod 3) :
    boseThird D (x, i) (x, j) = (x, -i - j) := by simp [boseThird]

theorem boseThird_same (D : K ≃+ K) {x y : K} (hxy : x ≠ y) (i : ZMod 3) :
    boseThird D (x, i) (y, i) = (midpoint D x y, i + 1) := by simp [boseThird, hxy]

theorem boseThird_up (D : K ≃+ K) {x y : K} (hxy : x ≠ y) (i : ZMod 3) :
    boseThird D (x, i) (y, i + 1) = (D y - x, i) := by
  have hi : i ≠ i + 1 := by revert i; decide
  simp [boseThird, hxy, hi]

theorem boseThird_down (D : K ≃+ K) {x y : K} (hxy : x ≠ y) (i : ZMod 3) :
    boseThird D (x, i + 1) (y, i) = (D x - y, i) := by
  have hi : i + 1 ≠ i := by revert i; decide
  simp [boseThird, hxy, hi, zmod_three_no_reverse]

theorem boseThird_comm (D : K ≃+ K) (x y : K × ZMod 3) :
    boseThird D x y = boseThird D y x := by
  obtain ⟨x, i⟩ := x
  obtain ⟨y, j⟩ := y
  by_cases hxy : x = y
  · subst y
    rw [boseThird_vertical, boseThird_vertical]
    congr 1
    abel
  · by_cases hij : i = j
    · subst j
      rw [boseThird_same D hxy, boseThird_same D (Ne.symm hxy), midpoint_comm]
    · rcases zmod_three_ne_cases hij with hji | hij
      · subst j
        rw [boseThird_up D hxy, boseThird_down D (Ne.symm hxy)]
      · subst i
        rw [boseThird_down D hxy, boseThird_up D (Ne.symm hxy)]

theorem boseThird_involutive (D : K ≃+ K) (hD : ∀ x, D x = x + x)
    (x y : K × ZMod 3) : boseThird D x (boseThird D x y) = y := by
  obtain ⟨x, i⟩ := x
  obtain ⟨y, j⟩ := y
  by_cases hxy : x = y
  · subst y
    rw [boseThird_vertical, boseThird_vertical]
    congr 1
    abel
  · by_cases hij : i = j
    · subst j
      rw [boseThird_same D hxy, boseThird_up D (midpoint_ne_left D hD hxy).symm]
      congr 1
      rw [midpoint_double]
      abel
    · rcases zmod_three_ne_cases hij with hji | hij
      · subst j
        rw [boseThird_up D hxy, boseThird_same D (double_sub_ne D hD hxy).symm,
          midpoint_double_sub]
      · subst i
        rw [boseThird_down D hxy, boseThird_down D (double_sub_ne_self D hD hxy).symm]
        congr 1
        abel

def boseOperation (D : K ≃+ K) (hD : ∀ x, D x = x + x) : SteinerOperation (K × ZMod 3) where
  third := boseThird D
  comm := boseThird_comm D
  involutive := boseThird_involutive D hD
  idempotent := by
    rintro ⟨x, i⟩
    rw [boseThird_vertical]
    congr 1
    revert i
    decide

end ResearchMain.Tuza
