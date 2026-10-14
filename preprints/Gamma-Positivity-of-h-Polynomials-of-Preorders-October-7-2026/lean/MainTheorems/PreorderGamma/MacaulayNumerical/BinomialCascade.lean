import MainTheorems.PreorderGamma.MacaulayNumerical.BinomialRaise

namespace ResearchMain.PreorderGamma.MacaulayNumerical

def cascadeValue (l : List (ℕ × ℕ)) : ℕ := (l.map fun p => p.1.choose p.2).sum

def cascadeRaiseValue (l : List (ℕ × ℕ)) : ℕ :=
  (l.map fun p => (p.1 + 1).choose (p.2 + 1)).sum

inductive IsStrictCascade : ℕ → List (ℕ × ℕ) → Prop
  | nil (d : ℕ) : IsStrictCascade d []
  | cons {d a : ℕ} {l : List (ℕ × ℕ)}
      (ha : d + 1 ≤ a) (hl : IsStrictCascade d l)
      (hbound : ∀ p ∈ l, p.1 < a) : IsStrictCascade (d + 1) ((a, d + 1) :: l)

def binomialCascade : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | d + 1, m =>
      if m = 0 then [] else
        (binomialTop (d + 1) m, d + 1) ::
          binomialCascade d (m - (binomialTop (d + 1) m).choose (d + 1))

@[simp] theorem binomialCascade_zero (d : ℕ) : binomialCascade d 0 = [] := by
  cases d <;> simp [binomialCascade]

theorem binomialCascade_upper {d m a : ℕ} (hm : m < a.choose d) :
    ∀ p ∈ binomialCascade d m, p.1 < a := by
  induction d generalizing m a with
  | zero => simp [binomialCascade]
  | succ d ih =>
      by_cases hzero : m = 0
      · simp [hzero]
      · let b := binomialTop (d + 1) m
        have hb : b < a := by
          have hchoose := binomialTop_choose_le (show 0 < d + 1 by omega) m
          change b.choose (d + 1) ≤ m at hchoose
          by_contra hnot
          have hmono := Nat.choose_le_choose (d + 1) (show a ≤ b by omega)
          omega
        have htail := ih (binomialTop_remainder_lt d m)
        intro p hp
        simp only [binomialCascade, ite_eq_right hzero, List.mem_cons] at hp
        obtain rfl | hp := hp
        · exact hb
        · exact (htail p hp).trans hb

theorem binomialCascade_strict (d m : ℕ) : IsStrictCascade d (binomialCascade d m) := by
  induction d generalizing m with
  | zero => exact IsStrictCascade.nil 0
  | succ d ih =>
      by_cases hzero : m = 0
      · simpa [hzero] using IsStrictCascade.nil (d + 1)
      · have htop : d + 1 ≤ binomialTop (d + 1) m :=
          le_binomialTop (by omega) (by simp; omega)
        rw [binomialCascade, ite_eq_right hzero]
        exact IsStrictCascade.cons htop (ih _) (binomialCascade_upper
          (binomialTop_remainder_lt d m))

theorem binomialCascade_value (d m : ℕ) (h : 0 < d ∨ m = 0) :
    cascadeValue (binomialCascade d m) = m := by
  induction d generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      simp [hm, binomialCascade, cascadeValue]
  | succ d ih =>
      by_cases hzero : m = 0
      · simp [hzero, cascadeValue]
      · have hrem := binomialTop_remainder_lt d m
        have htail : 0 < d ∨ m - (binomialTop (d + 1) m).choose (d + 1) = 0 := by
          by_cases hd : d = 0
          · right
            subst d
            simp only [Nat.choose_zero_right] at hrem ⊢
            omega
          · left
            omega
        have hvalue := ih _ htail
        have hle := binomialTop_choose_le (show 0 < d + 1 by omega) m
        simp only [binomialCascade, ite_eq_right hzero, cascadeValue, List.map_cons,
          List.sum_cons]
        change (binomialTop (d + 1) m).choose (d + 1) +
          cascadeValue (binomialCascade d
            (m - (binomialTop (d + 1) m).choose (d + 1))) = m
        rw [hvalue]
        omega

theorem binomialCascade_raise (d m : ℕ) :
    cascadeRaiseValue (binomialCascade d m) = macaulayRaise d m := by
  induction d generalizing m with
  | zero => rfl
  | succ d ih =>
      by_cases hzero : m = 0
      · simp [hzero, cascadeRaiseValue]
      · simp only [binomialCascade, ite_eq_right hzero, cascadeRaiseValue,
          List.map_cons, List.sum_cons, macaulayRaise]
        exact congrArg (fun t => (binomialTop (d + 1) m + 1).choose (d + 2) + t) (ih _)

theorem strictCascade_value_lt_choose {d a : ℕ} {l : List (ℕ × ℕ)}
    (h : IsStrictCascade d l) (hbound : ∀ p ∈ l, p.1 < a) (hda : d ≤ a) :
    cascadeValue l < a.choose d := by
  induction h generalizing a with
  | nil d =>
      have hpos := Nat.choose_pos hda
      simpa [cascadeValue] using hpos
  | @cons d b l hb hl hbl ih =>
      have hba : b < a := hbound (b, d + 1) (by simp)
      have htail := ih hbl (show d ≤ b by omega)
      have hmono := Nat.choose_le_choose (d + 1) (show b + 1 ≤ a by omega)
      have hpascal := Nat.choose_succ_succ' b d
      change b.choose (d + 1) + cascadeValue l < a.choose (d + 1)
      omega

theorem strictCascade_eq_binomialCascade {d : ℕ} {l : List (ℕ × ℕ)}
    (h : IsStrictCascade d l) : l = binomialCascade d (cascadeValue l) := by
  induction h with
  | nil d => simp [cascadeValue]
  | @cons d a l ha hl hbound ih =>
      have htail := strictCascade_value_lt_choose hl hbound (show d ≤ a by omega)
      have hpos := Nat.choose_pos ha
      have hvalue : cascadeValue ((a, d + 1) :: l) = a.choose (d + 1) + cascadeValue l := rfl
      have hne : cascadeValue ((a, d + 1) :: l) ≠ 0 := by omega
      have htop : binomialTop (d + 1) (cascadeValue ((a, d + 1) :: l)) = a := by
        apply binomialTop_eq_of_bounds (by omega)
        · omega
        · have hpascal := Nat.choose_succ_succ' a d
          omega
      have hrem : cascadeValue ((a, d + 1) :: l) - a.choose (d + 1) =
          cascadeValue l := by omega
      rw [binomialCascade, ite_eq_right hne, htop, hrem]
      exact congrArg (List.cons (a, d + 1)) ih

theorem strictCascade_unique {d m : ℕ} {l l' : List (ℕ × ℕ)}
    (hl : IsStrictCascade d l) (hl' : IsStrictCascade d l')
    (hm : cascadeValue l = m) (hm' : cascadeValue l' = m) : l = l' := by
  rw [strictCascade_eq_binomialCascade hl, strictCascade_eq_binomialCascade hl', hm, hm']

theorem macaulayRaise_eq_strictCascade {d m : ℕ} {l : List (ℕ × ℕ)}
    (hl : IsStrictCascade d l) (hm : cascadeValue l = m) :
    macaulayRaise d m = cascadeRaiseValue l := by
  rw [strictCascade_eq_binomialCascade hl, hm, binomialCascade_raise]

theorem strictCascade_exists {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ∃ l : List (ℕ × ℕ), IsStrictCascade d l ∧ cascadeValue l = m ∧
      cascadeRaiseValue l = macaulayRaise d m :=
  ⟨binomialCascade d m, binomialCascade_strict d m,
    binomialCascade_value d m (Or.inl hd), binomialCascade_raise d m⟩

end ResearchMain.PreorderGamma.MacaulayNumerical
