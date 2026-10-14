import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

namespace ResearchMain.PreorderGamma.MacaulayNumerical

open scoped BigOperators

theorem linear_le_choose (d n : ℕ) : n + 1 ≤ (n + d + 1).choose (d + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpos : 0 < (n + d + 1).choose d := Nat.choose_pos (by omega)
      have hpascal := Nat.choose_succ_succ' (n + d + 1) d
      have hstep : (n + 1 + d + 1).choose (d + 1) =
          (n + d + 1).choose d + (n + d + 1).choose (d + 1) := by
        have htop : n + d + 1 + 1 = n + 1 + d + 1 := by omega
        simpa only [htop] using hpascal
      rw [hstep]
      omega

theorem choose_search_bound {d : ℕ} (hd : 0 < d) (m : ℕ) :
    m < (m + d + 1).choose d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  change m < (m + (k + 1) + 1).choose (k + 1)
  have h := linear_le_choose k (m + 1)
  have heq : m + 1 + k + 1 = m + (k + 1) + 1 := by omega
  rw [heq] at h
  omega

def binomialCandidates (d m : ℕ) : Finset ℕ :=
  (Finset.range (m + d + 1)).filter fun a => a.choose d ≤ m

def binomialTop (d m : ℕ) : ℕ := (binomialCandidates d m).sup id

theorem binomialCandidates_nonempty {d : ℕ} (hd : 0 < d) (m : ℕ) :
    (binomialCandidates d m).Nonempty := by
  refine ⟨0, ?_⟩
  simp [binomialCandidates, Nat.choose_eq_zero_of_lt hd]

theorem binomialTop_mem {d : ℕ} (hd : 0 < d) (m : ℕ) :
    binomialTop d m ∈ binomialCandidates d m := by
  have h := (binomialCandidates d m).sup_mem_of_nonempty
    (f := id) (binomialCandidates_nonempty hd m)
  simpa [binomialTop] using h

theorem binomialTop_choose_le {d : ℕ} (hd : 0 < d) (m : ℕ) :
    (binomialTop d m).choose d ≤ m :=
  (Finset.mem_filter.mp (binomialTop_mem hd m)).2

theorem le_binomialTop {d m a : ℕ} (hd : 0 < d) (ha : a.choose d ≤ m) :
    a ≤ binomialTop d m := by
  have hbound : a < m + d + 1 := by
    by_contra hnot
    have hchoose := Nat.choose_le_choose d (show m + d + 1 ≤ a by omega)
    have hlarge := choose_search_bound hd m
    omega
  exact Finset.le_sup (s := binomialCandidates d m) (f := id)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbound, ha⟩)

theorem binomialTop_succ_choose_gt {d : ℕ} (hd : 0 < d) (m : ℕ) :
    m < (binomialTop d m + 1).choose d := by
  by_contra hnot
  have h := le_binomialTop hd (show (binomialTop d m + 1).choose d ≤ m by omega)
  omega

theorem binomialTop_eq_of_bounds {d m a : ℕ} (hd : 0 < d)
    (hle : a.choose d ≤ m) (hlt : m < (a + 1).choose d) :
    binomialTop d m = a := by
  apply Nat.le_antisymm
  · by_contra hnot
    have hchoose := Nat.choose_le_choose d
      (show a + 1 ≤ binomialTop d m by omega)
    have htop := binomialTop_choose_le hd m
    omega
  · exact le_binomialTop hd hle

theorem binomialTop_mono {d : ℕ} (hd : 0 < d) : Monotone (binomialTop d) := by
  intro m n hmn
  exact le_binomialTop hd ((binomialTop_choose_le hd m).trans hmn)

theorem binomialTop_lower {d : ℕ} (hd : 0 < d) (m : ℕ) :
    d - 1 ≤ binomialTop d m := by
  exact le_binomialTop hd (by rw [Nat.choose_eq_zero_of_lt (by omega)]; omega)

theorem binomialTop_remainder_lt (d m : ℕ) :
    m - (binomialTop (d + 1) m).choose (d + 1) <
      (binomialTop (d + 1) m).choose d := by
  have hle := binomialTop_choose_le (show 0 < d + 1 by omega) m
  have hlt := binomialTop_succ_choose_gt (show 0 < d + 1 by omega) m
  rw [Nat.choose_succ_succ'] at hlt
  omega

def macaulayRaise : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, m =>
      (binomialTop (d + 1) m + 1).choose (d + 2) +
        macaulayRaise d (m - (binomialTop (d + 1) m).choose (d + 1))

@[simp] theorem macaulayRaise_zero_degree (m : ℕ) : macaulayRaise 0 m = 0 := rfl

theorem macaulayRaise_upper (d : ℕ) {m a : ℕ} (hm : m < a.choose d) :
    macaulayRaise d m ≤ (a + 1).choose (d + 1) := by
  induction d generalizing m a with
  | zero => simp
  | succ d ih =>
      let b := binomialTop (d + 1) m
      have hb : b.choose (d + 1) ≤ m := binomialTop_choose_le (by omega) m
      have hba : b < a := by
        by_contra hnot
        have hchoose := Nat.choose_le_choose (d + 1) (show a ≤ b by omega)
        omega
      have hrem : m - b.choose (d + 1) < b.choose d :=
        binomialTop_remainder_lt d m
      have hsmall := ih hrem
      change (b + 1).choose (d + 2) +
        macaulayRaise d (m - b.choose (d + 1)) ≤ (a + 1).choose (d + 2)
      calc
        _ ≤ (b + 1).choose (d + 2) + (b + 1).choose (d + 1) :=
          Nat.add_le_add_left hsmall _
        _ = (b + 2).choose (d + 2) := by
          exact (Nat.add_comm _ _).trans
            (Nat.choose_succ_succ' (b + 1) (d + 1)).symm
        _ ≤ (a + 1).choose (d + 2) := Nat.choose_le_choose _ (by omega)

theorem macaulayRaise_mono (d : ℕ) : Monotone (macaulayRaise d) := by
  induction d with
  | zero => intro m n hmn; simp
  | succ d ih =>
      intro m n hmn
      let b := binomialTop (d + 1) m
      let c := binomialTop (d + 1) n
      have hbc : b ≤ c := binomialTop_mono (by omega) hmn
      change (b + 1).choose (d + 2) +
          macaulayRaise d (m - b.choose (d + 1)) ≤
        (c + 1).choose (d + 2) + macaulayRaise d (n - c.choose (d + 1))
      obtain heq | hlt := hbc.eq_or_lt
      · rw [heq]
        exact Nat.add_le_add_left (ih (Nat.sub_le_sub_right hmn _)) _
      · have hrem := binomialTop_remainder_lt d m
        have hsmall := macaulayRaise_upper d hrem
        calc
          _ ≤ (b + 1).choose (d + 2) + (b + 1).choose (d + 1) :=
            Nat.add_le_add_left hsmall _
          _ = (b + 2).choose (d + 2) := by
            exact (Nat.add_comm _ _).trans
              (Nat.choose_succ_succ' (b + 1) (d + 1)).symm
          _ ≤ (c + 1).choose (d + 2) := Nat.choose_le_choose _ (by omega)
          _ ≤ _ := Nat.le_add_right _ _

@[simp] theorem binomialTop_zero (d : ℕ) : binomialTop (d + 1) 0 = d := by
  apply binomialTop_eq_of_bounds (by omega)
  · simp
  · simp

@[simp] theorem macaulayRaise_zero (d : ℕ) : macaulayRaise d 0 = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [macaulayRaise, ih]

end ResearchMain.PreorderGamma.MacaulayNumerical
