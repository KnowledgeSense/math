import AlternativeQCharlier.Continuants

namespace AlternativeQCharlier
noncomputable section

/-- The finite product-sum tail of the normalized determinant. -/
def tail (t : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 1
  | m, n+1 => 1 + t m * tail t (m+1) n

 theorem tail_bounds (t : ℕ → ℝ)
    (hn : ∀ m, 0 ≤ t m) (hb : ∀ m, t m ≤ 5/16) (m n : ℕ) :
    1 ≤ tail t m n ∧ tail t m n ≤ 16/11 := by
  induction n generalizing m with
  | zero => norm_num [tail]
  | succ n ih =>
    have h := ih (m+1)
    simp only [tail]
    constructor
    · nlinarith [mul_nonneg (hn m) (show 0 ≤ tail t (m+1) n by linarith)]
    · have hm := mul_le_mul (hb m) h.2
        (show 0 ≤ tail t (m+1) n by linarith) (by norm_num : (0:ℝ) ≤ 5/16)
      norm_num at hm ⊢
      linarith

 theorem normalized_continuant (t : ℕ → ℝ) (m n : ℕ) :
    continuant (fun i => 1+t i) (fun i => t (i+1)) m n = tail t m n := by
  induction n using Nat.twoStepInduction generalizing m with
  | zero => rfl
  | one => simp [continuant, tail]
  | more n ih ih' =>
    simp only [continuant, ih, ih', tail]
    ring

 theorem normalized_A (t : ℕ → ℝ) (m n : ℕ) :
    A (fun i => 1+t i) (fun i => t (i+1)) m n = tail t m n := by
  rw [A_eq_continuant, normalized_continuant]

 theorem finite_B_margin (t : ℕ → ℝ)
    (hn : ∀ m, 0 ≤ t m) (hb : ∀ m, t m ≤ 5/16)
    (hr : ∀ m, t (m+2) ≤ 3/8*t (m+1)) (m n : ℕ) :
    (25/88)*t (m+1) ≤
      t (m+1) - (1+t m-t (m+1))*t (m+2)*tail t (m+3) n := by
  have ht := tail_bounds t hn hb (m+3) n
  have hd0 : 0 ≤ 1+t m-t (m+1) := by linarith [hn m, hb (m+1)]
  have hd1 : 1+t m-t (m+1) ≤ 21/16 := by linarith [hb m, hn (m+1)]
  have hprod := mul_le_mul hd1 (hr m) (hn (m+2)) (by norm_num : (0:ℝ) ≤ 21/16)
  have hprod2 := mul_le_mul hprod ht.2 (by linarith : 0 ≤ tail t (m+3) n)
    (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (hn (m+1))))
  nlinarith

 theorem normalized_B_succ (t : ℕ → ℝ) (m n : ℕ) :
    B (fun i => 1+t i) (fun i => t (i+1)) m (n+1) =
      t (m+1) - (1+t m-t (m+1))*t (m+2)*tail t (m+3) n := by
  rw [B_succ, normalized_A, normalized_A]
  simp only [tail]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  ring

 theorem normalized_B_pos (t : ℕ → ℝ)
    (hn : ∀ m, 0 ≤ t m) (hp : ∀ m, 0 < t (m+1)) (hb : ∀ m, t m ≤ 5/16)
    (hr : ∀ m, t (m+2) ≤ 3/8*t (m+1)) (m n : ℕ) :
    0 < B (fun i => 1+t i) (fun i => t (i+1)) m n := by
  cases n with
  | zero => simpa using hp m
  | succ n =>
    rw [normalized_B_succ]
    have hmargin := finite_B_margin t hn hb hr m n
    have hstrict : 0 < (25/88 : ℝ)*t (m+1) := mul_pos (by norm_num) (hp m)
    linarith

end
end AlternativeQCharlier
