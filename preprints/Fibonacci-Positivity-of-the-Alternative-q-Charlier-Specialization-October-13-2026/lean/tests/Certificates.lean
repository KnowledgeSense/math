import AlternativeQCharlier

open AlternativeQCharlier

example (ρ q : ℝ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1/4)
    (hq : 0 < q) (hq' : q ≤ 1/5) (w : Word) :
    0 < cloneSchur (x ρ q) (y ρ q) w :=
  cloneSchur_pos ⟨hρ, hρ', hq, hq'⟩ w

example (l : List Bool) : (Word.fromList l).toList = l := Word.toList_fromList l

example (ρ q : ℝ) (h : ParameterBox ρ q) (m n : ℕ) :
    0 < B (x ρ q) (y ρ q) m n := B_pos h m n

example (w : Word) : 0 < cloneSchur (x (1/4) (1/5)) (y (1/4) (1/5)) w :=
  cloneSchur_pos (by norm_num [ParameterBox]) w
