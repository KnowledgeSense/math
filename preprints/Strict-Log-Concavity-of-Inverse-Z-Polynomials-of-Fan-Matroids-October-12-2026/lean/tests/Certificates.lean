import Fan

open Fan Polynomial

example (n : ℕ) (hn : 1≤n) := fan_inverseZ_main n hn
example : inverseZ 0=1 := inverseZ_zero
example : inverseZ 1=1+X := inverseZ_one
example (n : ℕ) : graphicRank (graph n).edgeSet=n := graph_rank n
example (n k : ℕ) (hn : 0<n) (hk : k≤n) := inverseZ_coefficient_formula n k hn hk
example (n k : ℕ) (hn : 0<n) (hk : n<k) : (inverseZ n).coeff k=0 :=
  inverseZ_coefficient_above n k hn hk
example (n : ℕ) (hn : 0<n) : 0<(inverseZ n).coeff 0 :=
  inverseZ_coefficient_pos n 0 hn (by omega)
example (n : ℕ) (hn : 0<n) : 0<(inverseZ n).coeff n :=
  inverseZ_coefficient_pos n n hn le_rfl
example : (inverseZ 2).coeff 0*(inverseZ 2).coeff 2<(inverseZ 2).coeff 1^2 := by
  simpa using inverseZ_coefficient_strict 2 1 (by omega) (by omega) (by omega)
example : (inverseZ 3).coeff 0*(inverseZ 3).coeff 2<(inverseZ 3).coeff 1^2 := by
  simpa using inverseZ_coefficient_strict 3 1 (by omega) (by omega) (by omega)
example : (inverseZ 4).coeff 1*(inverseZ 4).coeff 3<(inverseZ 4).coeff 2^2 := by
  simpa using inverseZ_coefficient_strict 4 2 (by omega) (by omega) (by omega)
example : (inverseZ 2).coeff 0=2 := by
  have h := inverseZ_coefficient_formula 2 0 (by omega) (by omega)
  norm_num [ballotWeight,delannoy] at h
  exact_mod_cast h
example : (inverseZ 2).coeff 1=3 := by
  have h := inverseZ_coefficient_formula 2 1 (by omega) (by omega)
  norm_num [ballotWeight,delannoy,Nat.choose,Finset.sum_range_succ] at h
  exact_mod_cast h
example : (inverseZ 3).coeff 1=9 := by
  have h := inverseZ_coefficient_formula 3 1 (by omega) (by omega)
  norm_num [ballotWeight,delannoy,Nat.choose,Finset.sum_range_succ] at h
  exact_mod_cast h
