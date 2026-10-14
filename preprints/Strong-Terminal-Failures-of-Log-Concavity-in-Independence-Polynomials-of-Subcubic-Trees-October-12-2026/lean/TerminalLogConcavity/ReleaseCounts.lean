import TerminalLogConcavity.ReleaseTree
import TerminalLogConcavity.BlockSum

namespace TerminalLogConcavity
open scoped BigOperators

noncomputable def decorationCost (D : Decoration) : ℤ := Fintype.card D.forest.Vertex + 1

theorem sum_map_range_int (f : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem sum_map_intersperse_int {α : Type*} (f : α → ℤ) (sep : α) (l : List α) (hl : l ≠ []) :
    ((l.intersperse sep).map f).sum = (l.map f).sum + ((l.length : ℤ) - 1) * f sep := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      rw [List.intersperse_cons_cons]
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [ih (by simp)]
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      ring

theorem sum_map_flatten_int {α : Type*} (f : α → ℤ) (ls : List (List α)) :
    (ls.flatten.map f).sum = (ls.map (fun l => (l.map f).sum)).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [Function.comp_def]

theorem site_cost {q : ℕ} (hq : 1 ≤ q) (t i k : ℕ) :
    decorationCost (siteDecoration q t i k) =
      4 * (2 : ℤ) ^ t * ((siteParameter q i k : ℤ) + 2 * interfaceParameter q i) - 5 := by
  have hp := Block.scaled_card t (show 1 ≤ siteParameter q i k by have := siteParameter_pos (i := i) (k := k) hq; omega)
  have hmpos : 1 ≤ interfaceParameter q i := by
    unfold interfaceParameter massParameter
    have : 0 < q ^ 2 := by positivity
    omega
  have hm := Block.scaled_card t hmpos
  have hp' : (Fintype.card (Block.scaled t (siteParameter q i k)).Vertex : ℤ) + 3 =
      4 * 2 ^ t * siteParameter q i k := by exact_mod_cast hp
  have hm' : (Fintype.card (Block.scaled t (interfaceParameter q i)).Vertex : ℤ) + 3 =
      4 * 2 ^ t * interfaceParameter q i := by exact_mod_cast hm
  change (Fintype.card (interfaceForest (Block.scaled t (siteParameter q i k))
    (Block.scaled t (interfaceParameter q i))).Vertex : ℤ) + 1 = _
  rw [interface_card]
  push_cast
  nlinarith

theorem coupler_cost {q : ℕ} (hq : 1 ≤ q) (t : ℕ) :
    decorationCost (couplerDecoration q t) = 4 * (2 : ℤ) ^ t * (2 * baseCoupling q) - 2 := by
  have hp : 1 ≤ 2 * baseCoupling q := by
    unfold baseCoupling
    have : 0 < q ^ 2 := by positivity
    omega
  have h := Block.scaled_card t hp
  have h' : (Fintype.card (Block.scaled t (2 * baseCoupling q)).Vertex : ℤ) + 3 =
      4 * (2 : ℤ) ^ t * (2 * baseCoupling q) := by exact_mod_cast h
  change (Fintype.card (Block.scaled t (2 * baseCoupling q)).Vertex : ℤ) + 1 = _
  omega

@[simp] theorem bridge_cost : decorationCost Block.leaf.decoration = 2 := by
  change (Fintype.card Block.leaf.Vertex : ℤ) + 1 = 2
  rw [Block.card_leaf]
  norm_num

theorem site_parameter_sum {q : ℕ} (hq : 2 ≤ q) (i : ℕ) :
    (∑ k ∈ Finset.range q, (siteParameter q i (k + 1) : ℤ)) =
      (baseCoupling q : ℤ) * (2 * q - 2) + (i : ℤ) ^ 2 := by
  have hk (k : ℕ) : (siteParameter q i (k + 1) : ℤ) =
      (baseCoupling q : ℤ) * (2 - (if k = 0 then 1 else 0) - (if k = q - 1 then 1 else 0)) +
        (if k = 0 then (i : ℤ) ^ 2 else 0) := by
    unfold siteParameter endpointWeight
    by_cases h0 : k = 0
    · subst k; simp [show ¬ 0 = q - 1 by omega]
    · by_cases hlast : k = q - 1
      · have h1 : k + 1 ≠ 1 := by omega
        have hq' : k + 1 = q := by omega
        simp [hlast, show q - 1 ≠ 0 by omega, show q - 1 + 1 = q by omega, show q ≠ 1 by omega]
      · have h1 : k + 1 ≠ 1 := by omega
        have hq' : k + 1 ≠ q := by omega
        simp [h0, hlast, hq']
  simp_rw [hk]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [Finset.sum_sub_distrib, show 0 < q by omega, show q - 1 < q by omega]
  ; ring ; simp

theorem chain_cost {q : ℕ} (hq : 2 ≤ q) (t i : ℕ) :
    ((chainDecorations q t i).map decorationCost).sum =
      4 * (2 : ℤ) ^ t * ((baseCoupling q : ℤ) * (4 * q - 4) + (i : ℤ) ^ 2 +
        2 * q * interfaceParameter q i) - 7 * q + 2 := by
  unfold chainDecorations
  rw [sum_map_intersperse_int _ _ _ (by intro h; have := congrArg List.length h; simp at this; omega)]
  simp only [List.map_map, List.length_map, List.length_range]
  rw [sum_map_range_int]
  simp_rw [Function.comp_apply, site_cost (show 1 ≤ q by omega) t i]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, site_parameter_sum hq]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [coupler_cost (show 1 ≤ q by omega)]
  ring

theorem twice_sum_successors (q : ℕ) :
    2 * (∑ i ∈ Finset.range q, ((i : ℤ) + 1)) = (q : ℤ) * (q + 1) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Finset.sum_range_succ]; push_cast; nlinarith

theorem release_cost {q : ℕ} (hq : 2 ≤ q) (t : ℕ) :
    ((releaseDecorations q t).map decorationCost).sum =
      4 * (2 : ℤ) ^ t * blockParameterSum q - 7 * q ^ 2 + 4 * q - 2 := by
  unfold releaseDecorations
  rw [sum_map_flatten_int, sum_map_intersperse_int _ _ _
    (by intro h; have := congrArg List.length h; simp at this; omega)]
  simp only [List.map_map, List.length_map, List.length_range, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, bridge_cost, add_zero]
  rw [sum_map_range_int]
  simp_rw [Function.comp_apply, chain_cost hq]
  have hs := twice_sum_successors q
  have hsq : (∑ i ∈ Finset.range q, ((i + 1 : ℕ) : ℤ) ^ 2) = squareSum q := by
    simp [squareSum, Nat.cast_sum, Nat.cast_pow]
  have hpow : 7 * q ^ 3 ≤ 16 * q ^ 4 := by
    have hh : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hS : (blockParameterSum q : ℤ) = 16 * (q : ℤ)^4 - 7 * (q : ℤ)^3 + (q : ℤ)^2 + squareSum q := by
    simp [blockParameterSum, Nat.cast_sub hpow]
  simp only [interfaceParameter, massParameter, baseCoupling]
  push_cast
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast at hsq
  rw [hsq, hS]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hs
  have hs' := congrArg (fun z : ℤ => 4 * 2 ^ t * q * z) hs
  nlinarith only [hs']

theorem releaseForest_count_identity {q : ℕ} (hq : 2 ≤ q) (t : ℕ) :
    Fintype.card (releaseForest q t).Vertex + 7 * q ^ 2 + 2 =
      4 * 2 ^ t * blockParameterSum q + 4 * q := by
  have h := release_cost hq t
  have hc : (Fintype.card (releaseForest q t).Vertex : ℤ) =
      ((releaseDecorations q t).map decorationCost).sum := by
    rw [releaseForest, decoratedPath_card]
    simp only [Nat.cast_list_sum, List.map_map, Function.comp_def, Nat.cast_add, Nat.cast_one]
    rfl
  rw [← hc] at h
  have he : (Fintype.card (releaseForest q t).Vertex : ℤ) + 7 * (q : ℤ)^2 + 2 =
      4 * (2 : ℤ)^t * blockParameterSum q + 4 * q := by linarith
  exact_mod_cast he

end TerminalLogConcavity
