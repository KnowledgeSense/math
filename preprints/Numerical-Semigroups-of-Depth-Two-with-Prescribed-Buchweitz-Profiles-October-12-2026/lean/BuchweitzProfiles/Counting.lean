import BuchweitzProfiles.Sumsets
import BuchweitzProfiles.Construction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Finset.Card

/-! Exact arithmetic rows used to count the digit-separated construction. -/
namespace BuchweitzProfiles

/-- Sums of exactly `l` of the three small generators. -/
def row (u M l : Nat) : Finset Nat :=
  (Finset.range (2*l+1)).image (fun b => l*u+b*M)

theorem mem_row {u M l x : Nat} :
    x ∈ row u M l ↔ ∃ b ≤ 2*l, l*u+b*M = x := by
  simp only [row, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨b, hb, hx⟩; exact ⟨b, by omega, hx⟩
  · rintro ⟨b, hb, hx⟩; exact ⟨b, by omega, hx⟩

theorem card_row (u M l : Nat) (hM : 0 < M) : (row u M l).card = 2*l+1 := by
  rw [row, Finset.card_image_of_injective]
  · simp
  · intro a b h
    dsimp at h
    have : a*M = b*M := by omega
    exact Nat.eq_of_mul_eq_mul_right hM this

theorem row_bounds {u M l x : Nat} (hx : x ∈ row u M l) :
    l*u ≤ x ∧ x ≤ l*(u+2*M) := by
  obtain ⟨b, hb, rfl⟩ := mem_row.mp hx
  constructor
  · omega
  · nlinarith [Nat.mul_le_mul_right M hb]

theorem rows_strictly_ordered {K M i j x y : Nat} (hM : 0 < M)
    (hi : i ≤ K) (hij : i < j)
    (hx : x ∈ row ((2*K+1)*M) M i)
    (hy : y ∈ row ((2*K+1)*M) M j) : x < y := by
  obtain ⟨_, hx⟩ := row_bounds hx
  obtain ⟨hy, _⟩ := row_bounds hy
  have h1 := Nat.mul_le_mul_right (2*M) hi
  have h2 := Nat.mul_le_mul_right ((2*K+1)*M) (show i+1 ≤ j by omega)
  nlinarith

theorem rows_disjoint {K M i j : Nat} (hM : 0 < M) (hi : i ≤ K)
    (hj : j ≤ K) (hne : i ≠ j) :
    Disjoint (row ((2*K+1)*M) M i) (row ((2*K+1)*M) M j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hne with h | h
  · have := rows_strictly_ordered hM hi h hx hy; omega
  · have := rows_strictly_ordered hM hj h hy hx; omega

theorem row_below_cutoff {K M l x : Nat} (hl : l ≤ K)
    (hx : x ∈ row ((2*K+1)*M) M l) :
    x < K*(((2*K+1)*M)+2*M)+1 := by
  have hh := (row_bounds hx).2
  have := Nat.mul_le_mul_right (((2*K+1)*M)+2*M) hl
  omega

theorem row_above_cutoff {K M l x : Nat} (hM : 0 < M) (hl : K+1 ≤ l)
    (hx : x ∈ row ((2*K+1)*M) M l) :
    K*(((2*K+1)*M)+2*M)+1 ≤ x := by
  have hh := (row_bounds hx).1
  have := Nat.mul_le_mul_right ((2*K+1)*M) hl
  nlinarith

/-- The three small generators as the first arithmetic row. -/
def smallGenerators (u M : Nat) : Finset Nat := row u M 1

theorem sumset_smallGenerators (u M n : Nat) :
    sumset (smallGenerators u M) n = row u M n := by
  induction n with
  | zero => ext x; simp [row, sumset]
  | succ n ih =>
    ext x
    rw [mem_sumset_succ]
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      rw [ih] at hy
      obtain ⟨b, hb, rfl⟩ := mem_row.mp hy
      obtain ⟨c, hc, rfl⟩ := mem_row.mp hz
      apply mem_row.mpr
      refine ⟨b+c, by omega, ?_⟩
      ring
    · intro hx
      obtain ⟨b, hb, rfl⟩ := mem_row.mp hx
      let c := min b 2
      have hc : c ≤ 2 := Nat.min_le_right _ _
      have hcb : c ≤ b := Nat.min_le_left _ _
      have hbc : b-c ≤ 2*n := by dsimp [c]; omega
      refine ⟨n*u+(b-c)*M, ?_, u+c*M, ?_, ?_⟩
      · rw [ih]; exact mem_row.mpr ⟨b-c, hbc, rfl⟩
      · exact mem_row.mpr ⟨c, hc, by omega⟩
      · have he : b-c+c = b := by omega
        calc
          n*u+(b-c)*M+(u+c*M) = (n+1)*u+(b-c+c)*M := by ring
          _ = _ := by rw [he]

theorem sumset_padding {C : Finset Nat} (hz : 0 ∈ C) {l n : Nat} (hln : l ≤ n) :
    sumset C l ⊆ sumset C n := by
  induction n, hln using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ n hn ih =>
    intro x hx
    exact mem_sumset_succ.mpr ⟨x, ih hx, 0, hz, by omega⟩

theorem sumset_insert_zero (U : Finset Nat) (n : Nat) :
    sumset (insert 0 U) n =
      (Finset.range (n+1)).biUnion (fun l => sumset U l) := by
  ext x
  constructor
  · intro hx
    suffices ∃ l ≤ n, x ∈ sumset U l by
      simpa only [Finset.mem_biUnion, Finset.mem_range, Nat.lt_succ_iff] using this
    induction n generalizing x with
    | zero => exact ⟨0, by omega, hx⟩
    | succ n ih =>
      obtain ⟨y, hy, z, hz, rfl⟩ := mem_sumset_succ.mp hx
      obtain ⟨l, hl, hy⟩ := ih y hy
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ⟨l, by omega, by simpa using hy⟩
      · exact ⟨l+1, by omega, mem_sumset_succ.mpr ⟨y, hy, z, hz, rfl⟩⟩
  · intro hx
    obtain ⟨l, hl, hx⟩ := Finset.mem_biUnion.mp hx
    have hln : l ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl
    exact sumset_padding (Finset.mem_insert_self _ _) hln
      (sumset_mono (Finset.subset_insert _ _) l hx)

theorem sum_odd_range (n : Nat) :
    (Finset.range (n+1)).sum (fun l => 2*l+1) = (n+1)^2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

theorem truncated_small_sumset (K M n : Nat) (hM : 0 < M) :
    (sumset (insert 0 (smallGenerators ((2*K+1)*M) M)) n).filter
      (· < K*(((2*K+1)*M)+2*M)+1) =
      (Finset.range (min n K+1)).biUnion (row ((2*K+1)*M) M) := by
  rw [sumset_insert_zero]
  simp_rw [sumset_smallGenerators]
  ext x
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_range,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨⟨l, hln, hx⟩, hcut⟩
    have hlK : l ≤ K := by
      by_contra h
      have := row_above_cutoff hM (show K+1 ≤ l by omega) hx
      omega
    exact ⟨l, by omega, hx⟩
  · rintro ⟨l, hl, hx⟩
    have hc := row_below_cutoff (show l ≤ K by omega) hx
    exact ⟨⟨l, by omega, hx⟩, by omega⟩

/-- The zero-residue contribution to the all-order truncated sumset count. -/
theorem truncatedCount_small (K M n : Nat) (hM : 0 < M) :
    truncatedCount (insert 0 (smallGenerators ((2*K+1)*M) M))
      (K*(((2*K+1)*M)+2*M)+1) n = (min n K+1)^2 := by
  unfold truncatedCount
  rw [truncated_small_sumset K M n hM, Finset.card_biUnion]
  · simp_rw [card_row _ _ _ hM]
    exact sum_odd_range _
  · intro i hi j hj hij
    have hi' : i ≤ K := by simp only [Finset.mem_coe, Finset.mem_range] at hi; omega
    have hj' : j ≤ K := by simp only [Finset.mem_coe, Finset.mem_range] at hj; omega
    exact rows_disjoint hM hi' hj' hij

theorem digit_cutoff_nat (K M d t j l b : Nat)
    (hK : d ≤ K) (hM : 0 < M) (hd : 2 ≤ d)
    (ht : t ≤ 2*d-2) (hj0 : 0 < j) (hj : j < M) (hb : b ≤ 2*l) :
    ((l*((2*K+1)*M)+b*M : Nat) : ℤ) ≤
      digitRho K M d t j ↔
      l+2 ≤ d ∨ (l+1=d ∧ b<t) := by
  have hh := digit_cutoff (K:ℤ) M d t j l b (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have he : ((l*((2*K+1)*M)+b*M : Nat) : ℤ) =
      (l:ℤ)*digitUnit K M + (b:ℤ)*M := by push_cast; unfold digitUnit; ring
  rw [he, hh]
  omega

/-- A full row, a partially admitted row, or an empty row, exactly as in the paper. -/
theorem card_filtered_row (K M d t j l : Nat)
    (hK : d ≤ K) (hM : 0 < M) (hd : 2 ≤ d)
    (ht : t ≤ 2*d-2) (hj0 : 0 < j) (hj : j < M) :
    ((row ((2*K+1)*M) M l).filter
      (fun x : Nat => (x:ℤ) ≤ digitRho K M d t j)).card =
      if l+2 ≤ d then 2*l+1 else if l+1=d then t else 0 := by
  by_cases hlow : l+2 ≤ d
  · rw [ite_eq_left hlow]
    have he : (row ((2*K+1)*M) M l).filter
        (fun x : Nat => (x:ℤ) ≤ digitRho K M d t j) = row ((2*K+1)*M) M l := by
      apply Finset.filter_true_of_mem
      intro x hx
      obtain ⟨b, hb, rfl⟩ := mem_row.mp hx
      exact (digit_cutoff_nat K M d t j l b hK hM hd ht hj0 hj hb).2 (Or.inl hlow)
    rw [he, card_row _ _ _ hM]
  · rw [ite_eq_right hlow]
    by_cases heq : l+1=d
    · rw [ite_eq_left heq]
      have he : (row ((2*K+1)*M) M l).filter
          (fun x : Nat => (x:ℤ) ≤ digitRho K M d t j) =
          (Finset.range t).image (fun b => l*((2*K+1)*M)+b*M) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨hx, hc⟩
          obtain ⟨b, hb, rfl⟩ := mem_row.mp hx
          have hh := (digit_cutoff_nat K M d t j l b hK hM hd ht hj0 hj hb).1 hc
          exact ⟨b, by omega, rfl⟩
        · rintro ⟨b, hb, rfl⟩
          have hb' : b ≤ 2*l := by omega
          exact ⟨mem_row.mpr ⟨b, hb', rfl⟩,
            (digit_cutoff_nat K M d t j l b hK hM hd ht hj0 hj hb').2 (Or.inr ⟨heq, hb⟩)⟩
      rw [he, Finset.card_image_of_injective]
      · simp
      · intro a b hab
        dsimp at hab
        exact Nat.eq_of_mul_eq_mul_right hM (by omega)
    · rw [ite_eq_right heq]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hx, hc⟩ := Finset.mem_filter.mp hx
      obtain ⟨b, hb, rfl⟩ := mem_row.mp hx
      have hh := (digit_cutoff_nat K M d t j l b hK hM hd ht hj0 hj hb).1 hc
      omega

theorem sum_row_counts (d t n : Nat) (hd : 2 ≤ d) :
    (Finset.range n).sum (fun l =>
      if l+2 ≤ d then 2*l+1 else if l+1=d then t else 0) =
      (min n (d-1))^2 + if d ≤ n then t else 0 := by
  induction n with
  | zero => simp; omega
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hlow : n+2 ≤ d
    · have hnd : ¬d ≤ n := by omega
      have hnd' : ¬d ≤ n+1 := by omega
      simp only [ite_eq_left hlow, ite_eq_right hnd, ite_eq_right hnd',
        Nat.min_eq_left (show n ≤ d-1 by omega),
        Nat.min_eq_left (show n+1 ≤ d-1 by omega)]
      ring
    · by_cases heq : n+1=d
      · have hnd : ¬d ≤ n := by omega
        have hnd' : d ≤ n+1 := by omega
        have he : d-1=n := by omega
        simp only [ite_eq_right hlow, ite_eq_left heq, ite_eq_right hnd, ite_eq_left hnd', he,
          Nat.min_self, Nat.min_eq_right (show n ≤ n+1 by omega)]
        omega
      · have hnd : d ≤ n := by omega
        have hnd' : d ≤ n+1 := by omega
        simp only [ite_eq_right hlow, ite_eq_right heq, ite_eq_left hnd, ite_eq_left hnd',
          Nat.min_eq_right (show d-1 ≤ n by omega),
          Nat.min_eq_right (show d-1 ≤ n+1 by omega), Nat.add_zero]

/-- Exact count of all the admitted rows associated with one large generator. -/
theorem card_admitted_rows (K M d t j n : Nat)
    (hK : d ≤ K) (hM : 0 < M) (hd : 2 ≤ d)
    (ht : t ≤ 2*d-2) (hj0 : 0 < j) (hj : j < M) :
    (((Finset.range n).biUnion (row ((2*K+1)*M) M)).filter
      (fun x : Nat => (x:ℤ) ≤ digitRho K M d t j)).card =
      (min n (d-1))^2 + if d ≤ n then t else 0 := by
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  · simp_rw [card_filtered_row K M d t j _ hK hM hd ht hj0 hj]
    exact sum_row_counts d t n hd
  · intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hx, hc⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, _⟩ := Finset.mem_filter.mp hy
    obtain ⟨a', ha', hea⟩ := mem_row.mp hx
    obtain ⟨b', hb', heb⟩ := mem_row.mp hy
    have hca := (digit_cutoff_nat K M d t j a a' hK hM hd ht hj0 hj ha').1 (by simpa [hea] using hc)
    have hcb := (digit_cutoff_nat K M d t j b b' hK hM hd ht hj0 hj hb').1 (by simpa [heb] using hc)
    exact Finset.disjoint_left.mp (rows_disjoint hM (by omega) (by omega) hab) hx hy

end BuchweitzProfiles
