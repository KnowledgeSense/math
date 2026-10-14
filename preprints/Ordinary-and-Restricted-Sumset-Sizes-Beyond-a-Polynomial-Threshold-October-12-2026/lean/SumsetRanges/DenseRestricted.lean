import SumsetRanges.SeparatedConvolution
import SumsetRanges.RestrictedSetOperations

open Finset
namespace SumsetRanges

def denseSet (n x : ℕ) : Finset ℕ := insert x (range n)

@[simp] theorem card_denseSet (n x : ℕ) (hx : n≤x) : (denseSet n x).card=n+1 := by
  rw [denseSet,Finset.card_insert_of_notMem (by simpa using hx)]
  simp

theorem image_add_Icc (x a b : ℕ) : (Icc a b).image (fun y => x+y)=Icc (x+a) (x+b) := by
  ext z
  simp only [mem_image,mem_Icc]
  constructor
  · rintro ⟨y,⟨ha,hb⟩,rfl⟩
    omega
  · rintro ⟨ha,hb⟩
    exact ⟨z-x,⟨by omega,by omega⟩,by omega⟩

theorem card_union_interval_step (a b c d : ℕ) (hac : a≤c) (hbd : b≤d) :
    (Icc a b ∪ Icc c d).card ≤ (Icc a b ∪ Icc (c+1) (d+1)).card ∧
    (Icc a b ∪ Icc (c+1) (d+1)).card ≤ (Icc a b ∪ Icc c d).card+1 := by
  have hi : Icc a b ∩ Icc c d=Icc c b := by ext i; simp only [mem_inter,mem_Icc]; omega
  have hi' : Icc a b ∩ Icc (c+1) (d+1)=Icc (c+1) b := by
    ext i; simp only [mem_inter,mem_Icc]; omega
  have h0 := Finset.card_union_add_card_inter (Icc a b) (Icc c d)
  have h1 := Finset.card_union_add_card_inter (Icc a b) (Icc (c+1) (d+1))
  rw [hi] at h0
  rw [hi'] at h1
  simp only [Nat.card_Icc] at h0 h1
  omega

/-- Moving the outlying dense point by one changes each restricted sum count by
 zero or one, with a fixed sign. -/
theorem dense_restricted_step (n x q : ℕ) (hn : 1≤n) (hx : n≤x) :
    (restrictedSums (denseSet n x) q).card ≤ (restrictedSums (denseSet n (x+1)) q).card ∧
    (restrictedSums (denseSet n (x+1)) q).card ≤ (restrictedSums (denseSet n x) q).card+1 := by
  cases q with
  | zero => simp
  | succ q =>
    have hxn : x∉range n := by simpa using hx
    have hx1n : x+1∉range n := by simp; omega
    simp only [denseSet,restrictedSums_insert_succ _ _ hxn,restrictedSums_insert_succ _ _ hx1n]
    by_cases hqn : q+1≤n
    · rw [restrictedSums_range n (q+1) hn hqn,restrictedSums_range n q hn (by omega),
        image_add_Icc,image_add_Icc]
      have hchoose : (q+1).choose 2=q.choose 2+q := by
        rw [Nat.choose_succ_succ,Nat.choose_one_right,Nat.add_comm]
      have hac : (q+1).choose 2≤x+q.choose 2 := by rw [hchoose]; omega
      have hbd : (q+1)*(n-(q+1))+(q+1).choose 2≤x+(q*(n-q)+q.choose 2) := by
        rw [hchoose]
        have he : n-q=n-(q+1)+1 := by omega
        rw [he]
        have hDx := le_trans (Nat.sub_le n (q+1)) hx
        nlinarith
      have hh := card_union_interval_step ((q+1).choose 2) ((q+1)*(n-(q+1))+(q+1).choose 2)
        (x+q.choose 2) (x+(q*(n-q)+q.choose 2)) hac hbd
      simpa only [Nat.add_right_comm x 1] using hh
    · have hlt : n<q+1 := by omega
      rw [restrictedSums_range_of_lt n (q+1) hlt]
      simp only [Finset.empty_union]
      rw [Finset.card_image_of_injective _ (fun a b he => Nat.add_left_cancel he),
        Finset.card_image_of_injective _ (fun a b he => Nat.add_left_cancel he)]
      omega

@[simp] theorem dense_restricted_one (n x : ℕ) (hx : n≤x) :
    (restrictedSums (denseSet n x) 1).card=n+1 := by
  rw [restrictedSums_one,card_denseSet n x hx]

theorem card_restrictedSums_range_le (n q : ℕ) (hn : 1≤n) :
    (restrictedSums (range n) q).card ≤ q*n+1 := by
  by_cases hq : q≤n
  · rw [restrictedSums_range n q hn hq,Nat.card_Icc]
    have hh := Nat.mul_le_mul_left q (Nat.sub_le n q)
    omega
  · rw [restrictedSums_range_of_lt n q (by omega)]
    simp

theorem dense_restricted_bound (h n x q : ℕ) (hn : 1≤n) (hx : n≤x)
    (hq : 1≤q) (hqh : q≤h) : (restrictedSums (denseSet n x) q).card ≤ 2*h*(n+1) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
  rw [denseSet,restrictedSums_insert_succ _ _ (by simpa using hx)]
  have hh := Finset.card_union_le (restrictedSums (range n) (r+1))
    ((restrictedSums (range n) r).image (fun y => x+y))
  have hi := Finset.card_image_le (s := restrictedSums (range n) r) (f := fun y => x+y)
  have hb1 := card_restrictedSums_range_le n (r+1) hn
  have hb0 := card_restrictedSums_range_le n r hn
  nlinarith

theorem mem_restrictedSums_range_bound (n q y : ℕ) (hn : 1≤n)
    (hy : y∈restrictedSums (range n) q) : y≤q*(n-1) := by
  obtain ⟨S,hS,hSc,rfl⟩ := mem_restrictedSums.mp hy
  have hb := (nat_finset_sum_bounds S n hn hS).2
  rw [hSc] at hb
  omega

theorem dense_restricted_endpoint (h n q : ℕ) (hn : 1≤n) (hq : q+1≤h) :
    (restrictedSums (denseSet n (h*(n-1)+1)) (q+1)).card =
      (restrictedSums (range n) (q+1)).card + (restrictedSums (range n) q).card := by
  have hx : n≤h*(n-1)+1 := by nlinarith [Nat.sub_add_cancel hn]
  rw [denseSet,restrictedSums_insert_succ _ _ (by simpa using hx),
    Finset.card_union_of_disjoint,Finset.card_image_of_injective _ (fun a b he => Nat.add_left_cancel he)]
  apply Finset.disjoint_left.mpr
  intro y hy hz
  have hb := mem_restrictedSums_range_bound n (q+1) y hn hy
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hz
  have hh := Nat.mul_le_mul_right (n-1) hq
  omega

end SumsetRanges
