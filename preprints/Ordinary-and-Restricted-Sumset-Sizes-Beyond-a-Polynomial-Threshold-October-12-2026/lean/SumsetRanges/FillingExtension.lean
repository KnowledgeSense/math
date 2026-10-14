import SumsetRanges.PositionalCoverage

open Finset
open scoped Pointwise
namespace SumsetRanges

/-- Once an interval is filled, its endpoints extend filling to every larger number of summands. -/
theorem ordinary_filling_extend (A : Finset ℤ) (D q h : ℕ) (hq : 1≤q) (hqh : q≤h)
    (hA : ∀a∈A,0≤a ∧ a≤D) (h0 : 0∈A) (hD : (D:ℤ)∈A)
    (hfill : ordinarySums A q=Icc 0 ((q*D:ℕ):ℤ)) :
    ordinarySums A h=Icc 0 ((h*D:ℕ):ℤ) := by
  induction h, hqh using Nat.le_induction with
  | base => exact hfill
  | succ h hqh ih =>
      ext w
      constructor
      · intro hw
        obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp hw
        apply Finset.mem_Icc.mpr
        refine ⟨Finset.sum_nonneg (fun i _ => (hA _ (hv i)).1),?_⟩
        calc
          _ ≤ ∑_i : Fin (h+1),(D:ℤ) := Finset.sum_le_sum (fun i _ => (hA _ (hv i)).2)
          _ = _ := by simp
      · intro hw
        obtain ⟨hw0,hwD⟩ := Finset.mem_Icc.mp hw
        rw [ordinarySums,ih]
        apply Finset.mem_add.mpr
        by_cases hh : w≤((h*D:ℕ):ℤ)
        · exact ⟨0,h0,w,Finset.mem_Icc.mpr ⟨hw0,hh⟩,by simp⟩
        · have hDh : (D:ℤ)≤((h*D:ℕ):ℤ) := by
            exact_mod_cast (Nat.le_mul_of_pos_left D (by omega))
          refine ⟨D,hD,w-D,Finset.mem_Icc.mpr ⟨by omega,?_⟩,by ring⟩
          push_cast at hwD ⊢
          nlinarith

/-- Extend a bounded filling core to exactly n points, including a prescribed initial interval. -/
theorem filling_pad (A : Finset ℤ) (D h n l : ℕ)
    (hA : A⊆Icc 0 (D:ℤ)) (hn : n≤D+1)
    (hcard : A.card+l≤n) (hfill : ordinarySums A h=Icc 0 ((h*D:ℕ):ℤ)) :
    ∃B : Finset ℤ, B.card=n ∧ B⊆Icc 0 (D:ℤ) ∧
      (∀x : ℕ,x<l → (x:ℤ)∈B) ∧ ordinarySums B h=Icc 0 ((h*D:ℕ):ℤ) := by
  let P := (range l).image (fun x : ℕ => (x:ℤ))
  have hP : P⊆Icc 0 (D:ℤ) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    have hy' := Finset.mem_range.mp hy
    exact Finset.mem_Icc.mpr ⟨by positivity,by exact_mod_cast (by omega : y≤D)⟩
  have hAP : (A∪P).card≤n :=
    (Finset.card_union_le A P).trans ((Nat.add_le_add_left
      (Finset.card_image_le.trans_eq (Finset.card_range l)) _).trans hcard)
  have hcap : n≤(Icc 0 (D:ℤ)).card := by simpa using hn
  obtain ⟨B,hAB,hB,hBc⟩ := Finset.exists_subsuperset_card_eq (Finset.union_subset hA hP) hAP hcap
  refine ⟨B,hBc,hB,?_,?_⟩
  · intro x hx
    exact hAB (Finset.mem_union_right A (Finset.mem_image.mpr ⟨x,Finset.mem_range.mpr hx,rfl⟩))
  · apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨v,hv,rfl⟩ := (mem_ordinarySums _ _ _).mp hx
      have hb (i : Fin h) := Finset.mem_Icc.mp (hB (hv i))
      apply Finset.mem_Icc.mpr
      refine ⟨Finset.sum_nonneg (fun i _ => (hb i).1),?_⟩
      calc
        _ ≤ ∑_i : Fin h,(D:ℤ) := Finset.sum_le_sum (fun i _ => (hb i).2)
        _ = _ := by simp
    · rw [←hfill]
      exact ordinarySums_mono (Finset.subset_union_left.trans hAB) h

end SumsetRanges
