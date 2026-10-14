import SumsetRanges.ResidueBlowup

open Finset
namespace SumsetRanges

theorem bounded_pad (A : Finset ℤ) (D n l : ℕ)
    (hA : A⊆Icc 0 (D:ℤ)) (hn : n≤D+1) (hcard : A.card+l≤n) :
    ∃B : Finset ℤ, B.card=n ∧ A⊆B ∧ B⊆Icc 0 (D:ℤ) ∧
      (∀x : ℕ,x<l → (x:ℤ)∈B) := by
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
  refine ⟨B,hBc,Finset.subset_union_left.trans hAB,hB,?_⟩
  intro x hx
  exact hAB (Finset.mem_union_right A (Finset.mem_image.mpr ⟨x,Finset.mem_range.mpr hx,rfl⟩))

theorem restricted_filling_superset (A B : Finset ℤ) (h : ℕ) (D : ℤ)
    (hAB : A⊆B) (hB : B⊆Icc 0 D)
    (hf : restrictedSums A h=Icc (h.choose 2:ℤ) ((h:ℤ)*D-h.choose 2)) :
    restrictedSums B h=Icc (h.choose 2:ℤ) ((h:ℤ)*D-h.choose 2) := by
  apply Finset.Subset.antisymm
  · intro x hx
    simpa using Finset.mem_Icc.mpr (restrictedSums_int_bounds B 0 D
      (fun _ hb => Finset.mem_Icc.mp (hB hb)) h hx)
  · rw [←hf]
    exact restrictedSums_mono hAB h

/-- An overlapping terminal interval extends the restricted filling diameter. -/
theorem restricted_filling_terminal (A : Finset ℤ) (h : ℕ) (a b D : ℤ)
    (hA : A⊆Icc 0 b) (ha : 0≤a) (hab : a≤b) (hbD : b≤D)
    (hlength : (h:ℤ)≤D-a+1)
    (hgap : (h:ℤ)*a+h.choose 2≤(h:ℤ)*b-h.choose 2+1)
    (hf : restrictedSums A h=Icc (h.choose 2:ℤ) ((h:ℤ)*b-h.choose 2)) :
    restrictedSums (A∪Icc a D) h=Icc (h.choose 2:ℤ) ((h:ℤ)*D-h.choose 2) := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hB : ∀y∈A∪Icc a D,0≤y ∧ y≤D := by
      intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · have hh := Finset.mem_Icc.mp (hA hy); constructor <;> omega
      · have hh := Finset.mem_Icc.mp hy; constructor <;> omega
    simpa using Finset.mem_Icc.mpr (restrictedSums_int_bounds _ 0 D hB h hx)
  · intro x hx
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hx
    by_cases hxb : x≤(h:ℤ)*b-h.choose 2
    · apply restrictedSums_mono Finset.subset_union_left h
      rw [hf]
      exact Finset.mem_Icc.mpr ⟨hl,hxb⟩
    · apply restrictedSums_mono Finset.subset_union_right h
      rw [restrictedSums_int_Icc a D h (by omega) hlength]
      exact Finset.mem_Icc.mpr ⟨by omega,hu⟩

end SumsetRanges
