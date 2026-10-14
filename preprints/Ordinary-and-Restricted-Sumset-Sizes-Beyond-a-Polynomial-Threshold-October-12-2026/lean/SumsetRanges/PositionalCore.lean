import SumsetRanges.PositionalDigits

open Finset
namespace SumsetRanges

theorem sum_fin_prefix {α : Type*} [AddCommMonoid α] (s j : ℕ) (hj : j≤s) (f : ℕ → α) :
    (∑i : Fin s, if i.val<j then f i.val else 0)=∑i : Fin j,f i.val := by
  induction s with
  | zero =>
      have he : j=0 := by omega
      subst j
      simp
  | succ s ih =>
      by_cases hjs : j≤s
      · rw [Fin.sum_univ_castSucc]
        simpa [show ¬s<j by omega] using ih hjs
      · have he : j=s+1 := by omega
        subst j
        apply Finset.sum_congr rfl
        intro i _
        simp [i.isLt]

def topDigits (g s D : ℕ) : Finset ℤ :=
  insert (D:ℤ) ((range (D/g^s+1)).image (fun j => ((j*g^s:ℕ):ℤ)))

def positionalCore (g s D : ℕ) : Finset ℤ :=
  topDigits g s D ∪ univ.biUnion (fun i : Fin s =>
    ((digitSet g i.val).image (fun x : ℕ => (x:ℤ))) ∪
    ((digitSet g i.val).image (fun x : ℕ => (D:ℤ)-(x:ℤ))))

theorem topDigits_subset_core (g s D : ℕ) : topDigits g s D⊆positionalCore g s D :=
  Finset.subset_union_left

theorem digit_mem_core (g s D : ℕ) (i : Fin s) {x : ℕ} (hx : x∈digitSet g i.val) :
    (x:ℤ)∈positionalCore g s D := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_univ _,Finset.mem_union_left _ ?_⟩
  exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

theorem reflected_digit_mem_core (g s D : ℕ) (i : Fin s) {x : ℕ} (hx : x∈digitSet g i.val) :
    (D:ℤ)-(x:ℤ)∈positionalCore g s D := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_univ _,Finset.mem_union_right _ ?_⟩
  exact Finset.mem_image.mpr ⟨x,hx,rfl⟩

/-- Reflected low-position digits give a full interval of length g^s. -/
theorem mixed_digits_mem (g s D j t : ℕ) (hg : 1≤g) (hj : j≤s) (ht : t<g^s) :
    (t:ℤ)+(j:ℤ)*D+1-(g:ℤ)^j ∈ ordinarySums (positionalCore g s D) s := by
  obtain ⟨v,hv,he⟩ := bounded_digits g s t hg ht
  let a : Fin s → ℤ := fun i => if i.val<j then
    (D:ℤ)-((g-1-v i)*g^i.val:ℕ) else (v i*g^i.val:ℕ)
  have ha (i : Fin s) : a i∈positionalCore g s D := by
    dsimp [a]
    split_ifs with hi
    · exact reflected_digit_mem_core g s D i
        ((mem_digitSet _ _ _).mpr ⟨g-1-v i,by have := hv i; omega,rfl⟩)
    · exact digit_mem_core g s D i ((mem_digitSet _ _ _).mpr ⟨v i,hv i,rfl⟩)
  have hai (i : Fin s) : a i=(v i:ℤ)*(g:ℤ)^i.val+
      (if i.val<j then (D:ℤ) else 0)-
      (if i.val<j then ((g-1:ℕ):ℤ)*(g:ℤ)^i.val else 0) := by
    dsimp [a]
    split_ifs
    · have hvi : v i≤g-1 := by have := hv i; omega
      push_cast [Nat.cast_sub hvi]
      ring
    · simp
  apply (mem_ordinarySums _ _ _).mpr
  refine ⟨a,ha,?_⟩
  calc
    (∑i,a i) = (∑i,(v i:ℤ)*(g:ℤ)^i.val)+
        (∑i : Fin s,if i.val<j then (D:ℤ) else 0)-
        (∑i : Fin s,if i.val<j then ((g-1:ℕ):ℤ)*(g:ℤ)^i.val else 0) := by
      simp only [hai,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    _ = (t:ℤ)+(j:ℤ)*D-(((g:ℤ)^j)-1) := by
      rw [sum_fin_prefix s j hj (fun _ => (D:ℤ)),
        sum_fin_prefix s j hj (fun i => ((g-1:ℕ):ℤ)*(g:ℤ)^i)]
      have he' : (∑i,(v i:ℤ)*(g:ℤ)^i.val)=(t:ℤ) := by exact_mod_cast he
      have hs : (∑i : Fin j,((g-1:ℕ):ℤ)*(g:ℤ)^i.val)+1=(g:ℤ)^j := by
        exact_mod_cast maximal_digit_sum g j hg
      rw [he']
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      omega
    _ = _ := by ring

end SumsetRanges
