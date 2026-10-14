import GenericValueSemigroups.GenusConductor
import GenericValueSemigroups.FiniteWindow

namespace GenericValueSemigroups
open scoped BigOperators Classical

theorem weightSet_below_minimum {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0<r i)
    (m : ℕ) (hm : 0<m) (hmin : ∀ i, m≤r i) : weightSet r m={0} := by
  ext α
  rw [mem_weightSet r hr,Finset.mem_singleton]
  constructor
  · intro h
    funext i
    have hi : α i*r i ≤ weight r α :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (α j*r j)) (Finset.mem_univ i)
    have hz : α i=0 := by
      by_contra hne
      have hh := Nat.le_mul_of_pos_left (r i) (by omega : 0<α i)
      have hh' := hmin i
      omega
    exact hz
  · rintro rfl
    simpa [weight] using hm

theorem no_positive_greedy_below_minimum {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (hd : 0<d) (m : ℕ) (hm : 0<m) (hmin : ∀ i,m≤r i)
    (n : ℕ) (hn : 0<n) (hnm : n<m) :
    n ∉ Set.range (greedy (weightAt r hr hd)) := by
  rintro ⟨j,hj⟩
  have hw : weightAt r hr hd j<m := lt_of_le_of_lt
    (weight_le_greedy (weightAt r hr hd) j) (by omega)
  have hc := (weightAt_lt_iff r hr hd j m).mp hw
  have hmC : weightCount r m=1 := by
    rw [weightCount,weightSet_below_minimum r hr m hm hmin,Finset.card_singleton]
  have hj0 : j=0 := by omega
  simp only [hj0,greedy_zero,weightAt_zero] at hj
  omega

theorem greedy_eq_index_of_unit_coordinate {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (hd : 0<d) (i : Fin d) (hi : r i=1) (n : ℕ) :
    greedy (weightAt r hr hd) n=n := by
  apply le_antisymm _ (index_le_greedy _ _)
  apply greedy_le_of_weight_bound (weightAt r hr hd) 0
  intro j
  have hh := weightCount_large r hr i j
  rw [hi,mul_one] at hh
  have hw := (weightAt_lt_iff r hr hd j (j+1)).mpr hh
  omega

theorem greedy_range_eq_univ_iff {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (hd : 0<d) :
    Set.range (greedy (weightAt r hr hd))=Set.univ ↔ ∃ i,r i=1 := by
  constructor
  · intro h
    by_contra hnone
    have hn := no_positive_greedy_below_minimum r hr hd 2 (by omega)
      (fun i => by have hp := hr i; have hh : r i≠1 := fun he => hnone ⟨i,he⟩; omega)
      1 (by omega) (by omega)
    rw [h] at hn
    exact hn (Set.mem_univ _)
  · rintro ⟨i,hi⟩
    apply Set.eq_univ_of_forall
    intro n
    exact ⟨n,greedy_eq_index_of_unit_coordinate r hr hd i hi n⟩

theorem greedy_genus_ge_minimum_sub_one {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (hd : 0<d) (m : ℕ) (hm : 0<m) (hmin : ∀ i,m≤r i)
    (gaps : Finset ℕ) (hg : ∀ n, n∈gaps ↔ n∉Set.range (greedy (weightAt r hr hd))) :
    m-1≤gaps.card := by
  have hsub : (Finset.range (m-1)).image (fun n => n+1) ⊆ gaps := by
    intro n hn
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hn
    apply (hg _).mpr
    apply no_positive_greedy_below_minimum r hr hd m hm hmin
    · omega
    · have hh := Finset.mem_range.mp hj; omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h),Finset.card_range] at hc
  exact hc

/-- Positive indecomposable elements are precisely the minimal additive generators. -/
def IsMinimalGenerator (S : Set ℕ) (n : ℕ) : Prop :=
  n∈S ∧ 0<n ∧ ∀ a∈S, ∀ b∈S, n=a+b → a=0 ∨ b=0

/-- Every minimal generator lies below a conductor plus a positive semigroup element. -/
theorem minimal_generator_lt_conductor_add (S : Set ℕ) (C m : ℕ)
    (hC : 0<C) (hm : 0<m) (hmS : m∈S) (htail : ∀ n,C≤n → n∈S)
    (n : ℕ) (hn : IsMinimalGenerator S n) : n<C+m := by
  by_contra hbad
  have hsub : n-m∈S := htail _ (by omega)
  have h := hn.2.2 m hmS (n-m) hsub (by omega)
  omega

theorem exists_minimum_coordinate {d : ℕ} (r : Fin d → ℕ) (hd : 0<d) :
    ∃ i : Fin d, ∀ j, r i≤r j := by
  let S := Finset.univ.image r
  have hS : S.Nonempty := ⟨r ⟨0,hd⟩,Finset.mem_image.mpr ⟨⟨0,hd⟩,Finset.mem_univ _,rfl⟩⟩
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
  refine ⟨i,?_⟩
  intro j
  rw [hi]
  exact Finset.min'_le S _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)

end GenericValueSemigroups
