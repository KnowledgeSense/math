import ASR312.ForcedZeros

namespace ASR312

 theorem alternates_prefix {l L : List Entry} (hp : l <+: L) (ha : Alternates L) : Alternates l := by
  obtain ⟨t,ht⟩ := hp.filter (· != .zero)
  unfold Alternates nonzeroEntries at ha ⊢
  rw [← ht] at ha
  exact (List.isChain_append.mp ha).1

 theorem startsPositive_prefix {l L : List Entry} (hp : l <+: L) (hs : StartsPositive L) :
    StartsPositive l := by
  obtain ⟨t,ht⟩ := hp.filter (· != .zero)
  unfold StartsPositive nonzeroEntries at hs ⊢
  rw [← ht] at hs
  cases hx : l.filter (· != .zero) with
  | nil => simp
  | cons a l => simpa [hx] using hs

 theorem take_ofFn {α : Type*} {n p : ℕ} (hp : p ≤ n) (f : Fin n → α) :
    (List.ofFn f).take p = List.ofFn (fun i : Fin p => f (Fin.castLE hp i)) := by
  apply List.ext_getElem
  · simp [hp]
  · intro j h₁ h₂
    simp only [List.getElem_take,List.getElem_ofFn]
    rfl

 def prefixSum {n : ℕ} (f : Fin n → Entry) (p : ℕ) : ℤ :=
  ∑ j ∈ Finset.univ.filter (fun j => j.val < p), (f j).value

 theorem prefixSum_eq {n p : ℕ} (f : Fin n → Entry) (hp : p ≤ n) :
    prefixSum f p = entrySum ((List.ofFn f).take p) := by
  rw [take_ofFn hp]
  simp only [entrySum,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  symm
  apply Finset.sum_bij (fun j _ => Fin.castLE hp j)
  · intro j _
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.val_castLE]
    exact j.isLt
  · intro a _ b _ hab
    exact Fin.ext (congrArg (fun j : Fin n => j.val) hab)
  · intro b hb
    have hbp : b.val < p := (Finset.mem_filter.mp hb).2
    exact ⟨⟨b.val,hbp⟩,Finset.mem_univ _,Fin.ext rfl⟩
  · intro j _
    rfl

 theorem prefixSum_bounds {n p : ℕ} (f : Fin n → Entry) (hp : p ≤ n)
    (ha : Alternates (List.ofFn f)) (hs : StartsPositive (List.ofFn f)) :
    0 ≤ prefixSum f p ∧ prefixSum f p ≤ 1 := by
  rw [prefixSum_eq f hp]
  exact column_sum_bounds _ (alternates_prefix (List.take_prefix p _) ha)
    (startsPositive_prefix (List.take_prefix p _) hs)

 theorem plus_after_prefix_of_total {n p : ℕ} (f : Fin n → Entry)
    (hs : ∑ j, (f j).value = 1) (hp : prefixSum f p = 0) :
    ∃ j, p ≤ j.val ∧ f j = .plus := by
  classical
  by_contra hh
  have hn : ∀ j, p ≤ j.val → f j ≠ .plus := by simpa using hh
  have hle : (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬j.val < p), (f j).value) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have hjp : p ≤ j.val := by have := (Finset.mem_filter.mp hj).2; omega
    have hnot := hn j hjp
    cases he : f j <;> simp_all [Entry.value]
  have he := Finset.sum_filter_add_sum_filter_not (s:=(Finset.univ : Finset (Fin n)))
    (p:=fun j => j.val < p) (f:=fun j => (f j).value)
  change prefixSum f p + _ = _ at he
  rw [hp,hs] at he
  omega

end ASR312
