import ASR312.FirstColumn
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

namespace ASR312

 def Entry.value : Entry → ℤ
  | .minus => -1
  | .zero => 0
  | .plus => 1

 def entrySum (l : List Entry) : ℤ := (l.map Entry.value).sum
 def endValue (o : Option Entry) : ℤ := (o.getD .zero).value

 theorem nonzeroEntries_sum (l : List Entry) : entrySum (nonzeroEntries l) = entrySum l := by
  induction l with
  | nil => rfl
  | cons a l ih => cases a <;> simp_all [nonzeroEntries,entrySum,Entry.value]

 theorem nonzeroEntries_ne_zero (l : List Entry) : ∀ x ∈ nonzeroEntries l, x ≠ .zero := by
  intro x hx
  exact of_decide_eq_true (by simpa [nonzeroEntries] using (List.mem_filter.mp hx).2)

 theorem alternating_sum_endpoints (l : List Entry) (ha : l.IsChain (· ≠ ·))
    (hz : ∀ x ∈ l, x ≠ .zero) :
    2 * entrySum l = endValue l.head? + endValue l.getLast? := by
  induction l with
  | nil => simp [entrySum,endValue,Entry.value]
  | cons a l ih =>
    cases l with
    | nil => simp [entrySum,endValue]; omega
    | cons b l =>
      have hh := List.isChain_cons_cons.mp ha
      have htail : ∀ x ∈ b::l, x ≠ .zero := fun x hx => hz x (List.mem_cons_of_mem a hx)
      have he := ih hh.2 htail
      have haz := hz a (by simp)
      have hbz := hz b (by simp)
      have hab : a.value+b.value = 0 := by cases a <;> cases b <;> simp_all [Entry.value]
      simp only [entrySum,List.map_cons,List.sum_cons] at he ⊢
      simp only [List.head?_cons,endValue,Option.getD_some] at he ⊢
      have hl : (a::b::l).getLast? = (b::l).getLast? := by simp
      rw [hl]
      omega

 theorem endValue_bounds (o : Option Entry) : -1 ≤ endValue o ∧ endValue o ≤ 1 := by
  cases o with
  | none => norm_num [endValue,Entry.value]
  | some x => cases x <;> norm_num [endValue,Entry.value]

 theorem row_sum_one_or_zero (l : List Entry) (ha : Alternates l)
    (hs : StartsPositive l) (he : EndsPositive l) :
    entrySum l = if nonzeroEntries l = [] then 0 else 1 := by
  have hsum := alternating_sum_endpoints (nonzeroEntries l) ha (nonzeroEntries_ne_zero l)
  rw [nonzeroEntries_sum] at hsum
  by_cases hz : nonzeroEntries l = []
  · rw [ite_eq_left hz]
    rw [hz] at hsum
    norm_num [endValue,Entry.value] at hsum
    omega
  · rw [ite_eq_right hz]
    have hs' : (nonzeroEntries l).head? = some .plus := hs.resolve_left (by simpa using hz)
    have he' : (nonzeroEntries l).getLast? = some .plus := he.resolve_left (by simpa using hz)
    rw [hs',he'] at hsum
    norm_num [endValue,Entry.value] at hsum
    omega

 theorem column_sum_bounds (l : List Entry) (ha : Alternates l) (hs : StartsPositive l) :
    0 ≤ entrySum l ∧ entrySum l ≤ 1 := by
  have hsum := alternating_sum_endpoints (nonzeroEntries l) ha (nonzeroEntries_ne_zero l)
  rw [nonzeroEntries_sum] at hsum
  have hb := endValue_bounds (nonzeroEntries l).getLast?
  rcases hs with hs | hs
  · have hn : nonzeroEntries l = [] := by simpa using hs
    rw [hn] at hsum
    norm_num [endValue,Entry.value] at hsum
    omega
  · rw [hs] at hsum
    change 2 * entrySum l = 1 + endValue (nonzeroEntries l).getLast? at hsum
    omega

end ASR312
