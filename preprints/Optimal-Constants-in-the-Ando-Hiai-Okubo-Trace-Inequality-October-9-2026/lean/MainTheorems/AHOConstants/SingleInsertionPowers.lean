import MainTheorems.AHOConstants.SpectralPowers
import Mathlib.Data.List.TakeDrop

namespace ResearchMain.AHOConstants

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def insertedMatrix {m : ℕ} (X : Matrix I I ℂ) (j : Fin (m + 1))
    (N : Fin (m + 1) → Matrix I I ℂ) (i : Fin (m + 1)) : Matrix I I ℂ :=
  if i = j then X * N i else N i

omit [DecidableEq I] in
theorem ofFn_insertedMatrix {m : ℕ} (X : Matrix I I ℂ) (j : Fin (m + 1))
    (N : Fin (m + 1) → Matrix I I ℂ) :
    List.ofFn (insertedMatrix X j N) = (List.ofFn N).set j.val (X * N j) := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  have hin : i < m + 1 := by simpa using hi
  simp only [List.getElem_ofFn, List.getElem_set, insertedMatrix]
  by_cases hij : i = j.val
  · subst i
    simp
  · have hfin : (⟨i, hin⟩ : Fin (m + 1)) ≠ j := fun h => hij (congrArg Fin.val h)
    simp only [Ne.symm hij, hfin, ite_false]

theorem spectralPower_list_product {B : Matrix I I ℂ} (hB : B.PosSemidef)
    (xs : List ℝ) (hx : ∀ r ∈ xs, 0 ≤ r) :
    (xs.map (spectralPower B)).prod = spectralPower B xs.sum := by
  revert hx
  induction xs with
  | nil => intro _; simpa using (spectralPower_zero B hB).symm
  | cons r xs ih =>
    intro hx
    have ht : ∀ s ∈ xs, 0 ≤ s := fun s hs => hx s (by simp [hs])
    rw [List.map_cons, List.prod_cons, ih ht, List.sum_cons]
    exact (spectralPower_add B hB (hx r (by simp)) (List.sum_nonneg ht)).symm

theorem insertedMatrix_trace_of_powers {m : ℕ} (X : Matrix I I ℂ)
    {B : Matrix I I ℂ} (hB : B.PosSemidef) (j : Fin (m + 1))
    (q : Fin (m + 1) → ℝ) (hq : ∀ i, 0 ≤ q i) (hsum : (∑ i, q i) = 1) :
    Matrix.trace (List.ofFn (insertedMatrix X j (fun i => spectralPower B (q i)))).prod =
      Matrix.trace (X * B) := by
  let xs := List.ofFn q
  have hxs : ∀ r ∈ xs, 0 ≤ r := by
    intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact hq i
  have hj : j.val < xs.length := by simpa [xs] using j.isLt
  have hsplit : xs.take j.val ++ [q j] ++ xs.drop (j.val + 1) = xs := by
    rw [List.append_assoc]
    have he : xs.get ⟨j.val, hj⟩ = q j := by
      simp only [xs, List.get_eq_getElem, List.getElem_ofFn]
    rw [← he, List.singleton_append, List.cons_get_drop_succ, List.take_append_drop]
  have hmass : q j + (xs.drop (j.val + 1)).sum + (xs.take j.val).sum = 1 := by
    have hm := congrArg List.sum hsplit
    simp only [List.sum_append, List.sum_singleton] at hm
    have hxsum : xs.sum = 1 := by simpa only [xs, List.sum_ofFn] using hsum
    linarith
  have ht : ∀ r ∈ xs.take j.val, 0 ≤ r := fun r hr => hxs r (List.mem_of_mem_take hr)
  have hd : ∀ r ∈ xs.drop (j.val + 1), 0 ≤ r :=
    fun r hr => hxs r (List.mem_of_mem_drop hr)
  rw [ofFn_insertedMatrix]
  have hmap : List.ofFn (fun i => spectralPower B (q i)) = xs.map (spectralPower B) := by
    simp only [xs, List.map_ofFn]
    rfl
  rw [hmap, List.set_eq_take_append_cons_drop]
  simp only [List.length_map, hj, ite_true, ← List.map_take, ← List.map_drop,
    List.prod_append, List.prod_cons]
  rw [spectralPower_list_product hB _ ht, spectralPower_list_product hB _ hd]
  rw [Matrix.trace_mul_comm (spectralPower B (xs.take j.val).sum)
    ((X * spectralPower B (q j)) * spectralPower B (xs.drop (j.val + 1)).sum)]
  simp only [Matrix.mul_assoc]
  rw [← spectralPower_add B hB (List.sum_nonneg hd) (List.sum_nonneg ht),
    ← spectralPower_add B hB (hq j) (add_nonneg (List.sum_nonneg hd) (List.sum_nonneg ht))]
  have hmass' : q j + ((xs.drop (j.val + 1)).sum + (xs.take j.val).sum) = 1 := by
    linarith
  rw [hmass', spectralPower_one B hB]

end ResearchMain.AHOConstants
