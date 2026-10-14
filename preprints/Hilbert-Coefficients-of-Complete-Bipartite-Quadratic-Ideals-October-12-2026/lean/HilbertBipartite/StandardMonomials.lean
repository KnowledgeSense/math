import HilbertBipartite.Definitions

namespace HilbertBipartite

lemma coefficient_le_degree {p : Nat} (a : BlockExponent p) (i : Fin p) :
    a i ≤ blockDegree a := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)

lemma half_coefficient_le_halfDegree {p : Nat} (a : BlockExponent p) (i : Fin p) :
    a i / 2 ≤ halfDegree a := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (a j / 2)) (Finset.mem_univ i)

lemma standard_left_bound {p q s : Nat} {a : BlockExponent p} {b : BlockExponent q}
    (h : ¬ PowerCriterion s a b) (i : Fin p) : a i < 2*s := by
  by_cases hi : a i < 2*s
  · exact hi
  · have hdeg := coefficient_le_degree a i
    have hhalf := half_coefficient_le_halfDegree a i
    have hp : PowerCriterion s a b := by
      unfold PowerCriterion
      constructor
      · omega
      constructor <;> omega
    exact False.elim (h hp)

lemma powerCriterion_swap {p q s : Nat} (a : BlockExponent p) (b : BlockExponent q) :
    PowerCriterion s a b ↔ PowerCriterion s b a := by
  unfold PowerCriterion
  omega

lemma standard_right_bound {p q s : Nat} {a : BlockExponent p} {b : BlockExponent q}
    (h : ¬ PowerCriterion s a b) (i : Fin q) : b i < 2*s := by
  apply standard_left_bound (a := b) (b := a)
  exact fun hh => h ((powerCriterion_swap a b).mpr hh)

@[simp] theorem mem_exponentBox {p s : Nat} {a : BlockExponent p} :
    a ∈ exponentBox p s ↔ ∀ i, a i < 2*s := by
  classical
  simp [exponentBox, Finset.mem_finsupp_iff]

/-- The finite enumeration imposes no artificial restriction: precisely all
standard exponent pairs are included. -/
@[simp] theorem mem_standardExponents {p q s : Nat} {a : BlockExponent p}
    {b : BlockExponent q} : (a,b) ∈ standardExponents p q s ↔ ¬ PowerCriterion s a b := by
  classical
  simp only [standardExponents, Finset.mem_filter, Finset.mem_product, mem_exponentBox]
  exact ⟨fun h => h.2, fun h => ⟨⟨standard_left_bound h, standard_right_bound h⟩, h⟩⟩

end HilbertBipartite
