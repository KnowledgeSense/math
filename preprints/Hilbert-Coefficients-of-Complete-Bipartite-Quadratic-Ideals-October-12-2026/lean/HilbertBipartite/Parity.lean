import HilbertBipartite.StandardMonomials
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring

namespace HilbertBipartite

noncomputable def binaryExponent {p : Nat} (E : Finset (Fin p)) : BlockExponent p :=
  ∑ i ∈ E, Finsupp.single i 1

@[simp] theorem binaryExponent_apply {p : Nat} (E : Finset (Fin p)) (i : Fin p) :
    binaryExponent E i = if i ∈ E then 1 else 0 := by
  classical
  simp [binaryExponent, Finsupp.single_apply]

noncomputable def doubleWithSubset {p : Nat} (b : BlockExponent p) (E : Finset (Fin p)) :
    BlockExponent p := 2 • b + binaryExponent E

@[simp] theorem doubleWithSubset_apply {p : Nat} (b : BlockExponent p)
    (E : Finset (Fin p)) (i : Fin p) :
    doubleWithSubset b E i = 2*b i + if i ∈ E then 1 else 0 := by
  simp [doubleWithSubset, two_nsmul, two_mul]

theorem doubleWithSubset_half {p : Nat} (b : BlockExponent p) (E : Finset (Fin p))
    (i : Fin p) : doubleWithSubset b E i / 2 = b i := by
  rw [doubleWithSubset_apply]
  split <;> omega

theorem doubleWithSubset_odd {p : Nat} (b : BlockExponent p) (E : Finset (Fin p))
    (i : Fin p) : doubleWithSubset b E i % 2 = if i ∈ E then 1 else 0 := by
  rw [doubleWithSubset_apply]
  split <;> omega

theorem halfDegree_doubleWithSubset {p : Nat} (b : BlockExponent p) (E : Finset (Fin p)) :
    halfDegree (doubleWithSubset b E) = blockDegree b := by
  unfold halfDegree blockDegree
  apply Finset.sum_congr rfl
  intro i _
  exact doubleWithSubset_half b E i

theorem degree_doubleWithSubset {p : Nat} (b : BlockExponent p) (E : Finset (Fin p)) :
    blockDegree (doubleWithSubset b E) = 2*blockDegree b + E.card := by
  unfold blockDegree
  simp_rw [doubleWithSubset_apply]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  simp

theorem doubleWithSubset_injective {p : Nat} :
    Function.Injective (fun x : BlockExponent p × Finset (Fin p) => doubleWithSubset x.1 x.2) := by
  intro ⟨a, E⟩ ⟨b, F⟩ he
  have hab : a = b := by
    ext i
    have hi := congrArg (fun f : BlockExponent p => f i / 2) he
    simpa only [doubleWithSubset_half] using hi
  have hEF : E = F := by
    ext i
    have hi := congrArg (fun f : BlockExponent p => f i % 2) he
    simp only [doubleWithSubset_odd] at hi
    split_ifs at hi <;> simp_all
  exact Prod.ext hab hEF

/-- Every exponent vector has a unique even part and a squarefree part. -/
theorem exists_doubleWithSubset {p : Nat} (a : BlockExponent p) :
    ∃ b : BlockExponent p, ∃ E : Finset (Fin p), a = doubleWithSubset b E := by
  let b : BlockExponent p := a.mapRange (· / 2) (by decide)
  let E : Finset (Fin p) := Finset.univ.filter (fun i => a i % 2 = 1)
  refine ⟨b, E, ?_⟩
  ext i
  rw [doubleWithSubset_apply]
  have hb : b i = a i / 2 := rfl
  have hE : i ∈ E ↔ a i % 2 = 1 := by simp [E]
  rw [hb]
  by_cases hi : a i % 2 = 1
  · rw [ite_eq_left (hE.mpr hi)]; omega
  · rw [ite_eq_right (fun h => hi (hE.mp h))]; omega

end HilbertBipartite
