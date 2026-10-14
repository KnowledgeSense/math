import CokernelPolynomiality.IntervalDecomposition

noncomputable section
namespace CokernelPolynomiality

def CokernelSubcategory.signature {n : ℕ} (C : CokernelSubcategory n) :
    Finset (Fin (n+1) × Fin (n+1)) := by
  classical
  exact Finset.univ.filter (fun p => C.contains (intervalRep n p.1.val p.2.val))

theorem CokernelSubcategory.signature_injective (n : ℕ) :
    Function.Injective (CokernelSubcategory.signature (n:=n)) := by
  classical
  intro C D h
  apply CokernelSubcategory.ext_intervals
  intro a b hab hbn
  let i : Fin (n+1) := ⟨a,by omega⟩
  let j : Fin (n+1) := ⟨b,by omega⟩
  have hh := congrArg (fun s => (i,j) ∈ s) h
  simpa only [signature,Finset.mem_filter,Finset.mem_univ,true_and] using Iff.of_eq hh

noncomputable instance (n : ℕ) : Fintype (CokernelSubcategory n) :=
  Fintype.ofInjective CokernelSubcategory.signature (CokernelSubcategory.signature_injective n)

/-- Number of first-column interval classes in the actual subcategory. -/
def CokernelSubcategory.firstColumnCard {n : ℕ} (C : CokernelSubcategory n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun b : Fin (n+1) => C.contains (intervalRep n 0 b.val))).card

/-- The categorical count, defined independently of the triangular closure
model and the proposed polynomial. -/
def categoryCount (n k : ℕ) : ℕ := by
  classical
  exact Fintype.card {C : CokernelSubcategory n // C.firstColumnCard=k}

end CokernelPolynomiality
