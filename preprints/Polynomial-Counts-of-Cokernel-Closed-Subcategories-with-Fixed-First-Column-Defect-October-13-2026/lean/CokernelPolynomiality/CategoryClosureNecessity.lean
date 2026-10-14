import CokernelPolynomiality.PairIntervalCokernel
import CokernelPolynomiality.IntervalDecomposition
import CokernelPolynomiality.FinitePoints

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

theorem CokernelSubcategory.contains_directPair_iff {n : ℕ} (C : CokernelSubcategory n)
    (V W : ChainRep n) : C.contains (directPair V W) ↔ C.contains V ∧ C.contains W := by
  have hi : C.contains (directPair V W) ↔ C.contains (biprod V W) :=
    ⟨C.iso_closed (directPairIsoBiprod V W),C.iso_closed (directPairIsoBiprod V W).symm⟩
  exact hi.trans (C.contains_biprod_iff V W)

theorem CokernelSubcategory.pair_cokernel_mem_le {n a b c d e f : ℕ} (C : CokernelSubcategory n)
    (hac : a ≤ c) (hae : a ≤ e) (hcb : c ≤ b) (heb : e ≤ b)
    (hbd : b ≤ d) (hdf : d ≤ f)
    (hA : C.contains (intervalRep n a b)) (hB : C.contains (intervalRep n c d))
    (hD : C.contains (intervalRep n e f)) :
    C.contains (intervalRep n (b+1) d) ∧ C.contains (intervalRep n (max c e) f) := by
  have hpair := (C.contains_directPair_iff _ _).mpr ⟨hB,hD⟩
  have hck := C.cokernel_mem (pairSource n a b c d e f hac hbd hae (hbd.trans hdf)) hA hpair
  have hout := C.iso_closed (pairCokernelIso n a b c d e f hac hae hcb heb hbd hdf) hck
  exact (C.contains_directPair_iff _ _).mp hout

/-- The three-point closure rule follows from actual categorical cokernels. -/
theorem CokernelSubcategory.interval_closure {n a b c d e f : ℕ} (C : CokernelSubcategory n)
    (hac : a ≤ c) (hcb : c ≤ b) (hbd : b ≤ d)
    (hae : a ≤ e) (heb : e ≤ b) (hbf : b ≤ f)
    (hA : C.contains (intervalRep n a b)) (hB : C.contains (intervalRep n c d))
    (hD : C.contains (intervalRep n e f)) :
    C.contains (intervalRep n (max c e) (max d f)) ∧
      C.contains (intervalRep n (b+1) (min d f)) := by
  rcases le_total d f with hdf | hfd
  · have h := C.pair_cokernel_mem_le hac hae hcb heb hbd hdf hA hB hD
    simpa only [max_eq_right hdf,min_eq_left hdf] using h.symm
  · have h := C.pair_cokernel_mem_le hae hac heb hcb hbf hfd hA hD hB
    simpa only [max_eq_left hfd,min_eq_right hfd,max_comm e c] using h.symm

theorem CokernelSubcategory.intervalSet_subset {n : ℕ} (C : CokernelSubcategory n) :
    C.intervalSet ⊆ triangle n := by
  intro p hp
  obtain ⟨hab,hbn,_⟩ := C.mem_intervalSet.mp hp
  exact mem_triangle.mpr ⟨hab,hbn⟩

theorem CokernelSubcategory.intervalSet_closed {n : ℕ} (C : CokernelSubcategory n) :
    IsClosed C.intervalSet := by
  intro a b c d e f hab hcd hef hac hcb hbd hae heb hbf
  obtain ⟨_,hbn,hA⟩ := C.mem_intervalSet.mp hab
  obtain ⟨_,hdn,hB⟩ := C.mem_intervalSet.mp hcd
  obtain ⟨_,hfn,hD⟩ := C.mem_intervalSet.mp hef
  have h := C.interval_closure hac hcb hbd hae heb hbf hA hB hD
  constructor
  · exact C.mem_intervalSet.mpr ⟨by omega,by omega,h.1⟩
  · intro hlt
    exact C.mem_intervalSet.mpr ⟨by omega,by omega,h.2⟩

end CokernelPolynomiality
