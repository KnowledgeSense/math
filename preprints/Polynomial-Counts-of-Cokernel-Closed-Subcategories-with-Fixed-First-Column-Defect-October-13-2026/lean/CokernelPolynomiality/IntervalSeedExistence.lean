import CokernelPolynomiality.SplitIntervalSeed
import Mathlib.Data.Finset.Max

noncomputable section
open CategoryTheory
namespace CokernelPolynomiality

theorem exists_intervalSeed {n : ℕ} (V : ChainRep n)
    (hne : ∃ (i : (Fin (n+1))ᵒᵈ) (x : V.obj i), x ≠ 0) : Nonempty (IntervalSeed V) := by
  classical
  let support : Finset (Fin (n+1)) := Finset.univ.filter (fun i => ∃ x : V.obj (OrderDual.toDual i), x ≠ 0)
  have hs : support.Nonempty := by
    obtain ⟨i,x,hx⟩ := hne
    exact ⟨i.ofDual,Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨x,hx⟩⟩⟩
  let b : Fin (n+1) := support.max' hs
  have hb : b ∈ support := Finset.max'_mem support hs
  obtain ⟨x,hx⟩ := (Finset.mem_filter.mp hb).2
  let active : Finset (Fin (n+1)) := Finset.univ.filter
    (fun i => ∃ h : i.val ≤ b.val, chainMap V (OrderDual.toDual i) (OrderDual.toDual b) h x ≠ 0)
  have hbactive : b ∈ active := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_refl b.val,?_⟩
    simpa using hx
  have ha : active.Nonempty := ⟨b,hbactive⟩
  let a : Fin (n+1) := active.min' ha
  have hamem : a ∈ active := Finset.min'_mem active ha
  obtain ⟨hab,hxa⟩ := (Finset.mem_filter.mp hamem).2
  obtain ⟨φ,hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hxa
  refine ⟨{ a := OrderDual.toDual a
            b := OrderDual.toDual b
            hab := hab
            vector := x
            functional := φ
            normalized := hφ
            below_zero := ?_
            above_zero := ?_ }⟩
  · intro i hi
    change i.ofDual.val < a.val at hi
    by_contra hzero
    have himem : i.ofDual ∈ active := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,⟨le_trans (le_of_lt hi) hab,hzero⟩⟩
    have hmin : a ≤ i.ofDual := Finset.min'_le active i.ofDual himem
    change a.val ≤ i.ofDual.val at hmin
    omega
  · intro i hi y
    change b.val < i.ofDual.val at hi
    by_contra hy
    have himem : i.ofDual ∈ support := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,⟨y,hy⟩⟩
    have hmax : i.ofDual ≤ b := Finset.le_max' support i.ofDual himem
    change i.ofDual.val ≤ b.val at hmax
    omega

end CokernelPolynomiality
