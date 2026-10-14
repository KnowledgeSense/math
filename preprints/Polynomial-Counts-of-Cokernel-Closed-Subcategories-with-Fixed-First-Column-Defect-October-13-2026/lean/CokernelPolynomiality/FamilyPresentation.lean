import CokernelPolynomiality.IndexedFamilies
import CokernelPolynomiality.IntervalHull

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

def intervalFamilySingletonIso (n a b : ℕ) :
    intervalFamily n 1 (fun _ => a) (fun _ => b) ≅ intervalRep n a b :=
  NatIso.ofComponents (fun i => (LinearEquiv.funUnique (Fin 1) ℂ
    (intervalSpace a b i.ofDual.val)).toFGModuleCatIso) (by
      intro i j f
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

theorem intervalFamilyEmpty_isZero (n : ℕ) :
    IsZero (intervalFamily n 0 (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)) := by
  apply isZero_of_vertices_zero
  intro i x
  funext j
  exact Fin.elim0 j

theorem IntervalHull.family_presentation {n : ℕ} {Y : Finset (ℕ × ℕ)} {V : ChainRep.{0} n}
    (hV : IntervalHull n Y V) : ∃ (m : ℕ) (c d : Fin m → ℕ),
      (∀j,c j≤d j ∧ d j≤n ∧ (c j,d j)∈Y) ∧ Nonempty (V ≅ intervalFamily n m c d) := by
  induction hV with
  | zero V hV =>
    exact ⟨0,(fun j => Fin.elim0 j),(fun j => Fin.elim0 j),
      (fun j => Fin.elim0 j),⟨hV.iso (intervalFamilyEmpty_isZero n)⟩⟩
  | interval a b hab hbn hY =>
    exact ⟨1,(fun _ => a),(fun _ => b),(fun _ => ⟨hab,hbn,hY⟩),
      ⟨(intervalFamilySingletonIso n a b).symm⟩⟩
  | biprod V W hV hW ihV ihW =>
    obtain ⟨m,c,d,hcd,⟨e⟩⟩ := ihV
    obtain ⟨k,c',d',hcd',⟨e'⟩⟩ := ihW
    refine ⟨m+k,Sum.elim c c' ∘ finSumFinEquiv.symm,
      Sum.elim d d' ∘ finSumFinEquiv.symm,?_,
      ⟨biprod.mapIso e e' ≪≫ (intervalFamilyConcatIso n m k c d c' d').symm⟩⟩
    intro j
    cases hj : finSumFinEquiv.symm j with
    | inl i => simpa only [Function.comp_apply,hj,Sum.elim_inl] using hcd i
    | inr i => simpa only [Function.comp_apply,hj,Sum.elim_inr] using hcd' i
  | iso e hV ih =>
    obtain ⟨m,c,d,hcd,⟨f⟩⟩ := ih
    exact ⟨m,c,d,hcd,⟨e.symm ≪≫ f⟩⟩

end CokernelPolynomiality
