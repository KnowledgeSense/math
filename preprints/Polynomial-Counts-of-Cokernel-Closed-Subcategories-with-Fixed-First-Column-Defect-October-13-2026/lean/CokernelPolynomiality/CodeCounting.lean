import CokernelPolynomiality.Factorization
import Mathlib.Data.Fintype.Sigma
import Mathlib.Order.Hom.PowersetCard

namespace CokernelPolynomiality
noncomputable section

abbrev ZeroEmbedding (q m : ℕ) := {e : Fin (q+1) ↪o Fin (m+1) // e 0 = 0}
abbrev NormalCode (i q : ℕ) := {c : Code i q // c.IsAdmissible ∧ c.IsNormalized}
abbrev AdmissibleCode (i m : ℕ) := {c : Code i m // c.IsAdmissible}
abbrev Representation (i m : ℕ) :=
  (q : Fin (2*i+1)) × (ZeroEmbedding q m × NormalCode i q)

 def codeCount (i m : ℕ) : ℕ := by
  classical
  exact Fintype.card (AdmissibleCode i m)

 def representationToCode {i m : ℕ} (s : Representation i m) : AdmissibleCode i m :=
  ⟨s.2.2.val.recode s.2.1.val,
    (s.2.2.val.recode_admissible_iff s.2.1.val s.2.1.property).mpr s.2.2.property.1⟩

 theorem representationToCode_surjective (i m : ℕ) :
    Function.Surjective (@representationToCode i m) := by
  intro c
  let q : Fin (2*i+1) := ⟨c.val.levelCount,by have := c.val.levelCount_le; omega⟩
  let e : ZeroEmbedding q m := ⟨c.val.levelEmbedding,c.val.levelEmbedding_zero⟩
  let nc : NormalCode i q := ⟨c.val.normalize,
    c.val.normalize_admissible_iff.mpr c.property,c.val.normalize_isNormalized⟩
  refine ⟨⟨q,e,nc⟩,?_⟩
  apply Subtype.ext
  exact c.val.normalize_recovery

 theorem representationToCode_injective (i m : ℕ) :
    Function.Injective (@representationToCode i m) := by
  intro a b hab
  rcases a with ⟨q,e,c⟩
  rcases b with ⟨r,e',c'⟩
  have hcode : c.val.recode e.val = c'.val.recode e'.val := congrArg Subtype.val hab
  have hqr := normalized_factorization_size_unique c.val c.property.2 c'.val c'.property.2
    e.val e.property e'.val e'.property hcode
  have hqr' : q = r := Fin.ext hqr
  subst r
  have he' := normalized_factorization_embedding_unique c.val c'.val c.property.2 c'.property.2
    e.val e'.val e.property e'.property hcode
  have he : e = e' := Subtype.ext he'
  subst e'
  have hc : c = c' := Subtype.ext (Code.recode_injective e.val hcode)
  subst c'
  rfl

 def representationEquiv (i m : ℕ) : Representation i m ≃ AdmissibleCode i m :=
  Equiv.ofBijective _ ⟨representationToCode_injective i m,representationToCode_surjective i m⟩

 theorem codeCount_sum_embeddings (i m : ℕ) :
    codeCount i m = ∑ q : Fin (2*i+1), Nat.card (ZeroEmbedding q m) * templateCount i q := by
  classical
  unfold codeCount
  rw [← Fintype.card_congr (representationEquiv i m), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro q _
  rw [Fintype.card_prod]
  congr 1
  exact Nat.card_eq_fintype_card.symm

end
end CokernelPolynomiality
