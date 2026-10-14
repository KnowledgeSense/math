import PenneyDensity.PairEncoding

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

 def probability {α : Type*} [Fintype α] (P : α → Prop) : ℝ :=
  (Nat.card {x // P x} : ℝ)/Nat.card α

 theorem probability_card_formula {α : Type*} [Fintype α] (P : α → Prop)
    [I : Fintype {x // P x}] :
    probability P=(@Fintype.card {x // P x} I : ℝ)/Fintype.card α := by
  simp only [probability,Nat.card_eq_fintype_card]

 theorem probability_nonneg {α : Type*} [Fintype α] (P : α → Prop) :
    0≤probability P := by unfold probability; positivity

 theorem probability_mono {α : Type*} [Fintype α] {P Q : α → Prop}
    (h : ∀ x,P x → Q x) : probability P≤probability Q := by
  simp only [probability,Nat.card_eq_fintype_card]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_subtype_mono P Q h

 theorem card_exists_le {α β : Type*} [Fintype α] [Fintype β] (P : β → α → Prop) :
    Fintype.card {x // ∃ b,P b x} ≤ ∑ b,Fintype.card {x // P b x} := by
  let f : {x // ∃ b,P b x} → Σ b,{x // P b x} :=
    fun x => ⟨Classical.choose x.property,⟨x.val,Classical.choose_spec x.property⟩⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : Σ b,{x // P b x} => z.2.val) he
  simpa only [Fintype.card_sigma] using Fintype.card_le_of_injective f hf

 theorem probability_exists_le {α β : Type*} [Fintype α] [Fintype β] (P : β → α → Prop) :
    probability (fun x => ∃ b,P b x)≤∑ b,probability (P b) := by
  simp only [probability,Nat.card_eq_fintype_card,← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hc := card_exists_le P
  have hcr := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at hcr
  convert hcr using 1

 theorem probability_or_le {α : Type*} [Fintype α] (P Q : α → Prop) :
    probability (fun x => P x ∨ Q x)≤probability P+probability Q := by
  have he : (fun x => P x ∨ Q x)=(fun x => ∃ b : Bool,if b then P x else Q x) := by
    funext x
    simp [Bool.exists_bool,or_comm]
  rw [he]
  simpa only [Fintype.sum_bool,Bool.false_eq_true,ite_true,ite_false] using
    probability_exists_le (fun b : Bool => fun x => if b then P x else Q x)

 theorem probability_difference_le {α : Type*} [Fintype α] {P Q E : α → Prop}
    (h : ∀ x,¬E x → (P x ↔ Q x)) : |probability P-probability Q|≤probability E := by
  have hp : probability P≤probability Q+probability E :=
    (probability_mono (fun x hx => by by_cases he : E x; exact Or.inr he; exact Or.inl ((h x he).mp hx))).trans
      (probability_or_le Q E)
  have hq : probability Q≤probability P+probability E :=
    (probability_mono (fun x hx => by by_cases he : E x; exact Or.inr he; exact Or.inl ((h x he).mpr hx))).trans
      (probability_or_le P E)
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

 theorem probability_equal_of_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : α → Prop) (Q : β → Prop) (h : ∀ x,P x ↔ Q (e x)) :
    probability P=probability Q := by
  unfold probability
  rw [Nat.card_congr (e.subtypeEquiv h),Nat.card_congr e]

 theorem density_eq_probability (n : ℕ) : density n=
    probability (fun f : Fin (n+n) → Bool => PropertyR (pairWords f false) (pairWords f true)) := by
  have he := probability_equal_of_equiv (pairBitsEquiv n)
    (fun f => PropertyR (pairWords f false) (pairWords f true))
    (fun p => PropertyR (toWord p.1) (toWord p.2)) (fun _ => Iff.rfl)
  rw [he]
  unfold density probability
  congr 1
  simp only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

end PenneyDensity
