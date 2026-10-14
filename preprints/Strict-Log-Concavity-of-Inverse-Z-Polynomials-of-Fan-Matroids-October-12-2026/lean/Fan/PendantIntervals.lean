import Fan.AppendConfigurations
import Fan.SeparatedIntervals
import Fan.SpokelessIntervals

namespace Fan
open scoped Classical

noncomputable instance : LocallyFiniteOrder Bool := Fintype.toLocallyFiniteOrder

noncomputable def bitEmbedding : Bool ↪o Finset (Fin 1) :=
  OrderEmbedding.ofMapLEIff bitSet bitSet_subset_iff

theorem bitSet_lastBit (S : Finset (Fin 1)) : bitSet (lastBit S)=S := by
  ext i
  fin_cases i
  simp only [mem_bitSet,lastBit_eq_true]
  rfl

theorem bitEmbedding_fills : ∀ a b y, bitEmbedding a ≤ y → y ≤ bitEmbedding b →
    ∃ x, bitEmbedding x=y := fun _ _ y _ _ => ⟨lastBit y,bitSet_lastBit y⟩

def bitRank (b : Bool) : ℕ := if b then 1 else 0

theorem bitEmbedding_rank (b : Bool) : (bitEmbedding b).card=bitRank b := by
  change (bitSet b).card=bitRank b
  cases b <;> simp [bitSet,bitRank]

theorem bitRank_mono : Monotone bitRank := by
  intro b c h
  cases b <;> cases c <;> simp_all [Bool.le_iff_imp,bitRank]

theorem bit_inverseKL : MatroidInverseZ.inverseKL bitRank false true=1 := by
  classical
  have h := MatroidInverseZ.inverseKL_interval_transport bitEmbedding bitEmbedding_fills
    bitRank Finset.card (fun a b => by rw [bitEmbedding_rank,bitEmbedding_rank]) false true
  rw [← h,MatroidInverseZ.boolean_inverseKL _ _ (by exact Finset.empty_subset _)]

noncomputable def singletonConfiguration (b : Bool) : Configuration 1 := ⟨(bitSet b,∅),by
  constructor
  · simp
  · intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    omega⟩

theorem configuration_one_joins (p : Configuration 1) : p.val.2=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have := p.property.1 j hj
  have := j.isLt
  omega

theorem configuration_one_eq (p : Configuration 1) : singletonConfiguration (lastBit p.val.1)=p := by
  apply Subtype.ext
  apply Prod.ext
  · exact bitSet_lastBit _
  · exact (configuration_one_joins p).symm

noncomputable def singletonEmbedding : Bool ↪o Configuration 1 :=
  OrderEmbedding.ofMapLEIff singletonConfiguration (fun b c => by
    change (bitSet b⊆bitSet c ∧ (∅ : Finset (Fin 1))⊆∅) ↔ b≤c
    simp only [Finset.empty_subset,and_true,bitSet_subset_iff])

theorem singletonEmbedding_fills : ∀ a b y, singletonEmbedding a ≤ y → y ≤ singletonEmbedding b →
    ∃ x, singletonEmbedding x=y := fun _ _ y _ _ => ⟨lastBit y.val.1,configuration_one_eq y⟩

theorem singleton_rank (b : Bool) : configurationRank (singletonEmbedding b)=bitRank b := by
  change (bitSet b ∪ ∅).card=bitRank b
  rw [Finset.union_empty]
  exact bitEmbedding_rank b

theorem singleton_false : singletonConfiguration false=(⊥ : Configuration 1) := by
  apply Subtype.ext
  rw [configuration_bot_val]
  rfl

theorem singleton_lowerQ (b : Bool) : lowerQ (singletonConfiguration b)=1 := by
  classical
  have h := MatroidInverseZ.inverseKL_interval_transport singletonEmbedding singletonEmbedding_fills
    bitRank configurationRank (fun a b => by rw [singleton_rank,singleton_rank]) false b
  change MatroidInverseZ.inverseKL configurationRank (singletonConfiguration false)
    (singletonConfiguration b)=_ at h
  rw [singleton_false] at h
  change lowerQ (singletonConfiguration b)=_ at h
  rw [h]
  cases b
  · exact MatroidInverseZ.inverseKL_self _ _
  · exact bit_inverseKL

theorem lowerQ_append_empty {n : ℕ} (p : Configuration (n+1)) :
    lowerQ (appendConfiguration p false false (allowed_false_false p.val))=lowerQ p := by
  have hc : Compatible p.val (singletonConfiguration false).val := by
    intro i j _ _ ⟨_,hj⟩
    exact Finset.notMem_empty j hj
  have h := lowerQ_join p (singletonConfiguration false) hc
  rw [singleton_lowerQ,mul_one] at h
  exact h

end Fan
