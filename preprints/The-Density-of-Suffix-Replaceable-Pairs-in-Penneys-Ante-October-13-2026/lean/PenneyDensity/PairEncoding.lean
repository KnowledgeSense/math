import PenneyDensity.BlockCounting
import PenneyDensity.Localization

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

 def pairBitsEquiv (n : ℕ) : (Fin (n+n) → Bool) ≃ WordOfLength n × WordOfLength n where
  toFun f := (fun i => f (i.castAdd n),fun i => f (Fin.natAdd n i))
  invFun p := Fin.addCases p.1 p.2
  left_inv f := by funext i; exact Fin.addCases_castAdd_natAdd f i
  right_inv p := by
    apply Prod.ext
    · funext i
      change Fin.addCases (motive := fun _ : Fin (n+n) => Bool) p.1 p.2 (Fin.castAdd n i)=p.1 i
      exact Fin.addCases_left i
    · funext i
      change Fin.addCases (motive := fun _ : Fin (n+n) => Bool) p.1 p.2 (Fin.natAdd n i)=p.2 i
      exact Fin.addCases_right i

 def wordIndex (n : ℕ) (b : Bool) (i : Fin n) : Fin (n+n) :=
  if b then Fin.natAdd n i else i.castAdd n

 def pairWords {n : ℕ} (f : Fin (n+n) → Bool) (b : Bool) : Word :=
  List.ofFn (fun i : Fin n => f (wordIndex n b i))

 def offset (n : ℕ) (b : Bool) : ℕ := if b then n else 0

 theorem wordIndex_val (n : ℕ) (b : Bool) (i : Fin n) :
    (wordIndex n b i).val=offset n b+i.val := by cases b <;> simp only [wordIndex,offset,Bool.false_eq_true,ite_false,ite_true,Fin.val_natAdd,Fin.val_castAdd,zero_add]

 theorem pairWords_length {n : ℕ} (f : Fin (n+n) → Bool) (b : Bool) :
    (pairWords f b).length=n := List.length_ofFn

 theorem pairWords_false {n : ℕ} (f : Fin (n+n) → Bool) :
    pairWords f false=toWord ((pairBitsEquiv n f).1) := rfl

 theorem pairWords_true {n : ℕ} (f : Fin (n+n) → Bool) :
    pairWords f true=toWord ((pairBitsEquiv n f).2) := rfl

 theorem offset_fit {n i m : ℕ} (b : Bool) (hi : i+m≤n) : offset n b+i+m≤n+n := by
  cases b <;> dsimp [offset] <;> omega

 theorem pair_block_eq_flat {n i m : ℕ} (f : Fin (n+n) → Bool)
    (b : Bool) (hi : i+m≤n) :
    ((pairWords f b).drop i).take m=
      ((List.ofFn f).drop (offset n b+i)).take m := by
  have hf := offset_fit b hi
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn,pairWords_length]
    omega
  · intro r hr hs
    simp only [pairWords,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp only [wordIndex_val]
    omega

 theorem pair_blocks_iff {n i j m : ℕ} (f : Fin (n+n) → Bool)
    (b c : Bool) (hi : i+m≤n) (hj : j+m≤n) :
    ((pairWords f b).drop i).take m=((pairWords f c).drop j).take m ↔
      EqualBlocks f (offset n b+i) (offset n c+j) m (offset_fit b hi) (offset_fit c hj) := by
  rw [pair_block_eq_flat f b hi,pair_block_eq_flat f c hj,
    equalBlocks_iff_lists]

 theorem different_indices_offset {n i j : ℕ} (b c : Bool) (hi : i<n) (hj : j<n)
    (hneq : b≠c ∨ i≠j) : offset n b+i≠offset n c+j := by
  cases b <;> cases c <;> simp only [offset,Bool.false_eq_true,ite_false,ite_true,zero_add] <;>
    simp_all <;> omega

 theorem card_equal_blocks_ne {N i j m : ℕ} (hi : i+m≤N) (hj : j+m≤N)
    (hne : i≠j) :
    Fintype.card {f : Fin N → Bool // EqualBlocks f i j m hi hj}=2^(N-m) := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact card_equal_blocks hij hj
  · have he : ∀ f : Fin N → Bool, EqualBlocks f i j m hi hj ↔ EqualBlocks f j i m hj hi := by
      intro f
      exact ⟨fun h r => (h r).symm,fun h r => (h r).symm⟩
    rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
    exact card_equal_blocks hji hi

 theorem card_pair_block_collision {n i j m : ℕ} (b c : Bool)
    (hi : i+m≤n) (hj : j+m≤n) (hiN : i<n) (hjN : j<n) (hneq : b≠c ∨ i≠j) :
    Fintype.card {f : Fin (n+n) → Bool //
      ((pairWords f b).drop i).take m=((pairWords f c).drop j).take m}=2^(n+n-m) := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (fun f => pair_blocks_iff f b c hi hj))]
  exact card_equal_blocks_ne (offset_fit b hi) (offset_fit c hj)
    (different_indices_offset b c hiN hjN hneq)

end PenneyDensity
