import PenneyDensity.CoordinateMarginal

noncomputable section
namespace PenneyDensity
attribute [local instance] Classical.propDecidable

 def boundaryWithin (n K : ℕ) (h : 2*K≤n) (i : Fin (2*K)) : Fin n :=
  ⟨if i.val<K then i.val else n-2*K+i.val,by split <;> omega⟩

 theorem boundaryWithin_injective (n K : ℕ) (h : 2*K≤n) :
    Function.Injective (boundaryWithin n K h) := by
  intro i j he
  apply Fin.ext
  have hh := congrArg Fin.val he
  dsimp [boundaryWithin] at hh
  split at hh <;> split at hh <;> omega

 theorem wordIndex_injective {n : ℕ} :
    Function.Injective (fun p : Bool × Fin n => wordIndex n p.1 p.2) := by
  rintro ⟨b,i⟩ ⟨c,j⟩ he
  have hh := congrArg Fin.val he
  simp only [wordIndex_val] at hh
  cases b <;> cases c <;> dsimp [offset] at hh
  · have hi : i=j := Fin.ext (by omega)
    simp [hi]
  · omega
  · omega
  · have hi : i=j := Fin.ext (by omega)
    simp [hi]

 def boundaryIndex (n K : ℕ) (h : 2*K≤n) (p : Bool × Fin (2*K)) : Fin (n+n) :=
  wordIndex n p.1 (boundaryWithin n K h p.2)

 theorem boundaryIndex_injective (n K : ℕ) (h : 2*K≤n) :
    Function.Injective (boundaryIndex n K h) := by
  rintro ⟨b,i⟩ ⟨c,j⟩ he
  change wordIndex n b (boundaryWithin n K h i)=wordIndex n c (boundaryWithin n K h j) at he
  have hh := wordIndex_injective (n := n) (a₁ := (b,boundaryWithin n K h i))
    (a₂ := (c,boundaryWithin n K h j)) he
  have hb := congrArg Prod.fst hh
  have hi := boundaryWithin_injective n K h (congrArg Prod.snd hh)
  exact Prod.ext hb hi

 def boundaryWords {K : ℕ} (g : Bool × Fin (2*K) → Bool) (b : Bool) : Word :=
  List.ofFn (fun i => g (b,i))

 def boundaryProbability (K : ℕ) : ℝ :=
  probability (fun g : Bool × Fin (2*K) → Bool => SmallOverlapAgreement (boundaryWords g) K)

 theorem boundary_prefix {n K k : ℕ} (h : 2*K≤n) (hk : k≤K)
    (f : Fin (n+n) → Bool) (b : Bool) :
    (pairWords f b).take k=
      (boundaryWords (fun p => f (boundaryIndex n K h p)) b).take k := by
  apply List.ext_getElem
  · simp only [List.length_take,pairWords_length,boundaryWords,List.length_ofFn]
    omega
  · intro r hr hs
    simp only [List.length_take,pairWords_length] at hr
    simp only [pairWords,boundaryWords,List.getElem_take,List.getElem_ofFn,boundaryIndex]
    congr 2
    apply Fin.ext
    dsimp [boundaryWithin]
    rw [ite_eq_left (by omega)]

 theorem boundary_suffix {n K k : ℕ} (h : 2*K≤n) (hk : k≤K)
    (f : Fin (n+n) → Bool) (b : Bool) :
    (pairWords f b).drop (n-k)=
      (boundaryWords (fun p => f (boundaryIndex n K h p)) b).drop (2*K-k) := by
  apply List.ext_getElem
  · simp only [List.length_drop,pairWords_length,boundaryWords,List.length_ofFn]
    omega
  · intro r hr hs
    simp only [List.length_drop,pairWords_length] at hr
    simp only [pairWords,boundaryWords,List.getElem_drop,List.getElem_ofFn,boundaryIndex]
    congr 2
    apply Fin.ext
    dsimp [boundaryWithin]
    rw [ite_eq_right (by omega)]
    omega

 theorem small_overlap_boundary {n K : ℕ} (h : 2*K<n) (f : Fin (n+n) → Bool) :
    SmallOverlapAgreement (pairWords f) K ↔
      SmallOverlapAgreement (boundaryWords (fun p => f (boundaryIndex n K (by omega) p))) K := by
  have hp (b c : Bool) (k : ℕ) (hk0 : 0<k) (hk : k≤K) :
      properOverlap (pairWords f b) (pairWords f c) k ↔
      properOverlap (boundaryWords (fun p => f (boundaryIndex n K (by omega) p)) b)
        (boundaryWords (fun p => f (boundaryIndex n K (by omega) p)) c) k := by
    have hkn : k<n := by omega
    have hk2 : k<2*K := by omega
    simp only [properOverlap,pairWords_length,boundaryWords,List.length_ofFn,
      hk0,hkn,hk2,true_and]
    rw [boundary_suffix (by omega) hk f b,boundary_prefix (by omega) hk f c]
    rfl
  constructor
  · intro he b k hk0 hk
    rw [← hp b false k hk0 hk,← hp b true k hk0 hk]
    exact he b k hk0 hk
  · intro he b k hk0 hk
    rw [hp b false k hk0 hk,hp b true k hk0 hk]
    exact he b k hk0 hk

 theorem small_overlap_probability {n K : ℕ} (h : 2*K<n) :
    probability (fun f : Fin (n+n) → Bool => SmallOverlapAgreement (pairWords f) K)=
      boundaryProbability K := by
  have he := probability_equal_of_equiv (Equiv.refl (Fin (n+n) → Bool))
    (fun f => SmallOverlapAgreement (pairWords f) K)
    (fun f => SmallOverlapAgreement
      (boundaryWords (fun p => f (boundaryIndex n K (by omega) p))) K)
    (small_overlap_boundary h)
  exact he.trans (probability_coordinate_pullback (α := Fin (n+n)) (β := Bool × Fin (2*K)) (boundaryIndex n K (by omega))
    (boundaryIndex_injective n K (by omega))
    (fun g : Bool × Fin (2*K) → Bool => SmallOverlapAgreement (boundaryWords g) K))

end PenneyDensity
