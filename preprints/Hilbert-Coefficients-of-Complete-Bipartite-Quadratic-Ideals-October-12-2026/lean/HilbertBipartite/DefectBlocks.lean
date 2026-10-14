import HilbertBipartite.Parity
import HilbertBipartite.DegreeLayers

namespace HilbertBipartite

noncomputable def degreeLayer (p l : Nat) : Finset (BlockExponent p) :=
  (Finset.univ : Finset (Fin p)).finsuppAntidiag l

@[simp] theorem mem_degreeLayer {p l : Nat} {a : BlockExponent p} :
    a ∈ degreeLayer p l ↔ blockDegree a = l := by
  simp [degreeLayer, Finset.mem_finsuppAntidiag, blockDegree]

theorem card_degreeLayer (p l : Nat) (hp : 1 ≤ p) :
    (degreeLayer p l).card = (l+p-1).choose (p-1) := by
  rw [degreeLayer, Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  have he : p+l-1 = l+(p-1) := by omega
  rw [he, Nat.choose_symm_add]
  congr 1
  omega

noncomputable def defectBlock (p q s t r k : Nat) : Finset (ExponentPair p q) :=
  (((degreeLayer q t) ×ˢ (Finset.univ : Finset (Fin p)).powersetCard k) ×ˢ
    degreeLayer p (s-t-r)).image
      (fun x => (doubleWithSubset x.2 x.1.2, x.1.1))

@[simp] theorem mem_defectBlock {p q s t r k : Nat} {a : BlockExponent p}
    {b : BlockExponent q} : (a,b) ∈ defectBlock p q s t r k ↔
    blockDegree b = t ∧ halfDegree a = s-t-r ∧ blockDegree a = 2*(s-t-r)+k := by
  classical
  constructor
  · intro h
    obtain ⟨⟨⟨b', E⟩, c⟩, hm, he⟩ := Finset.mem_image.mp h
    simp only [Finset.mem_product, mem_degreeLayer, Finset.mem_powersetCard,
      Finset.subset_univ, true_and] at hm
    have hae : doubleWithSubset c E = a := congrArg Prod.fst he
    have hbe : b' = b := congrArg Prod.snd he
    rcases hm with ⟨⟨hb', hE⟩, hc⟩
    rw [← hae, ← hbe, halfDegree_doubleWithSubset, degree_doubleWithSubset, hb', hc, hE]
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨hb, hh, ha⟩
    obtain ⟨c, E, rfl⟩ := exists_doubleWithSubset a
    rw [halfDegree_doubleWithSubset] at hh
    rw [degree_doubleWithSubset, hh] at ha
    have hE : E.card = k := by omega
    apply Finset.mem_image.mpr
    refine ⟨((b,E),c), ?_, rfl⟩
    simp only [Finset.mem_product, mem_degreeLayer, Finset.mem_powersetCard,
      Finset.subset_univ, true_and]
    exact ⟨⟨hb, hE⟩, hh⟩

theorem card_defectBlock (p q s t r k : Nat) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (defectBlock p q s t r k).card =
      (t+q-1).choose (q-1) * p.choose k * (s-t-r+p-1).choose (p-1) := by
  classical
  have hinj : Function.Injective
      (fun x : (BlockExponent q × Finset (Fin p)) × BlockExponent p =>
        (doubleWithSubset x.2 x.1.2, x.1.1)) := by
    intro ⟨⟨b,E⟩,a⟩ ⟨⟨b',E'⟩,a'⟩ he
    have haa : doubleWithSubset a E = doubleWithSubset a' E' := congrArg Prod.fst he
    have hbb : b = b' := congrArg Prod.snd he
    have hae : (a,E) = (a',E') := doubleWithSubset_injective (p := p) haa
    have haa' : a = a' := congrArg Prod.fst hae
    have hEE : E = E' := congrArg Prod.snd hae
    subst a'; subst b'; subst E'
    rfl
  rw [defectBlock, Finset.card_image_of_injective _ hinj]
  rw [Finset.card_product, Finset.card_product, card_degreeLayer _ _ hq,
    card_degreeLayer _ _ hp, Finset.card_powersetCard]
  simp

/-- The high-degree standard monomials missing on the left side. -/
noncomputable def defectExponents (p q s : Nat) : Finset (ExponentPair p q) :=
  (Finset.range (s+1)).biUnion (fun t =>
    (Finset.Icc 1 (s-t)).biUnion (fun r =>
      (Finset.Icc (t+2*r) p).biUnion (fun k => defectBlock p q s t r k)))

@[simp] theorem mem_defectExponents {p q s : Nat} {a : BlockExponent p}
    {b : BlockExponent q} : (a,b) ∈ defectExponents p q s ↔
      2*s ≤ blockDegree a + blockDegree b ∧ halfDegree a + blockDegree b < s := by
  classical
  simp only [defectExponents, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Icc,
    mem_defectBlock]
  constructor
  · rintro ⟨t, ht, r, ⟨hr, hrs⟩, k, ⟨hk, _⟩, hb, hh, ha⟩
    constructor <;> omega
  · rintro ⟨hdegree, hhalf⟩
    obtain ⟨c, E, he⟩ := exists_doubleWithSubset a
    have hha : halfDegree a = blockDegree c := by rw [he, halfDegree_doubleWithSubset]
    have hda : blockDegree a = 2*blockDegree c + E.card := by rw [he, degree_doubleWithSubset]
    have hEp : E.card ≤ p := by
      have := Finset.card_le_card (Finset.subset_univ E)
      simpa using this
    refine ⟨blockDegree b, by omega, s-blockDegree b-halfDegree a,
      ⟨by omega, by omega⟩, E.card, ⟨by omega, hEp⟩, rfl, ?_, ?_⟩ <;> omega

theorem card_defectExponents (p q s : Nat) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    (defectExponents p q s).card = correction p q s := by
  classical
  unfold defectExponents correction
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.card_biUnion]
      · apply Finset.sum_congr rfl
        intro k _
        exact card_defectBlock p q s t r k hp hq
      · intro k _ l _ hkl
        apply Finset.disjoint_left.mpr
        rintro ⟨a,b⟩ hk hl
        have ha := (mem_defectBlock.mp hk).2.2
        have hb := (mem_defectBlock.mp hl).2.2
        omega
    · intro r hr r' hr' hrr
      apply Finset.disjoint_left.mpr
      rintro ⟨a,b⟩ hx hy
      obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hy
      have ha := (mem_defectBlock.mp hk).2.1
      have hb := (mem_defectBlock.mp hl).2.1
      have hrb := Finset.mem_Icc.mp hr
      have hrb' := Finset.mem_Icc.mp hr'
      omega
  · intro t _ t' _ htt
    apply Finset.disjoint_left.mpr
    rintro ⟨a,b⟩ hx hy
    obtain ⟨r, _, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨r', _, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hy
    have ha := (mem_defectBlock.mp hk).1
    have hb := (mem_defectBlock.mp hl).1
    omega

end HilbertBipartite
