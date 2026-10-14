import MainTheorems.PreorderGamma.MacaulayNumerical.BinomialRaise
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Sort

namespace ResearchMain.PreorderGamma.MacaulayNumerical

open scoped BigOperators FinsetFamily
open Finset.Colex

def strictColex {n : ℕ} (s : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun t => t.card = s.card ∧ toColex t < toColex s

@[simp] theorem mem_strictColex {n : ℕ} {s t : Finset (Fin n)} :
    t ∈ strictColex s ↔ t.card = s.card ∧ toColex t < toColex s := by
  simp [strictColex]

@[simp] theorem self_not_mem_strictColex {n : ℕ} (s : Finset (Fin n)) :
    s ∉ strictColex s := by simp

@[simp] theorem strictColex_empty (n : ℕ) : strictColex (∅ : Finset (Fin n)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨hcard, hlt⟩ := mem_strictColex.mp ht
  have heq : t = ∅ := Finset.card_eq_zero.mp (by simpa only [Finset.card_empty] using hcard)
  subst t
  exact lt_irrefl _ hlt

theorem colex_erase_common {n : ℕ} {s t : Finset (Fin n)} {a : Fin n}
    (has : a ∈ s) (hat : a ∈ t) :
    toColex (s.erase a) < toColex (t.erase a) ↔ toColex s < toColex t := by
  simpa only [Finset.sdiff_singleton_eq_erase] using
    (toColex_sdiff_lt_toColex_sdiff
      (show ({a} : Finset (Fin n)) ⊆ s by simpa using has)
      (show ({a} : Finset (Fin n)) ⊆ t by simpa using hat))

theorem erase_max_lt {n : ℕ} {s : Finset (Fin n)} {a : Fin n}
    (hmax : ∀ b ∈ s, b ≤ a) : ∀ b ∈ s.erase a, b < a := by
  intro b hb
  obtain ⟨hne, hbs⟩ := Finset.mem_erase.mp hb
  exact lt_of_le_of_ne (hmax b hbs) hne

theorem strictColex_lt_choose {n : ℕ} {s : Finset (Fin n)} {a : Fin n}
    (hsmall : ∀ b ∈ s, b < a) :
    (strictColex s).card < a.val.choose s.card := by
  let all := (Finset.Iio a).powersetCard s.card
  have hsub : strictColex s ⊆ all := by
    intro t ht
    obtain ⟨hcard, hlt⟩ := mem_strictColex.mp ht
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hcard⟩
    intro b hb
    exact Finset.mem_Iio.mpr (forall_lt_mono hlt.le hsmall b hb)
  have hs : s ∈ all := Finset.mem_powersetCard.mpr
    ⟨fun b hb => Finset.mem_Iio.mpr (hsmall b hb), rfl⟩
  have hproper : strictColex s ⊂ all :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
      intro heq
      exact self_not_mem_strictColex s (heq.symm ▸ hs)⟩
  have h := Finset.card_lt_card hproper
  simpa [all, Finset.card_powersetCard, Fin.card_Iio] using h

theorem strictColex_split {n : ℕ} {s : Finset (Fin n)} {a : Fin n}
    (ha : a ∈ s) (hmax : ∀ b ∈ s, b ≤ a) :
    strictColex s = (Finset.Iio a).powersetCard s.card ∪
      (strictColex (s.erase a)).image (insert a) := by
  have hrsmall := erase_max_lt hmax
  ext t
  constructor
  · intro ht
    obtain ⟨hcard, hlt⟩ := mem_strictColex.mp ht
    have hle := forall_le_mono hlt.le hmax
    by_cases hat : a ∈ t
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_image.mpr
      refine ⟨t.erase a, ?_, Finset.insert_erase hat⟩
      apply mem_strictColex.mpr
      refine ⟨?_, (colex_erase_common hat ha).mpr hlt⟩
      rw [Finset.card_erase_of_mem hat, Finset.card_erase_of_mem ha, hcard]
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, hcard⟩
      intro b hb
      apply Finset.mem_Iio.mpr
      exact lt_of_le_of_ne (hle b hb) (by intro h; exact hat (h ▸ hb))
  · intro ht
    obtain hleft | hright := Finset.mem_union.mp ht
    · obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hleft
      apply mem_strictColex.mpr
      refine ⟨hcard, toColex_lt_toColex_iff_exists_forall_lt.mpr ?_⟩
      refine ⟨a, ha, ?_, fun b hb _ => Finset.mem_Iio.mp (hsub hb)⟩
      intro hat
      exact lt_irrefl a (Finset.mem_Iio.mp (hsub hat))
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hright
      obtain ⟨hcard, hlt⟩ := mem_strictColex.mp hu
      have husmall := forall_lt_mono hlt.le hrsmall
      have hau : a ∉ u := by intro hau; exact lt_irrefl a (husmall a hau)
      apply mem_strictColex.mpr
      refine ⟨?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hau, hcard, Finset.card_erase_of_mem ha]
        have hpos := Finset.card_pos.mpr ⟨a, ha⟩
        omega
      · apply (colex_erase_common (Finset.mem_insert_self a u) ha).mp
        simpa [hau] using hlt

theorem strictColex_card_split {n : ℕ} {s : Finset (Fin n)} {a : Fin n}
    (ha : a ∈ s) (hmax : ∀ b ∈ s, b ≤ a) :
    (strictColex s).card = a.val.choose s.card + (strictColex (s.erase a)).card := by
  have hrsmall := erase_max_lt hmax
  have hdisjoint : Disjoint ((Finset.Iio a).powersetCard s.card)
      ((strictColex (s.erase a)).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro t ht hu
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hu
    have hsub := (Finset.mem_powersetCard.mp ht).1
    exact lt_irrefl a (Finset.mem_Iio.mp (hsub (Finset.mem_insert_self a u)))
  have hinj : Set.InjOn (insert a)
      (↑(strictColex (s.erase a)) : Set (Finset (Fin n))) := by
    intro u hu v hv huv
    have husmall := forall_lt_mono (mem_strictColex.mp hu).2.le hrsmall
    have hvsmall := forall_lt_mono (mem_strictColex.mp hv).2.le hrsmall
    have hau : a ∉ u := by intro hau; exact lt_irrefl a (husmall a hau)
    have hav : a ∉ v := by intro hav; exact lt_irrefl a (hvsmall a hav)
    have heq := congrArg (fun w : Finset (Fin n) => w.erase a) huv
    simpa [hau, hav] using heq
  rw [strictColex_split ha hmax, Finset.card_union_of_disjoint hdisjoint,
    Finset.card_image_of_injOn hinj, Finset.card_powersetCard, Fin.card_Iio]

theorem binomialTop_strictColex {n : ℕ} {s : Finset (Fin n)} {a : Fin n}
    (ha : a ∈ s) (hmax : ∀ b ∈ s, b ≤ a) :
    binomialTop s.card (strictColex s).card = a.val := by
  have hpos := Finset.card_pos.mpr ⟨a, ha⟩
  have hcard := Finset.card_erase_of_mem ha
  have hsplit := strictColex_card_split ha hmax
  have hrem := strictColex_lt_choose (erase_max_lt hmax)
  apply binomialTop_eq_of_bounds hpos
  · omega
  · have hpascal := Nat.choose_succ_succ' a.val (s.card - 1)
    have hd : s.card - 1 + 1 = s.card := by omega
    rw [hd] at hpascal
    rw [hcard] at hrem
    omega

theorem initSeg_eq_insert_strictColex {n : ℕ} (s : Finset (Fin n)) :
    initSeg s = insert s (strictColex s) := by
  ext t
  simp only [mem_initSeg, Finset.mem_insert, mem_strictColex]
  constructor
  · rintro ⟨hcard, hle⟩
    obtain heq | hlt := hle.eq_or_lt
    · exact Or.inl (toColex.injective heq)
    · exact Or.inr ⟨hcard.symm, hlt⟩
  · rintro (rfl | ⟨hcard, hlt⟩)
    · exact ⟨rfl, le_rfl⟩
    · exact ⟨hcard.symm, hlt.le⟩

theorem initSeg_card_eq_rank_add_one {n : ℕ} (s : Finset (Fin n)) :
    (initSeg s).card = (strictColex s).card + 1 := by
  rw [initSeg_eq_insert_strictColex, Finset.card_insert_of_notMem
    (self_not_mem_strictColex s)]

end ResearchMain.PreorderGamma.MacaulayNumerical
