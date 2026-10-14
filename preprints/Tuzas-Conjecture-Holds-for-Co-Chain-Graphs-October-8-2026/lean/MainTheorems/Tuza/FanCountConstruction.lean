import MainTheorems.Tuza.FactorCard
import MainTheorems.Tuza.FanSupport

namespace ResearchMain.Tuza

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {c q : ℕ}

theorem exists_fanCount_packing_odd (hq : Odd q) (a : Fin c ↪ V) (b : Fin q ↪ V)
    (hd : ∀ i j, a i ≠ b j) (hc : ∀ i j, G.Adj (a i) (b j))
    (hb : ∀ i j, i ≠ j → G.Adj (b i) (b j)) :
    ∃ P : Finset (Finset V), Packing G P ∧ P.card = fanCount c q ∧ FanSupport a b P := by
  classical
  let _ : NeZero q := ⟨hq.pos.ne'⟩
  let e : ZMod q ≃ Fin q := Fintype.equivOfCardEq (by simp [ZMod.card])
  let j : Fin (min c q) ↪ Fin c := Fin.castLEEmb (min_le_left c q)
  obtain ⟨f : Fin (min c q) ↪ ZMod q⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin (min c q)) (β := ZMod q)
    (by simp [ZMod.card])
  obtain ⟨P, hP, hcard, hsupport⟩ := exists_fan_packing_supported
    (reflectionFactors (zmod_double_injective hq)) f (j.trans a) (e.toEmbedding.trans b)
    (fun i k => hd (j i) (e k)) (fun i k => hc (j i) (e k))
    (fun k k' hkk' => hb (e k) (e k') (fun hh => hkk' (e.injective hh)))
    (q / 2) (fun i => reflection_nat_card hq (f i))
  refine ⟨P, hP, ?_, ?_⟩
  · simpa [fanCount_odd hq, mul_comm] using hcard
  · exact hsupport.extend j e (fun _ => rfl) (fun _ => rfl)

theorem exists_fanCount_packing_even (hq : Even q) (hpos : 0 < q)
    (a : Fin c ↪ V) (b : Fin q ↪ V)
    (hd : ∀ i j, a i ≠ b j) (hc : ∀ i j, G.Adj (a i) (b j))
    (hb : ∀ i j, i ≠ j → G.Adj (b i) (b j)) :
    ∃ P : Finset (Finset V), Packing G P ∧ P.card = fanCount c q ∧ FanSupport a b P := by
  classical
  have hm := Nat.even_iff.mp hq
  have hodd : Odd (q - 1) := Nat.odd_iff.mpr (by omega)
  let _ : NeZero (q - 1) := ⟨hodd.pos.ne'⟩
  let e : Option (ZMod (q - 1)) ≃ Fin q := Fintype.equivOfCardEq (by
    simp only [Fintype.card_option, ZMod.card, Fintype.card_fin]
    omega)
  let j : Fin (min c (q - 1)) ↪ Fin c := Fin.castLEEmb (min_le_left c (q - 1))
  obtain ⟨f : Fin (min c (q - 1)) ↪ ZMod (q - 1)⟩ :=
    Function.Embedding.nonempty_of_card_le
      (α := Fin (min c (q - 1))) (β := ZMod (q - 1)) (by
      simp [ZMod.card])
  have hcard_edge (i : Fin (min c (q - 1))) :
      Nat.card (extendedReflectionGraph (f i)).edgeSet = q / 2 := by
    rw [extended_nat_card hodd]
    congr 1
    omega
  obtain ⟨P, hP, hcard, hsupport⟩ := exists_fan_packing_supported
    (extendedFactors (zmod_double_injective hodd)) f (j.trans a) (e.toEmbedding.trans b)
    (fun i k => hd (j i) (e k)) (fun i k => hc (j i) (e k))
    (fun k k' hkk' => hb (e k) (e k') (fun hh => hkk' (e.injective hh)))
    (q / 2) hcard_edge
  refine ⟨P, hP, ?_, ?_⟩
  · simpa [fanCount_even hq, mul_comm] using hcard
  · exact hsupport.extend j e (fun _ => rfl) (fun _ => rfl)

theorem exists_fanCount_packing (a : Fin c ↪ V) (b : Fin q ↪ V)
    (hd : ∀ i j, a i ≠ b j) (hc : ∀ i j, G.Adj (a i) (b j))
    (hb : ∀ i j, i ≠ j → G.Adj (b i) (b j)) :
    ∃ P : Finset (Finset V), Packing G P ∧ P.card = fanCount c q ∧ FanSupport a b P := by
  by_cases hz : q = 0
  · subst q
    exact ⟨∅, packing_empty G, by simp, by simp [FanSupport]⟩
  · by_cases he : Even q
    · exact exists_fanCount_packing_even he (Nat.pos_of_ne_zero hz) a b hd hc hb
    · exact exists_fanCount_packing_odd (Nat.not_even_iff_odd.mp he) a b hd hc hb

end ResearchMain.Tuza
