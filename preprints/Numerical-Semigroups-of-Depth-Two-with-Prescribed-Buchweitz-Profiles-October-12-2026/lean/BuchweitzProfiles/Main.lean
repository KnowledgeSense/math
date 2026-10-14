import BuchweitzProfiles.ConstructionCount
import BuchweitzProfiles.PrescribedPairs
import BuchweitzProfiles.ProfileBridge

namespace BuchweitzProfiles

private theorem cutoff_eq_multiplicity (N L : ℕ) :
    constructionCutoff N ((N+1)^2+2*L*(N+1)+1) = profileMultiplicity N L := by
  unfold constructionCutoff profileMultiplicity
  ring

/-- A complete construction from the prescribed pair statistics. -/
theorem numericalSemigroup_of_pairs (N L : ℕ) (a : ℕ → ℤ)
    (hN : 2 ≤ N) (hL : 1 ≤ L) (ha1 : a 1 = 1) (haN : a N ≤ L)
    (d t : Fin ((N+1)^2+2*L*(N+1)) → ℕ)
    (hd : ∀ j, 2 ≤ d j ∧ d j ≤ N+1)
    (ht : ∀ j, t j ≤ 2*d j-2)
    (hend : ∀ j, d j = N+1 → t j = 0)
    (hstatistics : ∀ n, 2 ≤ n → n ≤ N →
      (((Finset.univ : Finset (Fin ((N+1)^2+2*L*(N+1)))).filter
        (fun j => n+1 ≤ d j)).card : ℤ) * (2*(n:ℤ)-1) +
      ∑ j ∈ Finset.univ.filter (fun j => n = d j), (t j : ℤ) =
      2*(((N+1)^2+2*L*(N+1):ℕ):ℤ)+5-2*(n:ℤ)+a n-a (n-1)) :
    ∃ S : NumericalSemigroup, ∃ G : Finset ℕ,
      IsMultiplicity S (profileMultiplicity N L) ∧
      IsConductor S (2*profileMultiplicity N L) ∧
      (∀ n, n ∈ G ↔ n ∉ S) ∧ G.card = profileGenus N L ∧
      (∀ n, 2 ≤ n → n ≤ N → beta G n = a n) ∧
      (∀ n, N < n → beta G n < 0) := by
  let h := (N+1)^2+2*L*(N+1)
  let C := digitSet N h d t
  let m := profileMultiplicity N L
  have hm : 3 ≤ m := by
    dsimp [m, profileMultiplicity]
    have h1 : 1 ≤ (4*(N+1)+3)*((N+1)^2+2*L*(N+1)+1) := Nat.succ_le_of_lt (by positivity)
    nlinarith
  have hC : ∀ c ∈ C, c ≤ m-2 := by
    simpa only [C, h, m, cutoff_eq_multiplicity] using digitSet_bound N h d t hN hd ht
  have hz : 0 ∈ C := digitSet_zero N h d t
  have hp : ∃ c ∈ C, 0 < c := digitSet_positive N h d t
  have hc : C.card = h+4 := digitSet_card N h d t hN hd ht
  have hl : (L:ℤ)+(N:ℤ) < h := by
    have hh := largeCount_gt N L (by exact_mod_cast hN) (by exact_mod_cast hL)
    simpa [largeCount, h] using hh
  have hk : 2*((2*N+2:ℕ):ℤ)+1 < 2*((h:ℤ)+3) := by
    dsimp [h]
    have hNp : (2:ℤ) ≤ N := by exact_mod_cast hN
    have hLp : (1:ℤ) ≤ L := by exact_mod_cast hL
    have hnL : 0 ≤ (L:ℤ)*(N+1) := by positivity
    nlinarith [sq_nonneg (N:ℤ)]
  have hprof := profile_of_exact_row_count Finset.univ C m N (2*N+2) h L d t a
    hm hC hz hp hc hN (by exact_mod_cast hL) (by omega) hl hk ha1 haN
    (fun j _ => hd j) (fun j _ => hend j)
    (fun n hn => by
      simpa only [C, h, m, cutoff_eq_multiplicity] using digitSet_count N h d t hN hd ht n hn)
    hstatistics
  refine ⟨depthTwoSemigroup hm hC, gapset m C, depthTwo_multiplicity hm hC,
    depthTwo_conductor hm hC hz, ?_, ?_, ?_, hprof.2⟩
  · intro n
    rw [mem_depthTwoSemigroup, not_not]
    exact mem_gapset_iff hm hC n
  · rw [gapset_card hm hC, hc, profileGenus_eq]
  · intro n hn hnN
    exact hprof.1 n (by omega) hnN

/-- Every bounded integer profile is realized by a genuine depth-two numerical semigroup. -/
theorem prescribed_buchweitz_profile (N L : ℕ) (a : ℕ → ℤ)
    (hN : 2 ≤ N) (hL : 1 ≤ L)
    (ha : ∀ n, 2 ≤ n → n ≤ N → -(L:ℤ) ≤ a n ∧ a n ≤ L) :
    ∃ S : NumericalSemigroup, ∃ G : Finset ℕ,
      IsMultiplicity S (profileMultiplicity N L) ∧
      IsConductor S (2*profileMultiplicity N L) ∧
      (∀ n, n ∈ G ↔ n ∉ S) ∧ G.card = profileGenus N L ∧
      (∀ n, 2 ≤ n → n ≤ N → beta G n = a n) ∧
      (∀ n, N < n → beta G n < 0) := by
  let b : ℤ → ℤ := fun k => if k = 1 then 1 else a k.toNat
  have hb1 : b 1 = 1 := by simp [b]
  have hb : ∀ k : ℤ, 1 ≤ k → k ≤ N → -(L:ℤ) ≤ b k ∧ b k ≤ L := by
    intro k hk hkN
    by_cases he : k = 1
    · simp only [b, he, ite_true]
      constructor <;> omega
    · simp only [b, ite_eq_right he]
      exact ha k.toNat (by omega) (by omega)
  have hlen := prescribedPairs_length hN hL hb1 hb
  have hdata : ∃ d t : Fin ((N+1)^2+2*L*(N+1)) → ℕ,
      (∀ j, 2 ≤ d j ∧ d j ≤ N+1) ∧
      (∀ j, t j ≤ 2*d j-2) ∧
      (∀ j, d j = N+1 → t j = 0) ∧
      (∀ n, 2 ≤ n → n ≤ N →
        ((Finset.univ.filter (fun j => n+1 ≤ d j)).card : ℤ) * (2*(n:ℤ)-1) +
        ∑ j ∈ Finset.univ.filter (fun j => n = d j), (t j : ℤ) =
        2*(((N+1)^2+2*L*(N+1):ℕ):ℤ)+5-2*(n:ℤ)+b n-b (n-1:ℕ)) := by
    rw [← hlen]
    refine ⟨prescribedD, prescribedT, ?_, ?_, ?_, ?_⟩
    · intro j
      exact ⟨(prescribedPairs_bounds hN j).1, (prescribedPairs_bounds hN j).2.1⟩
    · intro j
      exact (prescribedPairs_bounds hN j).2.2.1
    · intro j
      exact (prescribedPairs_bounds hN j).2.2.2
    · exact prescribedPairs_statistics hN hL hb1 hb
  obtain ⟨d, t, hd, ht, hend, hs⟩ := hdata
  have hbN : b N ≤ L := (hb N (by omega) (by omega)).2
  obtain ⟨S, G, hm, hc, hg, hcard, hp, hn⟩ :=
    numericalSemigroup_of_pairs N L (fun n => b n) hN hL hb1 hbN d t hd ht hend hs
  refine ⟨S, G, hm, hc, hg, hcard, ?_, hn⟩
  intro n hn hnN
  rw [hp n hn hnN]
  simp only [b, ite_eq_right (by omega : (n:ℤ) ≠ 1), Int.toNat_natCast]

end BuchweitzProfiles
