import ASR312.DecreasingCompletionASM

namespace ASR312

theorem emptyRow_extension_witness {r k : ℕ} (A : Rectangle r k)
    (he : ExtendablyAvoids312 A) (q : Fin r) (hz : ∀ j, A q j = .zero) :
    ∃ (n : ℕ) (hr : r ≤ n) (hk : k ≤ n) (B : Rectangle n n) (c : Fin n),
      IsASM B ∧ Avoids312 B ∧ B (Fin.castLE hr q) c = .plus ∧ k ≤ c.val ∧
      ∀ i j, B (Fin.castLE hr i) (Fin.castLE hk j) = A i j := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  obtain ⟨c,hc⟩ := asm_row_exists_plus B hB (Fin.castLE hr q)
  have hkc : k ≤ c.val := by
    by_contra hn
    have hlt : c.val < k := by omega
    have hj : Fin.castLE hk ⟨c.val,hlt⟩ = c := Fin.ext rfl
    have hh := hmatch q ⟨c.val,hlt⟩
    rw [hj,hc,hz] at hh
    cases hh
  exact ⟨n,hr,hk,B,c,hB,hav,hc,hkc,hmatch⟩

theorem afterEmptyRow_no_minus {r k : ℕ} (A : Rectangle r k)
    (he : ExtendablyAvoids312 A) (q : Fin r) (hz : ∀ j, A q j = .zero)
    (i : Fin r) (j : Fin k) (hqi : q < i) : A i j ≠ .minus := by
  obtain ⟨n,hr,hk,B,c,hB,hav,hc,hkc,hmatch⟩ := emptyRow_extension_witness A he q hz
  intro hij
  have hBminus := (hmatch i j).trans hij
  obtain ⟨u,hu,hBu⟩ := plus_before_minus (B (Fin.castLE hr i))
    (hB.1.1 (Fin.castLE hr i)).2.1 (Fin.castLE hk j) hBminus
  obtain ⟨t,ht,hBt⟩ := plus_after_minus (fun t => B t (Fin.castLE hk j))
    (hB.2.2 (Fin.castLE hk j)).2 (Fin.castLE hr i) hBminus
  exact hav ⟨Fin.castLE hr q,Fin.castLE hr i,t,u,Fin.castLE hk j,c,hqi,ht,hu,
    by change j.val < c.val; omega,hc,hBu,hBt⟩

theorem afterEmptyRow_descending {r k : ℕ} (A : Rectangle r k)
    (he : ExtendablyAvoids312 A) (q : Fin r) (hz : ∀ j, A q j = .zero)
    (i t : Fin r) (j u : Fin k) (hqi : q < i) (hit : i < t) (hju : j < u)
    (hij : A i j = .plus) (htu : A t u = .plus) : False := by
  obtain ⟨n,hr,hk,B,c,_,hav,hc,hkc,hmatch⟩ := emptyRow_extension_witness A he q hz
  exact hav ⟨Fin.castLE hr q,Fin.castLE hr i,Fin.castLE hr t,Fin.castLE hk j,Fin.castLE hk u,c,
    hqi,hit,hju,by change u.val < c.val; omega,hc,(hmatch i j).trans hij,(hmatch t u).trans htu⟩

theorem afterEmptyRow_row_plus_unique {r k : ℕ} (A : Rectangle r k) (ha : IsASR A)
    (he : ExtendablyAvoids312 A) (q : Fin r) (hz : ∀ j, A q j = .zero)
    (i : Fin r) (hqi : q < i) {j u : Fin k} (hj : A i j = .plus) (hu : A i u = .plus) : j = u := by
  apply noMinus_sum_le_one_unique (A i) (afterEmptyRow_no_minus A he q hz i · hqi) _ hj hu
  have hs := row_sum_of_plus A ha i hj
  omega

end ASR312
