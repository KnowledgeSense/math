import ASR312.RowStructure

namespace ASR312

 theorem asm_row_exists_plus {n : ℕ} (A : Rectangle n n) (ha : IsASM A) (i : Fin n) :
    ∃ j, A i j = .plus := by
  obtain ⟨j,hj⟩ := ha.2.1 i
  cases he : A i j with
  | zero => exact False.elim (hj he)
  | plus => exact ⟨j,he⟩
  | minus =>
    obtain ⟨x,_,hx⟩ := plus_before_minus (A i) (ha.1.1 i).2.1 j he
    exact ⟨x,hx⟩

 theorem asm_top_right_of_minus_not_plus {n : ℕ} [NeZero n] (A : Rectangle n n)
    (ha : IsASM A) (hav : Avoids312 A) (i : Fin n) (hi : A i 0 = .plus)
    {z q b : Fin n} (hz : A i z = .minus) (hqi : q < i) (hzb : z < b) :
    A q b ≠ .plus := by
  intro hqb
  obtain ⟨t,hit,htz⟩ := plus_after_minus (fun t => A t z) (ha.2.2 z).2 i hz
  have hz0 : 0 < z := by
    apply Fin.pos_iff_ne_zero.mpr
    intro he
    subst z
    rw [hi] at hz
    cases hz
  exact hav ⟨q,i,t,0,z,b,hqi,hit,hz0,hzb,hqb,hi,htz⟩

 theorem top_right_of_minus_zero {r k : ℕ} (A : Rectangle r (k+1))
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (i : Fin r) (hi : A i 0 = .plus)
    {z b : Fin (k+1)} (hz : A i z = .minus)
    (qrow : Fin r) (hqi : qrow < i) (hzb : z < b) : A qrow b = .zero := by
  obtain ⟨n,hr,hk,B,hB,hav,heq⟩ := he
  let _ : NeZero n := ⟨by omega⟩
  have hzero : Fin.castLE hk (0 : Fin (k+1)) = (0 : Fin n) := Fin.ext rfl
  have hp (c : Fin (k+1)) (hzc : z < c) : A qrow c ≠ .plus := by
    have hh := asm_top_right_of_minus_not_plus B hB hav (Fin.castLE hr i)
      (by rw [← hzero,heq]; exact hi) (z:=Fin.castLE hk z)
      (q:=Fin.castLE hr qrow) (b:=Fin.castLE hk c) (by rw [heq]; exact hz) hqi hzc
    rwa [heq] at hh
  have hn : A qrow b ≠ .minus := by
    intro hqb
    obtain ⟨c,hbc,hqc⟩ := plus_after_minus (A qrow) (ha.1 qrow).2.2 b hqb
    exact hp c (lt_trans hzb hbc) hqc
  cases hx : A qrow b with
  | minus => exact False.elim (hn hx)
  | zero => rfl
  | plus => exact False.elim (hp b hzb hx)

 theorem firstColumn_minus_above_nonempty {r k : ℕ} (A : Rectangle r (k+1))
    (he : ExtendablyAvoids312 A) (i : Fin r) (hi : A i 0 = .plus)
    {z : Fin (k+1)} (hz : A i z = .minus) (q : Fin r) (hqi : q < i) :
    ∃ j, A q j ≠ .zero := by
  obtain ⟨n,hr,hk,B,hB,hav,heq⟩ := he
  let _ : NeZero n := ⟨by omega⟩
  have hzero : Fin.castLE hk (0 : Fin (k+1)) = (0 : Fin n) := Fin.ext rfl
  obtain ⟨b,hb⟩ := asm_row_exists_plus B hB (Fin.castLE hr q)
  have hbi : b.val < k+1 := by
    by_contra hh
    have hzb : Fin.castLE hk z < b := by change z.val < b.val; have := z.isLt; omega
    exact asm_top_right_of_minus_not_plus B hB hav (Fin.castLE hr i)
      (by rw [← hzero,heq]; exact hi) (by rw [heq]; exact hz) hqi hzb hb
  let j : Fin (k+1) := ⟨b.val,hbi⟩
  refine ⟨j,?_⟩
  have hb' : Fin.castLE hk j = b := Fin.ext rfl
  have hqj := heq q j
  rw [hb',hb] at hqj
  rw [← hqj]
  exact Entry.noConfusion

end ASR312
