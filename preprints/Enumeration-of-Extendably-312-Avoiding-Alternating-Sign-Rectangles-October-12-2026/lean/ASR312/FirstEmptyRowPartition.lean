import ASR312.BalancedFirstEmptyEquivalence

namespace ASR312

def prefixAt {r k : ℕ} (A : Rectangle r k) (q : Fin r) : Rectangle q.val k :=
  fun i j => A ⟨i.val,lt_trans i.isLt q.isLt⟩ j

abbrev FirstEmptyAt {r k : ℕ} (q : Fin r) :=
  {A : AvoidingRectangle r k k // nonemptyRows (prefixAt A.val q) = q.val ∧ ∀ j, A.val q j = .zero}

theorem firstEmptyAt_card {r k : ℕ} (q : Fin r) (hqk : q.val ≤ k) :
    Nat.card (FirstEmptyAt (k := k) q) = S q.val k q.val * (r-q.val-1).choose (k-q.val) := by
  have transport (p n m R K : ℕ) (hr : p+(n+1) = R) (hk : p+m = K) (hp : p < R) :
      Nat.card {A : AvoidingRectangle R K K //
        nonemptyRows (fun (i : Fin p) j => A.val ⟨i.val,lt_trans i.isLt hp⟩ j) = p ∧
          ∀ j, A.val ⟨p,hp⟩ j = .zero} = S p (p+m) p * n.choose m := by
    subst R; subst K
    exact firstEmptyBalanced_card p n m
  have hk : q.val+(k-q.val) = k := by omega
  have hh := transport q.val (r-q.val-1) (k-q.val) r k (by omega) hk q.isLt
  change Nat.card {A : AvoidingRectangle r k k //
    nonemptyRows (fun (i : Fin q.val) j => A.val ⟨i.val,lt_trans i.isLt q.isLt⟩ j) = q.val ∧
      ∀ j, A.val q j = .zero} = _
  simpa only [hk,Fin.eta] using hh

theorem firstEmptyAt_before {r k : ℕ} (q : Fin r) (A : FirstEmptyAt (k := k) q)
    (i : Fin r) (hi : i < q) : ∃ j, A.val.val i j ≠ .zero := by
  have hh := (nonemptyRows_eq_rows_iff _).mp A.property.1 ⟨i.val,hi⟩
  exact hh

theorem firstEmptyAt_unique {r k : ℕ} (q t : Fin r)
    (A : FirstEmptyAt (k := k) q) (B : FirstEmptyAt (k := k) t) (h : A.val = B.val) : q = t := by
  rcases lt_trichotomy q t with hqt | hqt | hqt
  · obtain ⟨j,hj⟩ := firstEmptyAt_before t B q hqt
    exact False.elim (hj (h ▸ A.property.2 j))
  · exact hqt
  · obtain ⟨j,hj⟩ := firstEmptyAt_before q A t hqt
    exact False.elim (hj (h.symm ▸ B.property.2 j))

theorem firstEmptyAt_exists {r k : ℕ} (hkr : k < r) (A : AvoidingRectangle r k k) :
    ∃ q : Fin r, q.val ≤ k ∧ nonemptyRows (prefixAt A.val q) = q.val ∧ ∀ j, A.val q j = .zero := by
  classical
  let e := (rowSupport A.val)ᶜ
  have hc : e.card = r-k := by
    simp only [e,Finset.card_compl,Fintype.card_fin,rowSupport_card,A.property.2.1]
  have he : e.Nonempty := Finset.card_pos.mp (by rw [hc]; omega)
  let q := e.min' he
  have hqm : q ∈ e := Finset.min'_mem e he
  have hqn : q ∉ rowSupport A.val := Finset.mem_compl.mp hqm
  have hbefore (i : Fin r) (hi : i < q) : i ∈ rowSupport A.val := by
    by_contra hn
    have him : i ∈ e := Finset.mem_compl.mpr hn
    have hh : q ≤ i := Finset.min'_le e i him
    exact (not_lt_of_ge hh) hi
  have hsub : Finset.Iio q ⊆ rowSupport A.val := by
    intro i hi
    exact hbefore i (Finset.mem_Iio.mp hi)
  have hqk := Finset.card_le_card hsub
  rw [Fin.card_Iio,rowSupport_card,A.property.2.1] at hqk
  refine ⟨q,hqk,?_,?_⟩
  · apply (nonemptyRows_eq_rows_iff _).mpr
    intro i
    exact (mem_rowSupport A.val ⟨i.val,lt_trans i.isLt q.isLt⟩).mp
      (hbefore ⟨i.val,lt_trans i.isLt q.isLt⟩ i.isLt)
  · intro j
    by_contra h
    exact hqn ((mem_rowSupport A.val q).mpr ⟨j,h⟩)

noncomputable def firstEmptyPartitionEquiv (r k : ℕ) (hkr : k < r) :
    (Σ q : Fin (k+1), FirstEmptyAt (k := k) (Fin.castLE hkr q)) ≃ AvoidingRectangle r k k := by
  apply Equiv.ofBijective (fun D => D.2.val)
  constructor
  · rintro ⟨q,A⟩ ⟨t,B⟩ h
    have hqt := firstEmptyAt_unique _ _ A B h
    have hqt' : q = t := Fin.ext (congrArg (fun i : Fin r => i.val) hqt)
    subst t
    have hAB : A = B := Subtype.ext h
    subst B
    rfl
  · intro A
    obtain ⟨q,hqk,hq,hz⟩ := firstEmptyAt_exists hkr A
    let t : Fin (k+1) := ⟨q.val,by omega⟩
    have ht : Fin.castLE hkr t = q := Fin.ext rfl
    refine ⟨⟨t,⟨A,?_,?_⟩⟩,rfl⟩
    · exact (congrArg (fun q => nonemptyRows (prefixAt A.val q)) ht).trans hq
    · simpa only [ht] using hz

end ASR312
