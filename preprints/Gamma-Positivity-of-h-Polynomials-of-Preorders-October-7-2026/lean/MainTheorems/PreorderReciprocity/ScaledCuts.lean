import MainTheorems.PreorderReciprocity.ScaledTransport

namespace ResearchMain.PreorderReciprocity

variable {L R : Type*} [Fintype L] [Fintype R]

theorem transport_closed_cut {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}
    (p : PreorderGamma.NaturalTransport r d s) (A : Finset L) (B : Finset R)
    (hout : ∀ a ∈ A, ∀ b, b ∉ B → p.flow a b = 0)
    (hin : ∀ b ∈ B, ∀ a, a ∉ A → p.flow a b = 0) :
    (∑ a ∈ A, d a) = ∑ b ∈ B, s b := by
  classical
  have hrow : ∀ a ∈ A, ∑ b ∈ B, p.flow a b = d a := by
    intro a ha
    rw [← p.row_sum a]
    exact Finset.sum_subset (Finset.subset_univ B)
      (fun b hb hnot => hout a ha b hnot)
  have hcol : ∀ b ∈ B, ∑ a ∈ A, p.flow a b = s b := by
    intro b hb
    rw [← p.column_sum b]
    exact Finset.sum_subset (Finset.subset_univ A)
      (fun a ha hnot => hin b hb a hnot)
  calc
    _ = ∑ a ∈ A, ∑ b ∈ B, p.flow a b :=
      Finset.sum_congr rfl fun a ha => (hrow a ha).symm
    _ = ∑ b ∈ B, ∑ a ∈ A, p.flow a b := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun b hb => hcol b hb

omit [Fintype L] [Fintype R] in
theorem scaled_subsum (k : ℕ) (hk : 0 < k) (x : L → ℕ)
    (A : Finset L) (hpos : ∀ a ∈ A, 0 < x a) :
    (∑ a ∈ A, (k * x a - 1)) = k * (∑ a ∈ A, x a) - A.card := by
  rw [Finset.sum_tsub_distrib _ (by
    intro a ha
    have h1 : 1 ≤ k := by omega
    have h2 : 1 ≤ x a := hpos a ha
    have h := Nat.mul_le_mul h1 h2
    simpa only [one_mul] using h), ← Finset.mul_sum]
  simp

omit [Fintype L] [Fintype R] in
theorem scaled_subsum_not_multiple (k : ℕ) (hk : 0 < k) (x : L → ℕ)
    (A : Finset L) (hpos : ∀ a ∈ A, 0 < x a)
    (hA : A.Nonempty) (hcard : A.card < k) :
    ¬∃ q : ℕ, (∑ a ∈ A, (k * x a - 1)) = k * q := by
  have hbound : A.card ≤ k * ∑ a ∈ A, x a := by
    calc
      _ = ∑ a ∈ A, 1 := by simp
      _ ≤ ∑ a ∈ A, k * x a := by
        apply Finset.sum_le_sum
        intro a ha
        have h1 : 1 ≤ k := by omega
        have h2 : 1 ≤ x a := hpos a ha
        have h := Nat.mul_le_mul h1 h2
        simpa only [one_mul] using h
      _ = _ := (Finset.mul_sum _ _ _).symm
  rintro ⟨q, hq⟩
  rw [scaled_subsum k hk x A hpos] at hq
  have heq : A.card + k * q = k * ∑ a ∈ A, x a := by omega
  have hd : k ∣ A.card + k * q := heq.symm ▸ dvd_mul_right k (∑ a ∈ A, x a)
  have hdkq : k ∣ k * q := dvd_mul_right k q
  have hdA : k ∣ A.card := (Nat.dvd_add_iff_left hdkq).mpr hd
  have hle := Nat.le_of_dvd (Finset.card_pos.mpr hA) hdA
  omega

theorem bounded_positive_residue (k t f : ℕ) (hk : 0 < k)
    (ht : 0 < t) (htk : t < k) (hf : 0 < f) (hfk : f < k)
    (hd : k ∣ f + t) : f = k - t := by
  obtain ⟨q, hq⟩ := hd
  have hqpos : 0 < q := by
    by_contra h
    have hz : q = 0 := by omega
    simp only [hz, mul_zero] at hq
    omega
  have hqbound : q < 2 := by
    apply (Nat.mul_lt_mul_left hk).mp
    rw [← hq]
    omega
  have hqone : q = 1 := by omega
  simp only [hqone, mul_one] at hq
  omega

theorem two_subtree_flows_exceed_capacity (k t u : ℕ) (htu : t + u < k) :
    k < (k - t) + (k - u) := by omega

omit [Fintype L] [Fintype R] in
theorem scaled_boundary_flow (k : ℕ) (hk : 0 < k) (x : L → ℕ)
    (A : Finset L) (hpos : ∀ a ∈ A, 0 < x a)
    (hA : A.Nonempty) (hcard : A.card < k) (q f : ℕ)
    (hf : 0 < f) (hfk : f ≤ k)
    (hbalance : (∑ a ∈ A, (k * x a - 1)) = k * q + f) : f = k - A.card := by
  have hbound : A.card ≤ k * ∑ a ∈ A, x a := by
    calc
      _ = ∑ a ∈ A, 1 := by simp
      _ ≤ ∑ a ∈ A, k * x a := by
        apply Finset.sum_le_sum
        intro a ha
        have h1 : 1 ≤ k := by omega
        have h2 : 1 ≤ x a := hpos a ha
        have h := Nat.mul_le_mul h1 h2
        simpa only [one_mul] using h
      _ = _ := (Finset.mul_sum _ _ _).symm
  rw [scaled_subsum k hk x A hpos] at hbalance
  have heq : k * q + (f + A.card) = k * ∑ a ∈ A, x a := by omega
  have hd : k ∣ k * q + (f + A.card) :=
    heq.symm ▸ dvd_mul_right k (∑ a ∈ A, x a)
  have hres : k ∣ f + A.card := (Nat.dvd_add_iff_right (dvd_mul_right k q)).mpr hd
  have hflt : f < k := by
    by_contra h
    have heqf : f = k := by omega
    rw [heqf] at hres
    have ht : k ∣ A.card := (Nat.dvd_add_iff_right (dvd_refl k)).mpr hres
    have hle := Nat.le_of_dvd (Finset.card_pos.mpr hA) ht
    omega
  exact bounded_positive_residue k A.card f hk (Finset.card_pos.mpr hA) hcard hf hflt hres

theorem scaled_closed_cut_contains_dummy (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : PreorderGamma.NaturalTransport (augmentedRelation r)
      (scaledDemand (R := R) k x) (fun _ : R => k))
    (A : Finset (Option L)) (B : Finset R) (hA : A.Nonempty)
    (hout : ∀ a ∈ A, ∀ b, b ∉ B → p.flow a b = 0)
    (hin : ∀ b ∈ B, ∀ a, a ∉ A → p.flow a b = 0) : none ∈ A := by
  classical
  by_contra hnone
  let S := Finset.univ.filter fun a : L => some a ∈ A
  have hmap : A = S.map Function.Embedding.some := by
    ext a
    cases a with
    | none => simp [hnone]
    | some a => simp [S]
  have hS : S.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    cases a with
    | none => exact False.elim (hnone ha)
    | some a => exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
  have hScard : S.card < k :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_lt
      (by simpa only [Finset.card_univ] using hk)
  have hcut := transport_closed_cut p A B hout hin
  rw [hmap, Finset.sum_map] at hcut
  simp only [Function.Embedding.some_apply, scaledDemand, Finset.sum_const,
    nsmul_eq_mul] at hcut
  have hforbidden := scaled_subsum_not_multiple k (by omega) x S
    (fun a ha => hpos a) hS hScard
  apply hforbidden
  exact ⟨B.card, hcut.trans (Nat.mul_comm _ _)⟩

theorem scaled_closed_cut_eq_univ (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : PreorderGamma.NaturalTransport (augmentedRelation r)
      (scaledDemand (R := R) k x) (fun _ : R => k))
    (A : Finset (Option L)) (B : Finset R) (hA : A.Nonempty)
    (hout : ∀ a ∈ A, ∀ b, b ∉ B → p.flow a b = 0)
    (hin : ∀ b ∈ B, ∀ a, a ∉ A → p.flow a b = 0) :
    A = Finset.univ ∧ B = Finset.univ := by
  classical
  have hnone := scaled_closed_cut_contains_dummy r x hpos k hk p A B hA hout hin
  have hall : ∀ a, a ∈ A := by
    intro a
    by_contra ha
    let Ac := Finset.univ \ A
    let Bc := Finset.univ \ B
    have hAc : Ac.Nonempty :=
      ⟨a, Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, ha⟩⟩
    have hoc : ∀ a ∈ Ac, ∀ b, b ∉ Bc → p.flow a b = 0 := by
      intro a ha b hb
      have hnot : a ∉ A := (Finset.mem_sdiff.mp ha).2
      have hbin : b ∈ B := by simpa [Bc] using hb
      exact hin b hbin a hnot
    have hic : ∀ b ∈ Bc, ∀ a, a ∉ Ac → p.flow a b = 0 := by
      intro b hb a ha
      have hnot : b ∉ B := (Finset.mem_sdiff.mp hb).2
      have hain : a ∈ A := by simpa [Ac] using ha
      exact hout a hain b hnot
    have hc := scaled_closed_cut_contains_dummy r x hpos k hk p Ac Bc hAc hoc hic
    exact (Finset.mem_sdiff.mp hc).2 hnone
  have hbll : ∀ b, b ∈ B := by
    intro b
    by_contra hb
    have hz : (∑ a, p.flow a b) = 0 :=
      Finset.sum_eq_zero fun a ha => hout a (hall a) b hb
    rw [p.column_sum] at hz
    omega
  exact ⟨Finset.eq_univ_of_forall hall, Finset.eq_univ_of_forall hbll⟩

theorem transport_single_edge_cut {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}
    (p : PreorderGamma.NaturalTransport r d s) (A : Finset L) (B : Finset R)
    (a₀ : L) (b₀ : R) (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∉ B)
    (hout : ∀ a ∈ A, ∀ b, b ∉ B → a ≠ a₀ ∨ b ≠ b₀ → p.flow a b = 0)
    (hin : ∀ b ∈ B, ∀ a, a ∉ A → p.flow a b = 0) :
    (∑ a ∈ A, d a) = (∑ b ∈ B, s b) + p.flow a₀ b₀ := by
  classical
  have hrow : ∀ a ∈ A, d a = (∑ b ∈ B, p.flow a b) + p.flow a b₀ := by
    intro a ha
    rw [← p.row_sum a]
    calc
      _ = ∑ b ∈ insert b₀ B, p.flow a b := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro b hb hnot
        have hnb : b ∉ B := fun h => hnot (Finset.mem_insert_of_mem h)
        have hne : b ≠ b₀ := by
          intro h
          apply hnot
          rw [h]
          exact Finset.mem_insert_self b₀ B
        exact hout a ha b hnb (Or.inr hne)
      _ = _ := by rw [Finset.sum_insert hb₀]; exact Nat.add_comm _ _
  have hcol : ∀ b ∈ B, (∑ a ∈ A, p.flow a b) = s b := by
    intro b hb
    rw [← p.column_sum b]
    exact Finset.sum_subset (Finset.subset_univ A)
      (fun a ha hnot => hin b hb a hnot)
  have hedge : (∑ a ∈ A, p.flow a b₀) = p.flow a₀ b₀ := by
    apply Finset.sum_eq_single a₀
    · intro a ha hne
      exact hout a ha b₀ hb₀ (Or.inl hne)
    · exact fun h => False.elim (h ha₀)
  calc
    _ = ∑ a ∈ A, ((∑ b ∈ B, p.flow a b) + p.flow a b₀) :=
      Finset.sum_congr rfl fun a ha => hrow a ha
    _ = (∑ a ∈ A, ∑ b ∈ B, p.flow a b) + ∑ a ∈ A, p.flow a b₀ :=
      Finset.sum_add_distrib
    _ = _ := by
      rw [Finset.sum_comm, hedge]
      congr 1
      exact Finset.sum_congr rfl fun b hb => hcol b hb

end ResearchMain.PreorderReciprocity
