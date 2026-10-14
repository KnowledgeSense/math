import ThagomizerTuran.KLRecurrence

/-! Transport of the actual recursive invariants through interval-preserving
ranked order embeddings, as needed for the proved graphic intervals. -/
namespace MatroidInverseZ

open Finset Polynomial

variable {α β : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
  [PartialOrder β] [LocallyFiniteOrder β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
/-- An interval-preserving order embedding has precisely the same finite closed intervals. -/
theorem map_Icc_interval (f : α ↪o β)
    (hI : ∀ a b y, f a ≤ y → y ≤ f b → ∃ x, f x = y) (a b : α) :
    (Icc a b).map f.toEmbedding = Icc (f a) (f b) := by
  ext y
  constructor
  · rintro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp h
    exact mem_Icc.mpr ⟨f.monotone (mem_Icc.mp hx).1, f.monotone (mem_Icc.mp hx).2⟩
  · intro hy
    obtain ⟨x, rfl⟩ := hI a b y (mem_Icc.mp hy).1 (mem_Icc.mp hy).2
    exact Finset.mem_map.mpr ⟨x, mem_Icc.mpr
      ⟨f.le_iff_le.mp (mem_Icc.mp hy).1, f.le_iff_le.mp (mem_Icc.mp hy).2⟩, rfl⟩

omit [DecidableEq α] [DecidableEq β] in
theorem map_Ico_interval (f : α ↪o β)
    (hI : ∀ a b y, f a ≤ y → y ≤ f b → ∃ x, f x = y) (a b : α) :
    (Ico a b).map f.toEmbedding = Ico (f a) (f b) := by
  ext y
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp h
    exact mem_Ico.mpr ⟨f.monotone (mem_Ico.mp hx).1, f.lt_iff_lt.mpr (mem_Ico.mp hx).2⟩
  · intro hy
    obtain ⟨x, rfl⟩ := hI a b y (mem_Ico.mp hy).1 (mem_Ico.mp hy).2.le
    exact Finset.mem_map.mpr ⟨x, mem_Ico.mpr
      ⟨f.le_iff_le.mp (mem_Ico.mp hy).1, f.lt_iff_lt.mp (mem_Ico.mp hy).2⟩, rfl⟩

omit [DecidableEq α] [DecidableEq β] in
theorem map_Ioc_interval (f : α ↪o β)
    (hI : ∀ a b y, f a ≤ y → y ≤ f b → ∃ x, f x = y) (a b : α) :
    (Ioc a b).map f.toEmbedding = Ioc (f a) (f b) := by
  ext y
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp h
    exact mem_Ioc.mpr ⟨f.lt_iff_lt.mpr (mem_Ioc.mp hx).1, f.monotone (mem_Ioc.mp hx).2⟩
  · intro hy
    obtain ⟨x, rfl⟩ := hI a b y (mem_Ioc.mp hy).1.le (mem_Ioc.mp hy).2
    exact Finset.mem_map.mpr ⟨x, mem_Ioc.mpr
      ⟨f.lt_iff_lt.mp (mem_Ioc.mp hy).1, f.le_iff_le.mp (mem_Ioc.mp hy).2⟩, rfl⟩

/-- Möbius invariants are unchanged by the actual interval identification. -/
theorem mu_interval_transport (f : α ↪o β)
    (hI : ∀ a b y, f a ≤ y → y ≤ f b → ∃ x, f x = y) :
    ∀ a b, IncidenceAlgebra.mu ℤ (f a) (f b) = IncidenceAlgebra.mu ℤ a b := by
  intro a b
  generalize hn : (Icc a b).card = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    rw [IncidenceAlgebra.mu_apply (f a) (f b), IncidenceAlgebra.mu_apply a b]
    simp only [f.injective.eq_iff]
    by_cases he : a = b
    · simp [he]
    · rw [ite_eq_right he, ite_eq_right he, ← map_Ico_interval f hI a b, sum_map]
      simp only [RelEmbedding.coe_toEmbedding]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hax := mem_Ico.mp hx
      exact ih (Icc a x).card (by
        rw [← hn]
        exact card_lt_card (Icc_ssubset_Icc_right (hax.1.trans hax.2.le) le_rfl hax.2)) a x rfl

theorem characteristic_interval_transport (f : α ↪o β)
    (hI : ∀ a b y, f a ≤ y → y ≤ f b → ∃ x, f x = y)
    (r : α → ℕ) (s : β → ℕ) (hr : ∀ a b, s (f b) - s (f a) = r b - r a)
    (a b : α) : characteristic s (f a) (f b) = characteristic r a b := by
  rw [characteristic, characteristic, ← map_Icc_interval f hI a b, sum_map]
  simp only [RelEmbedding.coe_toEmbedding]
  apply Finset.sum_congr rfl
  intro x _
  rw [mu_interval_transport f hI a x, hr x b]

/-- KL recursion transport uses the already proved uniqueness theorem. -/
theorem kl_interval_transport (f : α ↪o β)
    (hI : ∀ a b y, f a ≤ y → y ≤ f b → ∃ x, f x = y)
    (r : α → ℕ) (s : β → ℕ) (hr : ∀ a b, s (f b) - s (f a) = r b - r a) :
    ∀ a b, kl s (f b) (f a) = kl r b a := by
  apply kl_unique_of_recurrence r (fun a b => kl s (f b) (f a))
  intro a b
  rw [kl_recurrence]
  simp only [f.injective.eq_iff, hr a b]
  by_cases he : a = b
  · simp [he]
  · rw [ite_eq_right he, ite_eq_right he]
    congr 2
    rw [← map_Ioc_interval f hI a b, sum_map]
    simp only [RelEmbedding.coe_toEmbedding]
    apply Finset.sum_congr rfl
    intro x _
    rw [characteristic_interval_transport f hI r s hr a x]

/-- The inverse-KL incidence inverse transports through the same intervals. -/
theorem klInverse_interval_transport (f : α ↪o β)
    (hI : ∀ a b y, f a ≤ y → y ≤ f b → ∃ x, f x = y)
    (r : α → ℕ) (s : β → ℕ) (hr : ∀ a b, s (f b) - s (f a) = r b - r a) :
    ∀ a b, klInverse s (f a) (f b) = klInverse r a b := by
  intro a b
  generalize hn : (Icc a b).card = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    rw [klInverse_recurrence s (f a) (f b), klInverse_recurrence r a b]
    simp only [f.injective.eq_iff]
    by_cases he : a = b
    · simp [he]
    · rw [ite_eq_right he, ite_eq_right he, ← map_Ico_interval f hI a b, sum_map]
      simp only [RelEmbedding.coe_toEmbedding]
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hax := mem_Ico.mp hx
      rw [ih (Icc a x).card (by
        rw [← hn]
        exact card_lt_card (Icc_ssubset_Icc_right (hax.1.trans hax.2.le) le_rfl hax.2)) a x rfl,
        kl_interval_transport f hI r s hr x b]

theorem inverseKL_interval_transport (f : α ↪o β)
    (hI : ∀ a b y, f a ≤ y → y ≤ f b → ∃ x, f x = y)
    (r : α → ℕ) (s : β → ℕ) (hr : ∀ a b, s (f b) - s (f a) = r b - r a)
    (a b : α) : inverseKL s (f a) (f b) = inverseKL r a b := by
  simp only [inverseKL, hr a b, klInverse_interval_transport f hI r s hr a b]

/-- Ordinary inverse-Z transports through the proved ranked flat intervals. -/
theorem inverseZ_interval_transport (f : α ↪o β)
    (hI : ∀ a b y, f a ≤ y → y ≤ f b → ∃ x, f x = y)
    (r : α → ℕ) (s : β → ℕ) (hr : ∀ a b, s (f b) - s (f a) = r b - r a)
    (a b : α) : inverseZ s (f a) (f b) = inverseZ r a b := by
  rw [inverseZ, inverseZ, ← map_Icc_interval f hI a b, sum_map]
  simp only [RelEmbedding.coe_toEmbedding]
  apply Finset.sum_congr rfl
  intro x _
  rw [hr x b, mu_interval_transport f hI x b, inverseKL_interval_transport f hI r s hr a x]

end MatroidInverseZ
