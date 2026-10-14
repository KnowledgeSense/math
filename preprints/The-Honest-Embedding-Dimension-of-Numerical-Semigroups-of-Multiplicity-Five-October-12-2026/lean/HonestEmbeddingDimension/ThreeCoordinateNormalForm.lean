import HonestEmbeddingDimension.RelativeNormalForm

namespace HonestEmbeddingDimension

theorem subalgebraValues_coordinateAlgebra {d : ℕ} (f : Fin d → PowerSeries ℂ) :
    subalgebraValues (coordinateAlgebra f) = polynomialValues f := by
  ext n
  constructor
  · rintro ⟨g,hg,horder⟩
    obtain ⟨P,rfl⟩ := (mem_coordinateAlgebra_iff f g).mp hg
    exact ⟨P,horder⟩
  · rintro ⟨P,hP⟩
    exact ⟨MvPolynomial.aeval f P,(mem_coordinateAlgebra_iff f _).mpr ⟨P,rfl⟩,hP⟩

theorem partial_singleton_values {d : ℕ} (f : Fin d → PowerSeries ℂ) (i : Fin d)
    (m : ℕ) (hm : m ≠ 0) (hi : f i = PowerSeries.X ^ m) (n : ℕ) :
    n ∈ subalgebraValues (partialCoordinateAlgebra f {i}) ↔ m ∣ n := by
  have he : partialCoordinateAlgebra f {i} = parameterAlgebra m := by
    simp [partialCoordinateAlgebra,parameterAlgebra,hi]
  rw [he]
  exact parameterAlgebra_values m hm n

theorem partial_pair_values {d : ℕ} (f : Fin d → PowerSeries ℂ) (i j : Fin d)
    (m a : ℕ) (hm : 0 < m) (hcop : m.Coprime a)
    (hi : f i = PowerSeries.X ^ m) (hj : (f j).order = a) :
    subalgebraValues (partialCoordinateAlgebra f {i,j}) =
      {n | ∃ k l : ℕ, n = m*k+a*l} := by
  have he : partialCoordinateAlgebra f {i,j} = coordinateAlgebra (planeCoordinates m (f j)) := by
    simp [partialCoordinateAlgebra,coordinateAlgebra,planeCoordinates,hi,Set.pair_comm]
  rw [he,subalgebraValues_coordinateAlgebra]
  exact polynomial_plane_values m a hm hcop (f j) hj

/-- Normalize the first two characteristic values without changing any formal values. -/
theorem formal_two_coordinate_normal_form {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (hf0 : ∀ i, (f i).constantCoeff = 0) (m a : ℕ) (hm : 0 < m) (ha0 : 0 < a)
    (hmv : m ∈ formalValues f)
    (hminm : ∀ n ∈ formalValues f, 0 < n → m ≤ n)
    (hav : a ∈ formalValues f) (ha : ¬m ∣ a)
    (hmina : ∀ n ∈ formalValues f, ¬m ∣ n → a ≤ n) :
    ∃ (g : Fin d → PowerSeries ℂ) (i j : Fin d),
      (∀ k, (g k).constantCoeff = 0) ∧ formalValues g = formalValues f ∧
      i ≠ j ∧ g i = PowerSeries.X ^ m ∧ (g j).order = a := by
  obtain ⟨i,g,hgi,hg0,hgv⟩ := normalize_minimum_coordinate f hf0 m hm hmv hminm
  have hs := partial_singleton_values g i m (Nat.ne_of_gt hm) hgi
  obtain ⟨h,hh0,hhv,hfix,j,hj,hja⟩ := normalize_formal_coordinate_outside_subalgebra g hg0 {i} a ha0
    (by rwa [hgv]) (by rwa [hs]) (by
      intro n hn hout
      apply hmina n (by rwa [← hgv])
      rwa [← hs])
  refine ⟨h,i,j,hh0,hhv.trans hgv,?_,?_,hja⟩
  · simpa [eq_comm] using hj
  · rw [hfix i (Set.mem_singleton i),hgi]

/-- The first three characteristic values occur in a genuine formal coordinate normal form. -/
theorem formal_three_coordinate_normal_form {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (hf0 : ∀ i, (f i).constantCoeff = 0) (m a b : ℕ)
    (hm : 0 < m) (ha0 : 0 < a) (hb0 : 0 < b) (hcop : m.Coprime a)
    (hmv : m ∈ formalValues f)
    (hminm : ∀ n ∈ formalValues f, 0 < n → m ≤ n)
    (hav : a ∈ formalValues f) (ha : ¬m ∣ a)
    (hmina : ∀ n ∈ formalValues f, ¬m ∣ n → a ≤ n)
    (hbv : b ∈ formalValues f) (hb : ¬∃ k l : ℕ, b = m*k+a*l)
    (hminb : ∀ n ∈ formalValues f, (¬∃ k l : ℕ, n = m*k+a*l) → b ≤ n) :
    ∃ (g : Fin d → PowerSeries ℂ) (i j k : Fin d),
      (∀ l, (g l).constantCoeff = 0) ∧ formalValues g = formalValues f ∧
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      g i = PowerSeries.X ^ m ∧ (g j).order = a ∧ (g k).order = b := by
  obtain ⟨g,i,j,hg0,hgv,hij,hgi,hgj⟩ := formal_two_coordinate_normal_form f hf0 m a hm ha0
    hmv hminm hav ha hmina
  have hs := partial_pair_values g i j m a hm hcop hgi hgj
  obtain ⟨h,hh0,hhv,hfix,k,hk,hkb⟩ := normalize_formal_coordinate_outside_subalgebra g hg0 {i,j} b hb0
    (by rwa [hgv]) (by rwa [hs]) (by
      intro n hn hout
      apply hminb n (by rwa [← hgv])
      simpa only [hs,Set.mem_ofPred_eq] using hout)
  have hki : k ≠ i ∧ k ≠ j := by simpa using hk
  refine ⟨h,i,j,k,hh0,hhv.trans hgv,hij,hki.1.symm,hki.2.symm,?_,?_,hkb⟩
  · rw [hfix i (by simp),hgi]
  · rw [hfix j (by simp),hgj]

theorem three_le_of_distinct_coordinates {d : ℕ} (i j k : Fin d)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : 3 ≤ d := by
  have hc : ({i,j,k} : Finset (Fin d)).card = 3 := by
    simp [hij,hik,hjk]
  have h := Finset.card_le_univ ({i,j,k} : Finset (Fin d))
  simpa [hc] using h

theorem formalValues_reorder_three (f : Fin 3 → PowerSeries ℂ)
    (hf0 : ∀ i, (f i).constantCoeff = 0) (i j k : Fin 3)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    formalValues ![f i,f j,f k] = formalValues f := by
  let e : Fin 3 → Fin 3 := ![i,j,k]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e,eq_comm]
  have hs := Finite.surjective_of_injective he
  have h0 : ∀ a, ((![f i,f j,f k] : Fin 3 → PowerSeries ℂ) a).constantCoeff = 0 := by
    intro a
    fin_cases a <;> simp [hf0]
  rw [formalValues_eq_polynomialValues _ h0, formalValues_eq_polynomialValues _ hf0]
  apply polynomialValues_eq_of_coordinateAlgebra_eq
  have hh : (![f i,f j,f k] : Fin 3 → PowerSeries ℂ) = f ∘ e := by
    funext a
    fin_cases a <;> rfl
  rw [hh,coordinateAlgebra,hs.range_comp f]
  rfl

end HonestEmbeddingDimension
