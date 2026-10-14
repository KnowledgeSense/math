import MainTheorems.PreorderGamma.Macaulay.SquarefreeDownset

namespace ResearchMain.PreorderGamma.Macaulay

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

def squarefreeMonomial (F : Finset V) : V → ℕ := fun v => if v ∈ F then 1 else 0

def monomialDegree (m : V → ℕ) : ℕ := ∑ v, m v

omit [Fintype V] in
theorem squarefreeMonomial_injective : Function.Injective (squarefreeMonomial (V := V)) := by
  intro F G h
  ext v
  have hv := congrFun h v
  by_cases hF : v ∈ F <;> by_cases hG : v ∈ G <;>
    simp [squarefreeMonomial, hF, hG] at hv ⊢

omit [Fintype V] in
theorem squarefreeMonomial_le_iff {F G : Finset V} :
    squarefreeMonomial F ≤ squarefreeMonomial G ↔ F ⊆ G := by
  constructor
  · intro h v hv
    have hh := h v
    by_contra hn
    simp [squarefreeMonomial, hv, hn] at hh
  · intro h v
    by_cases hv : v ∈ F
    · simp [squarefreeMonomial, hv, h hv]
    · simp [squarefreeMonomial, hv]

@[simp] theorem monomialDegree_squarefree (F : Finset V) :
    monomialDegree (squarefreeMonomial F) = F.card := by
  simp [monomialDegree, squarefreeMonomial]

theorem exists_face_of_monomial_le {F : Finset V} {m : V → ℕ}
    (hm : m ≤ squarefreeMonomial F) : ∃ G ⊆ F, squarefreeMonomial G = m := by
  let G : Finset V := Finset.univ.filter fun v => m v = 1
  have he : squarefreeMonomial G = m := by
    funext v
    by_cases hv : m v = 1
    · simp [squarefreeMonomial, G, hv]
    · have hzero : m v = 0 := by
        have hbound : m v ≤ 1 := (hm v).trans (by
          by_cases hmem : v ∈ F <;> simp [squarefreeMonomial, hmem])
        omega
      simp [squarefreeMonomial, G, hzero]
  refine ⟨G, squarefreeMonomial_le_iff.mp ?_, he⟩
  rwa [he]

structure FiniteMulticomplex (V : Type*) [Fintype V] where
  monomials : Finset (V → ℕ)
  zero_mem : (0 : V → ℕ) ∈ monomials
  lower_closed : ∀ m ∈ monomials, ∀ a, a ≤ m → a ∈ monomials

noncomputable def FiniteMulticomplex.hilbert (C : FiniteMulticomplex V) (i : ℕ) : ℕ := by
  classical
  exact (C.monomials.filter (fun m => monomialDegree m = i)).card

noncomputable def multicomplexOfDownset (family : Finset (Finset V))
    (hzero : ∅ ∈ family) (hdown : ∀ F ∈ family, ∀ G ⊆ F, G ∈ family) : FiniteMulticomplex V := by
  classical
  refine ⟨family.image squarefreeMonomial, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨∅, hzero, by funext v; simp [squarefreeMonomial]⟩
  · intro m hm a ha
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨G, hGF, he⟩ := exists_face_of_monomial_le ha
    exact Finset.mem_image.mpr ⟨G, hdown F hF G hGF, he⟩

theorem multicomplexOfDownset_hilbert (family : Finset (Finset V))
    (hzero : ∅ ∈ family) (hdown : ∀ F ∈ family, ∀ G ⊆ F, G ∈ family) (i : ℕ) :
    (multicomplexOfDownset family hzero hdown).hilbert i =
      (family.filter (fun F => F.card = i)).card := by
  classical
  symm
  change (family.filter (fun F => F.card = i)).card =
    ((family.image squarefreeMonomial).filter (fun m => monomialDegree m = i)).card
  apply Finset.card_bij (fun F _ => squarefreeMonomial F)
  · intro F hF
    obtain ⟨hF, hc⟩ := Finset.mem_filter.mp hF
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨F, hF, rfl⟩, by rwa [monomialDegree_squarefree]⟩
  · intro F _ G _ he
    exact squarefreeMonomial_injective he
  · intro m hm
    obtain ⟨hm, hc⟩ := Finset.mem_filter.mp hm
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨F, Finset.mem_filter.mpr ⟨hF, by rwa [monomialDegree_squarefree] at hc⟩, rfl⟩

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

theorem preorder_g_multicomplex :
    ∃ C : FiniteMulticomplex (FaceVertex E), ∀ i, C.hilbert i = supportGVector (E := E) i := by
  let C := multicomplexOfDownset (canonicalBallotFamily (E := E))
    empty_mem_canonicalBallotFamily
    (fun _ hF _ hGF => canonicalBallotFamily_downward_closed hF hGF)
  refine ⟨C, fun i => ?_⟩
  rw [multicomplexOfDownset_hilbert, canonicalBallotFamily_degree_counts]

end ResearchMain.PreorderGamma.Macaulay
