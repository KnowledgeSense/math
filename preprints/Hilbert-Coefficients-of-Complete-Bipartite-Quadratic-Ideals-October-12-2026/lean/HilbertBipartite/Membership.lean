import HilbertBipartite.QuotientDimension

noncomputable section
namespace HilbertBipartite

lemma blockDegree_eq_degree {p : ℕ} (a : BlockExponent p) : blockDegree a = a.degree :=
  (Finsupp.degree_eq_sum a).symm

@[simp] lemma blockDegree_add {p : ℕ} (a b : BlockExponent p) :
    blockDegree (a+b) = blockDegree a + blockDegree b := by
  simp [blockDegree, Finset.sum_add_distrib]

@[simp] lemma blockDegree_zero (p : ℕ) : blockDegree (0 : BlockExponent p) = 0 := by
  simp [blockDegree]

@[simp] lemma blockDegree_single {p : ℕ} (i : Fin p) (n : ℕ) :
    blockDegree (Finsupp.single i n) = n := by
  rw [blockDegree_eq_degree, Finsupp.degree_single]

lemma sumElim_add {p q : ℕ} (a c : BlockExponent p) (b d : BlockExponent q) :
    Finsupp.sumElim (a+c) (b+d) = Finsupp.sumElim a b + Finsupp.sumElim c d := by
  ext i
  cases i <;> rfl

lemma generatorPowerExponents_add {σ : Type*} (G : Set (σ →₀ ℕ))
    {s t : ℕ} {a b : σ →₀ ℕ}
    (ha : a ∈ generatorPowerExponents G s) (hb : b ∈ generatorPowerExponents G t) :
    a+b ∈ generatorPowerExponents G (s+t) := by
  induction s generalizing a with
  | zero =>
    have : a=0 := ha
    simpa [this] using hb
  | succ s ih =>
    obtain ⟨c,hc,d,hd,rfl⟩ := ha
    rw [Nat.succ_add]
    exact ⟨c,hc,d+b,ih hd,add_assoc _ _ _⟩

lemma exists_single_split {p : ℕ} (a : BlockExponent p) (h : 0 < blockDegree a) :
    ∃ i : Fin p, ∃ a' : BlockExponent p, a = Finsupp.single i 1 + a' := by
  have hex : ∃ i, a i ≠ 0 := by
    by_contra hh
    push Not at hh
    have : a=0 := by ext i; exact hh i
    simp [this] at h
  obtain ⟨i,hi⟩ := hex
  obtain ⟨a',ha'⟩ := le_iff_exists_add.mp
    (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi))
  exact ⟨i,a',ha'⟩

/-- Equal-degree monomials in the two blocks are products of cross edges. -/
lemma cross_mem_generatorPowerExponents {p q t : ℕ}
    (a : BlockExponent p) (b : BlockExponent q)
    (ha : blockDegree a = t) (hb : blockDegree b = t) :
    Finsupp.sumElim a b ∈ generatorPowerExponents (bipartiteGeneratorExponents p q) t := by
  induction t generalizing a b with
  | zero =>
    have haz : a=0 := (Finsupp.degree_eq_zero_iff a).mp ((blockDegree_eq_degree a).symm.trans ha)
    have hbz : b=0 := (Finsupp.degree_eq_zero_iff b).mp ((blockDegree_eq_degree b).symm.trans hb)
    simp [haz,hbz,generatorPowerExponents]
  | succ t ih =>
    obtain ⟨i,a',rfl⟩ := exists_single_split a (by omega)
    obtain ⟨j,b',rfl⟩ := exists_single_split b (by omega)
    have ha' : blockDegree a' = t := by simp only [blockDegree_add,blockDegree_single] at ha; omega
    have hb' : blockDegree b' = t := by simp only [blockDegree_add,blockDegree_single] at hb; omega
    rw [sumElim_add]
    exact ⟨_, Or.inr ⟨i,j,by simp⟩, _, ih a' b' ha' hb', rfl⟩

/-- A monomial of degree `t` yields a product of `t` vertex squares. -/
lemma leftSquares_mem_generatorPowerExponents {p q t : ℕ}
    (a : BlockExponent p) (ha : blockDegree a = t) :
    Finsupp.sumElim (a+a) (0 : BlockExponent q) ∈
      generatorPowerExponents (bipartiteGeneratorExponents p q) t := by
  induction t generalizing a with
  | zero =>
    have haz : a=0 := (Finsupp.degree_eq_zero_iff a).mp ((blockDegree_eq_degree a).symm.trans ha)
    simp [haz,generatorPowerExponents]
  | succ t ih =>
    obtain ⟨i,a',rfl⟩ := exists_single_split a (by omega)
    have ha' : blockDegree a'=t := by simp only [blockDegree_add,blockDegree_single] at ha; omega
    have he : Finsupp.sumElim
        ((Finsupp.single i 1+a')+(Finsupp.single i 1+a')) (0 : BlockExponent q) =
        Finsupp.single (Sum.inl i) 2 + Finsupp.sumElim (a'+a') 0 := by
      rw [show (Finsupp.single i 1+a')+(Finsupp.single i 1+a') =
        Finsupp.single i 2+(a'+a') by rw [show Finsupp.single i 2 = Finsupp.single i 1 + Finsupp.single i 1 from (Finsupp.single_add i 1 1)]; ac_rfl]
      simpa using sumElim_add (Finsupp.single i 2) (a'+a') (0 : BlockExponent q) 0
    rw [he]
    exact ⟨_,Or.inl ⟨Sum.inl i,rfl⟩,_,ih a' ha',rfl⟩

/-- A monomial of degree `t` yields a product of `t` vertex squares. -/
lemma rightSquares_mem_generatorPowerExponents {p q t : ℕ}
    (a : BlockExponent q) (ha : blockDegree a = t) :
    Finsupp.sumElim (0 : BlockExponent p) (a+a) ∈
      generatorPowerExponents (bipartiteGeneratorExponents p q) t := by
  induction t generalizing a with
  | zero =>
    have haz : a=0 := (Finsupp.degree_eq_zero_iff a).mp ((blockDegree_eq_degree a).symm.trans ha)
    simp [haz,generatorPowerExponents]
  | succ t ih =>
    obtain ⟨i,a',rfl⟩ := exists_single_split a (by omega)
    have ha' : blockDegree a'=t := by simp only [blockDegree_add,blockDegree_single] at ha; omega
    have he : Finsupp.sumElim (0 : BlockExponent p)
        ((Finsupp.single i 1+a')+(Finsupp.single i 1+a')) =
        Finsupp.single (Sum.inr i) 2 + Finsupp.sumElim 0 (a'+a') := by
      rw [show (Finsupp.single i 1+a')+(Finsupp.single i 1+a') =
        Finsupp.single i 2+(a'+a') by rw [show Finsupp.single i 2 = Finsupp.single i 1 + Finsupp.single i 1 from (Finsupp.single_add i 1 1)]; ac_rfl]
      simpa using sumElim_add (0 : BlockExponent p) 0 (Finsupp.single i 2) (a'+a')
    rw [he]
    exact ⟨_,Or.inl ⟨Sum.inr i,rfl⟩,_,ih a' ha',rfl⟩

lemma exists_block_square_cross {p j t : ℕ} (a : BlockExponent p)
    (hj : j ≤ halfDegree a) (ht : 2*j+t ≤ blockDegree a) :
    ∃ c d : BlockExponent p, blockDegree c=j ∧ blockDegree d=t ∧ c+c+d ≤ a := by
  let half : BlockExponent p := a.mapRange (fun n => n/2) (by decide)
  have hhalf : half.degree = halfDegree a := by
    simp [Finsupp.degree_eq_sum, half, halfDegree]
  obtain ⟨c,hc,hcd⟩ := Finsupp.exists_le_degree_eq half j (hhalf.symm ▸ hj)
  have hcc : c+c ≤ a := by
    intro i
    have hci := hc i
    simp only [half,Finsupp.mapRange_apply] at hci
    change c i+c i ≤ a i
    omega
  obtain ⟨rest, hrest⟩ := le_iff_exists_add.mp hcc
  have hcdeg : blockDegree c=j := (blockDegree_eq_degree c).trans hcd
  have hrestdeg : t ≤ rest.degree := by
    rw [hrest,blockDegree_add,blockDegree_add,hcdeg] at ht
    rw [← blockDegree_eq_degree]
    omega
  obtain ⟨d,hd,hdd⟩ := Finsupp.exists_le_degree_eq rest t hrestdeg
  exact ⟨c,d,hcdeg,(blockDegree_eq_degree d).trans hdd, by
    rw [hrest]
    exact add_le_add_right hd _⟩

lemma sumElim_mono {p q : ℕ} {a c : BlockExponent p} {b d : BlockExponent q}
    (hac : a ≤ c) (hbd : b ≤ d) : Finsupp.sumElim a b ≤ Finsupp.sumElim c d := by
  intro i
  cases i with
  | inl i => exact hac i
  | inr i => exact hbd i

lemma powerCriterion_implies_membership_left {p q s : ℕ}
    (a : BlockExponent p) (b : BlockExponent q)
    (h : PowerCriterion s a b) (ha : s ≤ blockDegree a) :
    Finsupp.sumElim a b ∈ bipartitePowerExponents p q s := by
  let j := s-blockDegree b
  let t := s-j
  have hj : j ≤ halfDegree a := by dsimp [j]; obtain ⟨_,h,_⟩ := h; omega
  have ht : 2*j+t ≤ blockDegree a := by
    dsimp [j,t]
    obtain ⟨h,_,_⟩ := h
    omega
  have htb : t ≤ b.degree := by
    rw [← blockDegree_eq_degree]
    dsimp [t,j]
    omega
  obtain ⟨c,d,hc,hd,hcd⟩ := exists_block_square_cross a hj ht
  obtain ⟨e,he,hed⟩ := Finsupp.exists_le_degree_eq b t htb
  have hsum := generatorPowerExponents_add _
    (leftSquares_mem_generatorPowerExponents (q := q) c hc)
    (cross_mem_generatorPowerExponents d e hd ((blockDegree_eq_degree e).trans hed))
  have hst : j+t=s := by dsimp [t,j]; omega
  rw [hst] at hsum
  refine ⟨_,hsum,?_⟩
  rw [← sumElim_add]
  simpa using sumElim_mono hcd he

lemma powerCriterion_implies_membership_right {p q s : ℕ}
    (a : BlockExponent p) (b : BlockExponent q)
    (h : PowerCriterion s a b) (hb : s ≤ blockDegree b) :
    Finsupp.sumElim a b ∈ bipartitePowerExponents p q s := by
  let j := s-blockDegree a
  let t := s-j
  have hj : j ≤ halfDegree b := by dsimp [j]; obtain ⟨_,_,h⟩ := h; omega
  have ht : 2*j+t ≤ blockDegree b := by
    dsimp [j,t]
    obtain ⟨h,_,_⟩ := h
    omega
  have hta : t ≤ a.degree := by
    rw [← blockDegree_eq_degree]
    dsimp [t,j]
    omega
  obtain ⟨c,d,hc,hd,hcd⟩ := exists_block_square_cross b hj ht
  obtain ⟨e,he,hed⟩ := Finsupp.exists_le_degree_eq a t hta
  have hsum := generatorPowerExponents_add _
    (rightSquares_mem_generatorPowerExponents (p := p) c hc)
    (cross_mem_generatorPowerExponents e d ((blockDegree_eq_degree e).trans hed) hd)
  have hst : j+t=s := by dsimp [t,j]; omega
  rw [hst] at hsum
  refine ⟨_,hsum,?_⟩
  rw [← sumElim_add]
  simpa using sumElim_mono he hcd

/-- The three numerical inequalities suffice to construct a dividing product
of exactly `s` of the original quadratic generators. -/
theorem powerCriterion_implies_membership {p q s : ℕ}
    (a : BlockExponent p) (b : BlockExponent q) (h : PowerCriterion s a b) :
    Finsupp.sumElim a b ∈ bipartitePowerExponents p q s := by
  by_cases ha : s ≤ blockDegree a
  · exact powerCriterion_implies_membership_left a b h ha
  · exact powerCriterion_implies_membership_right a b h (by obtain ⟨h,_,_⟩ := h; omega)

lemma blockDegree_mono {p : ℕ} {a b : BlockExponent p} (h : a ≤ b) :
    blockDegree a ≤ blockDegree b := Finset.sum_le_sum (fun i _ => h i)

lemma halfDegree_mono {p : ℕ} {a b : BlockExponent p} (h : a ≤ b) :
    halfDegree a ≤ halfDegree b :=
  Finset.sum_le_sum (fun i _ => Nat.div_le_div_right (h i))

lemma halfDegree_add_le {p : ℕ} (a b : BlockExponent p) :
    halfDegree a + halfDegree b ≤ halfDegree (a+b) := by
  unfold halfDegree
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change a i/2+b i/2 ≤ (a i+b i)/2
  omega

lemma powerCriterion_mono {p q s : ℕ} {a c : BlockExponent p} {b d : BlockExponent q}
    (hac : a ≤ c) (hbd : b ≤ d) (h : PowerCriterion s a b) : PowerCriterion s c d := by
  have h1 := blockDegree_mono hac
  have h2 := blockDegree_mono hbd
  have h3 := halfDegree_mono hac
  have h4 := halfDegree_mono hbd
  unfold PowerCriterion at *
  omega

lemma powerCriterion_add {p q s t : ℕ} {a c : BlockExponent p} {b d : BlockExponent q}
    (h : PowerCriterion s a b) (h' : PowerCriterion t c d) :
    PowerCriterion (s+t) (a+c) (b+d) := by
  have h1 := halfDegree_add_le a c
  have h2 := halfDegree_add_le b d
  unfold PowerCriterion at *
  simp only [blockDegree_add]
  omega

def leftExponent {p q : ℕ} (a : (Fin p ⊕ Fin q) →₀ ℕ) : BlockExponent p :=
  (Finsupp.sumFinsuppEquivProdFinsupp a).1

def rightExponent {p q : ℕ} (a : (Fin p ⊕ Fin q) →₀ ℕ) : BlockExponent q :=
  (Finsupp.sumFinsuppEquivProdFinsupp a).2

@[simp] lemma leftExponent_apply {p q : ℕ} (a : (Fin p ⊕ Fin q) →₀ ℕ) (i : Fin p) :
    leftExponent a i = a (Sum.inl i) := rfl
@[simp] lemma rightExponent_apply {p q : ℕ} (a : (Fin p ⊕ Fin q) →₀ ℕ) (i : Fin q) :
    rightExponent a i = a (Sum.inr i) := rfl

@[simp] lemma leftExponent_sumElim {p q : ℕ} (a : BlockExponent p) (b : BlockExponent q) :
    leftExponent (Finsupp.sumElim a b) = a := by ext i; rfl
@[simp] lemma rightExponent_sumElim {p q : ℕ} (a : BlockExponent p) (b : BlockExponent q) :
    rightExponent (Finsupp.sumElim a b) = b := by ext i; rfl

@[simp] lemma leftExponent_add {p q : ℕ} (a b : (Fin p ⊕ Fin q) →₀ ℕ) :
    leftExponent (a+b) = leftExponent a+leftExponent b := by ext i; rfl
@[simp] lemma rightExponent_add {p q : ℕ} (a b : (Fin p ⊕ Fin q) →₀ ℕ) :
    rightExponent (a+b) = rightExponent a+rightExponent b := by ext i; rfl

@[simp] lemma leftExponent_zero (p q : ℕ) :
    leftExponent (0 : (Fin p ⊕ Fin q) →₀ ℕ)=0 := by ext i; rfl
@[simp] lemma rightExponent_zero (p q : ℕ) :
    rightExponent (0 : (Fin p ⊕ Fin q) →₀ ℕ)=0 := by ext i; rfl

@[simp] lemma leftExponent_single_inl {p q : ℕ} (i : Fin p) (n : ℕ) :
    leftExponent (Finsupp.single (Sum.inl i : Fin p ⊕ Fin q) n)=Finsupp.single i n := by
  classical
  ext j
  simp [Finsupp.single_apply]
@[simp] lemma rightExponent_single_inl {p q : ℕ} (i : Fin p) (n : ℕ) :
    rightExponent (Finsupp.single (Sum.inl i : Fin p ⊕ Fin q) n)=0 := by
  classical
  ext j
  simp
@[simp] lemma leftExponent_single_inr {p q : ℕ} (i : Fin q) (n : ℕ) :
    leftExponent (Finsupp.single (Sum.inr i : Fin p ⊕ Fin q) n)=0 := by
  classical
  ext j
  simp
@[simp] lemma rightExponent_single_inr {p q : ℕ} (i : Fin q) (n : ℕ) :
    rightExponent (Finsupp.single (Sum.inr i : Fin p ⊕ Fin q) n)=Finsupp.single i n := by
  classical
  ext j
  simp [Finsupp.single_apply]

@[simp] lemma halfDegree_zero (p : ℕ) : halfDegree (0 : BlockExponent p)=0 := by
  simp [halfDegree]
@[simp] lemma halfDegree_single {p : ℕ} (i : Fin p) (n : ℕ) :
    halfDegree (Finsupp.single i n)=n/2 := by
  classical
  simp only [halfDegree,Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

lemma generator_satisfies_criterion {p q : ℕ} {a : (Fin p ⊕ Fin q) →₀ ℕ}
    (ha : a ∈ bipartiteGeneratorExponents p q) :
    PowerCriterion 1 (leftExponent a) (rightExponent a) := by
  obtain (⟨i,rfl⟩ | ⟨i,j,rfl⟩) := ha
  · cases i <;> simp [PowerCriterion]
  · simp [PowerCriterion]

lemma generatorPower_satisfies_criterion {p q s : ℕ} {a : (Fin p ⊕ Fin q) →₀ ℕ}
    (ha : a ∈ generatorPowerExponents (bipartiteGeneratorExponents p q) s) :
    PowerCriterion s (leftExponent a) (rightExponent a) := by
  induction s generalizing a with
  | zero => simp [PowerCriterion]
  | succ s ih =>
    obtain ⟨b,hb,c,hc,rfl⟩ := ha
    simpa [Nat.add_comm] using powerCriterion_add (generator_satisfies_criterion hb) (ih hc)

/-- Every dividing product of quadratic generators satisfies the three bounds. -/
theorem membership_implies_powerCriterion {p q s : ℕ}
    (a : BlockExponent p) (b : BlockExponent q)
    (h : Finsupp.sumElim a b ∈ bipartitePowerExponents p q s) : PowerCriterion s a b := by
  obtain ⟨c,hc,hca⟩ := h
  exact powerCriterion_mono (fun i => hca (Sum.inl i)) (fun j => hca (Sum.inr j))
    (generatorPower_satisfies_criterion hc)

/-- Exact numerical membership criterion for powers of the original ideal. -/
theorem mem_bipartitePowerExponents_iff {p q s : ℕ}
    (a : BlockExponent p) (b : BlockExponent q) :
    Finsupp.sumElim a b ∈ bipartitePowerExponents p q s ↔ PowerCriterion s a b :=
  ⟨membership_implies_powerCriterion a b, powerCriterion_implies_membership a b⟩

/-- The actual quotient dimension is the standard-exponent count. -/
theorem finrank_bipartiteIdeal_pow (K : Type*) [Field K] (p q s : ℕ) :
    Module.finrank K (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s) =
      (standardExponents p q s).card :=
  finrank_bipartite_quotient_eq_standard_card K p q s mem_bipartitePowerExponents_iff

/-- Membership of a monic monomial in an actual ideal power. -/
theorem monomial_mem_bipartiteIdeal_pow_iff (K : Type*) [Field K]
    {p q s : ℕ} (a : BlockExponent p) (b : BlockExponent q) :
    MvPolynomial.monomial (Finsupp.sumElim a b) (1 : K) ∈ bipartiteIdeal K p q ^ s ↔
      PowerCriterion s a b := by
  classical
  rw [mem_bipartiteIdeal_pow_iff_support]
  simpa [MvPolynomial.support_monomial] using mem_bipartitePowerExponents_iff a b

/-- Standard monomials, indexed by the finite set used in the counting formula. -/
noncomputable def finiteStandardMonomialBasis (K : Type*) [Field K] (p q s : ℕ) :
    Module.Basis ↥(standardExponents p q s) K
      (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s) :=
  (bipartitePowerQuotientBasis p q s).reindex
    (standardPowerExponentEquiv p q s mem_bipartitePowerExponents_iff)

instance finite_bipartiteIdeal_pow_quotient (K : Type*) [Field K] (p q s : ℕ) :
    Module.Finite K (MvPolynomial (Fin p ⊕ Fin q) K ⧸ bipartiteIdeal K p q ^ s) :=
  Module.Finite.of_basis (finiteStandardMonomialBasis K p q s)

end HilbertBipartite
