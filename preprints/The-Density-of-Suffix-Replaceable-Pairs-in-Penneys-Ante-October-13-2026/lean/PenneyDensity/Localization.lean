import PenneyDensity.ForbiddenSuffixes

namespace PenneyDensity

def SmallOverlapAgreement (a : Bool → Word) (K : ℕ) : Prop :=
  ∀ b k, 0<k → k≤K →
    (properOverlap (a b) (a false) k ↔ properOverlap (a b) (a true) k)

def LongOverlap (a : Bool → Word) (K : ℕ) : Prop :=
  ∃ b c k, K<k ∧ properOverlap (a b) (a c) k

def BlockCollision (a : Bool → Word) (n K : ℕ) : Prop :=
  ∃ b c i j, i≤K ∧ j≤K ∧ (b≠c ∨ i≠j) ∧
    ((a b).drop i).take (n-2*K)=((a c).drop j).take (n-2*K)

def generator (a : Bool → Word) (n : ℕ) (b : Bool) (k : ℕ) : Word :=
  (a b).take (n-k)

 theorem generator_suffix_unique {a : Bool → Word} {n K : ℕ}
    (hlen : ∀ b,(a b).length=n) (hn : 2*K<n) (hB : ¬BlockCollision a n K)
    {b c : Bool} {k l : ℕ} (hk : k≤K) (hl : l≤K)
    (hs : (generator a n b k).IsSuffix (generator a n c l)) : b=c ∧ k=l := by
  have hkN : k≤n := by omega
  have hlN : l≤n := by omega
  have hlength := hs.length_le
  simp only [generator,List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)] at hlength
  have hlk : l≤k := by omega
  have he := List.suffix_iff_eq_drop.mp hs
  simp only [generator,List.length_take,hlen,Nat.min_eq_left (Nat.sub_le _ _)] at he
  have hdiff : n-l-(n-k)=k-l := by omega
  rw [hdiff,List.drop_take] at he
  have he' := congrArg (List.take (n-2*K)) he
  have hlow : n-2*K≤n-k := by omega
  have hlow' : n-2*K≤n-l-(k-l) := by omega
  simp only [List.take_take,Nat.min_eq_left hlow,Nat.min_eq_left hlow'] at he'
  have hsame : b=c ∧ 0=k-l := by
    by_contra hh
    apply hB
    refine ⟨b,c,0,k-l,by omega,by omega,?_,?_⟩
    · tauto
    · simpa only [List.drop_zero] using he'
  exact ⟨hsame.1,by omega⟩

 theorem words_distinct_of_no_collision {a : Bool → Word} {n K : ℕ}
    (hB : ¬BlockCollision a n K) : a false≠a true := by
  intro he
  apply hB
  exact ⟨false,true,0,0,by omega,by omega,Or.inl Bool.false_ne_true,by rw [he]⟩

 theorem forbidden_iff_generator {a : Bool → Word} {n : ℕ}
    (hlen : ∀ b,(a b).length=n) (t : Bool) (x : Word) :
    x∈forbidden (a false) (a true) (a t) ↔
      ∃ b k, properOverlap (a b) (a t) k ∧ x=generator a n b k := by
  constructor
  · rintro ⟨v,hv,k,hk,hx⟩
    rcases hv with rfl | rfl
    · exact ⟨false,k,hk,by simpa only [generator,hlen] using hx⟩
    · exact ⟨true,k,hk,by simpa only [generator,hlen] using hx⟩
  · rintro ⟨b,k,hk,hx⟩
    refine ⟨a b,?_,k,hk,?_⟩
    · cases b <;> simp
    · simpa only [generator,hlen] using hx

/-- The deterministic localization of the complete original property R;
no contexts or exceptional target pairs are silently omitted. -/
theorem propertyR_localization {a : Bool → Word} {n K : ℕ}
    (hlen : ∀ b,(a b).length=n) (hn : 2*K<n)
    (hA : ¬LongOverlap a K) (hB : ¬BlockCollision a n K) :
    PropertyR (a false) (a true) ↔ SmallOverlapAgreement a K := by
  have hne := words_distinct_of_no_collision hB
  have ha0 : a false≠[] := by
    intro he
    have hh := hlen false
    rw [he,List.length_nil] at hh
    omega
  have hlen' : (a false).length=(a true).length := by rw [hlen,hlen]
  have hsmall {b t k} (hk : properOverlap (a b) (a t) k) : k≤K := by
    by_contra hh
    exact hA ⟨b,t,k,by omega,hk⟩
  rw [propertyR_iff_suffix_cover hlen' hne ha0]
  constructor
  · rintro ⟨hft,htf⟩ b k hk0 hkK
    constructor
    · intro hk
      have hg : generator a n b k∈forbidden (a false) (a true) (a false) :=
        (forbidden_iff_generator hlen false _).mpr ⟨b,k,hk,rfl⟩
      obtain ⟨x,hx,hs⟩ := hft _ hg
      obtain ⟨c,l,hl,rfl⟩ := (forbidden_iff_generator hlen true x).mp hx
      obtain ⟨hcb,hlk⟩ := generator_suffix_unique hlen hn hB (hsmall hl) hkK hs
      subst c; subst l
      exact hl
    · intro hk
      have hg : generator a n b k∈forbidden (a false) (a true) (a true) :=
        (forbidden_iff_generator hlen true _).mpr ⟨b,k,hk,rfl⟩
      obtain ⟨x,hx,hs⟩ := htf _ hg
      obtain ⟨c,l,hl,rfl⟩ := (forbidden_iff_generator hlen false x).mp hx
      obtain ⟨hcb,hlk⟩ := generator_suffix_unique hlen hn hB (hsmall hl) hkK hs
      subst c; subst l
      exact hl
  · intro hE
    constructor
    · intro x hx
      obtain ⟨b,k,hk,rfl⟩ := (forbidden_iff_generator hlen false x).mp hx
      refine ⟨generator a n b k,?_,List.suffix_refl _⟩
      exact (forbidden_iff_generator hlen true _).mpr
        ⟨b,k,(hE b k hk.1 (hsmall hk)).mp hk,rfl⟩
    · intro x hx
      obtain ⟨b,k,hk,rfl⟩ := (forbidden_iff_generator hlen true x).mp hx
      refine ⟨generator a n b k,?_,List.suffix_refl _⟩
      exact (forbidden_iff_generator hlen false _).mpr
        ⟨b,k,(hE b k hk.1 (hsmall hk)).mpr hk,rfl⟩

end PenneyDensity
