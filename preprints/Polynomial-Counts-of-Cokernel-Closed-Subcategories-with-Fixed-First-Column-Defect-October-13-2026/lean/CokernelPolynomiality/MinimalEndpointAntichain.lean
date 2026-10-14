import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

noncomputable section
namespace CokernelPolynomiality

structure EndpointReduction (m : ℕ) (S : Finset (Fin m)) (c d : Fin m → ℕ) where
  P : Finset (Fin m)
  subset : P ⊆ S
  pivot : {j // j∈S} → {p // p∈P}
  le_c : ∀j,c (pivot j).val ≤ c j.val
  le_d : ∀j,d (pivot j).val ≤ d j.val
  fixed : ∀j,j.val∈P → (pivot j).val=j.val
  incomparable : ∀p∈P,∀q∈P,c p≤c q → d p≤d q → p=q
  enumeration : Fin P.card ≃ {p // p∈P}
  increasing : Monotone (fun j => c (enumeration j).val)
  decreasing : Antitone (fun j => d (enumeration j).val)

def MinimalEndpoint {m : ℕ} (S : Finset (Fin m)) (c d : Fin m → ℕ) (p : Fin m) : Prop :=
  p∈S ∧ ∀q∈S,c q≤c p → d q≤d p → c p=c q ∧ d p=d q ∧ p.val≤q.val

theorem exists_minimal_endpoint {m : ℕ} (S : Finset (Fin m)) (c d : Fin m → ℕ)
    (j : Fin m) (hj : j∈S) : ∃p,MinimalEndpoint S c d p ∧ c p≤c j ∧ d p≤d j := by
  classical
  let T := S.filter (fun p => c p≤c j ∧ d p≤d j)
  have ht : T.Nonempty := ⟨j,by simp [T,hj]⟩
  obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image T (fun p => (c p+d p)*(m+1)+p.val) ht
  have hps := Finset.mem_filter.mp hp
  refine ⟨p,⟨hps.1,?_⟩,hps.2⟩
  intro q hq hc hd
  have hqt : q∈T := Finset.mem_filter.mpr ⟨hq,hc.trans hps.2.1,hd.trans hps.2.2⟩
  have hh := hmin q hqt
  have hpv := p.isLt
  have hqv := q.isLt
  have hsum : c p+d p=c q+d q := by
    by_contra he
    have hlt : c q+d q+1 ≤ c p+d p := by omega
    have hm := Nat.mul_le_mul_right (m+1) hlt
    nlinarith
  rw [hsum] at hh
  exact ⟨by omega,by omega,by omega⟩

theorem minimal_endpoint_incomparable {m : ℕ} {S : Finset (Fin m)} {c d : Fin m → ℕ}
    {p q : Fin m} (hp : MinimalEndpoint S c d p) (hq : MinimalEndpoint S c d q)
    (hc : c p≤c q) (hd : d p≤d q) : p=q := by
  have h1 := hq.2 p hp.1 hc hd
  have h2 := hp.2 q hq.1 h1.1.le h1.2.1.le
  apply Fin.ext
  omega

theorem endpoint_reduction_exists (m : ℕ) (S : Finset (Fin m)) (c d : Fin m → ℕ) :
    Nonempty (EndpointReduction m S c d) := by
  classical
  let P := S.filter (MinimalEndpoint S c d)
  have hP (p : Fin m) : p∈P ↔ MinimalEndpoint S c d p := by
    simp only [P,Finset.mem_filter]
    exact ⟨And.right,fun h => ⟨h.1,h⟩⟩
  have hchoose (j : {j // j∈S}) : ∃p : {p // p∈P},c p.val≤c j.val ∧ d p.val≤d j.val := by
    obtain ⟨p,hp,hc,hd⟩ := exists_minimal_endpoint S c d j.val j.property
    exact ⟨⟨p,(hP p).mpr hp⟩,hc,hd⟩
  let pivot := fun j => Classical.choose (hchoose j)
  have hc (j : {j // j∈S}) : c (pivot j).val≤c j.val := (Classical.choose_spec (hchoose j)).1
  have hd (j : {j // j∈S}) : d (pivot j).val≤d j.val := (Classical.choose_spec (hchoose j)).2
  have hincomp : ∀p∈P,∀q∈P,c p≤c q → d p≤d q → p=q := by
    intro p hp q hq
    exact minimal_endpoint_incomparable ((hP p).mp hp) ((hP q).mp hq)
  have hinj : Function.Injective (fun p : {p // p∈P} => c p.val) := by
    intro p q he
    apply Subtype.ext
    rcases le_total (d p.val) (d q.val) with hd|hd
    · exact hincomp p.val p.property q.val q.property he.le hd
    · exact (hincomp q.val q.property p.val p.property he.ge hd).symm
  let e := @Fintype.orderIsoFinOfCardEq {p // p∈P}
    (LinearOrder.lift' (fun p => c p.val) hinj) inferInstance P.card (Fintype.card_coe P)
  refine ⟨⟨P,Finset.filter_subset _ _,pivot,hc,hd,?_,hincomp,e.toEquiv,?_,?_⟩⟩
  · intro j hj
    exact hincomp (pivot j).val (pivot j).property j.val hj (hc j) (hd j)
  · change Monotone (fun j => c (e j).val)
    exact fun _ _ h => e.map_rel_iff'.mpr h
  · intro i j hij
    change d (e j).val ≤ d (e i).val
    have hc' : c (e i).val≤c (e j).val := e.map_rel_iff'.mpr hij
    by_contra hn
    have hd' : d (e i).val≤d (e j).val := by omega
    have he := hincomp (e i).val (e i).property (e j).val (e j).property hc' hd'
    rw [he] at hn
    exact hn le_rfl

end CokernelPolynomiality
