import MainTheorems.Tuza.ProfileBounds
import MainTheorems.Tuza.ProfileEnumeration
import Mathlib.Data.List.OfFn

namespace ResearchMain.Tuza

theorem FerrersProfile.eq_of_degree {a b : ℕ} {d e : FerrersProfile a b}
    (h : d.degree = e.degree) : d = e := by
  cases d with
  | mk f hf ha =>
    cases e with
    | mk g hg hb =>
      change f = g at h
      cases h
      rfl

structure CertifiedProfile (a b : ℕ) where
  profile : FerrersProfile a b
  inequality : Inequality profile.graph

def profileTest {a b : ℕ} (certificates : List (CertifiedProfile a b)) (f : Fin a → ℕ) : Bool :=
  certificates.any fun c => decide (List.ofFn f = List.ofFn c.profile.degree)

theorem profileTest_sound {a b : ℕ} (d : FerrersProfile a b)
    (certificates : List (CertifiedProfile a b)) (h : profileTest certificates d.degree = true) :
    Inequality d.graph := by
  simp only [profileTest, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨c, _, hc⟩ := h
  have he := List.ofFn_injective hc
  have hd : d = c.profile := FerrersProfile.eq_of_degree he
  rw [hd]
  exact c.inequality

theorem checked_profiles_sound {a b : ℕ} (d : FerrersProfile a b)
    (certificates : List (CertifiedProfile a b))
    (h : (rowTuples a b).all (fun f => cutTest a b f || profileTest certificates f) = true) :
    Inequality d.graph := by
  have hm := (List.all_eq_true.mp h) d.degree (mem_rowTuples d.degree d.bound d.antitone)
  simp only [Bool.or_eq_true] at hm
  rcases hm with hcut | hcert
  · exact d.cutTest_sound hcut
  · exact profileTest_sound d certificates hcert

end ResearchMain.Tuza
