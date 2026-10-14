import Fan.FlatWeights

namespace Fan

noncomputable def configurationCast {m n : ℕ} (h : m=n) : Configuration m ≃o Configuration n :=
  h ▸ OrderIso.refl _

@[simp] theorem configurationCast_spokes {m n : ℕ} (h : m=n) (p : Configuration m) (i : Fin n) :
    i∈(configurationCast h p).val.1 ↔ Fin.cast h.symm i∈p.val.1 := by subst n; rfl
@[simp] theorem configurationCast_joins {m n : ℕ} (h : m=n) (p : Configuration m) (i : Fin n) :
    i∈(configurationCast h p).val.2 ↔ Fin.cast h.symm i∈p.val.2 := by subst n; rfl

@[simp] theorem configurationCast_rank {m n : ℕ} (h : m=n) (p : Configuration m) :
    configurationRank (configurationCast h p)=configurationRank p := by subst n; rfl
@[simp] theorem configurationCast_weight {m n : ℕ} (h : m=n) (p : Configuration m) :
    flatWeight (configurationCast h p)=flatWeight p := by subst n; rfl
@[simp] theorem configurationCast_upperMu {m n : ℕ} (h : m=n) (p : Configuration m) :
    upperMu (configurationCast h p)=upperMu p := by subst n; rfl
@[simp] theorem configurationCast_lowerQ {m n : ℕ} (h : m=n) (p : Configuration m) :
    lowerQ (configurationCast h p)=lowerQ p := by subst n; rfl
@[simp] theorem configurationCast_refl {n : ℕ} (p : Configuration n) : configurationCast rfl p=p := rfl
@[simp] theorem configurationCast_cancel {m n : ℕ} (h : m=n) (p : Configuration n) :
    configurationCast h (configurationCast h.symm p)=p := by subst n; rfl

/-- A zero-length prefix is included vacuously. -/
def EndsNonhub {n : ℕ} (p : Configuration n) : Prop :=
  ∀ i : Fin n, i.val+1=n → i∉p.val.1

theorem EndsNonhub.compatible {m n : ℕ} {p : Configuration m} (hp : EndsNonhub p)
    (q : Configuration n) : Compatible p.val q.val := by
  intro i j hi _ ⟨hpi,_⟩
  exact hp i hi hpi

@[simp] theorem endsNonhub_succ {n : ℕ} (p : Configuration (n+1)) :
    EndsNonhub p ↔ Fin.last n∉p.val.1 := by
  constructor
  · exact fun h => h (Fin.last n) rfl
  · intro h i hi
    have he : i=Fin.last n := Fin.ext (by change i.val=n; omega)
    simpa only [he] using h

@[simp] theorem EndsNonhub.configurationCast {m n : ℕ} (h : m=n) (p : Configuration m) :
    EndsNonhub (configurationCast h p) ↔ EndsNonhub p := by subst n; rfl

end Fan
