import TerminalLogConcavity.ReleaseEnvelope
import TerminalLogConcavity.ModelComparison

namespace TerminalLogConcavity
set_option backward.isDefEq.respectTransparency false

private theorem sum_flatMap_le {α : Type*} (l : List α) (f : α → List ℕ) (g : α → ℕ) (c : ℕ)
    (h : ∀ x ∈ l, (f x).sum ≤ c*g x) :
    (l.flatMap f).sum ≤ c*(l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons]
    nlinarith

private theorem sum_map_flatten_nat {α : Type*} (f : α → ℕ) (ls : List (List α)) :
    (ls.flatten.map f).sum = (ls.map (fun l => (l.map f).sum)).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [Function.comp_def]

noncomputable def decorationOrder (D : Decoration) : ℕ := Fintype.card D.forest.Vertex+1

theorem interfaceEnvelope_sum_le {p m : Block} {A : ℕ} (hA : 1 ≤ A) (hp : p.d ≤ 2*A) (hm : m.d ≤ 2*A) :
    (interfaceEnvelopeWeights p m).sum ≤ 2*A*(Fintype.card (interfaceForest p m).Vertex+1) := by
  have hwp := p.nodeWeights_sum_le_card_mul
  have hwm := m.nodeWeights_sum_le_card_mul
  have hp' := Nat.mul_le_mul_left (Fintype.card p.Vertex) hp
  have hm' := Nat.mul_le_mul_left (Fintype.card m.Vertex) hm
  have hc := interface_card p m
  simp only [interfaceEnvelopeWeights,List.sum_append,List.sum_cons,List.sum_nil,add_zero]
  nlinarith

theorem occurring_block_d_uniform {q H p : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H)
    (hp : 1 ≤ p) (hpmax : p ≤ massParameter q+q) :
    (Block.scaled (thresholdIndex (target q H)) p).d ≤ 2*selectedAmplifier q H^(massParameter q+q) := by
  have h := occurring_block_d_bound hq hH hp hpmax
  have hn : (Block.scaled (thresholdIndex (target q H)) p).d ≤ 2*selectedAmplifier q H^p := by exact_mod_cast h
  exact hn.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (amplifier_pos _) hpmax))

theorem chainEnvelope_sum_le {q H i : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H) (hi : i ≤ q) :
    (chainEnvelopeWeights q (thresholdIndex (target q H)) i).sum ≤
      2*selectedAmplifier q H^(massParameter q+q)*
        ((chainDecorations q (thresholdIndex (target q H)) i).map decorationOrder).sum := by
  let t := thresholdIndex (target q H)
  let A := selectedAmplifier q H^(massParameter q+q)
  have hA : 1 ≤ A := Nat.one_le_pow _ _ (amplifier_pos _)
  rw [← chain_nodes_decorations,List.map_map]
  apply sum_flatMap_le
  intro v _
  cases v with
  | site k =>
    have hp : 1 ≤ siteParameter q i k := by have := siteParameter_pos (i := i) (k := k) (show 1 ≤ q by omega); omega
    have hm : 1 ≤ interfaceParameter q i := by
      unfold interfaceParameter massParameter
      have : 0 < q^2 := by positivity
      omega
    exact interfaceEnvelope_sum_le hA
      (occurring_block_d_uniform hq hH hp ((siteParameter_le hi).trans (by omega)))
      (occurring_block_d_uniform hq hH hm (interfaceParameter_le hi))
  | coupler =>
    have hp : 1 ≤ 2*baseCoupling q := by
      unfold baseCoupling
      have : 0 < q^2 := by positivity
      omega
    have hd := occurring_block_d_uniform hq hH hp (show 2*baseCoupling q ≤ massParameter q+q by unfold baseCoupling massParameter; omega)
    have hw := (Block.scaled t (2*baseCoupling q)).nodeWeights_sum_le_card_mul
    have hm := Nat.mul_le_mul_left (Fintype.card (Block.scaled t (2*baseCoupling q)).Vertex) hd
    change (Block.scaled t (2*baseCoupling q)).nodeWeights.sum ≤ 2*A*(Fintype.card (Block.scaled t (2*baseCoupling q)).Vertex+1)
    dsimp [t,A] at *
    nlinarith

theorem releaseOrder_sum_chains (q t : ℕ) :
    Fintype.card (releaseForest q t).Vertex =
      ((List.range q).map (fun i => ((chainDecorations q t (i+1)).map decorationOrder).sum)).sum + 2*(q-1) := by
  rw [releaseForest,decoratedPath_card]
  change ((releaseDecorations q t).map decorationOrder).sum = _
  rw [releaseDecorations,sum_map_flatten_nat,sum_map_intersperse_nat]
  simp only [List.map_map,Function.comp_def,List.length_map,List.length_range,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  have he : decorationOrder Block.leaf.decoration = 2 := by
    change Fintype.card Block.leaf.Vertex+1=2
    rw [Block.card_leaf]
  rw [he]
  omega

theorem releaseEnvelope_le_order {q H : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H) :
    (releaseEnvelopeWeights q (thresholdIndex (target q H))).sum ≤
      2*selectedAmplifier q H^(massParameter q+q)*Fintype.card (releaseTree (q-1) H).Vertex := by
  have hq' : q-1+1=q := by omega
  simp only [releaseTree,hq']
  rw [releaseEnvelopeWeights,List.sum_append,List.sum_replicate,smul_eq_mul,mul_one,releaseOrder_sum_chains]
  have h := sum_flatMap_le (List.range q) (fun i => chainEnvelopeWeights q (thresholdIndex (target q H)) (i+1))
    (fun i => ((chainDecorations q (thresholdIndex (target q H)) (i+1)).map decorationOrder).sum)
    (2*selectedAmplifier q H^(massParameter q+q))
    (fun i hi => chainEnvelope_sum_le hq hH (by have := List.mem_range.mp hi; omega))
  have hA : 1 ≤ selectedAmplifier q H^(massParameter q+q) := Nat.one_le_pow _ _ (amplifier_pos _)
  nlinarith

theorem two_pow_le_amplifier (t : ℕ) : 2^t ≤ amplifier t := by
  induction t with
  | zero => decide
  | succ t ih => rw [pow_succ,amplifier_succ]; nlinarith [amplifier_pos t]

theorem releaseEnvelope_sum_bound {q H : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H) :
    (releaseEnvelopeWeights q (thresholdIndex (target q H))).sum ≤
      132*q^4*selectedAmplifier q H^(massParameter q+q+1) := by
  let t := thresholdIndex (target q H)
  have hN := releaseForest_count_identity hq t
  have hS := blockParameterSum_lt hq
  have hN' : Fintype.card (releaseForest q t).Vertex ≤ 64*2^t*q^4 := by
    have hm := Nat.mul_le_mul_left (4*2^t) (Nat.le_of_lt hS)
    have hqsmall : 4*q ≤ 7*q^2+2 := by nlinarith
    nlinarith
  have h := releaseEnvelope_le_order hq hH
  have hq' : q-1+1=q := by omega
  simp only [releaseTree,hq'] at h
  have hm := Nat.mul_le_mul_left (2*selectedAmplifier q H^(massParameter q+q)) hN'
  have hell := two_pow_le_amplifier t
  have hm' := Nat.mul_le_mul_left (128*q^4*selectedAmplifier q H^(massParameter q+q)) hell
  rw [pow_succ (selectedAmplifier q H) (massParameter q+q)]
  change 2^t ≤ selectedAmplifier q H at hell
  have hnonneg := Nat.zero_le (q^4*selectedAmplifier q H^(massParameter q+q)*selectedAmplifier q H)
  dsimp [t,selectedAmplifier] at *
  nlinarith only [h,hm,hm',hnonneg]

end TerminalLogConcavity
