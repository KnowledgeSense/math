import TerminalLogConcavity.ReleaseTree
import TerminalLogConcavity.BlockEnvelope

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

noncomputable def interfaceEnvelopeWeights (p m : Block) : List ℕ :=
  p.nodeWeights ++ m.nodeWeights ++ m.nodeWeights ++ [1+p.d]
noncomputable def interfaceUpperP (m : Block) : ℕ[X] := 1 + C (m.d^2) * X

/-- Finite linear-product envelopes suffice for both interface states. -/
theorem interface_envelope (p m : Block) :
    CoeffLE (interfaceA p m) (linearProduct (interfaceEnvelopeWeights p m) * interfaceUpperP m) ∧
    CoeffLE (interfaceB p m) (linearProduct (interfaceEnvelopeWeights p m) * (interfaceUpperP m + C p.d)) := by
  let R := linearProduct p.nodeWeights * linearProduct m.nodeWeights ^ 2
  have hE : CoeffLE (interfaceE p m) (R * interfaceUpperP m) := by
    have h := p.node_envelope.1.mul ((m.node_envelope.1.pow 2).add
      ((CoeffLE.refl X).mul (m.node_envelope.2.pow 2)))
    convert h using 1 <;> simp only [interfaceE,R,interfaceUpperP,C_pow] ; ring
  have hO : CoeffLE (interfaceO p m) (R * C p.d) := by
    have h := p.node_envelope.2.mul (m.node_envelope.1.pow 2)
    convert h using 1 <;> simp only [interfaceO,R] ; ring
  have hR : linearProduct (interfaceEnvelopeWeights p m) = R * (1+C (1+p.d)*X) := by
    simp only [interfaceEnvelopeWeights,linearProduct_append,linearProduct,mul_one,R,pow_two]
    ring
  rw [hR]
  constructor
  · have h := hE.add ((CoeffLE.refl X).mul (hE.add hO))
    apply h.trans
    have hg : CoeffLE (interfaceUpperP m + X*(interfaceUpperP m+C p.d))
        (interfaceUpperP m * (1+C (1+p.d)*X)) := by
      have h := CoeffLE.le_add_right (interfaceUpperP m+X*(interfaceUpperP m+C p.d))
        (C (m.d^2*p.d)*X^2)
      convert h using 1
      simp only [interfaceUpperP,C_add,C_mul,map_one]
      ring
    convert (CoeffLE.refl R).mul hg using 1 <;> ring
  · have h := hE.add hO
    apply h.trans
    have h' := CoeffLE.le_mul_one_add (R*(interfaceUpperP m+C p.d)) (C (1+p.d)*X)
    convert h' using 1 <;> ring

noncomputable def upperSiteWeight (q t i k : ℕ) : ℕ[X] × ℕ[X] :=
  let p := Block.scaled t (siteParameter q i k)
  let m := Block.scaled t (interfaceParameter q i)
  (interfaceUpperP m, interfaceUpperP m+C p.d)
noncomputable def upperCouplerWeight (q t : ℕ) : ℕ[X] × ℕ[X] :=
  (1,C (Block.scaled t (2*baseCoupling q)).d)
noncomputable def siteEnvelopeWeights (q t i k : ℕ) : List ℕ :=
  interfaceEnvelopeWeights (Block.scaled t (siteParameter q i k)) (Block.scaled t (interfaceParameter q i))
noncomputable def couplerEnvelopeWeights (q t : ℕ) : List ℕ :=
  (Block.scaled t (2*baseCoupling q)).nodeWeights

end TerminalLogConcavity
