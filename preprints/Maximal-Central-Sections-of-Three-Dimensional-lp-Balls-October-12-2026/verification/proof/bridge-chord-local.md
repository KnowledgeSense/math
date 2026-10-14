# High-p local chord argument

## 1. Statement and inherited chord formula

For p≥16, 1−1/(4p)≤u≤1 and 0≤v≤1/(2p),

    A(p,u,v) ≤ A(p,u,0) − (2/3)v² ≤ T(p) − (2/3)v².       (L1)

The first inequality is strict when v>0 with the displayed coefficient; equality A=T is possible only at (u,v)=(1,0).

Use the same parallel-chord coordinates and identities as TAIL_COMPONENT_PROOF_v2 §§1,5,6. Write δ=1−u, R(z)=(1−|z|^p)^(1/p), S0=1+u², A0=A(p,u,0). The exact graph formula is A=√(S0+v²)∫W(u,−vz;R(z)) dz, over z∈[−1,1]. Chord length W is even and concave on its support, and W(H)≤W(0) also outside its support. At the positive endpoint a(H)>0 with b=ua−H>0,

    a^p+b^p=R^p,
    −a''=(p−1)a^(p−2)b^(p−2)R^p/[a^(p−1)+u b^(p−1)]³.

These identities were proved and independently verified for the tail component; their hypotheses here are checked below.

## 2. Uniform endpoint balance on |z|≤19/20

Let r=19/20. Exact integer arithmetic gives r^16<1/2 and (21/20)^16>2. Thus for p≥16 and |z|≤r,

    R(z)>r,  2^(1/p)<21/20,  u≥63/64>49/50.

For every H with |H|≤v|z|, |H|/R<1/(2p)≤1/32<u. Continuation from H=0 therefore prevents either a or b reaching zero: a=0 would force |H|=R, while b=0 would force H=uR.

Since max(a,b)≥2^(−1/p)R and |a−b|≤δR+|H|,

    min(a,b)/max(a,b)
       ≥1−(21/20)(1/4+1/2)/p >1−(4/5)/p.

Monotonicity of (1−K/p)^p for p>K gives the p-independent rational lower bound

    [min(a,b)/max(a,b)]^p ≥ρ:=(19/20)^16.

Set κ=(20/21)^3 ρ/(1+ρ)². The same Hölder estimate as tail(T12)–(T15) now gives −a''≥(p−1)κ/R and

    W(H)≤W(0)−(p−1)κ H²/R

on the full displacement segment. All real p≥16 are covered, not only integer p.

## 3. Integration and strictness

Using R≤1 on [−r,r] and the central-chord bound elsewhere, define I=(2/3)r³κ. Then

    A ≤ A0 + [A0/(2S0)−√(S0+v²)(p−1)I]v².

Here concavity of the square root supplies the positive Jacobian term. Since A0<6, S0>49/25 and √(S0+v²)>7/5, the coefficient is strictly below 75/49−(7/5)15I. The standard-library exact checker code/check_bridge_chord_local.py verifies

    (7/5)15I−75/49
       =789362966856300451229686510456277614191533975
        /1178476946217713373853838226356831958728197803
       >2/3.

This proves (L1). Finally A0=V_p√(1+u²)/(1+u^p)^(1/p) is strictly increasing in 0<u<1 for p>2, since its logarithmic derivative is u/(1+u²)−u^(p−1)/(1+u^p)>0. Thus v=0,u<1 also gives A<T; at u=1,v=0 equality holds by definition.

The exact arithmetic output is logs/bridge_chord_local_exact.json. Dependencies are the independently checked tail v2 (SHA ed3b1eddb3fae72a6907d1ec2f940d7a5f6550bb7e535dc0abd3de81cb6edb0d) and elementary inequalities. No numerical quadrature, sampling, old derivative constants or unverified external theorem is used in this local component.
