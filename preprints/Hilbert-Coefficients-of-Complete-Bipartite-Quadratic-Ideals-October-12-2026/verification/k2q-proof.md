# Consecutive negative Hilbert coefficients in the two-variable part family

Author: Knowledge Sense

## Theorem
Let k be any field and let q >= 2. Put n = q + 2,

    S = k[a,b,y_1,...,y_q],
    I_q = (a^2,b^2,y_1^2,...,y_q^2, a y_1,...,a y_q,b y_1,...,b y_q).

This is an Artinian quadratic monomial ideal, defined over every field. Define its Hilbert coefficients by the eventual polynomial

    length(S/I_q^s) = sum_{i=0}^n (-1)^i e_i(I_q) binom(s+n-i-1,n-i).

Then e_0 = 2^n, e_1 = (n-1) 2^(n-2), e_2 = binom(n-2,2) 2^(n-4), e_n = 0, and every e_i with 3 <= i <= n-1 is strictly negative. More exactly, setting r = n-i-1:

- If r >= 1, then

    e_i = - 2^(r-1)/i * binom(i+r-1,i-1) * [2i(i-2)+(i-3)r].

- If r = 0, then

    e_{n-1} = 3-n+(-1)^(n-1).

The formula with a rational-looking factor is an integer because of the equivalent binomial formula derived below. In particular these connected complete-bipartite examples simultaneously have n-3 consecutive negative coefficients.

## 1. Exact monomial membership
For a monomial m, let A be its total degree in a,b, and B its total degree in the y variables. Let o_A be the number of odd exponents among a,b, and o_B the number of odd y exponents. Let nu(m) be the largest number of quadratic generators whose product divides m. Then

    nu(m) = min(floor((A+B)/2), A+(B-o_B)/2, B+(A-o_A)/2).                 (1)

Proof. In any generator product, each cross generator uses one token from each side. Suppose t cross generators are used. If a side originally has total N and k odd exponents, the smallest possible number of odd residual exponents after removing t tokens is

    delta(N,k,t) = max(k-t, (N-t) mod 2),     0 <= t <= N.

For t <= k, remove a token from t odd coordinates. For t >= k, first remove one from every odd coordinate, leaving only even exponents; remove pairs thereafter, with one final token if the remaining removal count is odd. This proves attainability as well as the lower bound. Any choices of t removed tokens on the two sides can be paired, because all cross generators are present.

Assume A <= B and choose t=A. The a,b side is exhausted, and the residual odd count on the other side is max(o_B-A,(B-A) mod 2). Thus the number of pairs is

    min(floor((A+B)/2), A+(B-o_B)/2).

The third quantity in (1) is at least floor((A+B)/2), because B >= A >= o_A. The opposite ordering is symmetric. Each of the three quantities is also an upper bound for any pairing, proving (1). Consequently m belongs to I_q^s exactly when nu(m) >= s.

## 2. Count the excess over the square of the maximal ideal
Every monomial of total degree below 2s survives in S/I_q^s. Their number is binom(2s+n-1,n). Write E_s for the number of further surviving monomials, of total degree at least 2s.

By (1), such a monomial survives if either

    B+(A-o_A)/2 < s,                         (type A)
    A+(B-o_B)/2 < s.                         (type B)

These types are disjoint: the sum of their left sides is A+B+(A-o_A+B-o_B)/2, which is at least A+B >= 2s.

Type A: from A+B >= 2s and its strict inequality one gets o_A-B >= 2. Since o_A <= 2, necessarily o_A=2, B=0 and A=2s. The two positive odd exponents summing to 2s have exactly s choices. Hence type A contributes s.

Type B: write every y exponent as 2 beta_j + epsilon_j, with epsilon_j in {0,1}. Set k=sum epsilon_j, l=sum beta_j, and t=A. The inequality is t+l<s. Put r=s-t-l >= 1. The total-degree condition becomes

    k >= t+2r.

There are t+1 choices of the a,b exponents, binom(q,k) choices of the odd y coordinates, and binom(l+q-1,q-1) choices of beta. Therefore

    E_s = s + sum_{t>=0,r>=1,k>=t+2r, k<=q, t+r<=s}
                 (t+1) binom(q,k) binom(s-t-r+q-1,q-1).                (2)

Summing these contributions gives the generating series

    sum_{s>=1} E_s z^s
      = z/(1-z)^2 + P_q(z) z/(1-z)^q,                                (3)

where the finite polynomial is

    P_q(z) = sum_{t>=0,r>=1,t+2r<=q}
                (t+1) [sum_{k=t+2r}^q binom(q,k)] z^(t+r-1).          (4)

In particular deg P_q <= q-2 and its leading coefficient is q-1.

## 3. Hilbert numerator and coefficient convention
For any m-primary ideal in n variables, write

    sum_{s>=1} length(S/I^s) z^s = z h_I(z)/(1-z)^(n+1).

If h_I is a polynomial, its Taylor expansion gives e_i(I) = [u^i] h_I(1+u). Indeed the term e_i (z-1)^i contributes (-1)^i e_i binom(s+n-i-1,n-i) for sufficiently large s. This checks the alternating-sign convention directly.

For the ideal m^2 in n variables, decompose every monomial exponent as twice an integer plus a zero-or-one remainder. Its order is floor(total degree/2). It follows that

    h_{m^2,n}(z) = sum_{j>=0} binom(n+1,2j+1) z^j.

Put A_n(u)=h_{m^2,n}(1+u). The binomial identity gives A_0=1, A_1=2 and A_n=2 A_{n-1}+u A_{n-2}. In particular

    A_n(u) = sum_i binom(n-i,i) 2^(n-2i) u^i,

and

    sum_{q>=0} A_{q+2}(u) v^q = (4+u+2uv)/(1-2v-uv^2).               (5)

Combining (3) with n=q+2 gives

    h_{I_q}(z)=h_{m^2,q+2}(z)+(1-z)^(q+1)+(1-z)^3 P_q(z),

and hence

    h_{I_q}(1+u)=A_{q+2}(u)+(-1)^(q+1)u^(q+1)-u^3 P_q(1+u).          (6)

For q=0 and q=1 the same identity remains valid if P_q=0. The corresponding ideal is respectively (a^2,b^2) and the three-variable star; (2) still holds. Including these two values is only a generating-function convenience.

## 4. Extract every coefficient exactly
Introduce Q_k(z)=sum_{t>=0,r>=1,t+2r<=k}(t+1)z^(t+r-1). Summing the three independent indices yields

    sum_{k>=0} Q_k(z) w^k = w^2/[(1-w)(1-zw)^2(1-zw^2)].

Because P_q is the binomial transform of Q_k, substitution w=v/(1-v) gives

    sum_{q>=0} P_q(1+u) v^q
      = v^2(1-v)^2/[(1-2v)(1-(2+u)v)^2(1-2v-uv^2)].                 (7)

Equations (5)--(7) show that F(u,v)=sum_{q>=0} h_{I_q}(1+u)v^q is

    (4+u+2uv)/(1-2v-uv^2)
    - u^3 v^2(1-v)^2/[(1-2v)(1-(2+u)v)^2(1-2v-uv^2)]
    - u/(1+uv).

A polynomial multiplication, or partial fractions with respect to u, gives

    F(u,v)= -(7v-3)/(v(2v-1))
            -(v-1)(2v-1)/[v(uv+2v-1)^2]
            +(2v-3)/[v(uv+2v-1)]
            +1/[v(uv+1)].                                           (8)

Negative powers of v cancel in this identity of rational functions. For each i>=1 the coefficient of u^i in (8) is

    sum_{q>=0} e_i(I_q) v^q
       = v^(i-1) {[(2-i)+(i-1)v]/(1-2v)^(i+1)+(-1)^i}.              (9)

For r=q-i+1>=0 this is

    e_i = (2-i)2^r binom(i+r,i)
          +(i-1)2^(r-1) binom(i+r-1,i)
          +(-1)^i 1_{r=0}.                                         (10)

At r=0 the second binomial is zero, so the expression with 2^(-1) is interpreted as zero. For r<0 the coefficient is zero. In particular e_n=0. The first three coefficients in the theorem follow directly, as does e_0=2^n.

For 3<=i<=n-2 we have r>=1. Factoring (10) gives exactly the negative formula in the theorem; its bracket is strictly positive. For i=n-1 one obtains e_i=2-i+(-1)^i<0. This proves the entire consecutive-negative block.

## 5. The first example and its relation to the published conjecture
For q=2 the ideal is the four-cycle ideal with every square adjoined. Formula (2) is simply E_s=2s, for every s>=1. Thus

    length(S/I_2^s) = binom(2s+3,4)+2s
      = 16 binom(s+3,4)-12 binom(s+2,3)+binom(s+1,2)+2 binom(s,1).

Its Hilbert numerator is 7+4z+7z^2-2z^3, and (e_0,...,e_4)=(16,12,1,-2,0).

Fröberg, journal version J. Experimental Mathematics 1(2), 315--321 (2025), DOI 10.56994/JXM.001.002.007, defines the same alternating-sign convention on p.315 and states the nonnegativity Conjecture 1.1 on p.316. Conjecture 3.2, C4 bullet on p.320, predicts the same excess 2s but prints (16,12,1,2). These two predictions are inconsistent under the printed definition. The C4 calculation verifies the length prediction and gives e_3=-2. The general complete-bipartite classification is supplied in kpq-proof.md.
