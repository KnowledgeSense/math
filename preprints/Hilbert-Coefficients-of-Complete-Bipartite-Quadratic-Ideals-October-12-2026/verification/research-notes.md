# Mathematical research materials

Author: Knowledge Sense

Let k be any field, 1 <= p <= q, n=p+q, S=k[x_1,...,x_p,y_1,...,y_q], and
I=(x_a^2,y_b^2,x_a y_b : 1<=a<=p,1<=b<=q).
All powers are ordinary powers. The lengths of the quotients S/I^s are their finite k-vector-space dimensions, equivalently their lengths after localization at the homogeneous maximal ideal.

The Hilbert-coefficient convention is

    length(S/I^s)=sum_{i=0}^n (-1)^i e_i binom(s+n-i-1,n-i).

For this family the identity holds for every integer s>=1, not just eventually.
The main theorem gives e_i=2^(n-2i)binom(n-i,i)>0 for 0<=i<=p;
sign(e_i)=(-1)^(p+1) for p+1<=i<=n-1; and e_n=0.
All coefficients are nonnegative exactly when p is odd.
The high-index interval is empty for p=q=1. For even p it contains q-1 strictly negative coefficients.

The complete parity classification for all positive part sizes p,q is proved in kpq-proof.md. Its monomial-packing argument is given in k2q-proof.md, Section 1, and applies to arbitrary positive p,q.

## Length formula and low-degree identity

    D_{a;b}(s)=sum_{t>=0,r>=1,t+2r<=a,t+r<=s}
      binom(t+b-1,b-1) binom(s-t-r+a-1,a-1) sum_{j=t+2r}^a binom(a,j).
    L_{p,q}(s)=binom(2s+n-1,n)+D_{p;q}(s)+D_{q;p}(s).

The proof defines P_{a;b}(z), with degree a-2 for a>=2 and P_{1;b}=0, and

    sum_{s>=1}L(s)z^s=zh(z)/(1-z)^(n+1),
    h(z)=h_{m^2,n}(z)+(1-z)^(q+1)P_{p;q}(z)+(1-z)^(p+1)P_{q;p}(z).

The baseline has h_{m^2,n}(z)=sum_{j>=0}binom(n+1,2j+1)z^j and
h_{m^2,n}(1+u)=sum_i 2^(n-2i)binom(n-i,i)u^i.
The recurrence A_n(u)=2A_{n-1}(u)+uA_{n-2}(u), with A_0=1,A_1=2, proves the latter identity.
Since deg h<=n-1, the binomial-coefficient expression for L(s) is valid from s=1 onward and e_n=0.

## Conventions for generating functions

- In the rational bivariate generating function, x-y is not a unit in a formal power-series ring. After a common denominator is taken the antisymmetric numerator is divisible by x-y; the other denominators have constant term one.
- Coefficients beyond the degree of h are taken to be zero. Symmetry extends the formulas to all positive ordered part sizes.
- The normalized integral identity in kpq-proof.md, Section 4 concerns r<i-1; this is guaranteed when q<i<=p+q-1. The endpoint r=0 is included.
- The integrals denote rational polynomial identities concerning integer lengths. No ordering or rational inversion is required in the original field k, so the theorem holds in positive characteristic.

## The square graph

For p=q=2, L(s)=binom(2s+3,4)+2s for all s>=1. In the stated alternating-sign convention this is

    L(s)=16 binom(s+3,4)-12 binom(s+2,3)+binom(s+1,2)+2s,
    (e_0,e_1,e_2,e_3,e_4)=(16,12,1,-2,0).

The first three lengths are 7,39,132. Fröberg's published Conjecture 3.2 (p.320) predicts this same length formula but prints +2 as the third coefficient. The formula itself gives -2 under his own convention (p.315). The general p,q classification is the contribution beyond this isolated sign discrepancy and proves counterexamples to his Conjecture 1.1 (p.316) on nonnegative coefficients for quadratic Artinian algebras.

## Prior structural results and distinct nearby computations

The construction I=Q_x+Q_y+m_x m_y is an established fiber-product ideal. Nguyen--Vu, Notation 4.3 and Proposition 4.4, provide general powers decompositions and exact intersections; the monomial hypotheses are satisfied over every field. The present results evaluate the lengths explicitly and classify the signs of all Hilbert coefficients by the parity of the smaller part size.

Nguyen--Vu's v3 corrects Lemma 5.3(ii); their arXiv comment says the other parts are unaffected. The cited Proposition 4.4 is retained. Do--Nguyen--Seyed Fakhari 2024, Lemma 5.6, restates the splitting as exact sequences; Remark 5.4 corrects a regularity formula when both factor ideals are zero, whereas both Q_x and Q_y are nonzero here.

Negative higher coefficients for general ideals, including consecutive negative values, precede this result. Mafi--Naderi's Examples 2.1--2.2 (pp.7--8 in arXiv:1707.09843v3) have cubic or mixed-degree generators.

Banerjee--Goel--Verma, Theorem 3.3 and Example 3.11, computes lengths for
S/(J(K_{a,b})+(m^[Q])^s), where the edge ideal is fixed before taking powers of pure powers. Here the length is for S/(J(K_{a,b})+m^[2])^s: the entire sum is powered. The former ambient quotient has dimension max(a,b); the Hilbert-coefficient convention here uses the regular ambient dimension a+b. At K_{2,2},Q=2,s=2 their formula gives 23, while the present length is 39. At s=1,Q=2 the two quotients coincide.

## Primary bibliography

1. Ralf Fröberg, Hilbert Coefficients of Quadratic Algebras, Journal of Experimental Mathematics 1(2) (2025), 315--321. DOI 10.56994/JXM.001.002.007. Journal PDF: https://jexpmath.org/index.php/jem/article/download/Vol-1Issue-2Paper-7/Vol-1Issue-2Paper-7 . Earlier version: arXiv:2311.02860v1 (6 November 2023).
2. Hop D. Nguyen and Thanh Vu, Homological invariants of powers of fiber products, Acta Mathematica Vietnamica 44 (2019), 617--638. Corrected version: arXiv:1803.04016v3, https://arxiv.org/pdf/1803.04016v3 . Notation 4.3 / Proposition 4.4, pp.9--10.
3. Hoang Viet Do, Hop D. Nguyen and Seyed Amin Seyed Fakhari, On the ordinary and symbolic powers of fiber products, Journal of Algebra 678 (2025), 570--600. DOI 10.1016/j.jalgebra.2025.04.029. The cited numbering follows arXiv:2409.17551v1, available at https://arxiv.org/pdf/2409.17551v1 . Lemma 5.6, p.16.
4. Amir Mafi and Dler Naderi, Results on the Hilbert coefficients and reduction numbers, Proceedings -- Mathematical Sciences 129 (2019), article 60. DOI 10.1007/s12044-019-0510-z. The cited example numbering follows arXiv:1707.09843v3, available at https://arxiv.org/pdf/1707.09843v3 . Examples 2.1--2.2, pp.7--8.
5. Arindam Banerjee, Kriti Goel and J. K. Verma, On the Hilbert-Samuel coefficients of Frobenius powers of an ideal, arXiv:2203.10173v1, https://arxiv.org/pdf/2203.10173v1 . Theorem 3.3, p.8; Example 3.11, pp.12--13.

Supplemental checks are in check.py and certificate.json. The proofs do not rely on a finite parameter search.
