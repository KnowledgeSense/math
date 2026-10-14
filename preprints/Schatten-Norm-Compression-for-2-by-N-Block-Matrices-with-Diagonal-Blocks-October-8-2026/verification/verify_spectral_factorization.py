"""Exact rational-polynomial checks for negative-power spectral factorization.

Standard-library rational Laurent polynomials in (t, R, alpha, theta).
R is independent during calculation, and is specialized to t**alpha
only in the mathematical interpretation. Negative powers permit the
exact substitution (t,R)->(1/t,1/R) with no numerical exponent values.
"""

from fractions import Fraction


class P:
    def __init__(self, value=0):
        if isinstance(value, dict):
            self.d = {key: Fraction(x) for key, x in value.items() if x}
        elif value:
            self.d = {(0, 0, 0, 0): Fraction(value)}
        else:
            self.d = {}

    def __add__(self, other):
        other = other if isinstance(other, P) else P(other)
        terms = self.d.copy()
        for key, value in other.d.items():
            terms[key] = terms.get(key, 0) + value
            if not terms[key]:
                del terms[key]
        return P(terms)

    __radd__ = __add__

    def __neg__(self):
        return P({key: -value for key, value in self.d.items()})

    def __sub__(self, other):
        return self + -(other if isinstance(other, P) else P(other))

    def __rsub__(self, other):
        return P(other) + -self

    def __mul__(self, other):
        other = other if isinstance(other, P) else P(other)
        terms = {}
        for i, value in self.d.items():
            for j, value2 in other.d.items():
                key = tuple(a + b for a, b in zip(i, j))
                terms[key] = terms.get(key, 0) + value * value2
        return P(terms)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        result = P(1)
        for _ in range(n):
            result = result * self
        return result

    def inverse_t_R(self):
        return P({
            (-key[0], -key[1], key[2], key[3]): value
            for key, value in self.d.items()
        })


t = P({(1, 0, 0, 0): 1})
R = P({(0, 1, 0, 0): 1})
alpha = P({(0, 0, 1, 0): 1})
theta = P({(0, 0, 0, 1): 1})
delta = t - 1
den = t * delta
q = theta * (1 - theta)
a = t + (1 - t) * theta
A = R + (1 - R) * theta

# E0, E1 and W are numerators over the common denominator den.
E0 = 2*t*t*(R-1) - alpha*(t+2*t*R-R)*delta
E1 = 2*t*(R-1) - alpha*t*(2-t+R)*delta
W = alpha*(t+R)*delta - 2*t*(R-1)
varpi = alpha*delta*(R+1) - (t+1)*(R-1)

# Twice q11, multiplied by den.
q11_twice_num = (
    alpha*theta**2*den
    + alpha*R*(1-theta)**2*delta
    + 2*t*(R-1)*q
)

# N0=t*Lambda_t(0), N1=t*Lambda_t(1).
N0 = (alpha+2)*(R-t)*varpi + (alpha+1)*(R-1)*E0
N1 = (alpha+2)*t*(R-t)*varpi + (alpha+1)*(R-1)*E1

checks = {
    "theta-square identity":
        theta**2*a-theta+q*(1+theta-t*theta),
    "complementary theta-square identity":
        (1-theta)**2*a-t*(1-theta)-q*(1-theta-t*(2-theta)),
    "2au=qE(theta), denominator cleared":
        a*q11_twice_num-alpha*A*den-q*((1-theta)*E0+theta*E1),
    "E1-E0=delta*omega":
        E1-E0-delta*W,
    "E0-tE1=alpha*delta^2*(h-1)":
        E0-t*E1-alpha*delta**3*(R-t),
    "omega+E1=-alpha*delta*(h-1)":
        W+E1+alpha*delta**2*(R-t),
    "invariant factorization, denominator cleared":
        E0*E1-t*W*W-2*alpha*(R-t)*varpi*t*delta**2,
    "t*omega-E1 final expansion":
        t*W-E1-2*alpha*(1+R)*den+2*(1+t)*(R-1)*t,
    "Lambda inversion at theta=0":
        N0-t**3*R**2*N1.inverse_t_R(),
    "Lambda inversion at theta=1":
        N1-t**3*R**2*N0.inverse_t_R(),
}

for name, residual in checks.items():
    print(f"{name}: {len(residual.d)} nonzero monomials")
    if residual.d:
        raise AssertionError((name, residual.d))
