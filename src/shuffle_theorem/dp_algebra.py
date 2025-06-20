from sage.misc.all import cached_function
from sage.rings.all import PolynomialRing
from sage.rings.rational_field import QQ
from sage.combinat.sf.sf import SymmetricFunctions

# Stuff from Mellit's file

@cached_function
def RR(k):
    ring = PolynomialRing(QQ, names=['q', 't', 'u', 'v'] + [f'y{i}' for i in range(k)])
    return ring.fraction_field()


@cached_function
def VV(k):
    return SymmetricFunctions(RR(k))

qq = RR(0).gen(0)
tt = RR(0).gen(1)
uu = RR(0).gen(2)
vv = RR(0).gen(3)


@cached_function
def yy(i):
    return RR(i+1).gen(i+4)


@cached_function
def XX(k):
    return VV(k).monomial()([1])


@cached_function
def XX0(k):
    return VV(k).one()

@cached_function
def space_index(f):
    """
    Finds the space of the symmetric function f.
    If f is in VV(k), returns k.
    """
    return len(f.parent().base_ring().gens()) - 4

def delta0(f, x, y):
    return ((qq - 1) * y * f + (y - qq * x) * f.subs({x: y, y: x})) / (qq * (y - x))


def deltastar0(f, x, y):
    return ((qq - 1) * x * f + (y - qq * x) * f.subs({x: y, y: x})) / (y - x)


def act_on_coefficients(operator, f):
    k = space_index(f)
    return sum(VV(k).monomial()(mu) * operator(cf) for (mu, cf) in VV(k).monomial()(f))


def TT(f, i):
    return act_on_coefficients(lambda g: deltastar0(g, yy(i), yy(i+1)), f)


def TTstar(f, i):
    return act_on_coefficients(lambda g: delta0(g, yy(i), yy(i+1)), f)


def dplus0(f, power=1):
    k = space_index(f)
    if f == 0:
        return 0
    if power == 0:
        return f
    f = sum(cf(RR(k+1).gens()[:-1]) * VV(k+1).monomial()(mu) for (mu, cf) in VV(k).monomial()(f))
    f = f(XX(k+1) + (qq - 1) * yy(k) * XX0(k+1))
    return dplus0(f, power=power-1)

def dplus(f, power=1):
    k = space_index(f)
    if f == 0:
        return 0
    if power == 0:
        return f
    f = -dplus0(f) * yy(k)
    for i in range(k):
        f = TT(f, k-i-1)
    return dplus(f, power=power-1)


def dplusstar(f, power=1):
    if power == 0:
        return f
    substitutions = [qq, tt, uu, vv] + [yy(i+1) for i in range(space_index(f))] + [tt*yy(0)]
    return dplusstar(act_on_coefficients(lambda g: g(substitutions), dplus0(f)), power=power-1)


def dminus0(f, power=1, old=True):
    k = space_index(f)
    if power == 0:
        return f
    eps = 1 if old else 0
    f = f(XX(k) - (qq-1) * yy(k-1) * XX0(k))
    out = 0
    for (mu, cf) in VV(k).monomial()(f):
        RT = RR(k-1)['T']
        T = RT.gens()[0]
        num = RT(RR(k)(cf).numerator()(list(RR(k-1).gens())+[T]))
        den = RT(RR(k)(cf).denominator()(list(RR(k-1).gens())+[T]))
        assert len(den.coefficients()) == 1
        for i in range(num.degree()+1):
            out += num[i+den.degree()]/den(T=1) * VV(k-1).monomial()(mu) * VV(k-1).elementary()[i+eps]*(-1)**i
    return dminus0(out, power=power-1)


def dminus(f, power=1):
    return dminus0(f, power=power, old=False)


def dcomm(f, power=1):
    if power == 0:
        return f
    return dcomm((dminus(dplus(f)) - dplus(dminus(f))) / (qq - 1), power=power-1)


def dword(w, f=XX0(0)):
    for x in w:
        if x == 1:
            f = dplus(f)
        elif x == 0:
            f = dcomm(f)
        else:
            f = dminus(f)
    return f


def zz(i, f, power=1):

    if f == 0:
        return 0
    if power == 0:
        return f
    k = space_index(f)

    for j in range(i):
        f = TT(f, i-j-1)
    for j in range(i-1):
        f = TTstar(f, j)
    f = (-qq**k / (qq-1))*(dplusstar(dminus(f)) - dminus(dplusstar(f)))
    for j in range(i):
        f = qq**(-1) * TT(f, j)

    return zz(i, f, power=power-1)


def D_alpha(alpha, f=RR(0).one()):
    def d_inner(alpha0, f0):
        if len(alpha0) == 0:
            return f0
        elif len(alpha0) == 1:
            return (-yy(0))**alpha0[0] * f0
        return d_inner(alpha0[:-1], (dplusstar(dminus((-yy(0))**(alpha0[-1]) * f0))
                                      + zz(0, (-yy(0))**(alpha0[-1]) * f0)))
    return dminus(d_inner(alpha, dplusstar(f)))
