'''
SageMath module.
Tools for the shuffle theorem and variants.
'''

# TODO: Write documentation!

# Import packages.
from more_itertools.recipes import partition
from math import exp
from sage.arith.misc import gcd, xgcd
from sage.categories.algebra_functor import GroupAlgebraFunctor
from sage.combinat.partition import Partitions
from sage.combinat.composition import Compositions
from sage.combinat.permutation import Permutations
from sage.combinat.sf.sf import SymmetricFunctions
from sage.combinat.ncsf_qsym.qsym import QuasiSymmetricFunctions
from sage.graphs.digraph import DiGraph
from sage.combinat.sf.macdonald import cmunu
from sage.groups.braid import BraidGroup
from sage.misc.all import cached_function, prod
from sage.rings.all import PolynomialRing, QQ


# Define q, t, u.
QQqt = QQ['q', 't', 'u'].fraction_field()
QQqt.inject_variables(verbose=False)
q = QQqt.gens()[0]
t = QQqt.gens()[1]
u = QQqt.gens()[2]

# Define the Symmetric Functions algebra over Q.
Sym = SymmetricFunctions(QQ)
Sym.inject_shorthands(verbose=False)

# Define the Symmetric Functions algebra over Q(q,t).
Symqt = SymmetricFunctions(QQqt)
Symqt.inject_shorthands(verbose=False)
H = Symqt.macdonald().Ht()

# Define the QuasiSymmetric Functions algebra over Q.
QSym = QuasiSymmetricFunctions(QQ)
QSym.inject_shorthands(verbose=False)

# Define the QuasiSymmetric Functions algebra over Q(q,t).
QSymqt = QuasiSymmetricFunctions(QQqt)
QSymqt.inject_shorthands(verbose=False)


def qt(items, qstat='qstat', tstat='tstat', x=False, read=None):
    # Computes the q,t-polynomial associated to any set, a q-statistic, and a t-statistic.

    if x == False:
        return sum(q**getattr(s, qstat)() * t**getattr(s, tstat)() for s in items)

    else:
        f = sum(q**getattr(s, qstat)() * t**getattr(s, tstat)() * QSymqt.Fundamental()(s.gessel(read))
                for s in items)
        if f.is_symmetric():
            return Symqt.schur()(f.to_symmetric_function())
        else:
            return f


def characteristic_function(path):

    # if not (path.labels == None and path.rises == [] and path.valleys == []):
    #     raise ValueError('I can only compute the characteristic funcion of a plain path.')

    def is_under(i, j):
        assert 0 <= i <= path.width and 0 <= j <= path.height

        if j == 0:
            if i <= path.shift:
                return True
            else:
                return False
        elif path.columns()[j-1] <= i <= path.main_diagonal()[j] + path.shift:
            return True
        else:
            return False

    collisions = [(i, j) for i in range(path.width+1) for j in range(path.height+1) if is_under(i, j)]
    collisions = sorted(collisions, key=lambda c: (path.rank(*c), c[1]), reverse=True)

    f = XX0(0)
    level = 0

    for c in collisions:
        # if c == (0, 0):
        #     pass
        if c == (path.width, path.height):
            pass
            # f = dminus(f, level)
            # level -= 1
        elif c[1] < path.height and path.columns()[c[1]] < c[0]:
            pass
            # if c[1] not in path.rises:
            #     f *= t
        elif path[c[0]+c[1]-1] == 1 and path[c[0]+c[1]] == 0:
            f = dplus(f, level)
            level += 1
        elif path[c[0]+c[1]-1] == 0 and path[c[0]+c[1]] == 1:
            f = dminus(f, level)
            level -= 1
        elif path[c[0]+c[1]-1] == 1 and path[c[0]+c[1]] == 1:
            exp = len([h for h in range(c[1], path.height) if h < (path.columns()[h]-c[0])/path.slope+c[1] <= h+1])
            f = q**(-exp)*(dminus(dplus(f, level), level+1) - dplus(dminus(f, level), level-1))/(q-1)
        elif path[c[0]+c[1]-1] == 0 and path[c[0]+c[1]] == 0:
            exp = len([h for h in range(c[1], path.height) if h < (path.columns()[h]-c[0])/path.slope+c[1] <= h+1])
            f *= q**exp
        else:
            raise ValueError('Something went wrong here.')

    f *= t**path.area()
    return Symqt.schur()(f)


def qteval(f, q=q, t=t, u=u):
    if f == 0:
        return 0
    elif QSymqt.Fundamental()(f).is_symmetric():
        return sum(cf.subs(q=q, t=t, u=u)*Symqt.schur()(mu) for (mu, cf) in Symqt.schur()(f))
    else:
        return sum(cf.subs(q=q, t=t, u=u)*QSymqt.Fundamental()(mu) for (mu, cf) in QSymqt.Fundamental()(f))


def omega(f):
    # The involution omega (e <-> h).
    return f.omega()


def omega_bar(f):
    # The involution omega bar (e <-> h, q <-> 1/q, t <-> 1/t).
    return qteval(f.omega(), q=1/q, t=1/t)


def scalar(f, g):
    # Hall scalar product on Sym.
    if f == 0 or g == 0:
        return 0
    else:
        return (f * Symqt.schur()[0]).scalar(g * Symqt.schur()[0])


def star_scalar(f, g):
    # Star scalar product on Symqt.
    return scalar(f, g.omega()(Symqt.schur()[1]*(1-q)*(1-t)))


def scalar_qt(f, g):
    # qt scalar product on Symqt (this is the one used to define the nonmodified Macdonald's P).
    return f.scalar_qt(g)


def B_mu(mu):
    # The constant B_\mu.
    return sum(q**c[1] * t**c[0] for c in mu.cells())


def nabla(f, power=1):
    # The nabla operator.
    if f == 0:
        return 0
    else:
        return f.nabla(power=power)


def Delta(f, g):
    # Delta operator.
    if g == 0:
        return 0
    else:
        g = g*Symqt.schur()[0]
        return Symqt.schur()(sum(cf*f(B_mu(mu)*Symqt.schur()[0])*Symqt.macdonald().Ht()(mu) for (mu, cf) in Symqt.macdonald().Ht()(g)))


def Deltaprime(f, g):
    # Delta' operator.
    if g == 0:
        return 0
    else:
        return Symqt.schur()(sum(cf*f((B_mu(mu)-1)*Symqt.schur()[0])*Symqt.macdonald().Ht()(mu) for (mu, cf) in Symqt.macdonald().Ht()(g)))


def Pi(f, power=1):
    # Pi operator.
    if f == 0:
        return 0
    elif f.degree() == 0:
        return 0
    else:
        return sum(sum(Symqt.elementary()[i]((B_mu(mu)-1)*Symqt.schur()[0])*(-1)**i for i in range(f.degree()))**power
                   * (cf * Symqt.macdonald().Ht()(mu)) for (mu, cf) in Symqt.macdonald().Ht()(f))


def w_mu(mu):
    # The constant w_\mu.
    return prod((q**mu.arm_length(c[0], c[1]) - t**(mu.leg_length(c[0], c[1])+1))*(t**mu.leg_length(c[0], c[1]) - q**(mu.arm_length(c[0], c[1])+1)) for c in mu.cells())


def Theta(f, g):
    # Theta operator.
    # It's equivalent to Pi(f(Symqt.schur()[1]/((1-q)*(1-t))) * Pi(g, power=-1)), but much faster.

    def theta_ek(k, g):
        # This is Theta(e[k], g). It is computed using the Pieri coefficients for e*[k].
        sf = 0
        for (nu, cc) in Symqt.macdonald().Ht()(g):
            wnu = w_mu(nu)
            for mu in Partitions(k+g.degree(), inner=nu):
                wmu = w_mu(mu)
                sf += (prod((1-(q**c[1])*(t**c[0])) for c in mu.cells() if c not in nu.cells())
                       * (wnu/wmu) * cmunu(mu, nu) * cc * Symqt.macdonald().Ht()(mu))
        return Symqt.macdonald().Ht()(sf)

    if f.degree() == 0:
        return Symqt.schur()(f * g)
    else:
        sf = sum(cc * theta_ek(gamma[0], Theta(Symqt.elementary()[gamma[1:]], g))
                 for (gamma, cc) in Symqt.elementary()(f))
        return Symqt.schur()(sf)


def C_alpha(alpha, f=Symqt.schur()[0]):
    # Zabrocki's operator C_\alpha.
    if len(alpha) == 0:
        return f
    else:
        sf = sum((-q)**(1-alpha[-1]) * q**(-r) * Symqt.homogeneous()[alpha[-1]+r] *
                 f.skew_by(Symqt.homogeneous()[r](Symqt.schur()[1]*(1-q))) for r in range(f.degree()+1))
        return C_alpha(alpha[:-1], sf)


def B_alpha(alpha, f=Symqt.schur()[0]):
    # Zabrocki's operator B_\alpha. It's reversed wrt C_\alpha, because reasons.
    if len(alpha) == 0:
        return f
    else:
        sf = sum((-1)**r * Symqt.elementary()[alpha[0]+r]
                 * f.skew_by(Symqt.homogeneous()[r](Symqt.schur()[1]*(1-q))) for r in range(f.degree()+1))
        return B_alpha(alpha[1:], sf)


def E_nk(n, k):
    # The E_{n,k} symmetric functions.
    return sum([C_alpha(alpha, Symqt.schur()[0]) for alpha in Compositions(n) if len(alpha) == k])


# Stuff from Bergeron's file

def D_n(n, f):
    return Q_mn(1, n, f=f)


def Q_mn(m, n, mu=None, f=None):

    if mu == None:
        mu = [1]
    if f == None:
        f = Symqt.schur()[0]
        # f = (-1)**n * Symqt.schur()[0]

    if len(mu) == 0:
        return f
    elif len(mu) == 1:
        if m == 0:
            return f * Symqt.schur()[1]
            # return f * (q*t)/(q*t-1) * Symqt.homogeneous()[n](Symqt.schur()[1] * (1-q*t)/(q*t))
        elif n == 0:
            # This is NOT the same as https://academic.oup.com/imrn/article/2016/14/4229/2451634 if m > 1.
            return f-(1-q)*(1-t)*Delta(Symqt.schur()[1], f)
        else:
            m *= mu[0]
            n *= mu[0]

            (d, n1, m1) = xgcd(m, n)

            if m1 > 0:
                n1 = -n1
            else:
                m1 = int(m/d)+m1
                n1 = int(n/d)-n1

            return (1/((1-q)*(1-t))
                    * (Q_mn(m-m1, n-n1, f=Q_mn(m1, n1, f=f)) - Q_mn(m1, n1, f=Q_mn(m-m1, n-n1, f=f))))
    else:
        return Q_mn(m, n, mu[1:], Q_mn(mu[0]*m, mu[0]*n, mu=[1], f=f))


def F_mn(m, n, f):
    # The Elliptic Hall Algebra machinery that takes a seed f and returns a (m,n)-family of symmetric functions.

    return sum(((q*t-1)/(q*t))**len(mu) * scalar(f, Symqt.forgotten()(mu)((q*t)/(q*t-1)*Symqt.schur()[1])) * Q_mn(m, n, mu=mu) for mu in Partitions(f.degree()))

    # return sum(cf * ((q*t-1)/(q*t))**len(mu) * Q_mn(m, n, mu=mu, f=Symqt.schur()[0]) for (mu, cf) in Symqt.homogeneous()(f((q*t)/(1-q*t)*Symqt.schur()[1])))


def iota(mu):
    return sum(mu[k]-k-1 for k in range(len(mu)) if mu[k] > k)


def e_mn(m, n=None):
    if n is None:
        return e_mn(m, m)
    elif (m, n) == (0, 0):
        return 0
    else:
        d = gcd(m, n)
        return F_mn(m/d, n/d, Symqt.elementary()[d])


def h_mn(m, n=None):
    if n is None:
        return h_mn(m, m)
    elif (m, n) == (0, 0):
        return 0
    else:
        d = gcd(m, n)
        return F_mn(m/d, n/d, (-1/(q*t))**(d-1) * Symqt.homogeneous()[d])


def p_mn(m, n=None):
    if n is None:
        return h_mn(m, m)
    elif (m, n) == (0, 0):
        return 0
    else:
        d = gcd(m, n)
        return F_mn(m/d, n/d, (-1)**(d-1) * Symqt.powersum()[d])


def pi_mn(m, n=None):
    if n is None:
        return h_mn(m, m)
    elif (m, n) == (0, 0):
        return 0
    else:
        d = gcd(m, n)
        return F_mn(m/d, n/d, sum((-1/(q*t))**j * Symqt.schur()([j+1]+[1]*(d-j-1)) for j in range(d)))


def E_mn(m, n, r):
    if (m, n) == (0, 0):
        return 0
    else:
        d = gcd(m, n)
        return F_mn(m/d, n/d, E_nk(d, r) * Symqt.schur()[0])


def C_alpha_mn(m, n, alpha, f=Symqt.schur()[0]):
    if (m, n) == (0, 0):
        return 0
    else:
        d = gcd(m, n)
        if not sum(alpha) == d:
            raise ValueError('The composition does not have the right length.')
        return F_mn(m/d, n/d, C_alpha(alpha, f))


# Stuff from Mellit's file

@cached_function
def RR(k):
    ring = PolynomialRing(QQ, names=['q', 't', 'u'] + ['y%d' % (i,) for i in range(k)])
    return ring.fraction_field()


@cached_function
def VV(k):
    return SymmetricFunctions(RR(k))


@cached_function
def qq(k):
    return RR(k).gen(0)


@cached_function
def tt(k):
    return RR(k).gen(1)


@cached_function
def uu(k):
    return RR(k).gen(2)


@cached_function
def yy(k, i):
    return RR(k).gen(i+3)


@cached_function
def XX(k):
    return VV(k).monomial()([1])


@cached_function
def XX0(k):
    return VV(k).monomial()([])


def delta0(f, k, x, y):
    return ((qq(k)-1)*y*f + (y-q*x)*f.subs({x: y, y: x}))/(q*(y-x))


def deltastar0(f, k, x, y):
    return ((qq(k)-1)*x*f + (y-q*x)*f.subs({x: y, y: x}))/(y-x)


def act_on_coefficients(operator, f, k):
    return sum(VV(k).monomial()(mu) * operator(cf) for (mu, cf) in VV(k).monomial()(f))


def TT(f, k, i):
    return act_on_coefficients(lambda g: deltastar0(g, k, yy(k, i), yy(k, i+1)), f, k)


def TTstar(f, k, i):
    return act_on_coefficients(lambda g: delta0(g, k, yy(k, i), yy(k, i+1)), f, k)


def dplus0(f, k):
    f1 = 0
    for p, cf in VV(k).monomial()(f):
        f1 += cf(RR(k+1).gens()[:-1]) * VV(k+1).monomial()(p)
    return f1(XX(k+1)+(qq(k+1)-1)*yy(k+1, k)*XX0(k+1))


def dplus(f, k):
    if f == 0:
        return 0
    f = -dplus0(f, k)*yy(k+1, k)
    for i in range(k):
        f = TT(f, k+1, k-i-1)
    return f


def dequal(f, k):
    for i in range(k-1):
        f = TTstar(f, k, k-i-2)
    return f * yy(k, 0)


def dplusstar(f, k):
    substitutions = [qq(k+1), tt(k+1), uu(k+1)] + [yy(k+1, i+1) for i in range(k)] + [tt(k+1)*yy(k+1, 0)]
    return act_on_coefficients(lambda g: g(substitutions), dplus0(f, k), k+1)


def dplusnabla(f, k):
    return -dplusstar(f, k)*qq(k+1)**k


def dminus0(f, k):
    f1 = f(XX(k)-(qq(k)-1)*yy(k, k-1)*XX0(k))
    f2 = 0
    for (mu, cf) in VV(k).monomial()(f1):
        cf = RR(k)(cf)
        den = cf.denominator()
        assert all(v in (qq(k), tt(k)) for v in den.variables())
        den = den([qq(k-1), tt(k-1), uu(k-1)] + [0]*k)
        RT = RR(k-1)['T']
        T = RT.gens()[0]
        num = RT(cf.numerator()(list(RR(k-1).gens())+[T]))
        for i in range(num.degree()+1):
            f2 += num[i]/den * VV(k-1).monomial()(mu) * VV(k-1).elementary()[i+1]*(-1)**i
    return f2


def dminus(f, k):
    if f == 0:
        return 0
    f1 = f(XX(k)-(qq(k)-1)*yy(k, k-1)*XX0(k))
    f2 = 0
    for (mu, cf) in VV(k).monomial()(f1):
        cf = RR(k)(cf)
        den = cf.denominator()
        assert all(v in (qq(k), tt(k)) for v in den.variables())
        den = den([qq(k-1), tt(k-1), uu(k-1)] + [0]*k)
        RT = RR(k-1)['T']
        T = RT.gens()[0]
        num = RT(cf.numerator()(list(RR(k-1).gens())+[T]))
        for i in range(num.degree()+1):
            f2 += num[i]/den * VV(k-1).monomial()(mu) * VV(k-1).elementary()[i]*(-1)**i \
                * (1 if i > 0 else 1-uu(k-1)*qq(k-1)**(1-k))
    return f2


# Quiver stuff

@cached_function
def QV(k):
    graph = DiGraph(k, loops=True, multiedges=True)

    for i in range(k):
        graph.add_edges([(i, i, 'y' + str(j) + 'd' + str(i)) for j in range(i+1)])

    for i in range(k-1):
        graph.add_edges([(i, i+1, 'dplus' + str(i)), (i, i+1, 'dplusstar' + str(i)), (i+1, i, 'dminus' + str(i+1))])

    return graph


@cached_function
def QVA(k):
    return QV(k).path_semigroup().algebra(QQqt)


# # Braid stuff

# @cached_function
# def BB(n):
#     return BraidGroup(('T%d' % (i+1,) for i in range(n-1)))


# @cached_function
# def Ti(k, n, m):
#     return BB(m+n).algebra(QQqt).gens()[k-1]


# @cached_function
# def idem(n, m):
#     return sum(q ^ sigma.number_of_inversions()*BB(m+n).algebra(QQqt).one()*BB(m+n)(sigma.reduced_word()) for sigma in Permutations(n))


# Stuff for actions
def act_as_y1(f, k):
    for i in range(k-1):
        f = TT(f, k, k-i-2)
    return (1 / (q**(k-1)*(q-1)))*(dplus(dminus(f, k), k-1) - dminus(dplus(f, k), k+1))


def act_as_z1(f, k):
    if f == 0:
        return 0
    for i in range(k-1):
        f = TTstar(f, k, i)
    return (q**k / (1-q))*(dplusstar(dminus(f, k), k-1) - dminus(dplusstar(f, k), k+1))


def zz(k, i, f):

    if f == 0:
        return 0

    for j in range(i):
        f = TT(f, k, i-j-1)
    for j in range(k-1):
        f = TTstar(f, k, j)
    f = (-q**k / (q-1))*(dplusstar(dminus(f, k), k-1) - dminus(dplusstar(f, k), k+1))
    for j in range(i):
        f = q**(-1) * TT(f, k, j)

    return f


def rho(m, n, operator, f, k):
    # if m == 0 or n == 0:
    #     print(m, n, operator, f, k)

    if gcd(m, n) != 1:
        raise ValueError('m, n must be coprime')

    if operator == 'd-':
        return dminus(f, k)

    elif operator == 'd+':

        if m == 0 and n == 1:
            f = dplus(f, k)
            # print(f)
            f += (q*t)**(-1) * u * (1 + u*yy(k+1, 0)) * yy(k+1, 0) * act_as_z1(f, k+1)
            # f *= 1 + u*yy(k+1, 0) + u*yy(k+1, 0)*u*yy(k+1, 0)
            return f

        elif m == 1 and n == 0:
            return -q**k * dplusstar(f, k)

        else:
            (d, n1, m1) = xgcd(m, n)

            if m1 > 0:
                n1 = -n1
            else:
                m1 = int(m/d)+m1
                n1 = int(n/d)-n1

            f = (-1/(q*t)) * rhostar(m1, n1, 'y1', rho(m-m1, n-n1, 'd+', f, k), k+1)

            return f

    elif operator[0] == 'y':
        i = int(operator[1:])-1

        if m == 0 and n == 1:
            # f = yy(k, i) * f
            for j in range(i):
                f = TTstar(f, k, i-j-1)
            for j in range(k-1):
                f = TT(f, k, j)
            f = (q**(-k+1) / (q-1)) * (dplus(dminus(f, k), k-1) - dminus(dplus(f, k), k+1))
            # print(f)
            f += (q*t)**(-1) * u * (1 + u*yy(k, 0)) * yy(k, 0) * act_as_z1(f, k)
            # f *= (1 + u*yy(k, 0) + u*yy(k, 0)*u*yy(k, 0))
            for j in range(i):
                f = q * TTstar(f, k, j)
            return f

        elif m == 1 and n == 0:
            for j in range(i):
                f = TTstar(f, k, i-j-1)
            for j in range(k-1):
                f = TT(f, k, j)
            f = (-1 / (q-1))*(dplusstar(dminus(f, k), k-1) - q*dminus(dplusstar(f, k), k+1))
            for j in range(i):
                f = q * TTstar(f, k, j)

            return f

        else:
            (d, n1, m1) = xgcd(m, n)

            if m1 > 0:
                n1 = -n1
            else:
                m1 = int(m/d)+m1
                n1 = int(n/d)-n1

            for j in range(i):
                f = TTstar(f, k, i-j-1)
            f = (-1/(q*t)) * rhostar(m1, n1, 'y1', rho(m-m1, n-n1, 'y1', f, k), k)
            for j in range(i):
                f = q * TTstar(f, k, j)

            return f

    return 'If you are reading this, something went horribly wrong'


def rhostar(m, n, operator, f, k):
    # if m == 0 or n == 0:
    #     print('*', m, n, operator, f, k)

    if gcd(m, n) != 1:
        raise ValueError('m, n must be coprime')

    if operator == 'd-':
        return dminus(f, k)

    elif operator == 'd+':

        if m == 1 and n == 0:
            return dplusstar(f, k)

        elif m == 0 and n == 1:
            return -q**(-k) * dplus(f, k)

        else:
            (d, n1, m1) = xgcd(m, n)

            if m1 > 0:
                n1 = -n1
            else:
                m1 = int(m/d)+m1
                n1 = int(n/d)-n1

            f = -rho(m-m1, n-n1, 'y1', rhostar(m1, n1, 'd+', f, k), k+1)
            # f = f + uu(k+1)*rho(m-m1, n-n1, 'y1', f, k+1) + uu(k+1) * \
            #     rho(m-m1, n-n1, 'y1', uu(k+1)*rho(m-m1, n-n1, 'y1', f, k+1), k+1)

            # f = -rhostar(m1, n1, 'd+', f, k)
            # f = f + (1/(q*t)) * u * (rhostar(m1, n1, 'y1', rho(m-m1, n-n1, 'y1', f, k+1), k+1) + u *
            #                          rho(m-m1, n-n1, 'y1', rhostar(m1, n1, 'y1', rho(m-m1, n-n1, 'y1', f, k+1), k+1), k+1))
            # f = rho(m-m1, n-n1, 'y1', f, k+1)

            return f

    elif operator[0] == 'y':
        i = int(operator[1:])-1

        if m == 1 and n == 0:
            for j in range(i):
                f = TT(f, k, i-j-1)
            for j in range(k-1):
                f = TTstar(f, k, j)
            # f = (1 - u*yy(k, 0))*f
            f = (-q**k / (q-1))*(dplusstar(dminus(f, k), k-1) - dminus(dplusstar(f, k), k+1))
            # f = (1 + u*yy(k, 0) + u*yy(k, 0)*u*yy(k, 0))*f
            for j in range(i):
                f = q**(-1) * TT(f, k, j)

            return f

        elif m == 0 and n == 1:
            for j in range(i):
                f = TT(f, k, i-j-1)
            for j in range(k-1):
                f = TTstar(f, k, j)
            f = (1 / (q-1))*(q*dplus(dminus(f, k), k-1) - dminus(dplus(f, k), k+1))
            for j in range(i):
                f = q**(-1) * TT(f, k, j)

            return f

        else:
            (d, n1, m1) = xgcd(m, n)

            if m1 > 0:
                n1 = -n1
            else:
                m1 = int(m/d)+m1
                n1 = int(n/d)-n1

            for j in range(i):
                f = TT(f, k, i-j-1)

            f = -rho(m-m1, n-n1, 'y1', rhostar(m1, n1, 'y1', f, k), k)
            # f += uu(k)*rho(m-m1, n-n1, 'y1', f, k) + uu(k)*rho(m-m1, n-n1, 'y1', uu(k)*rho(m-m1, n-n1, 'y1', f, k), k)

            # f = -rhostar(m1, n1, 'y1', f, k)
            # f = f + (1/(q*t)) * u * (rhostar(m1, n1, 'y1', rho(m-m1, n-n1, 'y1', f, k), k) + u *
            #                          rho(m-m1, n-n1, 'y1', rhostar(m1, n1, 'y1', rho(m-m1, n-n1, 'y1', f, k), k), k))
            # f = rho(m-m1, n-n1, 'y1', f, k)

            for j in range(i):
                f = q**(-1) * TT(f, k, j)

            return f

    return 'If you are reading this, something went horribly wrong'


def rhostar_mn_alpha(m, n, alpha):
    f = XX0(0)

    for i in range(len(alpha)):
        f = rhostar(m, n, 'd+', f, i)

    for (i, alpha_i) in enumerate(alpha):
        for j in range(alpha_i-1):
            f = rhostar(m, n, 'y' + str(i+1), f, len(alpha))

    for i in range(len(alpha)):
        f = rhostar(m, n, 'd-', f, len(alpha)-i)

    return (-1)**(sum(alpha)*(m+1)) * q**(len(alpha) - sum(alpha)) * f
