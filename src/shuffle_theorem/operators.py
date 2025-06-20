'''
SageMath module.
'''

# Import packages.
from sage.categories.tensor import tensor
from sage.combinat.partition import Partitions
from sage.combinat.sf.sf import SymmetricFunctions
from sage.combinat.ncsf_qsym.qsym import QuasiSymmetricFunctions
from sage.combinat.sf.macdonald import cmunu
from sage.misc.all import cached_function, prod
from sage.rings.all import QQ
from .dp_algebra import RR, qq, tt, uu, vv

# Define the Symmetric Functions and QuasiSymmetric Functions algebras over Q and Q(q,t,u,v).
QQqt = RR(0)
Sym = SymmetricFunctions(QQ)
Symqt = SymmetricFunctions(QQqt)
QSym = QuasiSymmetricFunctions(QQ)
QSymqt = QuasiSymmetricFunctions(QQqt)


def qt(items, qstat='qstat', tstat='tstat', x=False, read=None):
    # Computes the q,t-polynomial associated to any set, a q-statistic, and a t-statistic.
    # x is a boolean that determines whether to return the q,t-polynomial or the symmetric function.
    # if x is True, read is the reading word used to compute the associated quasisymmetric function.

    if not isinstance(items, (list, tuple, set)):
        raise TypeError("items must be a list or tuple of objects with qstat and tstat attributes")
    if not all(hasattr(s, qstat) and hasattr(s, tstat) for s in items):
        raise ValueError(f"Each item in items must have attributes '{qstat}' and '{tstat}'")

    if not items:
        return 0

    if x is False:
        return sum(qq(0)**getattr(s, qstat)() * tt(0)**getattr(s, tstat)() for s in items)

    f = sum(qq(0)**getattr(s, qstat)() * tt(0)**getattr(s, tstat)() * QSymqt.Fundamental()(s.gessel(read)) for s in items)
    return f.to_symmetric_function() if f.is_symmetric() else f

    
def qteval(f, q=qq, t=tt, u=uu, v=vv):
    # Evaluates q, t, u, v if f is a symmetric function or a tensor of symmetric functions over Q(q,t,u,v).

    if f * QQqt.one() in QQqt:
        # If f is a scalar, we can directly substitute the variables
        return (f * QQqt.one()).subs(q=q, t=t, u=u, v=v)
    try:
        # If f is a tensor of symmetric functions, we evaluate each component
        return sum(tensor([f.parent().tensor_factors()[i](mu[i]) for i in range(len(mu))]) 
                   * cf.subs(q=q, t=t, u=u, v=v) for (mu, cf) in f)
    except AttributeError:
        # This handles the case where f is a single symmetric function
        return sum(cf.subs(q=q, t=t, u=u, v=v) * f.parent()(mu) for (mu, cf) in f)


## Cached constants.

@cached_function
def B_mu(mu):
    # Computes the B operator on a partition mu.
    return sum(qq**c[1] * tt**c[0] for c in mu.cells())

@cached_function
def c_munu(mu,nu):
    return cmunu(mu, nu)

@cached_function
def w_mu(mu):
    # The constant w_\mu.
    return prod((qq**mu.arm_length(c[0], c[1]) - tt**(mu.leg_length(c[0], c[1])+1)) * 
                (tt**mu.leg_length(c[0], c[1]) - qq**(mu.arm_length(c[0], c[1])+1)) for c in mu.cells())


# Symmetric function operators.

def Delta(f, g, prime=False, power=1):
    # Computes the Delta operator on symmetric functions.
    # https://math.berkeley.edu/~mhaiman/ftp/glenn-adriano/positivity.pdf

    return sum(cf * ((f((B_mu(mu) - (1 if prime else 0)) * Symqt.one()).scalar(Symqt.one()))**power)
               * Symqt.macdonald().Ht()(mu) for (mu, cf) in Symqt.macdonald().Ht()(g * Symqt.one()))

def Pi(f, power=1):
    # Pi operator.
    return Delta(sum((-1) ** i * Symqt.elementary()[i] for i in range(f.degree())), f, power=power, prime=True)

def Xi(f):
    # This is essentially Delta(e[1], Theta(f, 1))
    # https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/delta-and-theta-operator-expansions/7C386B423A6C5FADB60654023E77DB78
    return (1-qq)*(1-tt) * Delta(sum((-1) ** i * Symqt.elementary()[i] for i in range(f.degree())) 
                               * (Symqt.monomial()[1] + Symqt.one()), f(Symqt.monomial()[1]/(1-qq)/(1-tt)), prime=True)

def Theta(f, g):
    # Computes the Theta operator on symmetric functions.
    # https://www.sciencedirect.com/science/article/pii/S0001870820304758

    if f.degree() == 0:
        return f * g

    if (g*Symqt.one()).degree() == 0:
        return 0

    @cached_function
    def pars(k, nu):
        return Partitions(k+sum(nu), inner=nu)

    @cached_function
    def theta_ek(k, g):
        # This is Theta(e[k], g). It is computed using the Pieri coefficients for e[k].
        sf = 0
        for (nu, cc) in Symqt.macdonald().Ht()(g):
            for mu in pars(k, nu):
                sf += (prod((1-(qq**c[1])*(tt**c[0])) for c in mu.cells() if c not in nu.cells())
                       * (w_mu(nu)/w_mu(mu)) * c_munu(mu, nu) * cc * Symqt.macdonald().Ht()(mu))
        return sf

    return sum(cc * theta_ek(gamma[0], Theta(Symqt.elementary()[gamma[1:]], g))
               for (gamma, cc) in Symqt.elementary()(f))

def C_alpha(alpha, f=Symqt.one()):
    # Zabrocki's operator C_\alpha.
    # TODO: Add reference to the paper.
    if len(alpha) == 0:
        return f
    sf = sum((-qq)**(1-alpha[-1]) * qq**(-r) * Symqt.homogeneous()[alpha[-1]+r] *
             f.skew_by(Symqt.homogeneous()[r](Symqt.monomial()[1]*(1-qq))) for r in range(f.degree()+1))
    return C_alpha(alpha[:-1], sf)

def B_alpha(alpha, f=Symqt.one()):
    # Zabrocki's operator B_\alpha. It's reversed wrt C_\alpha.
    # TODO: Add reference to the paper.
    if len(alpha) == 0:
        return f
    sf = sum((-1)**r * Symqt.elementary()[alpha[0]+r]
             * f.skew_by(Symqt.homogeneous()[r](Symqt.monomial()[1]*(1-qq))) for r in range(f.degree()+1))
    return B_alpha(alpha[1:], sf)


# Operators on tensors of symmetric functions.

def super_nabla(f, power=1):
    # Computes the super nabla operator on symmetric functions.
    # https://arxiv.org/abs/2303.00560
    
    if f in Symqt:
        # If f is a single symmetric function, we can directly apply the operator.
        return sum(cf * tensor([Symqt.macdonald().Ht()(mu)]*(power+1)) for (mu, cf) in Symqt.macdonald().Ht()(f))

    # If f is a tensor of symmetric functions, we apply the operator to the last component.    
    length = len(list(f)[0][0])
    return sum(cf * tensor([Symqt.macdonald().Ht()(mu[i]) for i in range(length)] +
        [Symqt.macdonald().Ht()(mu[-1])] * power) for (mu, cf) in tensor([Symqt.macdonald().Ht()]*length)(f))

def plethystic_evaluation(f, x=None):
    # Computes the plethystic evaluation of a tensor of symmetric functions in a tuple of variables x.
    # If the tuple is shorter than the number of tensor factors, it is padded with the identity function.

    x += [Symqt.monomial()[1]] * (len(f.parent().tensor_factors()) - len(x))

    return sum(cf * tensor([f.parent().tensor_factors()[i](mu[i])(x[i] * Sym.one()) for i in range(len(mu))])
               for (mu, cf) in f)