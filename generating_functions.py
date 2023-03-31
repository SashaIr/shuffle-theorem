'''
SageMath module.
Tools for the shuffle theorem and variants.
'''

from sage.combinat.species.series import LazyPowerSeries, LazyPowerSeriesRing
from sage.rings.all import NN

from .symmetric_functions import *

L = LazyPowerSeriesRing(Symqt)


def Elementary(Z=Symqt.schur()[1]):
    for i in NN:
        yield Symqt.elementary()[i](Z)


def Homogeneous(Z=Symqt.schur()[1]):
    for i in NN:
        yield Symqt.homogeneous()[i](Z)


def PowerSum(Z=Symqt.schur()[1]):
    for i in NN:
        yield Symqt.powersum()[i](Z)


def Monomial(Z=Symqt.schur()[1]):
    for mu in Partitions():
        yield Symqt.monomial()(mu)(Z)


def Schur(Z=Symqt.schur()[1]):
    for mu in Partitions():
        yield Symqt.schur()(mu)(Z)


def Exp(Z=Symqt.schur()[1]):
    return L(Homogeneous(Z))


def translate_by(Z):
    return lambda f: f(Symqt.schur()[1]+Z)


def multiply_by(Z):
    return lambda f: Exp(Symqt.schur()[1]*Z)*L(f.restrict_degree(d, exact=True) for d in range(f.degree()))
