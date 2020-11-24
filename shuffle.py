
'''
SageMath module.
Tools for the shuffle theorem and variants.
'''

#from sage.combinat.shuffle import ShuffleProduct


def shuffle_two(a, b):
    # Given two lists, returns the shuffle of the two,
    # i.e. all the lists obtained by shuffling a and b.

    if len(a) == 0:
        yield b
    elif len(b) == 0:
        yield a
    else:
        for p in shuffle_two(a[1:], b):
            yield [a[0]] + p
        for p in shuffle_two(a, b[1:]):
            yield [b[0]] + p


def shuffle_list(l):
    # Given a list of lists, returns all the possible shuffles of the elements.

    if len(l) == 0:
        return []
    elif len(l) == 1:
        return [l[0]]
    else:
        return [y for x in shuffle_two(l[0], l[1]) for y in shuffle_list([x] + shuffle_list(l[2:]))]


def shuffle_munu(mu=[], nu=[]):
    # Given two compositions mu, nu, it returns the list of all shuffles
    # of the lists [1, 2, ..., mu[1]], [mu[1]+1, mu[1]+2, ..., mu[1]+mu[2]], ...
    # of the lists [sum([mu])+nu[1], sum([mu])+nu[1]-1, ..., sum([mu])], ...

    sh_mu = [[]]
    for i in range(0, len(mu)):
        auxsh = []
        for ww in sh_mu:
            auxsh = auxsh + list(shuffle_two(ww, [j + sum(mu[:i]) for j in range(1, mu[i]+1)]))
        sh_mu = auxsh

    sh_nu = [[]]
    for i in range(0, len(nu)):
        auxsh = []
        for ww in sh_nu:
            auxsh = auxsh + list(shuffle_two(ww, [sum(mu) + sum(nu[:i+1]) - j for j in range(0, nu[i])]))
        sh_nu = auxsh

    return [z for x in sh_mu for y in sh_nu for z in shuffle_two(x, y)]
