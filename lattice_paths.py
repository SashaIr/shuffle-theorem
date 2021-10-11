'''
SageMath module.
Tools for the shuffle theorem and variants.
'''

# TODO: Write documentation!

from itertools import combinations
from more_itertools import distinct_combinations
from multiset import Multiset
from six import add_metaclass

from sage.arith.misc import gcd
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.combinat.composition import Composition
from sage.combinat.partition import Partition
from sage.combinat.permutation import Permutation
from sage.functions.other import floor
from sage.misc.all import cached_method, lazy_attribute, lazy_class_attribute
from sage.misc.latex import latex
from sage.misc.mrange import cantor_product
from sage.rings.all import Integer, Rational
from sage.sets.disjoint_union_enumerated_sets import \
    DisjointUnionEnumeratedSets
from sage.sets.family import Family
from sage.sets.positive_integers import PositiveIntegers
from sage.sets.set_from_iterator import EnumeratedSetFromIterator
from sage.structure.dynamic_class import \
    DynamicInheritComparisonClasscallMetaclass
from sage.structure.global_options import GlobalOptions
from sage.structure.list_clone import ClonableIntArray  # type: ignore
from sage.structure.set_factories import (ParentWithSetFactory,
                                          SelfParentPolicy,
                                          SetFactory)
from sage.structure.unique_representation import UniqueRepresentation

from .symmetric_functions import characteristic_function


def _format_constraints(constraints, reverse=False):

    defaults = {'width': None, 'height': None, 'shift': None, 'square': False,
                'labelled': True, 'labels': None, 'decorated_rises': 0, 'decorated_valleys': 0, }

    if reverse is False:
        args, kwargs = constraints
        formatted_constraints = [defaults[key] for key in defaults]

        for i, arg in enumerate(args):
            formatted_constraints[i] = arg

        for i, key in enumerate(defaults):
            if key in kwargs:
                formatted_constraints[i] = kwargs[key]

        return tuple(formatted_constraints)

    elif reverse is True:
        formatted_constraints = defaults
        constraints = list(constraints)

        for c in enumerate(constraints):
            formatted_constraints[list(defaults)[c[0]]] = c[1]

        return formatted_constraints


def _generate_lattice_paths(m, n, shift=None, rises=[], valleys=[], _level=0, _slope=None, _going_up=False, _flag=False):
    '''
    Builds all the lattice paths from (0,0) to (m,n), as generator,
    where a path is a 0-1 sequence where 0 denotes an east step, 1 denotes a north step.

    If a shift is specified, it will only build the paths with exactly that shift,
    otherwise it will build all the paths ending east.

    The paths will have rises and valleys in the specified rows.

    The variables _level, _slope, _going_up, and _flag are internal.
    '''

    if n == 0:
        if shift is None or _flag is True:
            yield [0]*m
    elif m != 0:
        if shift is not None:
            if _level < - shift:
                return None
            elif _level == -shift:
                _flag = True

        if _slope is None:

            m1 = m-len(rises)-len(valleys)
            n1 = n-len(rises)-len(valleys)

            if m1 <= 0 or n1 <= 0:
                return None

            _slope = Rational(m1/n1)

        if 0 in rises:
            if _going_up == True:
                for p in _generate_lattice_paths(
                        m,
                        n-1,
                        shift=shift,
                        rises=[i-1 for i in rises[1:]],
                        valleys=[i-1 for i in valleys],
                        _level=_level+1,
                        _slope=_slope,
                        _going_up=True,
                        _flag=_flag):
                    yield [1] + p

        else:
            for p in _generate_lattice_paths(
                    m-1,
                    n,
                    shift=shift,
                    rises=rises,
                    valleys=valleys,
                    _level=_level-1,
                    _slope=_slope,
                    _going_up=False,
                    _flag=_flag):
                yield [0] + p

            if 0 in valleys:
                if _going_up == False:
                    for p in _generate_lattice_paths(
                            m,
                            n-1,
                            shift=shift,
                            rises=[i-1 for i in rises],
                            valleys=[i-1 for i in valleys[1:]],
                            _level=_level+1,
                            _slope=_slope,
                            _going_up=True,
                            _flag=_flag):
                        yield [1] + p
            else:
                for p in _generate_lattice_paths(
                        m,
                        n-1,
                    shift=shift,
                        rises=[i-1 for i in rises],
                        valleys=[i-1 for i in valleys],
                        _level=_level+_slope,
                        _slope=_slope,
                        _going_up=True,
                        _flag=_flag):
                    yield [1] + p


def _lattice_paths(width, height=None, shift=None, labelled=True, labels=None, decorated_rises=0, decorated_valleys=0):

    if height is None:
        # If no value is specified, the grid is assumed to be a square.
        height = width

    # Sets the deafult set of labels to [n].
    if labels is None:
        labels = tuple([0] + [1]*(height))

    for r in combinations(range(1, height), decorated_rises):
        for v in combinations([i for i in range(height) if i not in r], decorated_valleys):
            for path in _generate_lattice_paths(width, height, shift=shift, rises=r, valleys=v):
                if labelled is False:
                    yield path, None, r, v
                else:
                    for l in LatticePath(path, rises=r, valleys=v).labellings(labels):
                        yield path, l, r, v


def _mu_labellings(blocks, label_composition, strict=True, increasing=True):

    if len(blocks) == 0:
        yield []
    else:
        if strict == True:
            label_choices = combinations(set(label_composition), blocks[0])
        else:
            label_choices = distinct_combinations(label_composition, blocks[0])
        for chosen_labels in label_choices:
            chosen_labels = sorted(list(chosen_labels), reverse=not increasing)
            for other_labels in _mu_labellings(blocks[1:],
                                               list((Multiset(label_composition) - Multiset(chosen_labels))),
                                               strict=strict,
                                               increasing=increasing):
                yield chosen_labels + other_labels


def _paths_size_shift(policy, width, height, shift, **kwargs):
    if height == width:
        if shift == 0:
            return DyckPaths_size(policy, width, **kwargs)
        else:
            return SquarePaths_size_shift(policy, width, shift, **kwargs)
    elif shift == 0:
        return RectangularDyckPaths_size(policy, width, height, **kwargs)
    else:
        return RectangularPaths_size_shift(policy, width, height, shift, **kwargs)


@add_metaclass(DynamicInheritComparisonClasscallMetaclass)
class LatticePath(ClonableIntArray):

    @staticmethod
    def __classcall_private__(cls, *args, **kwargs):
        return cls._auto_parent._element_constructor_(*args, **kwargs)

    @lazy_class_attribute
    def _auto_parent(cls):
        return RectangularPaths_all(SelfParentPolicy(LatticePaths, cls))

    def __init__(self, parent, path, labels=None, rises=[], valleys=[], latex_options={}):

        self.path = path
        self.labels = labels
        self.rises = rises
        self.valleys = valleys

        # Total length, width, and height of the path.
        self.length = len(self.path)
        self.height = sum(self.path)
        self.width = self.length-self.height

        # It's the slope, corrected to disregard the decorations.
        self.slope = 1 if self.width == self.height \
            else Rational((self.width - len(self.rises) - len(self.valleys)) /
                          (self.height - len(self.rises) - len(self.valleys)))

        # It's the disance between the main diagonal and the base diagonal.
        self.shift = - min(self.area_word()) if self.height > 0 else 0
        # Instruction on how to draw the path in LaTeX.
        self._latex_options = dict(latex_options)

        ClonableIntArray.__init__(self, parent, path)

    def check(self):
        if not (isinstance(self.path, list) and all(x in [0, 1] for x in self.path)):
            raise ValueError(f'Invalid path (= {self.path}), entries must be 0 and 1')

    def _repr_(self):
        representation = f'{self.parent().Element.__name__}({self.path}'
        if self.labels is not None:
            representation += f', labels={self.labels}'
        if self.rises != []:
            representation += f', rises={self.rises}'
        if self.valleys != []:
            representation += f', valleys={self.valleys}'
        representation += ')'
        return representation

    def qstat(self):
        # Sets a default q-statistic.
        return self.dinv()

    def tstat(self):
        # Sets a default t-statistic.
        return self.area()

    def labellings(self, composition=None):
        # Returns all the possible labellings of the path, provided that it has no labels and no decorations.
        # It is possible to specify which labels to use, composition[i] being the number of i's appearing.

        # The deafult set of labels is [n].
        if composition is None:
            composition = [0] + [1]*self.height

        if self.height != sum(composition):
            raise ValueError('The number of labels does not match the size of the path')

        # Find the composition given by the vertical steps of the path.
        peaks = [-1] + [i for i in range(self.height) if(
            i == self.height-1
            or (self.area_word()[i+1] < self.area_word()[i] and i in self.rises)
            or (self.area_word()[i+1] < self.area_word()[i] + self.slope - 1 and i not in self.rises)
            or (self.area_word()[i+1] == self.area_word()[i]
                and i in self.rises and i+1 not in self.valleys)
            or (self.area_word()[i+1] == self.area_word()[i] + self.slope - 1
                and i not in self.rises and i+1 not in self.valleys)
        )]

        blocks = [peaks[i+1] - peaks[i] for i in range(len(peaks)-1)]

        # Define the set of labels.
        labels = [x for y in [[i]*composition[i] for i in range(len(composition))] for x in y]
        return [
            labelling
            for labelling in _mu_labellings(blocks, labels)
            if not (
                (
                    self.length > 0
                    and self.area_word()[0] == 0
                    and labelling[0] == 0
                )
                or (
                    len(
                        [
                            i
                            for i in range(self.height)
                            if self.area_word()[i] == -self.shift
                            and labelling[i] > 0
                            and i not in self.valleys
                        ]
                    )
                    == 0
                )
            )
        ]

    def characteristic_function(self):
        # Returns the characteristic function of the path, computed in terms of d+ d- operators.

        # if self.labels is not None or self.rises != [] or self.valleys != []:
        #     raise NotImplementedError('The characteristic function can only be computed for plain paths')

        return characteristic_function(self)

    def word(self):

        def is_under(i, j):
            assert 0 <= i <= self.width and 0 <= j <= self.height

            if j == 0:
                return i <= self.shift
            elif self.columns()[j-1] <= i <= self.main_diagonal()[j] + self.shift:
                return True
            else:
                return False

        collisions = [(i, j) for i in range(self.width+1) for j in range(self.height+1) if is_under(i, j)]
        collisions = sorted(collisions, key=lambda c: (self.rank(*c), c[1]), reverse=True)

        level = 0
        word = []

        for c in collisions:
            # if c == (0, 0):
            #     pass
            if c == (self.width, self.height):
                pass
            elif c[1] < self.height and self.columns()[c[1]] < c[0]:
                pass
            elif self.path[c[0]+c[1]-1] == 1 and self.path[c[0]+c[1]] == 0:
                word += ['d+']
            elif self.path[c[0]+c[1]-1] == 0 and self.path[c[0]+c[1]] == 1:
                word += ['d-']
            elif self.path[c[0]+c[1]-1] == 1 and self.path[c[0]+c[1]] == 1:
                word += ['[]']
            elif self.path[c[0]+c[1]-1] == 0 and self.path[c[0]+c[1]] == 0:
                pass
            else:
                raise ValueError('Something went wrong here.')

        return word[::-1]

    @cached_method
    def area_word(self):
        # Returns the area word of the path.

        return [self.main_diagonal()[i]-self.columns()[i] for i in range(self.height)]

    @cached_method
    def main_diagonal(self):
        # Returns x-coordinates of the y-integer points of the main diagonal (not the base diagonal).

        main_diagonal = [0]
        position = 0
        # block_height = 1

        for i in range(self.height):
            position += 1 if (i in self.rises or i in self.valleys) else self.slope
            main_diagonal += [position]

            # # This code changes the slope in each streak of decorated rises.
            # if i+1 in self.rises:
            #     block_height += 1
            # else:
            #     main_diagonal += [position+Rational((block_height+self.slope-1)*(i+1)/block_height)
            #                       for i in range(block_height)]
            #     position += block_height-1+self.slope
            #     block_height = 1

        return main_diagonal

    @cached_method
    def columns(self):
        # Returns the index of the column (numbered starting from 0) containing the label with index i.

        columns = []
        position = 0

        for i in self.path:
            if i == 1:
                columns += [position]
            else:
                position += 1

        return columns

    def ferrer(self):
        # Returns the (English) Ferrer diagram above the path, as partition.
        return Partition(self.columns()[::-1])

    def area(self):
        return sum(
            floor(self.area_word()[i] + self.shift)
            for i in range(self.height)
            if i not in self.rises
        )

    def dinv(self):
        # Returns the dinv. If the path is labelled, it takes the labelling into account.
        # Currently works for any rectangular path with no decorated rises, and any square path.
        # TODO: It does not work for any rectangular path with decorated rises.
        # TODO: It does not allow for decorated contractible valleys.

        temp_dinv = sum(
            len(
                [
                    j
                    for j in range(self.height)
                    if (
                        (self.labels is None or self.labels[i] < self.labels[j])
                        and (
                            (self.area_word()[i], i)
                            < (self.area_word()[j], j)
                            < (
                                self.area_word()[i]
                                + (1 if i in self.rises else self.slope),
                                i,
                            )
                        )
                    )
                ]
            )
            for i in range(self.height)
        )

        # max_dinv = 0
        # for i in range(self.height):
        #     max_dinv += len([j for j in range(self.height) if (
        #         (self.area_word()[i], i) < (self.area_word()[j], j) < (
        #             self.area_word()[i] + (1 if i in self.rises else self.slope), i)
        #     )])

        # alt_ferrer_dinv = 0
        # ferrer = self.ferrer()

        # for c in ferrer.cells():
        #     if (self.height*ferrer.arm_length(*c) <= self.width*(ferrer.leg_length(*c)+1)
        #             and self.width*ferrer.leg_length(*c) < self.height*(ferrer.arm_length(*c)+1)):
        #         alt_ferrer_dinv += 1

        ferrer_dinv = 0
        ferrer = self.ferrer()

        for c in ferrer.cells():
            if (self.height*(ferrer.arm_length(*c)+1) <= self.width*(ferrer.leg_length(*c)+1)
                    and self.width*ferrer.leg_length(*c) < self.height*ferrer.arm_length(*c)):
                ferrer_dinv += 1

            if (self.height*ferrer.arm_length(*c) <= self.width*ferrer.leg_length(*c)
                    and self.width*(ferrer.leg_length(*c)+1) < self.height*(ferrer.arm_length(*c)+1)):
                ferrer_dinv -= 1

        bonus_dinv = len([i for i in range(self.height) if self.area_word()[i] < 0
                          and (self.labels is None or self.labels[i] > 0)])

        # alt_bonus_dinv = 0
        # area_coordinate = 0
        # for i in self.path:
        #     if i == 1:
        #         area_coordinate += self.slope
        #     else:
        #         area_coordinate -= 1
        #         if area_coordinate < 0:
        #             alt_bonus_dinv += 1

        # print(temp_dinv, max_dinv, alt_ferrer_dinv, alt_bonus_dinv)

        # return temp_dinv - max_dinv + alt_ferrer_dinv + alt_bonus_dinv
        return temp_dinv + ferrer_dinv + bonus_dinv

    def zero(self):
        return 0

    def rank(self, i, j):
        return self.main_diagonal()[j]-i

    def diagonal_composition(self):
        zeros = [i for i in range(self.height) if self.area_word()[i] == - self.shift] + [self.height]
        return [zeros[i+1] - zeros[i] for i in range(len(zeros)-1)]

    def diagonal_word(self):
        # Returns the word obtained by sorting the diagonals in decreasing order, bottom to top.
        return [self.labels[i] for i in sorted(list(range(self.height)),
                                               key=lambda i: (self.area_word()[i], self.labels[i]))]

    def diagonals(self):
        # Computes the list whose entries are the labels appearing in each diagonal, bottom to top.

        if self.labels is None:
            raise AttributeError('The path is not labelled.')
            
        step = int(self.height/gcd(self.width, self.height))
        diagonals = [[]]*int((self.shift + max(self.area_word()))*step + 1)

        for i in range(self.height):
            diagonals[(self.area_word()[i] + self.shift)*step] = diagonals[(self.area_word()[i] +
                                                                            self.shift)*step] + [self.labels[i]]

        return [sorted(d) for d in diagonals]

    def zeta(self):
        # https://www.combinatorics.org/ojs/index.php/eljc/article/view/v24i1p64

        # Sweeps the steps of the path according to the distance from the main diagonal of their ending point.
        # In case of a tie, the leftmost step is sweeped first. The path is then reversed.

        if self.labels is not None or self.rises != [] or self.valleys != []:
            raise NotImplementedError('The zeta map can only be computed for plain paths')

        def rank(x, y):
            # Gives the rank of the cell with cartesian coordinates (x,y).
            # https://arxiv.org/abs/1501.00631 p.19

            # return y*self.width - x*self.height + (x*gcd(self.width, self.height) // self.width)
            return (y*self.width - x*self.height, y)

        path = [self[i] for i in sorted(range(len(self)),
                                        key=lambda j: (rank(j+1-sum(self[:j+1]), sum(self[:j+1]))))]

        return self.__class__(self._auto_parent, path[::-1])

    def reading_word(self, read=None):
        # Computes the reading word of a path

        if read is None:
            read = 'diagonal'

        if read == 'diagonal':
            # Reading word according to the dinv statistic,
            # i.e. along diagonals, left to right, bottom to top.
            return [self.labels[i] for i in sorted(list(range(self.height)),
                                                   key=lambda i: (self.area_word()[i], i))]
        elif read == 'vertical':
            # Reading word according to the pmaj statistic, i.e. along columns, bottom to top.
            return self.labels
        else:
            raise ValueError('Reading order not recognised')

    def gessel(self, read=None):
        ls = Permutation([i for i in self.reading_word(read)[::-1] if i > 0], check_input=True)
        return Composition(from_subset=(ls.idescents(), len(ls)))

    def set_latex_options(self, options):
        for option in options:
            self._latex_options[option] = options[option]

    def latex_options(self):

        path_latex_options = self._latex_options.copy()
        if 'bounce path' not in path_latex_options:
            path_latex_options['bounce path'] = self.parent().options.latex_bounce_path
        if 'colour' not in path_latex_options:
            path_latex_options['colour'] = self.parent().options.latex_colour
        if 'diagonal' not in path_latex_options:
            path_latex_options['diagonal'] = self.parent().options.latex_diagonal
        if 'tikz_scale' not in path_latex_options:
            path_latex_options['tikz_scale'] = self.parent().options.latex_tikz_scale
        if 'line width' not in path_latex_options:
            path_latex_options['line width'] = self.parent().options.latex_line_width * \
                path_latex_options['tikz_scale']
        if 'show_stats' not in path_latex_options:
            path_latex_options['show_stats'] = self.parent().options.latex_show_stats
        if 'qstat' not in path_latex_options:
            path_latex_options['qstat'] = self.parent().options.latex_qstat
        if 'tstat' not in path_latex_options:
            path_latex_options['tstat'] = self.parent().options.latex_tstat
        return path_latex_options

    def _latex_(self):

        latex.add_package_to_preamble_if_available('tikz')
        latex_options = self.latex_options()
        colour = latex_options['colour']
        line_width = latex_options['line width']
        scale = latex_options['tikz_scale']

        tikz = '\n'
        tikz += f'\\begin{{tikzpicture}}[scale={scale}]\n'
        tikz += f'    \\draw[draw=none, use as bounding box] (-1,-1) rectangle ({self.width+1},{self.height+1});\n'
        tikz += f'    \\draw[step=1.0, gray!60, thin] (0,0) grid ({self.width},{self.height});\n\n'

        if latex_options['diagonal'] == True:
            tikz += '    \\begin{scope}\n'
            tikz += f'        \\clip (0,0) rectangle ({self.width},{self.height});\n'

            tikz += f'        \\draw[gray!60, thin] (0,0)'

            for i in range(self.height+1):
                x = Rational(self.main_diagonal()[i] + self.shift)
                tikz += f' -- ({x.numerator()}/{x.denominator()}, {i})'

            tikz += ';\n'
            tikz += '    \\end{scope}\n\n'

        tikz += f'    \\draw[{colour}, line width={line_width}pt] (0,0)'
        labels = ''
        rises = ''
        valleys = ''

        x = y = 0
        for i in self.path:
            if i == 1 and self.labels is not None:
                labels += f'    \\draw ({x+0.5:.1f},{y+0.5:.1f}) circle (0.4cm) node {{${self.labels[y]}$}};\n'
            x += 1 - i
            y += i
            tikz += f' -- ({x},{y})'
        tikz += ';\n\n'

        for i in self.rises:
            rises += '    \\draw (%.1f,%.1f) node {$\\ast$};\n' % (
                [sum(self.path[:j]) for j in range(self.length)].index(i)-i-0.5, i+0.5)

        for i in self.valleys:
            valleys += '    \\draw (%.1f,%.1f) node {$\\bullet$};\n' % (
                [sum(self.path[:j]) for j in range(self.length)].index(i+1)-(i+1)-0.5, (i+1)-0.5)

        if latex_options['show_stats'] == True:
            stats = '\n'
            stats += '      \\node[below left] at (%d,0) {' % (self.width)

            colour = 0
            colours = ['blue', 'red', 'green']

            for stat in [repr(latex_options['qstat']), repr(latex_options['tstat'])]:
                stats += ' \\color{%s}{$%d$}' % (colours[colour % 3], getattr(self, stat)())
                colour += 1
            stats += '};\n'

        return (tikz + labels + rises + valleys + stats + '\\end{tikzpicture}')


class RectangularPath(LatticePath):

    @ staticmethod
    def __classcall_private__(cls, *args, **kwargs):
        return cls._auto_parent._element_constructor_(*args, **kwargs)

    def check(self):
        pass


class RectangularDyckPath(RectangularPath):

    @ staticmethod
    def __classcall_private__(cls, *args, **kwargs):
        return cls._auto_parent._element_constructor_(*args, **kwargs)

    def check(self):
        if not (self.shift == 0):
            raise ValueError(f'The path\'s shift is not 0')


class SquarePath(RectangularPath):

    @ staticmethod
    def __classcall_private__(cls, *args, **kwargs):
        return cls._auto_parent._element_constructor_(*args, **kwargs)

    def check(self):
        if not self.width == self.height:
            raise ValueError('Height and width are not the same')

    def dinv(self):
        dinv = 0  # Initializes dinv to 0.

        # Goes through the letters of the area word.
        for i in range(self.height):
            if self.area_word()[i] < 0:  # Bonus dinv
                if self.labels is None or self.labels[i] > 0:
                    dinv += 1
            if i not in self.valleys:  # Skip decorated valleys
                for j in range(i+1, self.height):  # Looks at the right.
                    if self.area_word()[j] == self.area_word()[i]-1:  # Secondary dinv
                        # Checks labels
                        if self.labels is None or self.labels[j] < self.labels[i]:
                            dinv += 1
                for j in range(i+1, self.height):
                    if self.area_word()[j] == self.area_word()[i]:  # Primary dinv
                        # Checks labels
                        if self.labels is None or self.labels[j] > self.labels[i]:
                            dinv += 1
            else:  # Subtract 1 for each decorated valley
                dinv += -1

        return dinv


class DyckPath(SquarePath, RectangularDyckPath):

    @ staticmethod
    def __classcall_private__(cls, *args, **kwargs):
        return cls._auto_parent._element_constructor_(*args, **kwargs)

    def check(self):
        pass

    def parking_word(self):
        # Returns the parking word of the path, i.e. the word whose descent set of the inverse gives the pmaj.
        if self.labels is None:
            labels = [x+1 for x in range(self.length)]
        else:
            labels = self.labels

        stack = Multiset()  # stack is the (multi)set of unused labels.
        parking_word = []  # Initializes the parking word to an empty string.

        adjusted_columns = self.columns()
        for v in self.valleys[::-1]:
            column = adjusted_columns[v]
            for i in range(self.height):
                if column <= adjusted_columns[i] <= column + self.area_word()[v]:
                    adjusted_columns[i] -= 1

        for i in range(self.width):
            # We add the labels in the i-th column to the stack.
            stack += Multiset([self.labels[j] for j in range(self.height) if adjusted_columns[j] == i])

            while((len(parking_word)+1)*self.width <= (i+1)*self.height):
                # We add to the parking word as many labels as the slope permits.

                if parking_word == [] or (stack & set(range(parking_word[-1]+1)) == set()):
                    # If there is no unused label that is smaller than the last one,
                    # we take the biggest label available.
                    u = max(stack)
                else:
                    # Otherwise, we take the highest unused label smaller than the last one.
                    u = max(stack & set(range(parking_word[-1]+1)))

                # We add the label to the parking word, and remove it from the unused labels.
                parking_word += [u]
                stack -= {u}

        return parking_word

    def pmaj(self):
        return sum(i for i in range(1, self.height) if self.parking_word()[-i] > self.parking_word()[-i-1])


class LatticePathsFactory(SetFactory):
    Element = LatticePath

    def __call__(self, width=None, height=None, shift=None, square=False, labelled=True, labels=None, decorated_rises=0, decorated_valleys=0, policy=None):

        if policy is None:
            policy = self._default_policy

        options = {
            'labelled': labelled,
            'labels': None if labels is None else tuple(labels),
            'decorated_rises': decorated_rises,
            'decorated_valleys': decorated_valleys,
        }

        if isinstance(width, (Integer, int)):
            if height is None or height == width:
                height = width
            elif square is True:
                raise ValueError('The paths are not square paths')

            if isinstance(shift, (Rational, Integer, int)):
                return RectangularPaths_size_shift_redirect(policy, width, height, shift, **options)
            elif height == width:
                return SquarePaths_size(policy, width, **options)
            else:
                return RectangularPaths_size(policy, width, height, **options)

        elif width is None:
            if height is not None:
                raise ValueError('Must specify width if height is set')
            if square is True:
                if shift == 0:
                    return DyckPaths_all(policy, **options)
                elif shift is None:
                    return SquarePaths_all(policy, **options)
                else:
                    raise ValueError('Can only set shift to 0 if the size is not specified')
            else:
                if shift == 0:
                    return RectangularDyckPaths_all(policy, **options)
                elif shift is None:
                    return RectangularPaths_all(policy, **options)
                else:
                    raise ValueError('Can only set shift to 0 if the size is not specified')
        else:
            raise ValueError(f'Invalid size (={width})')

        raise ValueError('If you\'re seeing this, something went horribly wrong')

    def add_constraints(self, constraints, options):

        constraints = _format_constraints(constraints, reverse=True)
        defaults = _format_constraints((), reverse=True)
        keys = defaults.keys()
        args, kwargs = options

        for i, arg in enumerate(args):
            if arg != defaults[keys[i]] and arg != constraints[keys[i]]:
                constraints[keys[i]] = arg

        for i, key in enumerate(defaults):
            if key in kwargs and kwargs[key] != defaults[key] and kwargs[key] != constraints[key]:
                constraints[key] = kwargs[key]

        return [constraints[key] for key in keys]

    @ lazy_attribute
    def _default_policy(self):
        return SelfParentPolicy(self, self.Element)


LatticePaths = LatticePathsFactory()
LatticePaths.__doc__ = LatticePathsFactory.__call__.__doc__


def RectangularPaths(*args, **kwargs):
    options = _format_constraints((args, kwargs))
    return LatticePaths(*options)


def RectangularDyckPaths(*args, **kwargs):
    options = _format_constraints((args, {**kwargs, 'shift': 0}))
    return LatticePaths(*options)


def SquarePaths(*args, **kwargs):
    options = _format_constraints((args, {**kwargs, 'square': True}))
    return LatticePaths(*options)


def DyckPaths(*args, **kwargs):
    options = _format_constraints((args, {**kwargs, 'shift': 0, 'square': True}))
    return LatticePaths(*options)


class RectangularPaths_all(ParentWithSetFactory, DisjointUnionEnumeratedSets):

    def __init__(self, policy, **kwargs):
        self._kwargs = kwargs
        ParentWithSetFactory.__init__(
            self, _format_constraints(((), kwargs)), policy, category=FiniteEnumeratedSets()
        )
        DisjointUnionEnumeratedSets.__init__(
            self, Family(
                EnumeratedSetFromIterator(cantor_product,
                                          ([PositiveIntegers(), PositiveIntegers()]),
                                          category=InfiniteEnumeratedSets(),
                                          ),
                lambda c: RectangularPaths_size(
                    policy=self.facade_policy(), width=c[0], height=c[1], **kwargs
                )
            ),
            facade=True, keepkey=False, category=self.category()
        )

    def __repr__(self):
        return 'Rectangular Paths'

    def check_element(self, element, check=True):
        return True

    # add options to class
    class options(GlobalOptions):
        r'''
        Set and display the options for Lattice Paths. If no parameters
        are set, then the function returns a copy of the options dictionary.

        The ``options`` to Lattice Paths can be accessed as the method
        :meth:`LatticePaths.options` of :class:`LatticePaths` and
        related parent classes.
        '''

        NAME = 'LatticePaths'
        module = 'shuffle_theorem'
        latex_tikz_scale = dict(default=1,
                                description='The default value for the tikz scale when latexed.',
                                checker=lambda x: True)  # More trouble than it's worth to check
        latex_diagonal = dict(default=True,
                              description='The default value for displaying the diagonal when latexed.',
                              checker=lambda x: isinstance(x, bool))
        latex_line_width = dict(default=2,
                                description='The default value for the line width as a '
                                'multiple of the tikz scale when latexed.',
                                checker=lambda x: True)  # More trouble than it's worth to check
        latex_colour = dict(default='blue!60',
                            description='The default value for the colour when latexed.',
                            checker=lambda x: isinstance(x, str))
        latex_bounce_path = dict(default=False,
                                 description='The default value for displaying the bounce path when latexed.',
                                 checker=lambda x: isinstance(x, bool))
        latex_show_stats = dict(default=True,
                                description='The default value for displaying the statistics when latexed.',
                                checker=lambda x: isinstance(x, bool))
        latex_qstat = dict(default='qstat',
                           description='The default statistics will depend on the class.',
                           checker=lambda x: isinstance(x, str))
        latex_tstat = dict(default='tstat',
                           description='The default statistics will depend on the class.',
                           checker=lambda x: isinstance(x, str))


class RectangularDyckPaths_all(RectangularPaths_all):

    def __init__(self, policy, **kwargs):
        self._kwargs = kwargs

        ParentWithSetFactory.__init__(
            self, _format_constraints(((), {**kwargs, 'shift': 0})), policy, category=FiniteEnumeratedSets()
        )
        DisjointUnionEnumeratedSets.__init__(
            self, Family(
                EnumeratedSetFromIterator(cantor_product,
                                          ([PositiveIntegers(), PositiveIntegers()]),
                                          category=InfiniteEnumeratedSets(),
                                          ),
                lambda c: _paths_size_shift(self.facade_policy(), c[0], c[1], 0, **kwargs)
            ),
            facade=True, keepkey=False, category=self.category()
        )

    def __repr__(self):
        return f'Rectangular Dyck Paths'

    def check_element(self, element, check=True):
        return True


class SquarePaths_all(RectangularPaths_all):

    def __init__(self, policy, **kwargs):
        self._kwargs = kwargs

        ParentWithSetFactory.__init__(
            self, _format_constraints(((), {**kwargs, 'square': True})), policy, category=FiniteEnumeratedSets()
        )
        DisjointUnionEnumeratedSets.__init__(
            self, Family(
                PositiveIntegers(),
                lambda size: SquarePaths_size(
                    policy=self.facade_policy(), size=size, **kwargs
                )
            ),
            facade=True, keepkey=False, category=self.category()
        )

    def __repr__(self):
        return 'Square Paths'

    def check_element(self, element, check=True):
        return True


class DyckPaths_all(SquarePaths_all, RectangularDyckPaths_all):

    def __init__(self, policy, **kwargs):
        self._kwargs = kwargs

        ParentWithSetFactory.__init__(
            self, _format_constraints(((), {**kwargs, 'square': True, 'shift': 0})), policy, category=FiniteEnumeratedSets()
        )
        DisjointUnionEnumeratedSets.__init__(
            self, Family(
                PositiveIntegers(),
                lambda size: _paths_size_shift(self.facade_policy(), size, size, 0, **kwargs)
            ),
            facade=True, keepkey=False, category=self.category()
        )

    def __repr__(self):
        return 'Dyck Paths'

    def check_element(self, element, check=True):
        return True


class RectangularPaths_size(ParentWithSetFactory, DisjointUnionEnumeratedSets):

    def __init__(self, policy, width, height, **kwargs):
        self._width = width
        self._height = height
        self._kwargs = kwargs

        if self._width == self._height:
            square = True
        else:
            square = False

        adjusted_height = height

        if 'decorated rises' in kwargs:
            adjusted_height -= kwargs['decorated_rises']
        if 'decorated_valleys' in kwargs:
            adjusted_height -= kwargs['decorated_valleys']

        ParentWithSetFactory.__init__(
            self, _format_constraints(((), {**kwargs, 'height': height, 'width': width, 'square': square})), policy, category=FiniteEnumeratedSets()
        )
        DisjointUnionEnumeratedSets.__init__(
            self, Family(
                [Rational(i/adjusted_height) for i in range((width-1)*adjusted_height+1)],
                lambda shift: _paths_size_shift(self.facade_policy(), width, height, shift, **kwargs)
            ),
            facade=True, keepkey=False, category=self.category()
        )

    def __repr__(self):
        return f'Rectangular Paths of size {self._width, self._height}'

    def check_element(self, element, check=True):
        return True


class SquarePaths_size(RectangularPaths_size):

    def __init__(self, policy, size, **kwargs):
        super().__init__(policy, size, size, **kwargs)

    def __repr__(self):
        return f'Square paths of size {self._width}'


class RectangularPaths_size_shift_redirect(ParentWithSetFactory, DisjointUnionEnumeratedSets):

    def __init__(self, policy, width, height, shift, **kwargs):

        self._width = width
        self._height = height
        self._shift = shift
        self._kwargs = kwargs

        if width == height:
            square = True
        else:
            square = False

        ParentWithSetFactory.__init__(
            self, _format_constraints(((), {**kwargs, 'width': width, 'height': height, 'shift': shift, 'square': square})), policy, category=FiniteEnumeratedSets()
        )
        DisjointUnionEnumeratedSets.__init__(
            self, Family(
                [x for x in range(1)],
                lambda x: _paths_size_shift(self.facade_policy(), width, height, shift, **kwargs)
            ),
            facade=True, keepkey=False, category=self.category()
        )

    def __repr__(self):
        if self._height == self._width:
            if self._shift == 0:
                return f'Dyck paths of size {self._width}'
            else:
                return f'Square paths of size {self._width} with shift {self._shift}'
        else:
            if self._shift == 0:
                return f'Rectangular Dyck paths of size {self._width}'
            else:
                return f'Rectangular paths of size {self._width} with shift {self._shift}'


class RectangularPaths_size_shift(ParentWithSetFactory, UniqueRepresentation):
    Element = RectangularPath

    def __init__(self, policy, width, height, shift, **kwargs):
        self._width = width
        self._height = height
        self._shift = shift
        self._kwargs = kwargs

        if self._width == self._height:
            square = True
        else:
            square = False

        ParentWithSetFactory.__init__(
            self, _format_constraints(((), {**kwargs, 'height': height, 'width': width, 'shift': shift, 'square': square})), policy, category=FiniteEnumeratedSets()
        )

    def __repr__(self):
        return f'Rectangular Paths of size {self._width, self._height} with shift {self._shift}'

    def an_element(self):
        return next(self.__iter__())

    def __iter__(self):
        for x in _lattice_paths(self._width, self._height, shift=self._shift, **self._kwargs):
            yield self.element_class(self, *x)

    # add options to class
    class options(GlobalOptions):
        r'''
        Set and display the options for Lattice Paths. If no parameters
        are set, then the function returns a copy of the options dictionary.

        The ``options`` to Lattice Paths can be accessed as the method
        :meth:`LatticePaths.options` of :class:`LatticePaths` and
        related parent classes.
        '''

        NAME = 'LatticePaths'
        module = 'shuffle_theorem'
        latex_tikz_scale = dict(default=1,
                                description='The default value for the tikz scale when latexed.',
                                checker=lambda x: True)  # More trouble than it's worth to check
        latex_diagonal = dict(default=True,
                              description='The default value for displaying the diagonal when latexed.',
                              checker=lambda x: isinstance(x, bool))
        latex_line_width = dict(default=2,
                                description='The default value for the line width as a '
                                'multiple of the tikz scale when latexed.',
                                checker=lambda x: True)  # More trouble than it's worth to check
        latex_colour = dict(default='blue!60',
                            description='The default value for the colour when latexed.',
                            checker=lambda x: isinstance(x, str))
        latex_bounce_path = dict(default=False,
                                 description='The default value for displaying the bounce path when latexed.',
                                 checker=lambda x: isinstance(x, bool))
        latex_show_stats = dict(default=True,
                                description='The default value for displaying the statistics when latexed.',
                                checker=lambda x: isinstance(x, bool))
        latex_qstat = dict(default='qstat',
                           description='The default statistics will depend on the class.',
                           checker=lambda x: isinstance(x, str))
        latex_tstat = dict(default='tstat',
                           description='The default statistics will depend on the class.',
                           checker=lambda x: isinstance(x, str))


class RectangularDyckPaths_size(RectangularPaths_size_shift):
    Element = RectangularDyckPath

    def __init__(self, policy, width, height, **kwargs):
        super().__init__(policy, width, height, 0, **kwargs)

    def __repr__(self):
        return f'Rectangular Dyck paths of size {self._width, self._height}'


class SquarePaths_size_shift(RectangularPaths_size_shift):
    Element = SquarePath

    def __init__(self, policy, size, shift, **kwargs):
        super().__init__(policy, size, size, shift, **kwargs)

    def __repr__(self):
        return f'Square paths of size {self._width} with shift {self._shift}'


class DyckPaths_size(SquarePaths_size_shift):
    Element = DyckPath

    def __init__(self, policy, size, **kwargs):
        super().__init__(policy, size, 0, **kwargs)

    def __repr__(self):
        return f'Dyck paths of size {self._width}'
