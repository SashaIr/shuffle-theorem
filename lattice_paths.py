'''
SageMath module.
Tools for the shuffle theorem and variants.
'''

# TODO: Write documentation!

from itertools import combinations
from more_itertools import distinct_combinations
from multiset import Multiset

from sage.arith.misc import gcd
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.combinat.composition import Composition
from sage.combinat.partition import Partition
from sage.combinat.permutation import Permutation
from sage.functions.other import floor
from sage.misc.all import cached_method
from sage.misc.latex import latex
from sage.rings.all import Rational, ZZ
from sage.structure.all import Parent
from sage.structure.list_clone import ClonableIntArray  # type: ignore
from sage.structure.global_options import GlobalOptions
from sage.structure.unique_representation import UniqueRepresentation

from shuffle_theorem.symmetric_functions import characteristic_function


def _generate_lattice_paths(m, n, dyck=True, rises=[], valleys=[], _shift=0, _slope=None, _going_up=False):
    '''
    Builds all the lattice paths from (0,0) to (m,n), as generator,
    where a path is a 0-1 sequence where 0 denotes an east step, 1 denotes a north step.

    If dyck is set to True, it will only build the paths that lie wealky above the main diagonal,
    otherwise it will build all the paths ending east.

    The paths will have rises and valleys in the specified rows.

    The variables _shift, _slope, and _going_up are internal.
    '''

    if n == 0:
        yield [0]*m
    elif m == 0:
        pass
    else:
        if _slope is None:

            m1 = m-len(rises)-len(valleys)
            n1 = n-len(rises)-len(valleys)

            if m1 <= 0 or n1 <= 0:
                raise ValueError('Too many rises and valleys.')

            _slope = Rational(m1/n1)

        if 0 in rises:
            if _going_up == True:
                for p in _generate_lattice_paths(
                        m,
                        n-1,
                        dyck=dyck,
                        rises=[i-1 for i in rises[1:]],
                        valleys=[i-1 for i in valleys],
                        _shift=_shift+1,
                        _slope=_slope,
                        _going_up=True):
                    yield [1] + p
            else:
                pass

        elif 0 not in rises:
            if _shift >= 1 or dyck == False:
                for p in _generate_lattice_paths(
                        m-1, n,
                        dyck=dyck,
                        rises=rises,
                        valleys=valleys,
                        _shift=_shift-1,
                        _slope=_slope,
                        _going_up=False):
                    yield [0] + p

            if 0 in valleys and _going_up == False:
                for p in _generate_lattice_paths(
                        m,
                        n-1,
                        dyck=dyck,
                        rises=[i-1 for i in rises],
                        valleys=[i-1 for i in valleys[1:]],
                        _shift=_shift+1,
                        _slope=_slope,
                        _going_up=True):
                    yield [1] + p

        if 0 not in rises and 0 not in valleys:

            for p in _generate_lattice_paths(
                    m, n-1,
                    dyck=dyck,
                    rises=[i-1 for i in rises],
                    valleys=[i-1 for i in valleys],
                    _shift=_shift+_slope,
                    _slope=_slope,
                    _going_up=True):
                yield [1] + p


def _lattice_paths(width, height=None, dyck=True, labelled=True, labels=None, drises=0, dvalleys=0):

    if height is None or width == height:
        # If no value is specified, the grid is assumed to be a square.
        height = width
        if dyck is True:
            item_class = DyckPath
            parent = DyckPaths()
        else:
            item_class = SquarePath
            parent = SquarePaths()
    else:
        if dyck is True:
            item_class = RectangularDyckPath
            parent = RectangularDyckPaths()
        else:
            item_class = RectangularPath
            parent = RectangularPaths()

    # Sets the deafult set of labels to [n].
    if labels is None:
        labels = [0] + [1]*(height)

    for r in combinations(range(1, height), drises):
        for v in combinations([i for i in range(height) if i not in r], dvalleys):
            for path in _generate_lattice_paths(width, height, rises=r, valleys=v, dyck=dyck):
                if labelled is False:
                    yield item_class(parent, path, rises=r, valleys=v)
                else:
                    for l in LatticePath(LatticePaths(), path, rises=r, valleys=v).labellings(labels):
                        yield item_class(parent, path, labels=l, rises=r, valleys=v)


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


class LatticePath(ClonableIntArray):

    def __init__(self, parent, path, labels=None, rises=[], valleys=[], latex_options={}):

        super().__init__(parent, path)

        # It's the actual path, stored as a string of 0's (east steps) and 1's (north steps)
        self.path = path

        # It's the list of the labels of the path, to read bottom to top. Default is None.
        self.labels = labels

        # These are the indices of the decorated rises and decorated valleys.
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

    def check(self):
        pass
        # if not (isinstance(self.path, list) and all(x in [0, 1] for x in self.path)):
        #     raise ValueError(f'Invalid path (= {self.path}), entries must be 0 and 1.')

        # if not self.valleys == []:
        #     raise ValueError('Decorated valleys are only supported for square paths.')

    def __len__(self):
        return len(self.path)

    def __getitem__(self, index):
        return self.path[index]

    def __repr__(self):
        representation = f'{self.__class__.__name__}({self.path}'
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

        if not self.height == sum(composition):
            raise ValueError('The number of labels does not match the size of the path.')

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
        labellings = [labelling for labelling in _mu_labellings(blocks, labels) if not (
            (self.length > 0 and self.area_word()[0] == 0 and labelling[0] == 0)
            or (len([i for i in range(self.height) if self.area_word()[i] == -self.shift and labelling[i] > 0 and i not in self.valleys]) == 0)
        )]

        return labellings

    @cached_method
    def area_word(self):
        # Returns the area word of the path.

        return [self.main_diagonal()[i]-self.columns()[i] for i in range(self.height)]

        # # This was more efficient without caching, but now it isn't.
        # area_word = []  # Initializes the area word to an empty string.
        # level = 0  # Sets starting level to 0.
        # height = 0  # Sets starting height to 0.

        # for i in self.path:
        #     if i == 1:  # If the Dyck path has a vertical step, it adds a letter to the area word, and then goes up a level.
        #         area_word += [level]
        #         level += 1 if (height in self.rises or height in self.valleys) else self.slope
        #         height += 1
        #     else:  # If the Dyck path has a horizontal step, it goes down a level.
        #         level -= 1

        # return area_word

    @cached_method
    def main_diagonal(self):
        # Returns x-coordinates of the y-integer points of the main diagonal (not the base diagonal).

        main_diagonal = [0]
        position = 0

        for i in range(self.height):
            position += 1 if (i in self.rises or i in self.valleys) else self.slope
            main_diagonal += [position]

        return main_diagonal

    @cached_method
    def columns(self):
        # Returns the index of the column (numbered starting from 0) containing the label with index i.
        # Returns x-coordinates of the y-integer points of the main diagonal (not the base diagonal).

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
        # Returns the area. Ignores rows with decorated rises.
        area = sum(floor(self.area_word()[i] + self.shift) for i in range(self.height) if i not in self.rises)
        return area

    def dinv(self):
        # Returns the dinv. If the path is labelled, it takes the labelling into account.
        # Currently works for any rectangular path with no decorated rises, and any square path.
        # TODO: It does not work for any rectangular path with decorated rises.
        # TODO: It does not allow for decorated contractible valleys.

        temp_dinv = 0
        for i in range(self.height):
            temp_dinv += len([j for j in range(self.height) if (
                (self.labels is None or self.labels[i] < self.labels[j]) and (
                    (self.area_word()[i] == self.area_word()[j] and i < j)
                    or (i+1 not in self.rises
                        and self.area_word()[i] < self.area_word()[j] < self.area_word()[i] + self.slope)
                    or (i+1 in self.rises
                        and self.area_word()[i] < self.area_word()[j] < self.area_word()[i] + 1)
                ))])

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

        return temp_dinv + ferrer_dinv + bonus_dinv

    def zero(self):
        return 0

    def diagonal_word(self):
        # Returns the word obtained by sorting the diagonals in decreasing order, bottom to top.
        return [self.labels[i] for i in sorted(list(range(self.height)),
                                               key=lambda i: (self.area_word()[i], self.labels[i]))]

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
            raise ValueError('Reading order not recognised.')

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
                labels += f'    \\draw ({x+0.5:+.1f},{y+0.5:+.1f}) circle (0.4cm) node {{${self.labels[y]}$}};'
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

        return (tikz + labels + rises + valleys + '\\end{tikzpicture}')


class RectangularPath(LatticePath):
    def check(self):
        pass


class RectangularDyckPath(RectangularPath):

    def check(self):
        pass
        # if not (self.shift == 0):
        #     raise ValueError(f'The path\'s shift is not 0.')

    def characteristic_function(self):
        # Returns the characteristic function of the path, computed in terms of d+ d- operators.

        if self.labels is not None or self.rises != [] or self.valleys != []:
            raise NotImplementedError('The characteristic function can only be computed for plain paths.')

        return characteristic_function(self)

    def zeta(self):
        # https://www.combinatorics.org/ojs/index.php/eljc/article/view/v24i1p64

        # Sweeps the steps of the path according to the distance from the main diagonal of their ending point.
        # In case of a tie, the leftmost step is sweeped first. The path is then reversed.

        if self.labels is not None or self.rises != [] or self.valleys != []:
            raise NotImplementedError('The zeta map can only be computed for plain paths.')

        def rank(x, y):
            # Gives the rank of the cell with cartesian coordinates (x,y).
            # https://arxiv.org/abs/1501.00631 p.19

            return y*self.width - x*self.height + (x*gcd(self.width, self.height) // self.width)

        path = [self[i] for i in sorted(range(len(self)),
                                        key=lambda j: (rank(j+1-sum(self[:j+1]), sum(self[:j+1]))))]

        return self.__class__(path[::-1])


class SquarePath(RectangularPath):
    def check(self):
        pass

    def dinv(self):
        dinv = 0  # Initializes dinv to 0.

        # Goes through the letters of the area word.
        for i in range(self.height):
            if self.area_word()[i] < 0:  # Bonus dinv
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
    def check(self):
        pass


class LatticePaths(UniqueRepresentation, Parent):

    @ staticmethod
    def __classcall_private__(cls, width=None, height=None, labelled=True, labels=None,
                              dyck=False, square=False, decorated_rises=0, decorated_valleys=0,
                              latex_options={}):
        '''
        Choose the correct parent
        '''

        if labels is not None:
            if labelled is False:
                raise ValueError('Cannot use the specified labels composition if labelling is False.')
            elif ((height is not None and len(labels) != height)
                  or (height is None and width is not None and len(labels) != width)):
                raise ValueError('The cardinality of the set of labels does not match the path\'s height.')

        if height is None and width is None:
            return LatticePaths_all(dyck=dyck,
                                    square=square,
                                    labelled=labelled,
                                    decorated_rises=decorated_rises,
                                    decorated_valleys=decorated_valleys)

        elif height is None or width is None or height == width:
            if height is not None:
                height = ZZ(height)
            else:
                height = ZZ(width)

            if height < 0:
                raise ValueError(f'Size (={height}) must be non-negative.')

            return LatticePaths_size(width=height,
                                     height=height,
                                     dyck=dyck,
                                     labelled=labelled,
                                     labels=labels,
                                     decorated_rises=decorated_rises,
                                     decorated_valleys=decorated_valleys)
        else:
            height = ZZ(height)
            width = ZZ(width)

            if height < 0:
                raise ValueError(f'Height (={height}) must be non-negative.')

            if width < 0:
                raise ValueError(f'Width (={width}) must be non-negative.')

            return LatticePaths_size(width=width,
                                     height=height,
                                     dyck=dyck,
                                     labelled=labelled,
                                     labels=labels,
                                     decorated_rises=decorated_rises,
                                     decorated_valleys=decorated_valleys)
    Element = LatticePath

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

    def _element_constructor_(self, word):
        '''
        Construct an element of ``self``.

        EXAMPLES::

            sage: LP = LatticePaths()
            sage: path = LP([1, 1, 0, 1, 0, 0]); path
            [1, 1, 0, 1, 0, 0]
            sage: path.parent() is LP
            True
        '''
        if isinstance(word, LatticePath) and word.parent() is self:
            return word
        return self.element_class(self, path=list(word))


class RectangularPaths(LatticePaths):
    @ staticmethod
    def __classcall_private__(cls, width=None, height=None, labelled=True, labels=None,
                              dyck=False, decorated_rises=0, decorated_valleys=0):

        return LatticePaths(width=width, height=height, labelled=labelled, labels=labels,
                            dyck=dyck, decorated_rises=decorated_rises, decorated_valleys=decorated_valleys)

    Element = RectangularPath


class RectangularDyckPaths(RectangularPaths):
    @ staticmethod
    def __classcall_private__(cls, width=None, height=None, labelled=True, labels=None,
                              decorated_rises=0, decorated_valleys=0):

        return LatticePaths(width=width, height=height, labelled=labelled, labels=labels,
                            dyck=True, decorated_rises=decorated_rises, decorated_valleys=decorated_valleys)

    Element = RectangularDyckPath


class SquarePaths(RectangularPaths):
    @ staticmethod
    def __classcall_private__(cls, size=None, labelled=True, labels=None,
                              dyck=False, decorated_rises=0, decorated_valleys=0):

        return LatticePaths(height=size, width=size, square=True, labelled=labelled, labels=labels,
                            dyck=dyck, decorated_rises=decorated_rises, decorated_valleys=decorated_valleys)

    Element = SquarePath


class DyckPaths(SquarePaths, RectangularDyckPaths):
    @ staticmethod
    def __classcall_private__(cls, size=None, labelled=True, labels=None,
                              decorated_rises=0, decorated_valleys=0):

        return LatticePaths(height=size, width=size, labelled=labelled, labels=labels,
                            dyck=True, square=True, decorated_rises=decorated_rises, decorated_valleys=decorated_valleys)

    Element = DyckPath


class LatticePaths_all(LatticePaths):
    '''
    All lattice paths.
    '''

    def __init__(self, dyck=False, square=False, labelled=True, decorated_rises=0, decorated_valleys=0):
        super().__init__(category=InfiniteEnumeratedSets())

        self.dyck = dyck
        self.square = square
        self.labelled = labelled
        self.decorated_rises = decorated_rises
        self.decorated_valleys = decorated_valleys

    def __iter__(self):

        if self.square is True:
            size = 0
            while True:
                for x in _lattice_paths(width=size, height=size, dyck=self.dyck,
                                        labelled=self.labelled, labels=None,
                                        drises=self.decorated_rises, dvalleys=self.decorated_valleys):
                    yield x
                size += 1
        else:
            semiperimeter = 0
            while True:
                for height in range(0, semiperimeter+1):
                    for x in _lattice_paths(width=semiperimeter-height, height=height, dyck=self.dyck,
                                            labelled=self.labelled, labels=None,
                                            drises=self.decorated_rises, dvalleys=self.decorated_valleys):
                        yield x
                semiperimeter += 1


class LatticePaths_size(LatticePaths):
    '''
    All lattice paths with a given size.
    '''

    def __init__(self, width=None, height=None, dyck=False, labelled=True, labels=None, decorated_rises=0, decorated_valleys=0):
        super().__init__(category=FiniteEnumeratedSets())

        self.height = height
        self.width = width
        self.dyck = dyck
        self.labelled = labelled
        self.labels = labels
        self.decorated_rises = decorated_rises
        self.decorated_valleys = decorated_valleys

    def __iter__(self):

        for x in _lattice_paths(width=self.width, height=self.height, dyck=self.dyck,
                                labelled=self.labelled, labels=self.labels,
                                drises=self.decorated_rises, dvalleys=self.decorated_valleys):
            yield x
