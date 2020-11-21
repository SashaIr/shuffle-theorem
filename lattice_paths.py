'''
SageMath module.
Tools for the shuffle theorem and variants.
'''

from itertools import combinations
from more_itertools import distinct_combinations
from multiset import Multiset
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.categories.infinite_enumerated_sets import InfiniteEnumeratedSets
from sage.rings.all import Rational, ZZ
from sage.structure.all import Parent
from sage.structure.list_clone import ClonableIntArray  # type: ignore
from sage.structure.global_options import GlobalOptions
from sage.structure.unique_representation import UniqueRepresentation


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


def _mu_labellings(blocks, labels, strict=True, increasing=True):

    if len(blocks) == 0:
        yield []
    else:
        if strict == True:
            label_choices = combinations(set(labels), blocks[0])
        else:
            label_choices = distinct_combinations(labels, blocks[0])
        for chosen_labels in label_choices:
            chosen_labels = sorted(list(chosen_labels), reverse=not increasing)
            for other_labels in _mu_labellings(blocks[1:],
                                               list((Multiset(labels) - Multiset(chosen_labels))),
                                               strict=strict,
                                               increasing=increasing):
                yield chosen_labels + other_labels


class LatticePath(ClonableIntArray):
    r'''
    # TODO: Write some actual documentation.
    '''

    def __init__(self, parent, path, labels=None, rises=[], valleys=[], latex_options={}):

        # TODO: Change this to allow for different inputs.
        if not (isinstance(path, list) and all(x in [0, 1] for x in path)):
            raise ValueError(f'Invalid path (= {path}), entries must be 0 and 1.')

        super().__init__(parent, path)

        # It's the actual path, stored as a string of 0's (east steps) and 1's (north steps)
        self.path = path
        # It's the list of the labels of the path, to read bottom to top. Default is None.
        self.labels = labels
        # These are the indices of the decorated rises.
        self.rises = rises
        # These are the indices of the decorated valleys.
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
        self.shift = - min(self.area_word()) if self.length > 0 else 0
        # It's the area word of the path, as list.
        self.aword = self.area_word()
        # Instruction on how to draw the path in LaTeX.
        self._latex_options = dict(latex_options)

    def check(self):
        pass

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
            or (self.aword[i+1] < self.aword[i] and i in self.rises)
            or (self.aword[i+1] < self.aword[i] + self.slope - 1 and i not in self.rises)
            or (self.aword[i+1] == self.aword[i]
                and i in self.rises and i+1 not in self.valleys)
            or (self.aword[i+1] == self.aword[i] + self.slope - 1
                and i not in self.rises and i+1 not in self.valleys)
        )]

        blocks = [peaks[i+1] - peaks[i] for i in range(len(peaks)-1)]

        # Define the set of labels.
        labels = [x for y in [[i]*composition[i] for i in range(len(composition))] for x in y]
        labellings = [labelling for labelling in _mu_labellings(blocks, labels) if not (
            (self.length > 0 and self.aword[0] == 0 and labelling[0] == 0)
            or (len([i for i in range(self.height) if self.aword[i] == -self.shift and labelling[i] > 0 and i not in self.valleys]) == 0)
        )]

        return labellings

    def column(self, i):
        # Returns the index of the column (numbered starting from 0) containing the label with index i.
        return [sum(self.path[:j]) for j in range(self.length)].index(i+1)-i-1

    def main_diagonal(self, i):
        # Returns x-coordinates of the y-integer points of the main diagonal.

        # return i
        decorations_below = len([j for j in range(i) if j in self.rises or j in self.valleys])

        return self.slope*(i-decorations_below) + decorations_below

    def area_word(self):
        # Returns the area word of the path.
        return [self.main_diagonal(i)-self.column(i) for i in range(self.height)]

    def area(self):
        # Returns the area. Ignores rows with decorated rises.
        area = sum(self.aword[i] + self.shift for i in range(self.height) if i not in self.rises)
        return area

    def dinv(self):
        dinv = 0  # Initializes dinv to 0.

        # Goes through the letters of the area word.
        for i in range(self.height):
            if self.aword[i] < 0:  # Bonus dinv
                dinv += 1
            if i not in self.valleys:  # Skip decorated valleys
                for j in range(i+1, self.height):  # Looks at the right.
                    if self.aword[j] == self.aword[i]-1:  # Secondary dinv
                        # Checks labels
                        if self.labels is None or self.labels[j] < self.labels[i]:
                            dinv += 1
                for j in range(i+1, self.height):
                    if self.aword[j] == self.aword[i]:  # Primary dinv
                        # Checks labels
                        if self.labels is None or self.labels[j] > self.labels[i]:
                            dinv += 1
            else:  # Subtract 1 for each decorated valley
                dinv += -1

        return dinv

    def zero(self):
        return 0


class RectangularPath(LatticePath):
    def check(self):
        pass


class RectangularDyckPath(RectangularPath):
    def check(self):
        pass


class SquarePath(RectangularPath):
    def check(self):
        pass


class DyckPath(SquarePath, RectangularDyckPath):
    def check(self):
        pass


class LatticePaths(UniqueRepresentation, Parent):

    @staticmethod
    def __classcall_private__(cls, height=None, width=None, labelled=True, labels=None,
                              dyck=False, square=False, decorated_rises=0, decorated_valleys=0):
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
        r"""
        Set and display the options for Dyck words. If no parameters
        are set, then the function returns a copy of the options dictionary.

        The ``options`` to Dyck words can be accessed as the method
        :meth:`DyckWords.options` of :class:`DyckWords` and
        related parent classes.

        @OPTIONS

        EXAMPLES::

            sage: D = DyckWord([1, 1, 0, 1, 0, 0])
            sage: D
            [1, 1, 0, 1, 0, 0]
            sage: DyckWords.options.display="lattice"
            sage: D
               ___
             _| x
            | x  .
            |  . .
            sage: DyckWords.options(diagram_style="line")
            sage: D
             /\/\
            /    \
            sage: DyckWords.options._reset()
        """
        NAME = 'DyckWords'
        module = 'sage.combinat.dyck_word'
        display = dict(default="list",
                       description='Specifies how Dyck words should be printed',
                       values=dict(list='displayed as a list',
                                   lattice='displayed on the lattice defined by ``diagram_style``'),
                       case_sensitive=False)
        ascii_art = dict(default="path",
                         description='Specifies how the ascii art of Dyck words should be printed',
                         values=dict(path="Using the path string",
                                     pretty_output="Using pretty printing"),
                         alias=dict(pretty_print="pretty_output", path_string="path"),
                         case_sensitive=False)
        diagram_style = dict(default="grid",
                             values=dict(grid='printing as paths on a grid using N and E steps',
                                         line='printing as paths on a line using NE and SE steps',),
                             alias={'N-E': 'grid', 'NE-SE': 'line'},
                             case_sensitive=False)
        latex_tikz_scale = dict(default=1,
                                description='The default value for the tikz scale when latexed',
                                checker=lambda x: True)  # More trouble than it's worth to check
        latex_diagonal = dict(default=False,
                              description='The default value for displaying the diagonal when latexed',
                              checker=lambda x: isinstance(x, bool))
        latex_line_width_scalar = dict(default=2,
                                       description='The default value for the line width as a '
                                       'multiple of the tikz scale when latexed',
                                       checker=lambda x: True)  # More trouble than it's worth to check
        latex_color = dict(default="black",
                           description='The default value for the color when latexed',
                           checker=lambda x: isinstance(x, str))
        latex_bounce_path = dict(default=False,
                                 description='The default value for displaying the bounce path when latexed',
                                 checker=lambda x: isinstance(x, bool))
        latex_peaks = dict(default=False,
                           description='The default value for displaying the peaks when latexed',
                           checker=lambda x: isinstance(x, bool))
        latex_valleys = dict(default=False,
                             description='The default value for displaying the valleys when latexed',
                             checker=lambda x: isinstance(x, bool))

    def _element_constructor_(self, word):
        """
        Construct an element of ``self``.

        EXAMPLES::

            sage: D = DyckWords()
            sage: elt = D([1, 1, 0, 1, 0, 0]); elt
            [1, 1, 0, 1, 0, 0]
            sage: elt.parent() is D
            True
        """
        if isinstance(word, DyckPath) and word.parent() is self:
            return word
        return self.element_class(self, list(word))


class RectangularPaths(LatticePaths):
    @staticmethod
    def __classcall_private__(cls, height=None, width=None, labelled=True, labels=None,
                              dyck=False, decorated_rises=0, decorated_valleys=0):

        return LatticePaths(height=height, width=width, labelled=labelled, labels=labels,
                            dyck=dyck, decorated_rises=decorated_rises, decorated_valleys=decorated_valleys)

    Element = RectangularPath


class RectangularDyckPaths(RectangularPaths):
    @staticmethod
    def __classcall_private__(cls, height=None, width=None, labelled=True, labels=None,
                              decorated_rises=0, decorated_valleys=0):

        return LatticePaths(height=height, width=width, labelled=labelled, labels=labels,
                            dyck=True, decorated_rises=decorated_rises, decorated_valleys=decorated_valleys)

    Element = RectangularDyckPath


class SquarePaths(RectangularPaths):
    @staticmethod
    def __classcall_private__(cls, size=None, labelled=True, labels=None,
                              dyck=False, decorated_rises=0, decorated_valleys=0):

        return LatticePaths(height=size, width=size, square=True, labelled=labelled, labels=labels,
                            dyck=dyck, decorated_rises=decorated_rises, decorated_valleys=decorated_valleys)

    Element = SquarePath


class DyckPaths(SquarePaths, RectangularDyckPaths):
    @staticmethod
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
