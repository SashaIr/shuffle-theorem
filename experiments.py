from shuffle_theorem.lattice_paths import DyckPath, DyckPaths, LatticePaths


class TestDyckPath(DyckPath):
    pass


class TestDyckPaths(DyckPaths):
    Element = TestDyckPath

    @ staticmethod
    def __classcall_private__(cls, size=None, labelled=True, labels=None,
                              decorated_rises=0, decorated_valleys=0):

        return (TestDyckPath(x) for x in LatticePaths(height=size, width=size,
                                                      labelled=labelled, labels=labels,
                                                      dyck=True, square=True,
                                                      decorated_rises=decorated_rises, decorated_valleys=decorated_valleys))
