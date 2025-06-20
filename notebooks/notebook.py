import marimo

__generated_with = "0.14.0"
app = marimo.App(width="medium")


@app.cell
def _():
    import marimo as mo
    return (mo,)


@app.cell
def _():
    import sys
    sys.path.append('src/')
    return


@app.cell
def _():
    from shuffle_theorem import operators, dp_algebra
    return (dp_algebra,)


@app.cell
def _():
    from sage.arith.all import binomial
    from sage.arith.misc import gcd, xgcd
    from sage.categories.tensor import tensor
    from sage.combinat.partition import Partitions, Partition
    from sage.combinat.composition import Compositions, Composition
    from sage.combinat.sf.sf import SymmetricFunctions
    from sage.combinat.ncsf_qsym.qsym import QuasiSymmetricFunctions
    from sage.combinat.skew_tableau import SemistandardSkewTableaux
    from sage.functions.other import ceil
    from sage.graphs.digraph import DiGraph
    from sage.combinat.sf.macdonald import cmunu
    from sage.misc.all import cached_function, prod
    from sage.rings.all import PolynomialRing, QQ
    return QQ, QuasiSymmetricFunctions, SymmetricFunctions, prod, tensor


@app.cell
def _(QQ, QuasiSymmetricFunctions, SymmetricFunctions, dp_algebra):
    # Define the Symmetric Functions and QuasiSymmetric Functions algebras over Q and Q(q,t,u,v).
    QQqt = dp_algebra.RR(0)
    Sym = SymmetricFunctions(QQ)
    Symqt = SymmetricFunctions(QQqt)
    QSym = QuasiSymmetricFunctions(QQ)
    QSymqt = QuasiSymmetricFunctions(QQqt)

    # Import shorthands
    QQqt.inject_variables(verbose=False)
    Sym.inject_shorthands(verbose=False)
    Symqt.inject_shorthands(verbose=False)
    QSym.inject_shorthands(verbose=False)
    QSymqt.inject_shorthands(verbose=False)
    Ht = Symqt.macdonald().Ht()

    return


@app.cell
def _(mo):
    def latex(item):
        return mo.md(f'$${item._latex_()}$$')
    return


@app.cell
def _():
    return


@app.cell
def _(dp_algebra):
    dir(dp_algebra.yy(2).parent())
    return


@app.cell
def _(dp_algebra, s):
    dir((s[3] * dp_algebra.XX0(1)).parent())
    return


@app.cell
def _(dp_algebra, q):
    (q * dp_algebra.XX0(5) * dp_algebra.yy(2)).parent().base_ring().gens()
    return


@app.cell
def _(dp_algebra, q):
    dir((q * dp_algebra.yy(1) * dp_algebra.yy(2) * dp_algebra.XX(5)).parent())
    return


@app.cell
def _():
    alpha = [4,2,1,1]
    return (alpha,)


@app.cell
def _(C_alpha, alpha, s):
    C_alpha(alpha, s[1])
    return


@app.cell
def _(alpha, dminus, dplus, e, prod, s, yy):
    e(dminus(prod(yy(len(alpha), i) ** (alpha[i]-1) for i in range(len(alpha))) * dplus(s[1], 0, power=len(alpha)), len(alpha), power=len(alpha)))
    return


@app.cell
def _(dp_algebra, s):
    s(dp_algebra.D_alpha([-1,-1,2], s[1]))
    return


@app.cell
def _(D_alpha, D_beta, s):
    s(D_beta([-2,2,-1], s[2])) == s(D_alpha([-2,2,-1], s[2]))
    return


@app.cell
def _(Dn, m, s):
    m(Dn(-2, s[3]))
    return


@app.cell
def _(e, m, q, s, t, tensor):
    list(q * tensor([s[2], m[3]]) + t * tensor([s[1,1], e[1,1]]))
    return


@app.cell
def _(e, m, q, s, t, tensor):
    (q * tensor([s[2], m[3]]) + t * tensor([s[1,1], e[1,1]])).parent()
    return


@app.cell
def _():
    return


@app.cell
def _(mo):
    import pathlib
    import anywidget
    import traitlets

    class TikzWidget(anywidget.AnyWidget):
        _esm = pathlib.Path(__file__).parent / "tikzjax-widget.js"
        tex = traitlets.Unicode("").tag(sync=True)

    # Wrap in Marimo UI
    oldcode = r"""
    \begin{tikzpicture}
      \draw (0,0) circle (1);
    \end{tikzpicture}
    """
    widget = mo.ui.anywidget(TikzWidget(tex=oldcode))
    widget
    return


@app.cell
def _(mo):
    # wire up head.html so its contents go into <head>
    app = mo.App(html_head_file="head.html")
    return


@app.cell
def _(mo):
    # Your TikZ code:
    code = r"""
    \begin{tikzpicture}
      \draw (0,0) circle (1);
      \node at (0,0) {Hello TikZJax!};
    \end{tikzpicture}
    """

    # Build the HTML+JS that will live in an <iframe> so that module scripts actually execute:
    html = f"""
    <div id="tikz-container"></div>
    <script type="module">
      import tikzjax from 'https://cdn.jsdelivr.net/npm/tikzjax@0.8.4/dist/tikzjax.js';
      tikzjax.renderTo(
        document.getElementById('tikz-container'),
        `{code}`
      );
    </script>
    """

    # Embed it in an iframe:
    mo.iframe(html, width="100%", height="400px")
    return


@app.cell
def _():
    return


if __name__ == "__main__":
    app.run()
