#!/usr/bin/env python3
"""Apply the audited corrections to article2.tex, producing article2_v2.tex.
Every replacement is checked; the script fails loudly if a target is missing."""
import sys, io

SRC = "/home/claude/work/article2.tex"
DST = "/home/claude/work/out/article2_v2.tex"

R = []
def rep(old, new, tag):
    R.append((old, new, tag))

# ---------------------------------------------------------------- preamble
rep(r"\newcommand{\UMn}{\bar{\mathcal{M}}_n^{\geq\frac{1}{2}}}",
    r"""\newcommand{\UMn}{\bar{\mathcal{M}}_n^{\geq\frac{1}{2}}}
\newcommand{\den}{\mathrm{den}}""",
    "preamble: den macro")

# ---------------------------------------------------------------- abstract
rep(r"""$n$, and conjecture that asymptotically all half-one metrics are extreme. We prove
the \emph{upper-half decomposition theorem}: every metric with all distances at least
$\tfrac{1}{2}$ is a convex combination of extreme metrics with denominator of the form $2^i3^j$,
where $i+j\leq\lfloor(m+1)/2\rfloor$ where $m=\binom{n}{2}$.""",
    r"""$n$, and conjecture that asymptotically all half-one metrics are extreme. We prove
the \emph{upper-half decomposition theorem}: every metric with all distances at least
$\tfrac{1}{2}$ is a convex combination of extreme metrics with denominator of the form
$2^i3^j$, where $i+j\leq m+1$ and $m=\binom{n}{2}$. Computation suggests the sharp
statement is $i+j\leq 2$, uniformly in $n$.""",
    "abstract: decomposition bound")

rep(r"""of $d$ on the boundary of $\bar{\mathcal{M}}_n$, identifying neighbors as partition metrics
or metrics with denominator $3$.""",
    r"""of $d$ on the boundary of $\bar{\mathcal{M}}_n$, identifying neighbors as partition metrics
or metrics with denominator $3$ when $\Gamma_d$ is connected, and as metrics with
denominator $2$, $4$ or $6$ otherwise.""",
    "abstract: neighbor denominators")

# ---------------------------------------------------------------- introduction
rep(r"""$n=4$: the \emph{midpoint metric} $m_4$, which places a single point at the midpoint of
each side of a unit equilateral triangle. This metric takes only values $\tfrac{1}{2}$ and
$1$, and belongs to the class we study here.""",
    r"""$n=4$: the \emph{midpoint metric} $m_4$, obtained by adjoining to the three vertices of a
unit equilateral triangle a fourth point lying at distance $\tfrac{1}{2}$ from each of them.
That fourth point is simultaneously a midpoint of all three sides, so $m_4$ admits no
isometric embedding into the plane. This metric takes only values $\tfrac{1}{2}$ and $1$,
and belongs to the class we study here.""",
    "intro: m_4 description")

rep(r"""  \item The upper-half decomposition (Theorem~\ref{thm:upper-half}): every $d\in[\tfrac{1}{2},1]^m$
        decomposes into extreme $2^i3^j$-denominator metrics.""",
    r"""  \item The upper-half decomposition (Theorem~\ref{thm:upper-half}): every $d\in[\tfrac{1}{2},1]^m$
        decomposes into extreme $2^i3^j$-denominator metrics, together with a conjecturally
        sharp form (Conjecture~\ref{conj:den12}).""",
    "intro: item 3")

# ---------------------------------------------------------------- Section 2
rep(r"""A \emph{germ} is a connected subgraph of $\Gamma_d$ containing exactly one odd cycle;
a \emph{colony} is a disjoint union of germs. A component of $\Gamma_d$ is \emph{rigid}
if it contains an odd cycle (all perturbations restricted to it vanish).

\textbf{Key theorem from \cite{Kehoe-extremeRays}:}
For a half-one metric $d$, the perturbation space $P_d$ has dimension equal to the number
of non-rigid components of $\Gamma_d$, with an explicit basis given by sign functions on
rooted spanning trees of each component.""",
    r"""A \emph{germ} is a connected subgraph of $\Gamma_d$ containing exactly one odd cycle;
a \emph{colony} is a disjoint union of germs. A component of $\Gamma_d$ is \emph{rigid}
if it contains an odd cycle (all perturbations restricted to it vanish). Isolated nodes
of $\Gamma_d$ are components, and are never rigid.

For half-one metrics the perturbation space admits a direct description, which we record
here because it is used repeatedly below.

\begin{lemma}\label{lem:perturbation}
Let $d\in\mathcal{H}_n$. A vector $\varepsilon\in\R^m$ preserves every tight constraint of
$d$ if and only if $\varepsilon$ vanishes on $\mathcal{U}_d$ and satisfies
$\varepsilon(E)=-\varepsilon(E')$ whenever $E,E'$ are adjacent in $\Gamma_d$. Consequently
$P_d$ has dimension equal to the number of bipartite components of $\Gamma_d$, with a basis
given by the alternating sign functions $\eta_\kappa$ of those components.
\end{lemma}

\begin{proof}
The tight constraints of $d$ are the bounding constraints $d_E=1$ for $E\in\mathcal{U}_d$
and the degeneracies $d_{ij}+d_{jk}=d_{ik}$. The former force $\varepsilon|_{\mathcal{U}_d}=0$.
Since $\tfrac{1}{2}+\tfrac{1}{2}=1$ is the only degenerate configuration available to a
half-one metric, every degenerate triangle has two non-unital short sides $E,E'$ and a unital
long side, so its constraint reads $\varepsilon(E)+\varepsilon(E')=0$; these are exactly the
adjacencies of $\Gamma_d$. A sign condition of this form has a nonzero solution on a
connected graph precisely when that graph is bipartite, and then the solution space is
one-dimensional.
\end{proof}""",
    "section 2: perturbation lemma")

# ---------------------------------------------------------------- Theorem 3.1 proof
rep(r"""$d$ is extreme iff $\Gamma_d$ contains a spanning short-sided colony,
iff every component of $\Gamma_d$ contains an odd cycle.
The second equivalence: a component with no odd cycle is a tree (even or no cycles),
hence non-rigid and contributing a free perturbation direction.
\end{proof}""",
    r"""$d$ is extreme iff $\Gamma_d$ contains a spanning short-sided colony,
iff every component of $\Gamma_d$ contains an odd cycle.
Alternatively, and independently of \cite{Kehoe-extremeRays}: by
Lemma~\ref{lem:perturbation}, $\dim P_d$ equals the number of bipartite components of
$\Gamma_d$, and $d$ is extreme exactly when $P_d=0$.
\end{proof}

\begin{remark}
A component containing no odd cycle is bipartite, but need not be a tree. For $n=4$ and
$\mathcal{N}_d=\{[1,3],[1,4],[2,3],[2,4]\}$ the graph $\Gamma_d$ is a single $4$-cycle,
with four nodes and four edges.
\end{remark}""",
    "Theorem 3.1 proof: bipartite not tree")

# ---------------------------------------------------------------- Prop 3.3 proof
rep(r"""$G_d$ tree-free of triangles means $\Gamma_d = L(G_d)$ (line graph). A non-path tree has
a vertex $v$ of degree $\geq 3$, whose three incident edges form a $3$-cycle in $\Gamma_d$.
By Theorem~\ref{thm:odd-cycle}, $d$ is extreme.""",
    r"""A tree contains no triangle, so two edges of $G_d$ sharing a vertex always complete a
triangle of $\mathbf{n}$ whose third side is unital; hence $\Gamma_d=L(G_d)$, the line
graph. A spanning tree is connected, so $L(G_d)$ is connected, and $\Gamma_d$ has a single
component. A non-path tree has a vertex $v$ of degree $\geq 3$, whose three incident edges
form a $3$-cycle in $\Gamma_d$. By Theorem~\ref{thm:odd-cycle}, $d$ is extreme.""",
    "Prop 3.3 proof: connectivity")

# ---------------------------------------------------------------- Prop 4.1 / threshold
rep(r"""\begin{proposition}[Kehoe, 2018]\label{prop:halfone-count}
$|\mathrm{ex}(\mathcal{H}_n)| > n^{n-2} - \tfrac{n!}{2}$ for all $n$, and
$|\mathrm{ex}(\mathcal{H}_n)| > B_n$ for all sufficiently large $n$,
where $B_n = |\Pi_n|$ is the $n$-th Bell number.
\end{proposition}""",
    r"""\begin{proposition}[Kehoe, 2018]\label{prop:halfone-count}
$|\mathrm{ex}(\mathcal{H}_n)| > n^{n-2} - \tfrac{n!}{2}$ for all $n$, and
$|\mathrm{ex}(\mathcal{H}_n)| > B_n$ for all $n\geq 5$,
where $B_n = |\Pi_n|$ is the $n$-th Bell number. The hypothesis $n\geq 5$ cannot be
weakened: $|\mathrm{ex}(\mathcal{H}_4)|=5$ while $B_4=15$.
\end{proposition}""",
    "Prop 4.1: explicit threshold")

rep(r"""Berend--Tassa \cite{Berrend10} give $B_n < \bigl(\tfrac{0.792n}{\ln(n+1)}\bigr)^n$.
Hence""",
    r"""The inequality is strict at every $n$: the all-unital metric $d\equiv 1$, whose
half-length graph is empty, is extreme and is not counted by any spanning tree. At $n=4$
this trivial metric is the only extreme half-one beyond the four stars $K_{1,3}$.

Berend--Tassa \cite{Berrend10} give $B_n < \bigl(\tfrac{0.792n}{\ln(n+1)}\bigr)^n$.
Hence""",
    "Prop 4.1 proof: strictness")

rep(r"""so eventually $B_n < |\mathrm{ex}(\mathcal{H}_n)|$.
\end{proof}

Exhaustive computer enumeration confirms that extreme half-ones first outnumber partitions
at $n=5$. Computer experiments strongly suggest:

\begin{conjecture}[Kehoe]\label{conj:density}
$|\mathcal{H}_n| \sim 2^{\binom{n}{2}}$, i.e.,
$\displaystyle\lim_{n\to\infty}\frac{|\mathcal{H}_n|}{2^{\binom{n}{2}}} = 1$.
\end{conjecture}""",
    r"""so $B_n < |\mathrm{ex}(\mathcal{H}_n)|$ once $n\geq 5$, the right-hand side of the displayed
bound being less than $1$ from that point on.
\end{proof}

Exhaustive computer enumeration confirms that extreme half-ones first outnumber partitions
at $n=5$:

\begin{center}
\begin{tabular}{r|r|r|r|r}
$n$ & $2^{\binom{n}{2}}$ & $|\mathrm{ex}(\mathcal{H}_n)|$ & $B_n$ & $n^{n-2}-\tfrac{n!}{2}$\\
\hline
$4$ & $64$ & $5$ & $15$ & $4$\\
$5$ & $1024$ & $168$ & $52$ & $65$\\
$6$ & $32768$ & $12326$ & $203$ & $936$\\
$7$ & $2097152$ & $1309868$ & $877$ & $14287$\\
$8$ & $268435456$ & $209717144$ & $4140$ & $241984$
\end{tabular}
\end{center}

Since every vector in $\{\tfrac{1}{2},1\}^{\binom{n}{2}}$ is a metric, $|\mathcal{H}_n| =
2^{\binom{n}{2}}$ identically; the content of the following conjecture concerns the extreme
ones.

\begin{conjecture}[Kehoe]\label{conj:density}
$|\mathrm{ex}(\mathcal{H}_n)| \sim 2^{\binom{n}{2}}$, i.e.,
$\displaystyle\lim_{n\to\infty}\frac{|\mathrm{ex}(\mathcal{H}_n)|}{2^{\binom{n}{2}}} = 1$.
\end{conjecture}

The proportions in the table above are $0.078$, $0.164$, $0.376$, $0.625$, $0.781$ for
$n=4,\ldots,8$.""",
    "Conjecture 4.2: ex(H_n), plus table")

# ---------------------------------------------------------------- heuristic
rep(r"""Choose two further points $k,l\notin\{i,j\}$ and assign the six remaining distances
on $\{i,j,k,l\}$ from $\{\tfrac{1}{2},1\}$ uniformly at random.
With probability $\tfrac{1}{16}$ the result is the extreme midpoint metric $m_4$
containing $[i,j]$.""",
    r"""Choose two further points $k,l\notin\{i,j\}$ and assign the five remaining distances
on $\{i,j,k,l\}$ from $\{\tfrac{1}{2},1\}$ uniformly at random. Exactly two of the $2^5$
assignments produce a copy of $m_4$ with $[i,j]$ half-length, namely the two stars centred
at $i$ and at $j$; so with probability $\tfrac{1}{16}$ the result is the extreme midpoint
metric $m_4$ containing $[i,j]$.""",
    "heuristic: five distances")

# ---------------------------------------------------------------- Theorem 5.2 statement
rep(r"""\begin{theorem}[Kehoe, 2018]\label{thm:upper-half}
Every $d\in\bar{\mathcal{M}}_n^{\geq 1/2}$ is a convex combination of extreme
metrics with denominator of the form $2^i3^j$, where $0\leq i+j\leq\lfloor(m+1)/2\rfloor$.
\end{theorem}""",
    r"""\begin{theorem}[Kehoe, 2018]\label{thm:upper-half}
Every $d\in\bar{\mathcal{M}}_n^{\geq 1/2}$ is a convex combination of extreme
metrics with denominator of the form $2^i3^j$, where $0\leq i+j\leq m+1$.
\end{theorem}""",
    "Theorem 5.2: corrected bound")

# ---------------------------------------------------------------- Prop 5.5
rep(r"""\begin{proposition}[Kehoe, 2018]\label{prop:non-extreme-decomp}
Let $d\in\mathcal{H}_n$ be non-extreme with $\Gamma_d$ connected. Then $d$ is the
average of:
\begin{itemize}
  \item two partition metrics (if all equilateral triangles of $d$ are uniformly signed), or
  \item a partition metric and an extreme positive-definite metric with denominator $3$, or
  \item two extreme positive-definite metric with denominator $3$s.
\end{itemize}
\end{proposition}""",
    r"""\begin{proposition}[Kehoe, 2018]\label{prop:non-extreme-decomp}
Let $d\in\mathcal{H}_n$ be non-extreme with $\Gamma_d$ connected. Then $d$ is a convex
combination of:
\begin{itemize}
  \item two partition metrics (if all equilateral triangles of $d$ are uniformly signed), or
  \item a partition metric and an extreme metric with denominator $3$, or
  \item two extreme metrics with denominator $3$.
\end{itemize}
In the first and third cases the combination is the average; in the second the weights are
$\tfrac{1}{4}$ and $\tfrac{3}{4}$.
\end{proposition}""",
    "Prop 5.5: convex combination, not average")

rep(r"""Since $\Gamma_d$ is connected and short-sided, every perturbation has the form
$\varepsilon\cdot\eta$ where $\eta(E)=(-1)^{l(E)}$ for non-unital edges $E$ and
$l$ is tree-distance from a root. Setting $d_\varepsilon=d+\varepsilon\eta$, the
five determining triangle inequality cases are:
\begin{enumerate}
  \item $\tfrac{1}{2}+\varepsilon\leq(\tfrac{1}{2}+\varepsilon)+(\tfrac{1}{2}+\varepsilon)
        \Rightarrow -\tfrac{1}{2}\leq\varepsilon$
  \item $\tfrac{1}{2}+\varepsilon\leq(\tfrac{1}{2}-\varepsilon)+(\tfrac{1}{2}+\varepsilon)
        \Rightarrow\varepsilon\leq\tfrac{1}{2}$
  \item $\tfrac{1}{2}-\varepsilon\leq(\tfrac{1}{2}+\varepsilon)+(\tfrac{1}{2}+\varepsilon)
        \Rightarrow-\tfrac{1}{6}\leq\varepsilon$
  \item $\tfrac{1}{2}+\varepsilon\leq 2\Rightarrow\varepsilon\leq\tfrac{3}{2}$
  \item $1\leq 1+(\tfrac{1}{2}+\varepsilon)\Rightarrow\varepsilon\leq\tfrac{1}{2}$
\end{enumerate}
In general: metricity for $-\tfrac{1}{6}\leq\varepsilon\leq\tfrac{1}{6}$.
When all equilateral triangles are uniformly signed (Case~1 only): range extends to
$[-\tfrac{1}{2},\tfrac{1}{2}]$, giving two partitions. When Case~2 occurs: setting
$\varepsilon=-\tfrac{1}{6}$ gives extreme $\tilde{d}$ with $\tilde{d}_{ij}=\tilde{d}_{jk}=\tfrac{1}{3}$
and $\tilde{d}_{ik}=\tfrac{2}{3}$ (extreme since $\dim(P_d)=1$).
\end{proof}""",
    r"""By Lemma~\ref{lem:perturbation}, $\Gamma_d$ is connected and bipartite and every
perturbation has the form $\varepsilon\cdot\eta$, where $\eta(E)=(-1)^{l(E)}$ on
$\mathcal{N}_d$ with $l$ the tree-distance from a root, and $\eta=0$ on $\mathcal{U}_d$.
Write $s_E=\eta(E)\in\{\pm1\}$ and $d_\varepsilon=d+\varepsilon\eta$. Sorting the
constraints on $d_\varepsilon$ by the number of non-unital sides of the triangle involved:

\begin{enumerate}
  \item \emph{Bounding constraints.} $0\leq\tfrac{1}{2}+s_E\varepsilon\leq 1$, that is
        $|\varepsilon|\leq\tfrac{1}{2}$.
  \item \emph{One non-unital side.} The triangle inequalities read
        $1\leq 1+(\tfrac{1}{2}+s_E\varepsilon)$ and
        $\tfrac{1}{2}+s_E\varepsilon\leq 2$, both implied by $|\varepsilon|\leq\tfrac{1}{2}$.
  \item \emph{Two non-unital sides.} Such a triangle is degenerate, so its two short sides
        are adjacent in $\Gamma_d$ and carry opposite signs; the equality
        $1=(\tfrac{1}{2}+\varepsilon)+(\tfrac{1}{2}-\varepsilon)$ persists, and the two
        remaining inequalities reduce to $|\varepsilon|\leq\tfrac{1}{2}$.
  \item \emph{Three non-unital sides (equilateral triangles).} For sides $E_1,E_2,E_3$ and
        each choice of long side $E_a$,
        \[(s_{E_a}-s_{E_b}-s_{E_c})\,\varepsilon\leq\tfrac{1}{2},\qquad
          s_{E_a}-s_{E_b}-s_{E_c}\in\{\pm1,\pm3\}.\]
\end{enumerate}

Only the last family can bind beyond $|\varepsilon|\leq\tfrac{1}{2}$, and it does so exactly
when the coefficient is $\pm3$, which happens precisely when the triangle is not uniformly
signed. Hence metricity holds on an interval $[a,b]$ with $a\in\{-\tfrac{1}{2},-\tfrac{1}{6}\}$
and $b\in\{\tfrac{1}{6},\tfrac{1}{2}\}$, and $a=-\tfrac{1}{2}$, $b=\tfrac{1}{2}$ exactly when
all equilateral triangles are uniformly signed.

Since $\dim P_d=1$, the segment $\{d_\varepsilon:\varepsilon\in[a,b]\}$ is the minimal face of
$\bar{\mathcal{M}}_n$ containing $d$, so $d_a$ and $d_b$ are extreme points. At
$\varepsilon=\pm\tfrac{1}{2}$ all non-unital distances become $0$ or $1$, giving a partition
metric; at $\varepsilon=\pm\tfrac{1}{6}$ they become $\tfrac{1}{3}$ or $\tfrac{2}{3}$, giving
denominator $3$. Finally $d=d_0=\tfrac{b}{b-a}d_a+\tfrac{-a}{b-a}d_b$, which is the average
when $b=-a$ and has weights $\tfrac{1}{4},\tfrac{3}{4}$ when $\{a,b\}=\{-\tfrac{1}{6},\tfrac{1}{2}\}$
or $\{-\tfrac{1}{2},\tfrac{1}{6}\}$.
\end{proof}""",
    "Prop 5.5 proof: corrected case analysis")

# ---------------------------------------------------------------- Theorem 5.6
rep(r"""\begin{theorem}[Kehoe, 2018]\label{thm:non-extreme-general}
Let $d\in\mathcal{H}_n$ be non-extreme with $\Gamma_d$ having $N\geq 1$ non-trivial
components and no isolated points. Then $d$ is a convex combination of $2^N$ extreme
$2^i3^j$-denominator metrics with $0\leq i+j\leq N$. If $\Gamma_d$ has isolated points,
replace $N$ by $N+1$.
\end{theorem}

\begin{proof}
Isolated points can be rigidified (deformed to $0$ or $1$, preserving metricity) in
one extra step. Assume no isolated points. View $d$ as a coproduct (disjoint union metric) on the
components of $\Gamma_d$; apply Proposition~\ref{prop:non-extreme-decomp} to each
non-rigid component independently.

At each step, a triangle becoming degenerate satisfies $\Delta - q\varepsilon = 0$
with $\Delta = d_{ij}+d_{jk}-d_{ik}>0$ and $q\in\{\pm1,\pm2,\pm3\}$ from the five cases.
If $d$ is an $r$-denominator metric, the perturbed metric has denominator dividing $rq$.
After $D'\leq N$ denominator-altering steps (non-rigid non-isolated components),
$i+j\leq N$.
\end{proof}""",
    r"""The passage from the connected case to the general one requires care: the components of
$\Gamma_d$ do \emph{not} perturb independently. An equilateral triangle contributes no edge
to $\Gamma_d$, so its three sides may lie in three different components, and the constraint
of item~(4) above then couples three distinct parameters.

\begin{example}\label{ex:coupling}
Take $n=4$ with $\mathcal{N}_d=\{[1,2],[1,3],[1,4],[2,3]\}$. Then $\Gamma_d$ has two
components, $\kappa_1=\{[1,2],[1,3],[1,4]\}$ (a path) and the isolated node
$\kappa_2=\{[2,3]\}$; neither carries an equilateral triangle, so the analysis of
Proposition~\ref{prop:non-extreme-decomp} allows $\varepsilon_{\kappa_1}$ and
$\varepsilon_{\kappa_2}$ to range over $[-\tfrac12,\tfrac12]$ separately. The equilateral
triangle $\{1,2,3\}$ has sides in both components, and the choice
$(\varepsilon_{\kappa_1},\varepsilon_{\kappa_2})=(-\tfrac12,\tfrac12)$ yields
$d_{12}=d_{13}=0$ with $d_{23}=1$, which is not a metric.
\end{example}

We therefore describe the whole face at once.

\begin{proposition}\label{prop:face}
Let $d\in\mathcal{H}_n$ and let $\kappa_1,\ldots,\kappa_N$ be the bipartite components of
$\Gamma_d$, with alternating sign functions $\eta_1,\ldots,\eta_N$ and $s_E=\eta_{\kappa}(E)$
for $E\in\kappa$. Put
\[
P_d=\Bigl\{\varepsilon\in\R^N:\ |\varepsilon_g|\leq\tfrac{1}{2}\ \ (1\leq g\leq N),\ \
s_{E_a}\varepsilon_{c(E_a)}-s_{E_b}\varepsilon_{c(E_b)}-s_{E_c}\varepsilon_{c(E_c)}\leq\tfrac{1}{2}
\Bigr\},
\]
the second family running over all equilateral triangles $\{E_a,E_b,E_c\}$ of $d$ and all
choices of long side $E_a$, with terms belonging to rigid components omitted. Then
$\varepsilon\mapsto d+\sum_g\varepsilon_g\eta_g$ is an affine isomorphism from $P_d$ onto the
minimal face of $\bar{\mathcal{M}}_n$ containing $d$, and carries $0$ to $d$.
\end{proposition}

\begin{proof}
By Lemma~\ref{lem:perturbation} the map is an affine isomorphism onto the affine span of that
face, so it suffices to check that the listed inequalities cut out exactly the metrics on that
span. Items~(1)--(3) of the proof of Proposition~\ref{prop:non-extreme-decomp} apply verbatim
and yield only $|\varepsilon_g|\leq\tfrac{1}{2}$; note that in item~(3) the two short sides are
adjacent in $\Gamma_d$ and hence lie in a common component with opposite signs, so the
degeneracy persists. Item~(4) gives the second family.
\end{proof}

\begin{theorem}\label{thm:non-extreme-general}
Let $d\in\mathcal{H}_n$ and let $N=\dim P_d$ be the number of bipartite components of
$\Gamma_d$, isolated nodes included. Then $d$ is a convex combination of at most $2^N$
extreme points of $\bar{\mathcal{M}}_n$, each with denominator of the form $2^i3^j$ where
$i+j\leq N+1$.
\end{theorem}

\begin{proof}
We bisect $P_d$ repeatedly. Let $p$ lie in $P_d$ and let $L_p$ be the lineality space of the
smallest face of $P_d$ containing $p$, that is, the kernel of the constraints tight at $p$. If
$L_p=0$ then $p$ is a vertex of $P_d$, hence an extreme point of $\bar{\mathcal{M}}_n$. Otherwise
choose $0\neq v\in L_p$ and let $[t^-,t^+]$ be the set of $t$ with $p+tv\in P_d$; this set is
compact because $P_d$ is bounded, and $t^-<0<t^+$ because $p$ lies in the relative interior of
its face. Then
\[
p=\tfrac{t^+}{t^+-t^-}\,(p+t^-v)+\tfrac{-t^-}{t^+-t^-}\,(p+t^+v),
\]
a convex combination of two points lying on strictly smaller faces. Recursing on each gives a
binary tree of depth at most $N$, whose leaves are vertices of $P_d$.

For the denominators, note that $d$ has denominator $2$ and that each bisection replaces the
current point $p$ by $p+t^\pm v$, where $t^\pm$ is the ratio of a slack $\tfrac{1}{2}-c\cdot p$
to a coefficient $c\cdot v$. Normalising $v$ to be integral, $c\cdot v$ is an integer of absolute
value at most $3$, since each constraint of Proposition~\ref{prop:face} has at most three terms
with coefficients $\pm1$. Hence each step multiplies the denominator by at most $3$, and after at
most $N$ steps the denominator divides $2\cdot 2^a3^b$ with $a+b\leq N$.
\end{proof}

\begin{remark}
The bound $i+j\leq N+1$ is far from what is observed. Exhaustive computation for $n\leq 5$ and
sampling for $6\leq n\leq 10$ produce, along every branch of the bisection, only the
denominators $1,2,3,4,6$. This suggests a bound independent of $n$ altogether; see
Conjecture~\ref{conj:den12}.
\end{remark}""",
    "Theorem 5.6: replaced by face description + bisection")

# ---------------------------------------------------------------- Proof of 5.2
rep(r"""\begin{proof}[Proof of Theorem~\ref{thm:upper-half}]
By Corollary~\ref{cor:upper-cube} and Lemma~\ref{lem:simplex}, $d\in\bar{\mathcal{M}}_n^{\geq1/2}$
is a convex combination of half-one metrics; by Theorem~\ref{thm:non-extreme-general} each
non-extreme half-one decomposes further. The bound $i+j\leq(m+1)/2$ comes from the
maximum number of non-trivial components of a partition of $m$ edges with at least one
isolated point (pair off $m-1$ edges, giving $\lfloor(m-1)/2\rfloor$ pairs plus one
isolated, so at most $(m+1)/2$ steps when $m$ is odd).
\end{proof}""",
    r"""\begin{proof}[Proof of Theorem~\ref{thm:upper-half}]
By Corollary~\ref{cor:upper-cube} and Lemma~\ref{lem:simplex}, $d\in\bar{\mathcal{M}}_n^{\geq1/2}$
is a convex combination of at most $m+1$ half-one metrics; by
Theorem~\ref{thm:non-extreme-general} each non-extreme half-one decomposes further, with
$i+j\leq N+1\leq m+1$ since $\Gamma_d$ has at most $m$ components.
\end{proof}

\begin{conjecture}\label{conj:den12}
Every $d\in\bar{\mathcal{M}}_n^{\geq 1/2}$ is a convex combination of extreme metrics whose
denominators divide $12$, uniformly in $n$.
\end{conjecture}

The bisection of Theorem~\ref{thm:non-extreme-general} realises this in every case we have
computed. The obstruction to a proof is that the coefficient $c\cdot v$ may equal $2$ or $3$ at
a second bisection as well as a first, and we have no argument forbidding the compounding that
would produce a denominator $8$, $9$ or $12$; no such compounding was observed.""",
    "Proof of 5.2 + denominator-12 conjecture")

# ---------------------------------------------------------------- Theorem 6.3 proof
rep(r"""Conversely, if $\tau^C$ has only positively signed and polar edges, $\varepsilon<0$
violates no triangle inequalities from $\tau^C$, so $p_\tau$ generates a feasible ray
intersecting $\bar{\mathcal{M}}_n$ at a second point $d_\tau$. By
Proposition~\ref{prop:non-extreme-decomp}, $d_\tau$ is a partition metric or a metric with denominator $3$.
\end{proof}""",
    r"""Conversely, suppose $\tau^C$ has only positively signed and polar edges. A positively
signed edge imposes $\varepsilon\geq 0$ and a polar edge imposes nothing, so $\varepsilon>0$
violates no constraint coming from $\tau^C$. Every constraint of $\bar{\mathcal{M}}_n$ not
tight at $d$ is strictly satisfied there, so small $\varepsilon>0$ remains feasible and
$p_\tau$ generates a feasible ray meeting the boundary at a second point $d_\tau$. The face
cut out by the unital constraints together with the degeneracies indexed by $\tau$ is
one-dimensional, since $\tau$ is a spanning tree, so $d_\tau$ is extreme. The upper bound on
$\varepsilon$ comes either from a bounding constraint, giving $\varepsilon=\tfrac{1}{2}$ and a
partition metric, or from an equilateral triangle, whose coefficient lies in $\{1,3\}$ by
item~(4) above and gives $\varepsilon\in\{\tfrac{1}{2},\tfrac{1}{6}\}$, hence denominator $3$.
\end{proof}""",
    "Theorem 6.3 proof: sign of epsilon")

# ---------------------------------------------------------------- Corollary 6.4
rep(r"""When a neighbor exists, $d_\tau$ is either a cover of an extreme half-one metric or an
extreme metric with denominator $6$.
\end{corollary}

\begin{proof}
Apply Theorem~\ref{thm:neighbor} to one coproduct (disjoint union) summand. Edge lengths in $\kappa$ become
either $\{0,1\}$ (denominator $2$ with other half-lengths) or $\{\tfrac{1}{3},\tfrac{2}{3}\}$
(denominator $6$ with other half-lengths).
\end{proof}""",
    r"""When a neighbor exists, $\den(d_\tau)\in\{2,4,6\}$: the edges of $\kappa$ take values in
$\{0,1\}$, in $\{\tfrac{1}{4},\tfrac{3}{4}\}$, or in $\{\tfrac{1}{3},\tfrac{2}{3}\}$
respectively, while all other non-unital edges remain at $\tfrac{1}{2}$.
\end{corollary}

\begin{proof}
The perturbation $\eta_\tau$ is supported on $\kappa$, so an equilateral triangle contributes
the constraint $(s_{E_a}-s_{E_b}-s_{E_c})\varepsilon\leq\tfrac{1}{2}$ with the terms outside
$\kappa$ deleted. The coefficient therefore ranges over $\{\pm1,\pm2,\pm3\}$ rather than
$\{\pm1,\pm3\}$, and the first blocking constraint gives
$\varepsilon\in\{\tfrac{1}{2},\tfrac{1}{4},\tfrac{1}{6}\}$. Since the edges outside $\kappa$
retain the value $\tfrac{1}{2}$, the denominator of $d_\tau$ is $2$, $4$ or $6$.
\end{proof}

\begin{example}
All three values occur. Denominator $4$ appears already at $n=6$: taking
$\mathcal{N}_d=\{[1,2],[1,3],[1,4],[1,5],[1,6],[2,3],[2,4],[2,5]\}$ and $\kappa$ the component
of $[1,2]$, one obtains the extreme metric
\[
d_{12}=d_{14}=\tfrac{1}{4},\quad d_{13}=d_{15}=d_{16}=\tfrac{3}{4},\quad
d_{23}=d_{24}=d_{25}=\tfrac{1}{2},\quad d_E=1\ \text{otherwise},
\]
whose tight constraints have rank $15=\binom{6}{2}$. Denominator $6$ first appears at $n=7$.
\end{example}""",
    "Corollary 6.4: denominators 2,4,6")

# ---------------------------------------------------------------- equation (1)
rep(r"""\begin{equation}\label{eq:triple-prob}
P_q = \tfrac{1}{2} - \tfrac{1}{2q^2}.
\end{equation}

\begin{proof}[Derivation of \eqref{eq:triple-prob}]
Fix $a_3=k$. The number of pairs $(a_1,a_2)$ with $a_1+a_2<k$ is $\binom{k}{2}$.
Summing over $k=1,\ldots,q$ gives $\binom{q+1}{3}$ infeasible ordered triples per
inequality; since a failing triple automatically passes the other two, the total infeasible
count is $\tfrac{q(q+1)(q-1)}{2}$, and the feasibility probability is as claimed.
\end{proof}

As $q\to\infty$, $P_q\to\tfrac{1}{2}=\mathrm{Vol}(\bar{\mathcal{M}}_3)$.""",
    r"""\begin{equation}\label{eq:triple-prob}
P_q = \tfrac{1}{2} + \tfrac{1}{2q^2}.
\end{equation}

\begin{proof}[Derivation of \eqref{eq:triple-prob}]
Fix $a_3=k$. The number of ordered pairs $(a_1,a_2)$ of levels with $a_1+a_2<k$ is
$\binom{k+1}{2}$. Summing over $k=0,\ldots,q-1$ gives $\binom{q+1}{3}$ infeasible ordered
triples per inequality; since a failing triple automatically passes the other two, the total
infeasible count is $\tfrac{q(q+1)(q-1)}{2}$, and
$P_q=1-\tfrac{(q+1)(q-1)}{2q^2}=\tfrac{1}{2}+\tfrac{1}{2q^2}$.
\end{proof}

As $q\to\infty$, $P_q\to\tfrac{1}{2}=\mathrm{Vol}(\bar{\mathcal{M}}_3)$, the approach being
from above.""",
    "equation (1): sign and model")

rep(r"""To understand why, we analyze the density of $q$-level points (rational points in
$[0,1]^m$ with denominator $q$) that are metrics. A random triple from $\{1,\ldots,q\}^3$
satisfies the triangle inequality with probability""",
    r"""To understand why, we analyze the density of $q$-level points that are metrics. Here the
$q$ levels are $0,\tfrac{1}{q-1},\ldots,1$, so that a $q$-level point of $[0,1]^m$ has
denominator dividing $q-1$. A random triple of levels satisfies the triangle inequality with
probability""",
    "q-level model")

def main():
    s = open(SRC, encoding="utf-8").read()
    for old, new, tag in R:
        if old not in s:
            print("MISSING TARGET:", tag, file=sys.stderr)
            print(repr(old[:120]), file=sys.stderr)
            sys.exit(1)
        if s.count(old) != 1:
            print("AMBIGUOUS TARGET:", tag, s.count(old), file=sys.stderr)
            sys.exit(1)
        s = s.replace(old, new)
        print("applied:", tag)
    import os
    os.makedirs(os.path.dirname(DST), exist_ok=True)
    open(DST, "w", encoding="utf-8").write(s)
    print("wrote", DST)

if __name__ == "__main__":
    main()
