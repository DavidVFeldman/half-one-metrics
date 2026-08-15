#!/usr/bin/env python3
"""Second-pass edits to article2_v2.tex:
   (a) correct the transposed Avis / Bandelt-Dress bibliography data,
   (b) remove per-theorem attribution tags (house standard for joint work),
   (c) cite the four bibliography entries that were never cited."""
import sys

P = "/home/claude/work/out/article2_v2.tex"
R = []
def rep(old, new, tag): R.append((old, new, tag))

# ---- (a) bibliography ------------------------------------------------------
rep(r"""\bibitem{Avis80}
D.~Avis, On the extreme rays of the metric cone,
\textit{Advances in Mathematics} no.~1 (1992), 47--105.""",
    r"""\bibitem{Avis80}
D.~Avis, On the extreme rays of the metric cone,
\textit{Canad.\ J.\ Math.}~32 no.~1 (1980), 126--144.""",
    "bib: Avis")

rep(r"""\bibitem{Dress92}
A.~Dress and H.-J.~Bandelt, A canonical decomposition theory for metrics on a finite set,
\textit{Canad.\ J.\ Math.}~32 no.~1 (1992), 126--144.""",
    r"""\bibitem{Dress92}
H.-J.~Bandelt and A.W.M.~Dress, A canonical decomposition theory for metrics on a finite
set, \textit{Advances in Mathematics}~92 no.~1 (1992), 47--105.""",
    "bib: Bandelt-Dress")

rep(r"""\bibitem{Berrend10}
D.~Berrend and T.~Tassa,""",
    r"""\bibitem{Berrend10}
D.~Berend and T.~Tassa,""",
    "bib: Berend spelling")

rep(r"""J.~Spencer, Maximal consistent families of triplets, \textit{J.\ Combinatorial Theory}
(1968), 1--8.""",
    r"""J.~Spencer, Maximal consistent families of triples, \textit{J.\ Combinatorial Theory}~5
(1968), 1--8.""",
    "bib: Spencer volume")

rep(r"""\bibitem{Kehoe-extremeRays}
E.R.~Kehoe, Extreme rays of the metric cone and the metric body: bowtie metrics and
half-one extremality (companion paper).""",
    r"""\bibitem{Kehoe-extremeRays}
E.R.~Kehoe, \textit{Extreme rays of the metric cone and the metric body},
Ph.D.\ dissertation, Colorado State University, Fort Collins.""",
    "bib: companion paper -> dissertation")

# ---- (c) uncited entries ---------------------------------------------------
rep(r"""irreducible building blocks for all metrics, and the problem of classifying them is
central to discrete geometry and phylogenetics \cite{Deza97, Dress92}.""",
    r"""irreducible building blocks for all metrics, and the problem of classifying them is
central to discrete geometry and phylogenetics \cite{Deza97, Dress92}. The corresponding
question for the metric cone was opened by Avis \cite{Avis80}, and the extreme metrics on
at most six points were classified by Koolen, Moulton and T\"onges \cite{Koolen00}.""",
    "cite Avis, Koolen")

rep(r"""A \emph{germ} is a connected subgraph of $\Gamma_d$ containing exactly one odd cycle;""",
    r"""Graph-theoretic terminology follows Bondy and Murty \cite{Bondy08}.
A \emph{germ} is a connected subgraph of $\Gamma_d$ containing exactly one odd cycle;""",
    "cite Bondy-Murty")

rep(r"""To understand why, we analyze the density of $q$-level points that are metrics.""",
    r"""To understand why, we analyze the density of $q$-level points that are metrics; for the
general theory of lattice-point counting in polytopes see Beck and Robins \cite{Beck09}.""",
    "cite Beck-Robins")

# ---- (b) attribution tags --------------------------------------------------
for tag in ("[Kehoe, 2019]", "[Kehoe, 2018]", "[Kehoe]"):
    pass  # handled below by scan

def main():
    s = open(P, encoding="utf-8").read()
    for old, new, tag in R:
        if s.count(old) != 1:
            print("TARGET PROBLEM:", tag, s.count(old), file=sys.stderr)
            sys.exit(1)
        s = s.replace(old, new)
        print("applied:", tag)
    n = 0
    for env in ("theorem", "proposition", "corollary", "conjecture", "lemma"):
        for tag in ("[Kehoe, 2019]", "[Kehoe, 2018]", "[Kehoe]"):
            old = "\\begin{%s}%s" % (env, tag)
            n += s.count(old)
            s = s.replace(old, "\\begin{%s}" % env)
    s = s.replace("[Gauss-Bonnet conjecture, Kehoe]", "[Gauss-Bonnet conjecture]")
    print("attribution tags removed:", n + 1)
    open(P, "w", encoding="utf-8").write(s)
    print("rewrote", P)

if __name__ == "__main__":
    main()
