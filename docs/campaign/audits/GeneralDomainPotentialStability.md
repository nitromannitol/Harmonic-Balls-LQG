# General-domain potential perturbation stability

Scope: the frozen `supersolutionsOn`, `leastSupersolutionOn`, and `clusterOn`
(`HarmonicBalls/Draft/Section5.lean:103`, `:109`, `:114`). The corrected
paper defines the ball competitor and infimum at `paper/lqg_harmonic_ball-corrected.tex:583`
and `:588`, and describes the general-domain extension at `:1017`. The
quantitative stability estimate here is a derived deterministic statement, not
a numbered result or a source assertion of one.

For locally finite μ and ν, R > 0, independently specified volume-growth
exponents for each measure on the same enclosing disc, open U contained in
that disc, z in U, and t ≥ 0, a bound by ε on the absolute difference of disc
potentials throughout closure U implies the absolute difference of the actual
least supersolutions is at most 2ε there, including z. The assumption itself
forces ε ≥ 0 because z lies in the closure. The result is stronger than the
requested t > 0 and does not assume boundary regularity or admissibility.

The transfer maps a μ-competitor w to w + qμ − qν + ε. Continuity follows
from continuity of both disc potentials on the closure; their distributional
Laplacians are −μ and −ν, so the shifted zero-Laplacian inequality proves the
ν-bound. The potential comparison gives the obstacle inequality. The GLB is
used at every closure point, with the separately established pole GLB at z.
The pointwise transfer bounds the destination obstacle gap below by the source
gap minus 2ε, yielding cluster membership for a source gap strictly greater
than 2ε. The symmetric statement follows by interchanging μ and ν. Uniform
potential convergence implies uniform convergence of infima for sequences
whose locally finite measures and potentially varying growth exponents satisfy
the displayed hypotheses individually.

The off-pole obstacle and inserted-pole conventions are those of the frozen
Lean definitions. At irregular boundary points the Green function has the
repository's zero-outside convention; source equivalence of the general-domain
carrier and its boundary interpretation remains open (G9/E46). No new
literature input is introduced. The potential-theoretic infrastructure uses
work of Leonardo Bonanno. No numbered-result closure is claimed.

All five declarations' `#print axioms` report only `propext`,
`Classical.choice`, and `Quot.sound`.
