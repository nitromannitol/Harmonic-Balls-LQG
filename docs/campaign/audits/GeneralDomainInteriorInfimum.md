# Interior regularity of the general-domain infimum

`HarmonicBalls.general_domain_interior_infimum_regularity` proves both
`ContinuousOn (leastSupersolutionOn μ U z t) U` and
`LaplacianLE (leastSupersolutionOn μ U z t) μ U`, for locally finite `μ`,
`0 < R`, `VolumeGrowth μ R βm βp`, open `U ⊆ ball 0 R`, `z ∈ U`, and
`0 < t`. The proof includes the pole and uses the actual frozen competitor
class. It assumes neither Green boundary regularity nor admissibility or
closure continuity of the infimum. The theorem concerns interior regularity;
it does not claim closure continuity or membership in `supersolutionsOn`.

The shifted infimum is upper semicontinuous. Its lower semicontinuous
regularization is a superharmonic majorant of the shifted obstacle. An interior
Poisson modification preserves the actual competitor class when a constant
bounds the obstacle above inside a disc and the shifted boundary data below.
A quantitative Harnack inequality controls these modifications. At the pole,
the shifted obstacle tends to minus infinity, giving a constant barrier. Away
from the pole, continuity of the obstacle and lower semicontinuity of the
regularization give a barrier with any positive error. Adding that error to a
competitor preserves admissibility; the Poisson modification and Harnack
inequality yield a lower bound for the original infimum with the same error.
Sending the error to zero proves lower semicontinuity, hence superharmonicity
of the actual shifted infimum and the two asserted interior conclusions.

`#print axioms` for the final theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`. The file credits Leonardo Bonanno for the
potential-theoretic infrastructure. This local theorem does not claim closure
of a numbered paper result; the separate source, definition, binder, and
dependency audits remain necessary for any such claim.
