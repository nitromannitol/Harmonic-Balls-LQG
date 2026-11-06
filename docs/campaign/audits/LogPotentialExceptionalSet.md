# Logarithmic potential exceptional set: work in progress

The E51 logarithmic exceptional-set bridge is **not yet proved**. The results in
`HarmonicBalls/Proofs/Potential/LogPotentialExceptionalSet.lean` use only the upper
positive-power volume-growth bound and finiteness on a ball. They establish:

* Every singleton has zero mass for the measure restricted to that ball.
* For any finite positive measure ν, `ν {x} = 0` for almost every x with respect
  to that bounded restriction, by applying product-measure Fubini to the diagonal.
* The existing layer-cake Riesz bound gives a uniform integral bound at poles in
  the closed ball; consequently the negative-power Riesz kernel is integrable
  against the product of ν restricted to that closed ball and μ restricted to
  the open ball.

The product result treats poles and μ-points in the same ball. For a compactly
supported ν and a smaller bounded μ-restriction, apply growth on a sufficiently
large common ball and then restrict the μ-factor. The required logarithmic bound,
product integrability of `newtonKernel`, the almost-everywhere integrability
conclusion, and the finite extended-real potential identification remain to be
proved. Neither polar-nullness nor a Green test-class equivalence follows from
the results above. In particular the real kernel has a finite junk value at the
diagonal, which is why the independent diagonal result is necessary.
