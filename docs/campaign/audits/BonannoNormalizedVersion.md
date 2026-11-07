# Bonanno normalized distribution version

Leonardo Bonanno's `DistC`, full-test coordinate inverse, normalized GFF,
measurable circle averages and canonical existence are used here. From the
project's `IsWholePlaneGFF P hC hcirc`, `reconstructedGFF hC` is measurable,
has the same distribution-valued law as any Bonanno normalized GFF on a
probability space, and satisfies `LQGMetric.IsNormalizedWPGFF`. The latter
includes the exact almost-sure equation `circleAvg H 1 0 = 0`.
For each fixed `r > 0` and `z`, `hcirc r z = circleAvg H r z` almost surely;
the exceptional set may depend on `r,z`. The proof transfers a joint event
under the full admissible observation law, using the canonical circle
increment and unit normalization. It makes no simultaneous claim for all
raw circle coordinates and adds no literature premise.

The local Bonanno `Statement/GFF.lean:41-50` predicate requires measurable
`Ω → DistC`, a Gaussian process of pairings on `TestC0`, centered pairings,
`logCov` covariance and a.s. unit circle normalization. The strong metric
interface `Statement/LQGMetric.lean:36-60` acts on `DistC → ContMetric` and
requires `IsGFFPlusCont h P` for its fieldwise axioms; that predicate requires
a measurable continuous-function shift of an `IsWholePlaneGFF` field
(`Statement/GFF.lean:53`). The current bridge proves the normalized GFF
part, not the metric interface or a log-singular shift.

The operator's source map identifies unported `LQGMetric/Assembly/MainFinal.lean:40`
`theorem12_proved : Theorem12`, with `Theorem12` in the unported
`Statement/Thm12.lean:49`. It is not locally available, and its proof closure
has not been audited here. The ported `Statement/Dimension.lean:48-62` defines
`IsLGDExponent γ χ` using zero-boundary GFF on the unit square, `chiDZZ` via
choice when a positive exponent exists (fallback `1/2`), `dGamma = 2/chiDZZ`
and `xiGamma = γ/dGamma`. A future application still needs the port and
closure check, the DZZ existence/physical exponent identification, and the
metric-interface translation; this bridge establishes none of those claims.
