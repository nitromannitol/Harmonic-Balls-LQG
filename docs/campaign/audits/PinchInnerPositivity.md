# Pinch-event measurable positive subset

`HarmonicBalls/Proofs/Sec11/PinchInnerPositivity.lean` proves the measurable
subset bridge at an arbitrary center and positive scale. Its inputs are a
pinch configuration, coordinate measurability of `D`, an almost-sure
Euclidean length metric, almost-everywhere measurability and almost-sure
local finiteness of the random measure, and positive outer measure of the
strengthened internal-bound event. The first theorem constructs a measurable
positive subset of that event. The second constructs one in the ordinary
pinch event and the length-metric realizations simultaneously.

The proof takes a fixed-center section of the existing jointly measurable
representative, uses its almost-everywhere agreement to obtain null
measurability, and takes a measurable subset equal almost everywhere. It
then intersects with a measurable full-measure subset of the length-metric
realizations and applies `pinchPointEvent_of_internalBounds`. Thus positivity
of an arbitrary nonmeasurable event alone is not used as inner positivity.

`pinchEventPositiveProbabilityStmt_of_internal_outer_positive` is a conditional
consumer of the frozen Lemma 11.12 statement. Its hypothesis chooses the four
configuration sets before γ, ξ, the probability space, field, measure, metric,
and M, and supplies the above regularity and strengthened outer positivity for
every choice satisfying the frozen hypotheses. In particular it does not assume
or prove inner positivity. It does not supply the common constrained-event
positivity, the metric coordinate measurability, or the necessary field-law
and Weyl-shift inputs. No numbered result is closed by this conditional result.
