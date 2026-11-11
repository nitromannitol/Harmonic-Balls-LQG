# Section 11 pinch metric-field consumer

`archive/HarmonicBalls/Audit/Section11PinchMetricFieldConsumer.lean` proves conditional
measurable-subset consumers for the original raw events. The imported
potential-theoretic infrastructure includes code by Leonardo Bonanno.

For arbitrary fixed `U T Q' Q` satisfying `IsPinchPointConfiguration`, real
`M` and centre `z`, positive `r`, `0 < γ < 2` and `α₀ < lqgQ γ`, the first
consumer assumes the staged `LQGMetricFieldAxioms`, the whole-plane GFF,
the LQG measure and metric predicates, and strictly positive outer measure of
the raw strengthened event. It produces a measurable positive subset contained
pointwise in that raw event. The second produces a measurable positive subset
of the raw ordinary event on which the original `D ω` is a Euclidean length
metric at every point of the subset. No positivity of `M` or `ξ` is needed by
these two consumers.

The first proof uses the existing null-measurability theorem in
`Steps/Sec11/PinchMetricMeasure.lean:119`, which itself obtains a single
pointwise measurable metric modification simultaneously for all pairs and
transfers the event by almost-sure equality. A null-measurable set has a
measurable subset of the same measure. The second intersects with a measurable
full-measure subset of the actual length-metric event, then applies the existing
pointwise internal-to-ordinary inclusion. Thus both inclusions are pointwise;
no strict coordinate measurability is asserted for an arbitrary `D`.

The last theorem returns exactly `PinchEventPositiveProbabilityStmt.{u}` at
`α₀ = 0`. Its hypothesis first chooses one configuration `U T Q' Q`, then
quantifies `γ ξ`, the measurable space, `P`, field, circle averages, measure,
metric and finally `M > 0`, exactly as in the frozen target. For each such
choice it requires the staged metric-field axioms and outer positivity of the
strengthened event at scale 1 and centre 0. It derives `0 < lqgQ γ` from
`0 < γ`. It does not infer the uniform configuration, the metric-field axioms,
or outer positivity from the frozen target's hypotheses.

This closes the measurable-subset and a.e. length-metric bridge identified in
`Section11PinchPositivity.md`, conditional on those assumptions, but does not
close Lemma 11.12. The buffered common-event positivity and shifted joint law
in `BufferedPinchCanonicalLaw.lean:29–44`, including their uniform
configuration and parameter scope, remain to be proved. Positive internal
metric-diameter moments and the identification/scope of physical ξ remain
under source review (fleet `INPUT-REQUESTS.md:190–206,250–264`); those
producers assume `0 < ξ`, while the frozen consumer quantifies arbitrary ξ.
The staged metric-field proposition in `Proposed/LQG.lean` remains pending
operator source-check. Rooted/Palm transfer and frequency remain separate
obligations for 11.13. C11 and the keyhole-encoding caveat in the existing
auditor's report remain unresolved source/semantic issues. No numbered result
or staged input is asserted as proved.
