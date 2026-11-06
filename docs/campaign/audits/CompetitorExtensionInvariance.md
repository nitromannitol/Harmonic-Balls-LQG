# General-domain competitor representatives

Scope: the frozen `supersolutionsOn` and `leastSupersolutionOn` in
`HarmonicBalls/Draft/Section5.lean:103` and `:110`, on `closure U` for open U.
This is a carrier comparison, not a source or numbered-result certification.

`mem_supersolutionsOn_of_eqOn` proves that competitor membership transfers
between ambient functions agreeing on `closure U`, assuming U is measurable.
Continuity and the obstacle constraint transfer on the closure; the displayed
distributional inequality transfers on U by `LaplacianLE.congr_eqOn`.
`exists_continuous_supersolutionOn_eqOn` applies Mathlib's closed-set Tietze
extension theorem to the continuous restriction and obtains a globally
continuous competitor agreeing on the closure. The empty carrier is included.

`supersolutionsOn_continuous_image_eq` proves equality of the evaluation images
at every point of `closure U`, and `leastSupersolutionOn_eq_sInf_continuous`
therefore proves equality of their real infima. These results assume only that U
is open; they do not require existence of a competitor, boundedness of the
evaluation set, or a separate hypothesis at the pole. Equality of sets gives
equality of real `sInf` values even when those values have junk semantics.

The results do not assert equality outside the carrier. The existing
`Section5InfimumSemantics.md` explains the unbounded-below unrestricted
ambient evaluations there. Irregular-boundary convention, Green-function
semantics, field/measure encodings and test-class certification remain open.
The Lean proof uses potential-theoretic infrastructure of Leonardo Bonanno.
