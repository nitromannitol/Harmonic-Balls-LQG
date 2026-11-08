# Fixed circle-average Gaussian tail

`IsWholePlaneGFF.circleAverage_gaussian_tail` fixes a positive radius and a centre before choosing positive constants depending on the threshold and the fixed circle. It bounds the strict absolute-value event for every natural number, including zero, with `ENNReal.ofReal (C * exp (-c * n^2))`.

The Gaussian law and zero mean are supplied by `IsWholePlaneGFF`; the proof transfers the Gaussian exponential moments through its law and applies the two Chernoff bounds. The denominator is the variance plus one, hence positive even for a degenerate Gaussian. The union bound uses outer measure and does not require an unstated measurable representative of the event. No new literature premise is used. The existing compact-centre variance bound found in `FixedSquareFrontierNull` is restricted to radii at most one, so no general-radius uniform variant is asserted here.

The import closure contains code by Leonardo Bonanno, through LatticeProb as documented in `FixedSquareFrontierNull`. The proof follows the existing Chernoff pattern in `Sec2/CircleAverageTail`. The declaration's printed axioms are `propext`, `Classical.choice`, and `Quot.sound`. The source scan found no forbidden proof tokens.
