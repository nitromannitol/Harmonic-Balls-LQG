# Geometric radial circle-average strong law

Task: `circle-average-geometric-radial-strong-law`.

For each fixed real `q > 1`, `IsWholePlaneGFF.ae_geometric_circle_radial_strong_law`
proves, on one probability-one event, convergence to zero of both
`hcirc ω (q ^ n) 0 / (n * Real.log q)` and
`hcirc ω (q⁻¹ ^ n) 0 / (n * Real.log q)` as `n → ∞`.
The statement quantifies over `q` outside the almost-sure event; it does not
assert one event simultaneously for all `q`. Division at `n = 0` uses Lean's
total real division and does not affect the limit.

The GFF and its unit-circle normalization are as defined in `Defs/GFF.lean`;
compare corrected paper lines 350–390, especially the covariance kernel and
normalization. `variance_circle_origin` derives the exact variance `|log r|`
from the concentric-increment variance and the almost-sure normalization.
Thus the variance along either geometric sequence is `n * log q`.

The general auxiliary Gaussian estimate uses a fixed exponential tilt and gives
`P(|Xₙ| > a n) ≤ 2 exp(-a² n / (2 b))` when `Var Xₙ = n b`, for
`a, b > 0`, including `n = 0`. Its right-hand side is summable. The first
Borel–Cantelli lemma and the countable tolerances `1 / (k + 1)` yield the
limit; no independence or Brownian identification is used. No external or
proposed input is introduced. This is a field ingredient only and does not
establish annular metric growth, properness, or a numbered-result closure.

The Lean source credits Leonardo Bonanno through its pinned LatticeProb import
closure. The printed axioms of both public declarations are `propext`,
`Classical.choice`, and `Quot.sound`.
