# General-domain fixed-pole Green Laplacian

`HarmonicBalls.hasLaplacian_greenFunction_bounded_domain` proves
`HasLaplacian (greenFunction V z) 0 (Measure.dirac z) V` for bounded open
`V` and `z ∈ V`. It is an analytic leaf, not a numbered-result closure.

The proof encloses `V` in a disc and uses
`exists_harmonicOnNhd_greenFunction_difference`. The correction has the sign
`G_V - G_disc = h` away from the pole. The disc identity and the zero
distributional Laplacian of `h` supply local integrability and the test
identity; the singleton pole is volume-null. No Green reciprocity or
variable-source integration is used. The fixed-disc form of this argument
also appears in `Proofs/Sec5/GeneralDomainObstacleMass.lean`.

The printed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The potential-theoretic infrastructure uses work of Leonardo Bonanno.
