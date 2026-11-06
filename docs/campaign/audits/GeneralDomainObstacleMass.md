# General-domain obstacle mass

Scope: the frozen `supersolutionsOn`, `leastSupersolutionOn`, and `clusterOn`
in `HarmonicBalls/Draft/Section5.lean`; this is a deterministic general-domain
analogue of the appendix distributional identity at
`paper/lqg_harmonic_ball-corrected.tex:3797`–`:3803`, and of the compactly
contained case of `:3804`–`:3827`. It does not close a numbered result or
resolve all of G9.

For a locally finite measure μ on ℂ, positive enclosing radius R, the stated
`VolumeGrowth μ R βm βp`, open `U ⊆ ball 0 R`, `z ∈ U`, and `t > 0`, the
module proves the distributional inequality `Δu ≥ 0` on `U \ {z}`, for the
actual frozen infimum and `u(x) = leastSupersolutionOn μ U z t x + t *
greenFunction U z x`. It proves existence of `ν ≤ μ` with
`Δu = μ|Λ + ν|frontier Λ − ofReal(t) δ_z` on U. The cluster Λ includes z
by definition; off z the obstacle inequality follows from the GLB, and the
odometer vanishes on `U \ Λ`.

The proof uses the general-domain infimum's interior continuity and Laplacian
bound, openness and harmonicity of the shifted infimum on Λ, and the enclosing
disc potential q. On noncontact discs, the shifted infimum and the Green
function are harmonic while q is superharmonic. On contact discs the
nonnegative odometer vanishes at the centre. The resulting local sub-mean
property implies the distributional inequality. The general Green identity
is derived from the disc identity and the harmonic correction; the identity
need only hold almost everywhere at the pole for integration against area.
`obstacleConservationOfMassStep2_holds` then consumes the shift `w = v + q`,
`q`, this Green identity, and the off-pole inequality. The Green potential and
test functions use the locally finite-measure and compact-support hypotheses
already required by these distributional APIs. The potential-theoretic
infrastructure uses work of Leonardo Bonanno. No new literature input is
introduced.

When `closure Λ ⊆ U`, boundedness of U makes the closure compact. A smooth
cutoff equal to one on a neighborhood of this closure has zero Laplacian there;
the odometer is zero outside the closure within U, and the cutoff is supported
in U. Testing yields `μ Λ + ν (frontier Λ) = ENNReal.ofReal t` and therefore
`μ Λ ≤ ENNReal.ofReal t`. Both restricted measures are supported on the
closure, and Λ is open, so their cutoff integrals equal their total masses.
The frontier term is retained: no boundary-null claim is used or proved.
There is no regularity or admissibility assumption on the boundary of U and
no weak normal derivative is invoked.

All eight declarations' `#print axioms` report only `propext`,
`Classical.choice`, and `Quot.sound`. The measure identity is on U; the point
value of the Green function is the repository convention, with its pole
singularity understood distributionally rather than as an infinite real value.
