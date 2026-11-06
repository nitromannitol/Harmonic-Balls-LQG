# General-domain quadrature audit

Source: corrected paper, Section 4 lines 773–786 and appendix lines 3797–3827. The appendix retains the dominated frontier mass. The cutoff proof here works in an arbitrary open U under compact containment; no regularity of ∂U is assumed.

All declarations use the actual cluster `clusterOn μ U z t` and the actual odometer `leastSupersolutionOn μ U z t + t * greenFunction U z`. Hypotheses: μ locally finite, `VolumeGrowth μ R βm βp`, `0 < R`, U open and contained in the radius-R ball, z ∈ U, t > 0, and closure of the cluster contained in U. The frontier measure ν is supplied by `general_odometer_mass_of_compact_containment`, satisfies ν ≤ μ, and participates in the actual `HasLaplacian` identity. Each existential theorem may choose its own such ν.

`general_clusterOn_harmonic_quadrature`: every real function harmonic on an open neighborhood O of the closure is integrable against μ restricted to the cluster plus ν restricted to its frontier, and its integral is t times its value at z.

`general_clusterOn_smooth_laplacian_quadrature`: the analogous inequality for `ContDiffOn ℝ ∞` functions with nonnegative classical Laplacian on O. The odometer is nonnegative off the pole, whose volume is zero.

The frontier-null corollaries explicitly consume `μ (frontier Λ) = 0`, remove the frontier term, and give mass equality, harmonic quadrature and mean value, plus the smooth inequality. They do not use a boundary regularity or admissibility hypothesis.

Remaining: extend the inequality to the requested C² subharmonic test class. `Section6.exists_compactlySupported_smooth_subharmonic_approximation` provides local uniform smooth approximation with nonnegative Laplacian on compact sets; passage to the limit for the finite obstacle measure remains to be formalized. The paper's enlarged Green-potential test class and numbered-result closure are not established here.
