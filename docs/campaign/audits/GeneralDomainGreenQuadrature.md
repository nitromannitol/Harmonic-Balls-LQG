# General-domain Green quadrature: partial audit

Source: corrected paper, Section 4, lines 749–786, and the Section 5 general-domain extension. The frontier-null hypothesis remains explicit. No numbered result is claimed here.

`general_clusterOn_obstacle_mass_le` proves domination of the obstacle mass by the original measure, using openness of the cluster and domination of the frontier measure. `integrable_greenFunction_ball_obstacle_mass` uses volume growth and compact containment to integrate the enclosing-disc Green kernel against this full mass, including frontier poles. `integrable_greenFunction_source_of_compact` gives the required Green-kernel integrability at a pole avoided by a finite compactly supported source measure.

`general_clusterOn_green_quadrature_away_closure` applies the existing harmonic quadrature to the kernel with the pole outside the closed cluster. Its kernel is oriented as `greenFunction O y x`; it does not establish the frozen test-class identity, which uses `greenFunction O x y`. `general_clusterOn_isHarmonicBall_of_frontier_null` establishes the ordinary harmonic-ball definition only.

The general-domain pointwise potential representation, frontier-pole quadrature, product integrability and Fubini, and `harmonicBallTestClass` consumer remain to be proved. The distributional odometer equation is a hypothesis of the away-closure lemma and is supplied for the same dominated frontier measure by `general_odometer_mass_of_compact_containment`. No new literature premise is introduced. The μ-null frontier is not established here.
