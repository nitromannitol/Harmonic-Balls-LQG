# Post-contact obstacle boundary layer: unresolved

The actual-infimum potential-theoretic infrastructure incorporates work by Leonardo Bonanno.
No post-contact boundary-layer estimate was established in this audit.

The scope gap is in corrected paper lines 824–836: Proposition 5.2 asserts continuity for every positive time, whereas its cited Proposition 7.2 (lines 2021–2026, proof lines 2038–2058) assumes compact containment and uses full mass. This is a gap in the cited argument, not a counterexample to the proposition.

The new `leastSupersolutionOn_uniform_lipschitz_time` (GeneralDomainTimeConvexity.lean:115) is uniform in space for the *values* of the least supersolution; it does not by itself provide a positive lower bound on the size of its noncontact set. `general_odometer_mass_decomposition` (GeneralDomainObstacleMass.lean:171) is an identity of distributions on the open domain; its compact-containment corollary cannot be applied after contact. `candidate_noncontact_eq_clusterOn` (GreenRegularObstacleCharacterization.lean:169) characterizes the actual infimum but does not supply a boundary nondegeneracy estimate. None controls the rate at which a positive noncontact layer can thin toward the circle.

The exact unproved deterministic geometric claim that would enable the existing reduction, stated here as a goal rather than an input, is the following. The intended hypotheses include local finiteness and volume growth (and any further LQG-specific hypotheses actually required); no proof or validity for all such measures is claimed:

```lean
∀ x ∈ sphere (0 : ℂ) 1, x ∉ closure (cluster μ 1 z t) →
  ∀ d : ℝ, 0 < d → ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : ℕ,
    x ∈ closure (cluster μ 1 z (t + dyadicScale n)) →
    ∃ y ∈ ball (0 : ℂ) 1,
      ball y ρ ⊆ cluster μ 1 z (t + dyadicScale n) ∩ ball x d
```

The relevant regime is `z ∈ ball (0 : ℂ) (1 / 2)`, `0 < t`, boundary contact, and `μ (cluster μ 1 z t) < ENNReal.ofReal t`. Under the explicit hypotheses of `cluster_right_continuity_of_boundary_interior_ball` (BoundaryInteriorBallContinuity.lean:49), this claim yields continuity. But `cluster_right_continuity_iff_boundary_interior_ball` (BoundaryInteriorBallNecessity.lean:86) shows it is equivalent to continuity under the already available mass/interior hypotheses: simply assuming it would rename the goal. An actual PDE-derived nondegeneracy estimate or a different geometric argument is still needed.

The existing `exists_open_connected_arc_boundary_jump` (MacroscopicBoundaryJumpModel.lean:197) gives open, connected, increasing sets with vanishing area increments, no new interior limit points, and a macroscopic new boundary arc. It is not an obstacle-cluster counterexample, and does not establish falsity of the proposed LQG assertion. It does show that the existing mass and topology conclusions alone cannot close the gap. `ae_future_closure_inter_ball_subset_closure` (InteriorTimeContinuity.lean:55) and `ae_cluster_right_continuity_of_sphere_inclusion` (line 80) record the corresponding conditional actual-cluster reduction, with their explicit hypotheses. First-contact and full-mass cases are handled separately in ContactScaledContinuity.lean:78 and MassSaturationContinuity.lean:74; neither covers the general deficient post-contact case.

No new Lean declaration or literature input is added. No claim of numbered-result closure is made.
