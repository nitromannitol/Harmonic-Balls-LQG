# General-domain affine covariance audit

Task: `general-domain-affine-covariance`. The deterministic results implement
Section 3.1, corrected paper lines 583–596, and the scaling comparison in Lemma
5.7, lines 885–925, for the general-domain definitions in Draft/Section5.lean
lines 103–116. The general-domain extension is discussed at paper lines
1013–1017. This is infrastructure, not a proof of Lemma 5.7 or 5.8.

* `greenFunction_positive_affine`: bounded domain, positive dilation; valid
  everywhere, including the repository's zero-valued diagonal convention.
* `supersolutionsOn_comp_positive_affine` and its `_inv` counterpart: the
  explicit inverse competitor maps, with transported measure
  `ofReal c • map (fun x => k⁻¹ • (x - a)) μ`. They use continuity on closure,
  distributional inequality transport, and the actual off-pole obstacle.
* `clusterOn_positive_affine`: arbitrary bounded set U, `0 < k`, `0 < c`,
  `0 ≤ t`; measure is `ofReal c • map (fun x => a + k • x) μ`, time is
  `c*t`. Neither openness, growth, local finiteness, nor Green regularity is
  assumed. The pole branch is handled directly.
* `leastSupersolutionOn_positive_affine` and `odometerOn_positive_affine`:
  closed-domain, off-pole points under the same assumptions. The proof uses
  the real infimum and an explicit lower bound, with zero as competitor.
* `leastSupersolutionOn_positive_affine_of_bddBelow` permits every point when
  original competitor values are bounded below. The `_at_pole` specialization
  obtains that bound for bounded open U containing z under local finiteness
  and the existing enclosing-disc `VolumeGrowth` estimate. The paper's Green
  function is singular at the pole whereas the Lean kernel is zero there, so
  the displayed odometer identity is stated off-pole.

The proof composes the established arbitrary-domain Green dilation and
translation, distributional dilation and translation, and positive measure
multiplication. No literature Prop, stochastic affine law, new axiom, or
regularity assumption is used. The irregular-boundary interpretation of the
frozen definition remains the existing G9 question; this result does not
assert general-domain compatibility or numbered-result closure.
