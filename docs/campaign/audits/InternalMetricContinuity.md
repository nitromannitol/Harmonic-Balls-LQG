# Internal distance continuity and countable diameter (h3, 2026-11-08)

The declarations in `HarmonicBalls/Proofs/Metric/InternalMetricContinuity.lean`
are helper results, not closures of numbered paper results. They assume no
additional literature inputs and do not use Pfeffer Definition 1.6 or Prop. 4.6.

## Results and dependencies

* Existing `Steps/Sec11/InternalMetricContinuity.lean:61,119` proves joint
  continuity on `U × U` for every open `U`; infinity is allowed. The proof
  uses local equality to the ambient metric and the internal triangle
  inequality. `continuousOn_internalDistance_pair` removes the redundant
  nonnegativity hypothesis via `distance_nonneg`.
* `iSup_internalDistance_eq_dense_seq` uses continuity and `Dense.ciSup`
  to reduce the supremum on arbitrary `K,L ⊆ U` to any fixed sequences
  dense in the relative topologies. Compactness and connectedness are not
  needed. The existence of an `ℕ → K` assumes `K` is nonempty; if `K` or
  `L` is empty the corresponding supremum is zero directly.
* `compact_internalDiameter_eq_dense_seq_lt_top` combines this equality
  with existing `internalDistance_compact_uniform_lt_top` for compact `K`
  in connected open `U`. No finiteness across different components is claimed.
* `measurable_iSup_internalDistance_of_dense_seq` proves measurability when
  every sample is a length metric and the countable evaluations are measurable.
  `aemeasurable_iSup_internalDistance_of_dense_seq` requires the countable
  internal-distance evaluations to be a.e. measurable. The representative
  theorem accepts a measurable version of each evaluation with individually
  a.e. equalities, combining them by a countable intersection.
* `SatisfiesLQGMetricAxioms.exists_local_internalDiameter_representative`
  obtains the point versions from locality and gives a representative
  measurable in `pairingSigmaAlgebra h U`. The a.e. equality uses the original
  measure space; no unproved inclusion of sigma algebras is assumed.

## Scope of the earlier z6 R2 concern

`docs/campaign/audits/MetricAnnulusScaleLaw.md:89` says axioms I–IV do not
provide continuity or a countable reduction. This is incorrect for an **open**
internal domain: the existing continuity theorem and the results above provide
both, and locality gives the stated local measurable representative. For a
closed annulus used as the path domain, these open-domain results do not apply;
no assertion for that case is made here. The paper's actual Proposition
`mass-diam-gen` (`paper/lqg_harmonic_ball-corrected.tex:2934-2940`) explicitly
uses `sup_{u,v ∈ V} D_h(u,v; W)` with `W` open; thus no choice of ambient versus
internal diameter is needed for that displayed proposition. This does not prove
any scale law or decide what a separate annulus functional means.

## Verification

The lock-free Lean check passes. The shared build and final commit are recorded
in the worker report. All seven declarations print only `propext`,
`Classical.choice`, and `Quot.sound`; the code scan finds no forbidden constructs.
