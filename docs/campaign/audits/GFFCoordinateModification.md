# GFF coordinate modifications and representation

`HarmonicBalls.Defs.GFF.IsWholePlaneGFF` (Defs/GFF.lean:93) requires
measurable deterministic test pairings, Gaussian finite-dimensional laws,
the prescribed means and covariances, and a continuous circle-average
modification. It does not require one event on which all pairings are linear.

`IsWholePlaneGFF.coordinateModification` proves all six fields survive a
measurable replacement equal almost surely at each deterministic test.
`diagonalSpike_sections` proves that a spike indexed by an injective curve
of tests has measurable, almost surely zero sections when its random index is
atomless. `IsWholePlaneGFF.exists_diagonal_modification` combines these: given
an atomless measurable parameter and samplewise linearity along that curve,
it constructs another full six-field GFF with the same circle averages and
coordinatewise pairings, whose pairings fail the indicated scalar relation
almost surely. This last result is conditional; the curve must in addition
consist of actual test functions and respect scalar multiplication to contradict
a distribution-valued representation. It is not a standalone GFF counterexample.

For a concrete construction choose nonzero smooth compactly supported φ₀ and
`a r = r • φ₀`. On the product of a distribution-valued normalized GFF and
an independent atomless real variable t (for example uniform on (1,2)), add
1 exactly when φ = t • φ₀. Every fixed φ changes on at most one t-fiber;
at each sample the relation between t • φ₀ and (2t) • φ₀ fails. Thus the
written argument identifies the precise failure of exchanging `∀ φ, ∀ᵐ ω`
with `∀ᵐ ω, ∀ φ`. The conditional theorem checks the mechanism in Lean,
but that mathematical construction is not yet a checked instance of all six
fields of this repository's GFF interface.

Leonardo Bonanno's `GFFExist.exists_normalizedWPGFF` (ExistGFF.lean:85)
constructs a distribution-valued field with his normalized GFF predicate;
`CircleAvgKolm.exists_continuous_version_circleAvg` (CircleAvgKolm.lean:175)
constructs a continuous circle-average version. `Section6.map_pairingProc_eq`
(AnnulusLawTransfer.lean:96) transfers only mean-zero pairing laws starting
from an existing project GFF. `IsWholePlaneGFF.exists_meanZero_distribution_version`
(MeanZeroDistributionVersion.lean:47) supplies equality almost everywhere
separately for each mean-zero test, not on a common event. The missing checked
bridge is a product-space construction of the project predicate for all test
and circle observables, including mixed covariances and measurable continuous
circle versions, together with its samplewise linear pairing representation.
No assertion of a full counterexample or numbered-result closure is made here.

A sufficient exact Lean target for instantiation (with the local instances
introduced after unpacking the existential) is:

```lean
∃ (Ω : Type) (m : MeasurableSpace Ω) (P : @Measure Ω m)
  (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
  (t : Ω → ℝ) (φ₀ : ℂ → ℝ),
  @IsWholePlaneGFF Ω m P hC hcirc ∧
  @Measurable Ω ℝ m _ t ∧
  (∀ r, ∀ᵐ ω ∂P, t ω ≠ r) ∧
  IsTestFunction Set.univ φ₀ ∧ φ₀ ≠ 0 ∧
  (∀ᵐ ω ∂P, hC ω (fun z => (2 * t ω) * φ₀ z) =
    2 * hC ω (fun z => t ω * φ₀ z))
```

This is a derived construction target, not a proposed literature input. The
published field construction motivating it is Bou-Rabee and Gwynne, §2.1,
equations (2.1)–(2.2), together with the jointly continuous circle-average
version cited there. The exact Lean target above is not yet compiled or
established by this audit.
