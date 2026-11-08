import HarmonicBalls.Proofs.Sec11.ClosureScales.TypicalBlockDensityFromOrigin
import HarmonicBalls.Proofs.Sec11.Closure.FixedGeometry
import HarmonicBalls.Proofs.Sec11.InternalPinchFrequency
import HarmonicBalls.Steps.Sec11.PinchMetricMeasure

/-!
# Lemma 11.13 (`ManyPinchScalesStmt`) from the rooted data step (draft lines 515-649)

The frozen statement `ManyPinchScalesStmt` (`HarmonicBalls/Draft/Section11.lean:259`) is reduced to one explicit step
Prop, `PinchRootedDataStep`. The step packages the written argument's obligations for each LQG geometry:

* the rooted comparison families (draft 565-608: marked identity, rooted laws `R z`, recentring and metric version
  `heq`, dyadic covering `ρ n`), in the shape of `ae_ae_pinch_block_density_of_recentered_rooted_law`;
* the origin data for one common law `Q` (draft 515-563: stationarity, germ triviality, locality, positivity at scale
  one, and the rate `δ < Q(internal pinch at scale 1)`), which `ae_ae_pinch_block_density_of_origin_law` consumes.

The consumer `manyPinchScalesStmt_of_rootedDataStep` proves the frozen statement from the step. It uses:
* z6's fixed geometry `exists_isPinchPointConfiguration` (`Closure/FixedGeometry.lean`, draft 271-311);
* the measurable modification of the metric `exists_measurable_metric_modification_of_metricFieldAxioms`;
* the staged metric-field axioms `LQGMetricFieldAxioms` (`Proposed/LQG.lean`), passed as the explicit hypothesis
  `hmetricAxioms` exactly as in `harmonicBallNotMetricBallStmt_of_stagedInputs` (pending operator source-check).

Nothing here is a literature input staged by this file. `PinchRootedDataStep` is an open proof obligation; the frozen
statement is not closed until it is discharged. The pointwise ergodic theorem is LatticeProb's (Leonardo Bonanno).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology ProbabilityTheory
open scoped ENNReal

universe u

open Classical in
/-- Rooted and origin data for the typical-point transfer at one LQG geometry, one mass parameter `M`, one rate `δ`
and one pinch configuration (draft 515-649). The fields are the arguments of
`ae_ae_pinch_block_density_of_origin_law`. -/
structure PinchRootedData {Ω : Type u} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (hμ : AEMeasurable μ P)
    (U T Q' Qset : Set ℂ) (M δ : ℝ) (hconfig : IsPinchPointConfiguration U T Q' Qset) : Type u where
  /-- Ambient laws `ν n` of the γ-field at dyadic scale `n` (draft 565-608). -/
  ν : ℕ → Measure Ω
  hμν : ∀ n, AEMeasurable μ (ν n)
  hlocν : ∀ n, ∀ᵐ ω ∂(ν n), IsLocallyFiniteMeasure (μ ω)
  hmetricν : ∀ n, ∀ᵐ ω ∂(ν n), IsEuclideanLengthMetric (D ω)
  /-- Weight of the weighted restriction kernel (draft 565-608). -/
  w : ℂ → ℝ≥0∞
  hw : Measurable w
  hpos : ∀ z, w z ≠ 0
  hfin : ∀ z, w z ≠ ∞
  /-- Dyadic covering measures and shifts of the marked field. -/
  ρ : ℕ → Measure ℂ
  shift : ℕ → ℂ × Ω → Ω
  hshift : ∀ n, Measurable (shift n)
  /-- Rooted laws `R n z` at each root `z`. -/
  R : ℕ → ℂ → Measure Ω
  hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
    (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
      shiftedRootReferenceLaw (ρ n) P (shift n)
  hac : ∀ n, ∀ᵐ z ∂(ρ n), P.map (fun ω => shift n (z, ω)) ≪ R n z
  hdom : ∀ n, ∀ᵐ z ∂(ρ n), R n z ≪ ν n
  /-- Recentring of the rooted sample at `z` and the common comparison law `Q`. -/
  recenter : ℂ → Ω → Ω
  hrec : ∀ n, ∀ᵐ z ∂(ρ n), AEMeasurable (recenter z) (R n z)
  Q : Measure Ω
  hQ : IsProbabilityMeasure Q
  hcomp : ∀ n, ∀ᵐ z ∂(ρ n), (R n z).map (recenter z) ≪ Q
  /-- Recentring identities for the measure and the metric (draft 583-634). -/
  heq : ∀ n, ∀ᵐ z ∂(ρ n), ∀ᵐ ω ∂(R n z),
    μ (recenter z ω) = (μ ω).map (fun y : ℂ => y - z) ∧
      ∀ x y, D (recenter z ω) x y = D ω (x + z) (y + z)
  /-- Origin indicators under `Q` (draft 515-563). -/
  X : ℕ → Ω → ℝ
  germ : ℝ → MeasurableSpace Ω
  hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ
  hX : ∀ n ω, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M
    ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0
  hXm : ∀ n, Measurable (X n)
  hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (X n)
  htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) → Q A = 0 ∨ Q A = 1
  hstat : Q.map (fun ω n => X (n + 1) ω) = Q.map (fun ω n => X n ω)
  hδ : δ < (Q {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M
    ((2 : ℝ)⁻¹ ^ 0) 0}).toReal

open Classical in
/-- **Open step (draft lines 515-649).** For every fixed pinch configuration, every `0 < γ < 2`, every `α₀ < lqgQ γ`
and every `M > 0`, there is a deterministic rate `δ ∈ (0,1)` such that, for every whole-plane GFF `P` with LQG measure
`μ` at exponent `α₀` and LQG metric `D` at exponents `(γ, ξ, α₀)`, the rooted data `PinchRootedData` exist for `μ` and
any measurable modification of `D`. Not proved here: this packages the rooted comparisons and the origin law. -/
def PinchRootedDataStep : Prop :=
  ∀ (U T Q' Qset : Set ℂ) (hconfig : IsPinchPointConfiguration U T Q' Qset) (γ α₀ ξ M : ℝ),
    0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
      (∀ x y, Measurable fun ω => D ω x y) → (∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) →
      ∀ hμ : AEMeasurable μ P, (∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) →
        Nonempty (PinchRootedData P μ D hμ U T Q' Qset M δ hconfig)

/-- Lemma 11.13 (`ManyPinchScalesStmt`) from the rooted data step and the staged metric-field axioms. The fixed
geometry is z6's `exists_isPinchPointConfiguration`; the rate is the one of `PinchRootedDataStep`. -/
theorem manyPinchScalesStmt_of_rootedDataStep
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hstep : PinchRootedDataStep.{u}) : ManyPinchScalesStmt.{u} := by
  obtain ⟨U, T, Q', Qset, hconfig⟩ := exists_isPinchPointConfiguration
  refine ⟨U, T, Q', Qset, hconfig, ?_⟩
  intro γ α₀ ξ hγ hγ2 hα M hM
  obtain ⟨δ, hδ, hdata⟩ := hstep U T Q' Qset hconfig γ α₀ ξ M hγ hγ2 hα hM
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ P hC hcirc μ D hgff hμ hD
  have : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  have hax := hmetricAxioms γ α₀ ξ hγ hγ2 hα Ω P hC hcirc hgff
  obtain ⟨D', hD'meas, hD'eq⟩ :=
    exists_measurable_metric_modification_of_metricFieldAxioms hax hgff hγ hγ2 hα hD
  have hμA : AEMeasurable μ P := hgff.aemeasurable_lqgMeasure hμ
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hmet : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) :=
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D hax hgff hγ hγ2 hα hD
  have hD'metric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D' ω) := by
    filter_upwards [hmet, hD'eq] with ω h1 h2
    rw [h2]
    exact h1
  have hD'LQG : IsLQGMetricOfField P γ ξ α₀ hC D' := by
    obtain ⟨𝔇, h𝔇, hrep⟩ := hD
    refine ⟨𝔇, h𝔇, ?_⟩
    filter_upwards [hrep, hD'eq] with ω h1 h2
    rw [h2]
    exact h1
  obtain ⟨d⟩ := hdata Ω P hC hcirc μ D' hgff hμ hD'LQG hD'meas hD'metric hμA hloc
  have : IsProbabilityMeasure d.Q := d.hQ
  have key := ae_ae_pinch_block_density_of_origin_law P hμA hloc hD'meas hD'metric d.ν d.hμν d.hlocν
    d.hmetricν hconfig M δ d.w d.hw d.hpos d.hfin d.ρ d.shift d.hshift d.R d.hrooted d.hac d.hdom
    d.recenter d.hrec d.Q d.hcomp d.heq d.X d.germ d.hgle d.hX d.hXm d.hXgerm d.htrivial d.hstat d.hδ
  filter_upwards [key, hD'eq] with ω hω hωeq
  rw [hωeq] at hω
  exact hω

end HarmonicBalls

#print axioms HarmonicBalls.manyPinchScalesStmt_of_rootedDataStep
