import HarmonicBalls.FirstPass.Canonical.Stmts
import HarmonicBalls.FirstPass.Closure.Bridge12Canonical
import HarmonicBalls.Proofs.Sec11.NotMetricBallGrowth

/-! # Canonical-exponent copies of Proposition 11.11 (FIRST-PASS fp-canonical-11-11-chain, worker z4)

Copies of `typical_boundary_ne_metricBall` (`Proofs/Sec11/TypicalBoundary.lean:15`),
`harmonicBallNotMetricBall_of_comparison_and_pinch` (`Proofs/Sec11/NotMetricBall.lean:14`),
`harmonicBallNotMetricBall_of_comparison_pinch_and_volumeGrowth` (`Proofs/Sec11/NotMetricBallGrowth.lean:32`),
`harmonicBallNotMetricBallStmt_of_comparison_pinch_and_volumeGrowth` (`Proofs/Sec11/NotMetricBallGrowth.lean:56`) and
`firstPass_11_11` (`FirstPass/S11.lean:111`), for the canonical exponent `ξ = lqgXi γ` (chat 224, Correction 1) and the
model-dependent pinch hypothesis `ManyPinchScalesCanonicalModelStmt` (chat 224, Correction 3), in the style of
Armstrong-Kuusi-Mourrat's harmonic-ball bookkeeping and the LQG literature (Duplantier-Sheffield, Berestycki-Powell).

Recipe: the proofs are the originals with the binder `ξ` removed and `ξ := lqgXi γ` substituted; the pinch hypothesis is
`ManyPinchScalesCanonicalModelStmt`, and the density `δ` is obtained after the model `(Ω, P, hC, hcirc, μ, D)` is
instantiated. The outer statements keep the `∀ ξ` metric-field-axiom hypothesis exactly as in the originals and
instantiate it at `lqgXi γ`. No `hWeyl` binder: the statements are closed by the stated hypotheses only. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Canonical copy of `typical_boundary_ne_metricBall` at the canonical exponent `ξ = lqgXi γ` (chat 224, Correction 1),
with the pinch hypothesis `ManyPinchScalesCanonicalModelStmt` (Correction 3). The density `δ` is obtained from the
pinch hypothesis at the instantiated model `(Ω, P, hC, hcirc, μ, D)`. -/
theorem typical_boundary_ne_metricBall_canonical
    (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : Closure.ManyPinchScalesCanonicalModelStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (Λ : Ω → ℝ → Set ℂ)
    (hmetricAxioms : LQGMetricFieldAxioms P γ (lqgXi γ) α₀ hC hcirc)
    (hnonatomic : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmetric : IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D)
    (hfamily : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ t : ℝ, 0 < t → ∀ w : ℂ, ∀ v : ℝ, 0 < v →
      z ∈ frontier (lqgMetricBall (D ω) w v) → Λ ω t ≠ lqgMetricBall (D ω) w v := by
  obtain ⟨C, hCpos, hcomparison⟩ := hbound
  obtain ⟨U, T, Q', Q, hconfig, hscales⟩ := hmany
  obtain ⟨δ, hδ, hdensity⟩ := hscales γ α₀ hγ hγ₂ hα C hCpos Ω P hC hcirc μ D hgff hμ hmetric
  filter_upwards [hcomparison γ α₀ hγ hγ₂ hα Ω P hC hcirc μ hgff hμ Λ hfamily,
    hdensity,
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ (lqgXi γ) α₀ hC hcirc D
      hmetricAxioms hgff hγ hγ₂ hα hmetric,
    hnonatomic hgff hγ hγ₂ hα μ hμ] with ω hcomparison hdensity hD hnonatomic
  have hz0 : ∀ᵐ z ∂(μ ω), z ≠ 0 := by
    simpa only [Set.mem_singleton_iff] using (measure_eq_zero_iff_ae_notMem.1 (hnonatomic 0))
  filter_upwards [hdensity, hz0] with z hdensity hz0
  have hnonneg : ∀ x y, 0 ≤ D ω x y := by
    intro x y
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  intro t ht w v hv hz
  have hw : w ≠ z := by
    intro heq
    subst w
    have hd := hD.distance_eq_of_mem_frontier_ball z z v hz
    rw [hD.self_eq_zero] at hd
    linarith
  exact ne_metricBall_of_frequently_pinch_and_annulusMassBound (μ ω) (D ω) U T Q' Q (Λ ω t)
    C v w z hconfig hD hnonneg hz0 hw hz
    (frequently_of_positive_dyadic_block_density _ hδ.1 hdensity)
    (fun r hr h0 => hcomparison t ht r hr z h0)

/-- Canonical copy of `harmonicBallNotMetricBall_of_comparison_and_pinch` at `ξ = lqgXi γ` (chat 224, Correction 1),
with `ManyPinchScalesCanonicalModelStmt` (Correction 3). -/
theorem harmonicBallNotMetricBall_of_comparison_and_pinch_canonical
    (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : Closure.ManyPinchScalesCanonicalModelStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (Λ : Ω → ℝ → Set ℂ)
    (hmetricAxioms : LQGMetricFieldAxioms P γ (lqgXi γ) α₀ hC hcirc)
    (hnonatomic : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmetric : IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D)
    (hfamily : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂volume, 0 < t → ∀ w : ℂ, ∀ r : ℝ,
      Λ ω t ≠ lqgMetricBall (D ω) w r := by
  filter_upwards [typical_boundary_ne_metricBall_canonical hbound hmany γ α₀ hγ hγ₂ hα
      Ω P hC hcirc μ D Λ hmetricAxioms hnonatomic hgff hμ hmetric hfamily,
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ (lqgXi γ) α₀ hC hcirc D
      hmetricAxioms hgff hγ hγ₂ hα hmetric,
    hμ, hfamily] with ω hpoint hD hμω hfamilyω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  have hnonneg : ∀ x y, 0 ≤ D ω x y := by
    intro x y
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  exact ae_time_ne_metricBall_of_ae_boundary_exclusion (μ ω) (Λ ω) (D ω) 0
    hfamilyω.2 hpoint hnonneg

/-- Canonical copy of `harmonicBallNotMetricBall_of_comparison_pinch_and_volumeGrowth` at `ξ = lqgXi γ`
(chat 224, Correction 1), with `ManyPinchScalesCanonicalModelStmt` (Correction 3). -/
theorem harmonicBallNotMetricBall_of_comparison_pinch_and_volumeGrowth_canonical
    (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : Closure.ManyPinchScalesCanonicalModelStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (Λ : Ω → ℝ → Set ℂ)
    (hmetricAxioms : LQGMetricFieldAxioms P γ (lqgXi γ) α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmetric : IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D)
    (hfamily : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂volume, 0 < t → ∀ w : ℂ, ∀ r : ℝ,
      Λ ω t ≠ lqgMetricBall (D ω) w r :=
  harmonicBallNotMetricBall_of_comparison_and_pinch_canonical hbound hmany γ α₀ hγ hγ₂ hα
    Ω P hC hcirc μ D Λ hmetricAxioms
    (lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ α₀ hC hcirc)
    hgff hμ hmetric hfamily

/-- Canonical copy of `harmonicBallNotMetricBallStmt_of_comparison_pinch_and_volumeGrowth` (Proposition 11.11,
`HarmonicBallNotMetricBallStmt`) for the canonical statement `HarmonicBallNotMetricBallCanonicalStmt` (chat 224,
Correction 1, `ξ := lqgXi γ`). The metric-field-axiom hypothesis is kept as in the original (`∀ ξ`) and is instantiated
at `ξ = lqgXi γ`. -/
theorem harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth
    (hbound : AnnulusMassBoundByHarmonicChainStmt.{u})
    (hmany : Closure.ManyPinchScalesCanonicalModelStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} := by
  intro γ α₀ hγ hγ₂ hα Ω _ P hC hcirc μ D hgff hμ hmetric Λ hfamily
  exact harmonicBallNotMetricBall_of_comparison_pinch_and_volumeGrowth_canonical hbound hmany hgrowth
    γ α₀ hγ hγ₂ hα Ω P hC hcirc μ D Λ
    (hmetricAxioms γ α₀ (lqgXi γ) hγ hγ₂ hα Ω P hC hcirc hgff)
    hgff hμ hmetric hfamily

/-- FIRST-PASS canonical Proposition 11.11 (prop:not-metric-balls, paper line 3150), the canonical copy of `firstPass_11_11`
(`FirstPass/S11.lean:111`) for `HarmonicBallNotMetricBallCanonicalStmt`. Uses the canonical pinch statement
`ManyPinchScalesCanonicalModelStmt` (Lemma 11.13, chat 224 Corrections 1 and 3), the Draft volume growth I2 and the
staged metric-field axioms (`∀ ξ`, as in `firstPass_11_11`). -/
theorem firstPass_11_11_canonical (h6: AnnulusMassBoundByHarmonicChainStmt.{u})
    (h13 : Closure.ManyPinchScalesCanonicalModelStmt.{u}) (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hmetricAxioms : ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} :=
  harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth h6 h13 hI2 hmetricAxioms

#print axioms typical_boundary_ne_metricBall_canonical
#print axioms harmonicBallNotMetricBall_of_comparison_and_pinch_canonical
#print axioms harmonicBallNotMetricBall_of_comparison_pinch_and_volumeGrowth_canonical
#print axioms harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth
#print axioms firstPass_11_11_canonical

end HarmonicBalls
