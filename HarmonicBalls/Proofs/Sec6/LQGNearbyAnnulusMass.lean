import HarmonicBalls.Proofs.Sec6.AnnulusMassSandwich
import HarmonicBalls.Proofs.Sec6.CountableNearbyAnnulusLocality
import HarmonicBalls.Proofs.Sec6.RootedNearbyAnnulusCounts

/-! # Nearby annulus masses for LQG

The imported good-annulus development uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
The mass envelope is a step toward centre stability; it does not bound the
Brownian avoidance probability in the definition of a good annulus.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology

universe u

/-- At each deterministic centre and positive radius, the masses of all
nearby annuli are simultaneously comparable with high probability. -/
theorem exists_nearby_lqg_annulus_mass_ratio_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {l u : ℝ≥0∞} (hl : l < 1) (hu : 1 < u)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧
      P {ω | ∃ w : ℂ, dist w z < ε ∧
        ¬ (l * μ ω (annulus z (3 * r) (5 * r)) < μ ω (annulus w (3 * r) (5 * r)) ∧
           μ ω (annulus w (3 * r) (5 * r)) < u * μ ω (annulus z (3 * r) (5 * r)))} ≤ δ := by
  let := h.isProbabilityMeasure
  have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hm := h.aemeasurable_lqgMeasure hμ
  let ν := hm.mk μ
  have hν : Measurable ν := hm.measurable_mk
  have hμν : μ =ᵐ[P] ν := hm.ae_eq_mk
  have hregular := ae_lqg_goodAnnulus_regular (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth)
    hγ hγ2 hQ h hμ (lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 hC hcirc)
    hr z (a := 1) (by norm_num)
  have hreg : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) ∧
      ν ω (sphere z (3 * r)) = 0 ∧ ν ω (sphere z (5 * r)) = 0 ∧
      0 < ν ω (annulus z (3 * r) (5 * r)) ∧
      ν ω (annulus z (3 * r) (5 * r)) ≠ ∞ := by
    filter_upwards [hμ, hμν, hregular,
      ae_lqg_sphere_eq_zero_of_translation h hμ hAff z (3 * r),
      ae_lqg_sphere_eq_zero_of_translation h hμ hAff z (5 * r)] with ω hloc heq hreg hi ho
    rw [← heq]
    exact ⟨hloc.isLocallyFiniteMeasure, hi, ho, by simpa using hreg.2.2, hreg.2.1⟩
  obtain ⟨ε, hε, hbound⟩ := exists_nearby_annulus_mass_ratio_probability
    P ν hν z (3 * r) (5 * r) hreg hl hu hδ
  refine ⟨ε, hε, ?_⟩
  have heq : {ω | ∃ w : ℂ, dist w z < ε ∧
      ¬ (l * μ ω (annulus z (3 * r) (5 * r)) < μ ω (annulus w (3 * r) (5 * r)) ∧
         μ ω (annulus w (3 * r) (5 * r)) < u * μ ω (annulus z (3 * r) (5 * r)))} =ᵐ[P]
      {ω | ∃ w : ℂ, dist w z < ε ∧
      ¬ (l * ν ω (annulus z (3 * r) (5 * r)) < ν ω (annulus w (3 * r) (5 * r)) ∧
         ν ω (annulus w (3 * r) (5 * r)) < u * ν ω (annulus z (3 * r) (5 * r)))} := by
    filter_upwards [hμν] with ω hω
    rw [hω]
  exact (measure_congr heq).trans_le hbound

/-- The nearby-mass comparison remains valid after sampling a root by any
almost surely normalized kernel; no measurability of the failure event is
required. -/
theorem exists_rooted_nearby_lqg_annulus_mass_ratio_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {Z : Type*} [MeasurableSpace Z] (κ : Kernel Ω Z) [IsSFiniteKernel κ]
    (hκ : ∀ᵐ ω ∂P, κ ω univ = 1)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {l u : ℝ≥0∞} (hl : l < 1) (hu : 1 < u)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧
      (P ⊗ₘ κ) {p | ∃ w : ℂ, dist w z < ε ∧
        ¬ (l * μ p.1 (annulus z (3 * r) (5 * r)) < μ p.1 (annulus w (3 * r) (5 * r)) ∧
           μ p.1 (annulus w (3 * r) (5 * r)) < u * μ p.1 (annulus z (3 * r) (5 * r)))} ≤ δ := by
  let := h.isProbabilityMeasure
  obtain ⟨ε, hε, hbound⟩ :=
    exists_nearby_lqg_annulus_mass_ratio_probability hgrowth hγ hγ2 h hμ hr z hl hu hδ
  refine ⟨ε, hε, ?_⟩
  have hp := measurePreserving_fst_compProd_of_ae_normalized P κ hκ
  have hpre := Measure.le_map_apply (μ := P ⊗ₘ κ) measurable_fst.aemeasurable
    {ω | ∃ w : ℂ, dist w z < ε ∧
      ¬ (l * μ ω (annulus z (3 * r) (5 * r)) < μ ω (annulus w (3 * r) (5 * r)) ∧
         μ ω (annulus w (3 * r) (5 * r)) < u * μ ω (annulus z (3 * r) (5 * r)))}
  rw [hp.map_eq] at hpre
  simpa only [preimage_ofPred_eq] using hpre.trans hbound

end HarmonicBalls.Section6
