import HarmonicBalls.Proofs.Sec6.ReverseNearbyGoodAnnulusProbability
import HarmonicBalls.Proofs.Sec6.NearbyGoodAnnulusProbability

/-! # Reverse nearby good-annulus probabilities for LQG

The imported LQG regularity development uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- At a deterministic centre and radius, the reverse-transfer failure
probability is uniformly small over individual nearby centres. The all-scales
volume-growth input remains explicit. -/
theorem exists_uniform_lqg_reverse_goodAnnulus_transfer_failure_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {z : ℂ} {r a a' b b' : ℝ} (hr : 0 < r)
    (ha' : 0 < a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ →
      P {ω | IsGoodAnnulus (μ ω) r w a b ∧
        ¬ IsGoodAnnulus (μ ω) r z a' b'} < ε := by
  let := h.isProbabilityMeasure
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
  obtain ⟨ν, hν, hνloc, hμν⟩ := exists_measurable_locallyFinite_rep
    (h.aemeasurable_lqgMeasure hμ) (hμ.mono fun _ hω => hω.isLocallyFiniteMeasure)
  have hregular := ae_lqg_goodAnnulus_regular (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth)
    hγ hγ2 hQ h hμ (lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 hC hcirc)
    hr z (a := 1) (by norm_num)
  have hreg : ∀ᵐ ω ∂P, ν ω (sphere z (3*r)) = 0 ∧
      ν ω (sphere z (5*r)) = 0 ∧ 0 < ν ω (annulus z (3*r) (5*r)) := by
    filter_upwards [hμν, hregular,
      ae_lqg_sphere_eq_zero_of_translation h hμ hAff z (3*r),
      ae_lqg_sphere_eq_zero_of_translation h hμ hAff z (5*r)] with ω he hreg h3 h5
    rw [← he]
    exact ⟨h3, h5, by simpa using hreg.2.2⟩
  obtain ⟨δ, hδ, hbound⟩ := exists_uniform_reverse_goodAnnulus_transfer_failure_probability
    P ν hν hνloc hr ha' ha hb hbb hreg hε
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  have heq : P {ω | IsGoodAnnulus (μ ω) r w a b ∧
      ¬ IsGoodAnnulus (μ ω) r z a' b'} =
      P {ω | IsGoodAnnulus (ν ω) r w a b ∧
      ¬ IsGoodAnnulus (ν ω) r z a' b'} := by
    apply measure_congr
    filter_upwards [hμν] with ω hω
    rw [hω]
  rw [heq]
  exact hbound w hw

/-- The individual-centre bound also holds after sampling any almost surely
normalized kernel, because the field marginal is unchanged. -/
theorem exists_uniform_rooted_lqg_reverse_goodAnnulus_transfer_failure_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {Z : Type*} [MeasurableSpace Z] (κ : Kernel Ω Z) [IsSFiniteKernel κ]
    (hκ : ∀ᵐ ω ∂P, κ ω univ = 1)
    {z : ℂ} {r a a' b b' : ℝ} (hr : 0 < r)
    (ha' : 0 < a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ →
      (P ⊗ₘ κ) {p | IsGoodAnnulus (μ p.1) r w a b ∧
        ¬ IsGoodAnnulus (μ p.1) r z a' b'} < ε := by
  let := h.isProbabilityMeasure
  have hmeas := h.aemeasurable_lqgMeasure hμ
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ hω => hω.isLocallyFiniteMeasure
  have hp := measurePreserving_fst_compProd_of_ae_normalized P κ hκ
  obtain ⟨δ, hδ, hbound⟩ :=
    exists_uniform_lqg_reverse_goodAnnulus_transfer_failure_probability
      hgrowth hγ hγ2 h hμ hr ha' ha hb hbb hε
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  have h1 := nullMeasurableSet_isGoodAnnulus_joint hmeas hloc
    (show Measurable (fun _ : Ω => w) from measurable_const)
    (show Measurable (fun _ : Ω => r) from measurable_const) (fun _ => hr)
    (ha'.trans ha) b
  have h2 := nullMeasurableSet_isGoodAnnulus_joint hmeas hloc
    (show Measurable (fun _ : Ω => z) from measurable_const)
    (show Measurable (fun _ : Ω => r) from measurable_const) (fun _ => hr) ha' b'
  have heq : (P ⊗ₘ κ) {p | IsGoodAnnulus (μ p.1) r w a b ∧
      ¬ IsGoodAnnulus (μ p.1) r z a' b'} =
      P {ω | IsGoodAnnulus (μ ω) r w a b ∧
        ¬ IsGoodAnnulus (μ ω) r z a' b'} := by
    change (P ⊗ₘ κ) (Prod.fst ⁻¹' ({ω | IsGoodAnnulus (μ ω) r w a b} ∩
      {ω | IsGoodAnnulus (μ ω) r z a' b'}ᶜ)) = _
    exact hp.measure_preimage (h1.inter h2.compl)
  rw [heq]
  exact hbound w hw

end HarmonicBalls.Section6
