import HarmonicBalls.Proofs.Sec6.NearbyGoodAnnulusContinuity
import HarmonicBalls.Proofs.Sec6.GoodAnnulusJointMeasurability
import HarmonicBalls.Proofs.Sec6.LQGNearbyAnnulusMass
import Mathlib.MeasureTheory.Integral.Indicator

/-! # Probability of good-annulus transfer along convergent centres

The imported LQG regularity development uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

/-- For a prescribed convergent sequence of centres, failure of transfer from
one good annulus to its relaxed counterpart has probability tending to zero.
The annulus regularity is needed only almost surely at the reference centre. -/
theorem tendsto_nearby_goodAnnulus_transfer_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    {z : ℂ} {r a a' b b' : ℝ} (hr : 0 < r)
    (ha' : 0 < a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    (hreg : ∀ᵐ ω ∂P, μ ω (sphere z (3*r)) = 0 ∧
      μ ω (sphere z (5*r)) = 0 ∧ 0 < μ ω (annulus z (3*r) (5*r)))
    (w : ℕ → ℂ) (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => P {ω | IsGoodAnnulus (μ ω) r z a b ∧
      ¬ IsGoodAnnulus (μ ω) r (w n) a' b'}) atTop (𝓝 0) := by
  have ha_pos : 0 < a := ha'.trans ha
  let E : ℕ → Set Ω := fun n => {ω | IsGoodAnnulus (μ ω) r z a b ∧
    ¬ IsGoodAnnulus (μ ω) r (w n) a' b'}
  have hE (n : ℕ) : MeasurableSet (E n) := by
    have h1 := measurableSet_isGoodAnnulus_joint hμ hloc
      (show Measurable (fun _ : Ω => z) from measurable_const)
      (show Measurable (fun _ : Ω => r) from measurable_const) (fun _ => hr) ha_pos b
    have h2 := measurableSet_isGoodAnnulus_joint hμ hloc
      (show Measurable (fun _ : Ω => w n) from measurable_const)
      (show Measurable (fun _ : Ω => r) from measurable_const) (fun _ => hr) ha' b'
    exact h1.inter h2.compl
  have hlim : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ E n ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hreg] with ω ⟨h3, h5, hp⟩
    by_cases hg : IsGoodAnnulus (μ ω) r z a b
    · let : IsLocallyFiniteMeasure (μ ω) := hloc ω
      have hf : μ ω (annulus z (3*r) (5*r)) ≠ ∞ :=
        ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset)
      obtain ⟨δ, hδ, hnear⟩ := exists_nearby_goodAnnulus (μ ω) z hr h3 h5 hp hf
        ha'.le ha hb hbb hg
      filter_upwards [(Metric.tendsto_nhds.mp hw) δ hδ] with n hn
      simp only [E, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      exact fun _ => hnear (w n) hn
    · exact Eventually.of_forall fun n => by simp [E, hg]
  simpa only [measure_empty] using
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty hE hlim

universe u

/-- For LQG, the transfer-failure probability tends to zero along each
prescribed sequence converging to a deterministic reference centre. -/
theorem tendsto_lqg_nearby_goodAnnulus_transfer_failure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {z : ℂ} {r a a' b b' : ℝ} (hr : 0 < r)
    (ha' : 0 < a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    (w : ℕ → ℂ) (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => P {ω | IsGoodAnnulus (μ ω) r z a b ∧
      ¬ IsGoodAnnulus (μ ω) r (w n) a' b'}) atTop (𝓝 0) := by
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
  have ht := tendsto_nearby_goodAnnulus_transfer_failure P ν hν hνloc hr ha' ha hb hbb hreg w hw
  have heq (n : ℕ) : P {ω | IsGoodAnnulus (μ ω) r z a b ∧
      ¬ IsGoodAnnulus (μ ω) r (w n) a' b'} =
      P {ω | IsGoodAnnulus (ν ω) r z a b ∧
      ¬ IsGoodAnnulus (ν ω) r (w n) a' b'} := by
    apply measure_congr
    filter_upwards [hμν] with ω hω
    rw [hω]
  simpa only [heq] using ht

/-- The same convergence holds after sampling a root with any almost surely
normalized kernel, because this sampling preserves the field marginal. -/
theorem tendsto_rooted_nearby_goodAnnulus_transfer_failure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {Z : Type*} [MeasurableSpace Z] (κ : Kernel Ω Z) [IsSFiniteKernel κ]
    (hκ : ∀ᵐ ω ∂P, κ ω univ = 1)
    {z : ℂ} {r a a' b b' : ℝ} (hr : 0 < r)
    (ha' : 0 < a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    (w : ℕ → ℂ) (hw : Tendsto w atTop (𝓝 z)) :
    Tendsto (fun n => (P ⊗ₘ κ) {p | IsGoodAnnulus (μ p.1) r z a b ∧
      ¬ IsGoodAnnulus (μ p.1) r (w n) a' b'}) atTop (𝓝 0) := by
  let := h.isProbabilityMeasure
  have hmeas := h.aemeasurable_lqgMeasure hμ
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ hω => hω.isLocallyFiniteMeasure
  have hp := measurePreserving_fst_compProd_of_ae_normalized P κ hκ
  have heq (n : ℕ) : (P ⊗ₘ κ) {p | IsGoodAnnulus (μ p.1) r z a b ∧
      ¬ IsGoodAnnulus (μ p.1) r (w n) a' b'} =
      P {ω | IsGoodAnnulus (μ ω) r z a b ∧
      ¬ IsGoodAnnulus (μ ω) r (w n) a' b'} := by
    have h1 := nullMeasurableSet_isGoodAnnulus_joint hmeas hloc
      (show Measurable (fun _ : Ω => z) from measurable_const)
      (show Measurable (fun _ : Ω => r) from measurable_const) (fun _ => hr)
      (ha'.trans ha) b
    have h2 := nullMeasurableSet_isGoodAnnulus_joint hmeas hloc
      (show Measurable (fun _ : Ω => w n) from measurable_const)
      (show Measurable (fun _ : Ω => r) from measurable_const) (fun _ => hr) ha' b'
    change (P ⊗ₘ κ) (Prod.fst ⁻¹' ({ω | IsGoodAnnulus (μ ω) r z a b} ∩
      {ω | IsGoodAnnulus (μ ω) r (w n) a' b'}ᶜ)) = _
    exact hp.measure_preimage (h1.inter h2.compl)
  simpa only [heq] using
    tendsto_lqg_nearby_goodAnnulus_transfer_failure hgrowth hγ hγ2 h hμ hr ha' ha hb hbb w hw

end HarmonicBalls.Section6
