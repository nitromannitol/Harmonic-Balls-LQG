import HarmonicBalls.Proofs.Sec6.JointRootAnnulusRegularity

/-! # Good-annulus transfer under rooted laws

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology
universe u

/-- Fixed-radius transfer in probability under a finite rooted law, for an
almost-everywhere measurable and locally finite random measure. -/
theorem tendsto_compProd_goodAnnulus_transfer_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : Kernel Ω ℂ)
    [IsFiniteMeasure (P ⊗ₘ κ)] {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    {r a a' b b' : ℝ} (hr : 0 < r)
    (ha' : 0 < a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    (hreg : ∀ᵐ p ∂(P ⊗ₘ κ), μ p.1 (sphere p.2 (3*r)) = 0 ∧
      μ p.1 (sphere p.2 (5*r)) = 0 ∧ 0 < μ p.1 (annulus p.2 (3*r) (5*r)))
    (w : ℕ → Ω × ℂ → ℂ) (hwmeas : ∀ n, Measurable (w n))
    (hw : ∀ᵐ p ∂(P ⊗ₘ κ), Tendsto (fun n => w n p) atTop (𝓝 p.2)) :
    Tendsto (fun n => (P ⊗ₘ κ) {p | IsGoodAnnulus (μ p.1) r p.2 a b ∧
      ¬ IsGoodAnnulus (μ p.1) r (w n p) a' b'}) atTop (𝓝 0) := by
  obtain ⟨ν, hν, hνloc, heq⟩ := exists_measurable_locallyFinite_rep hμ hloc
  have heq' := (quasiMeasurePreserving_fst_compProd P κ).ae_eq_comp heq
  have hreg' : ∀ᵐ p ∂(P ⊗ₘ κ), ν p.1 (sphere p.2 (3*r)) = 0 ∧
      ν p.1 (sphere p.2 (5*r)) = 0 ∧ 0 < ν p.1 (annulus p.2 (3*r) (5*r)) := by
    filter_upwards [hreg, heq'] with p hp he
    change μ p.1 = ν p.1 at he
    simpa only [← he] using hp
  have ht := tendsto_randomCentre_goodAnnulus_transfer_failure (P ⊗ₘ κ) ν hν hνloc
    hr ha' ha hb hbb hreg' w hwmeas hw
  have hevent (n : ℕ) :
      (P ⊗ₘ κ) {p | IsGoodAnnulus (μ p.1) r p.2 a b ∧
        ¬ IsGoodAnnulus (μ p.1) r (w n p) a' b'} =
      (P ⊗ₘ κ) {p | IsGoodAnnulus (ν p.1) r p.2 a b ∧
        ¬ IsGoodAnnulus (ν p.1) r (w n p) a' b'} := by
    apply measure_congr
    filter_upwards [heq'] with p he
    change μ p.1 = ν p.1 at he
    simp only [he]
  simpa only [hevent] using ht

/-- Fixed-radius zero-singularity good-annulus transfer in probability for
roots sampled from a kernel dominated by singular LQG mass of the same field. -/
theorem tendsto_singularRoot_zero_goodAnnulus_transfer_failure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) [IsFiniteMeasure (P ⊗ₘ κ)] (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    {r a a' b b' : ℝ} (hr : 0 < r)
    (ha' : 0 < a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    (w : ℕ → Ω × ℂ → ℂ) (hwmeas : ∀ n, Measurable (w n))
    (hw : ∀ᵐ p ∂(P ⊗ₘ κ), Tendsto (fun n => w n p) atTop (𝓝 p.2)) :
    Tendsto (fun n => (P ⊗ₘ κ) {p | IsGoodAnnulus (μ₀ p.1) r p.2 a b ∧
      ¬ IsGoodAnnulus (μ₀ p.1) r (w n p) a' b'}) atTop (𝓝 0) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hQ h hμ₀
  exact tendsto_compProd_goodAnnulus_transfer_failure P κ (h.aemeasurable_lqgMeasure hμ₀)
    (hV.mono fun _ hv => hv.1) hr ha' ha hb hbb
    (ae_compProd_zero_annulus_regular_at_singular_roots hgrowth hγ hγ2 hα h hμ hμ₀ κ hac hr)
    w hwmeas hw

end HarmonicBalls.Section6
