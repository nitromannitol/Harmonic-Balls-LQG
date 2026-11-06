import HarmonicBalls.Proofs.Sec6.RootedRelativeCollar

/-! # Relative collar mass at singular LQG roots

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology
universe u

/-- Relative collar failure tends to zero for a composition-product law,
using only almost-everywhere measurability and local finiteness of the
random measures. -/
theorem tendsto_compProd_relative_collar_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : Kernel Ω ℂ)
    [IsFiniteMeasure (P ⊗ₘ κ)] {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) (r R : ℝ) {d : ℝ≥0∞} (hd : 0 < d)
    (hreg : ∀ᵐ p ∂(P ⊗ₘ κ), μ p.1 (sphere p.2 r) = 0 ∧
      μ p.1 (sphere p.2 R) = 0 ∧ 0 < μ p.1 (annulus p.2 r R)) :
    Tendsto (fun n : ℕ => (P ⊗ₘ κ) {p | d * μ p.1 (annulus p.2 r R) <
      μ p.1 (annulus p.2 (r-1/((n : ℝ)+1)) (R+1/((n : ℝ)+1)) \
        annulus p.2 (r+1/((n : ℝ)+1)) (R-1/((n : ℝ)+1)))}) atTop (𝓝 0) := by
  obtain ⟨ν, hν, hνloc, heq⟩ := exists_measurable_locallyFinite_rep hμ hloc
  have heq' := (quasiMeasurePreserving_fst_compProd P κ).ae_eq_comp heq
  have hreg' : ∀ᵐ p ∂(P ⊗ₘ κ), ν p.1 (sphere p.2 r) = 0 ∧
      ν p.1 (sphere p.2 R) = 0 ∧ 0 < ν p.1 (annulus p.2 r R) := by
    filter_upwards [hreg, heq'] with p hp he
    change μ p.1 = ν p.1 at he
    simpa only [← he] using hp
  have ht := tendsto_rooted_relative_collar_failure (P ⊗ₘ κ) ν hν hνloc r R hd hreg'
  have hevent (n : ℕ) :
      (P ⊗ₘ κ) {p | d * μ p.1 (annulus p.2 r R) <
        μ p.1 (annulus p.2 (r-1/((n : ℝ)+1)) (R+1/((n : ℝ)+1)) \
          annulus p.2 (r+1/((n : ℝ)+1)) (R-1/((n : ℝ)+1)))} =
      (P ⊗ₘ κ) {p | d * ν p.1 (annulus p.2 r R) <
        ν p.1 (annulus p.2 (r-1/((n : ℝ)+1)) (R+1/((n : ℝ)+1)) \
          annulus p.2 (r+1/((n : ℝ)+1)) (R-1/((n : ℝ)+1)))} := by
    apply measure_congr
    filter_upwards [heq'] with p he
    change μ p.1 = ν p.1 at he
    simp only [he]
  simpa only [hevent] using ht

/-- For roots sampled from a kernel dominated by singular LQG mass, relative
collar failure for the zero-singularity measure tends to zero at every fixed
positive radius. The volume-growth input remains explicit. -/
theorem tendsto_singularRoot_zero_relative_collar_failure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) [IsFiniteMeasure (P ⊗ₘ κ)] (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    {r : ℝ} (hr : 0 < r) {d : ℝ≥0∞} (hd : 0 < d) :
    Tendsto (fun n : ℕ => (P ⊗ₘ κ) {p | d * μ₀ p.1 (annulus p.2 (3*r) (5*r)) <
      μ₀ p.1 (annulus p.2 (3*r-1/((n : ℝ)+1)) (5*r+1/((n : ℝ)+1)) \
        annulus p.2 (3*r+1/((n : ℝ)+1)) (5*r-1/((n : ℝ)+1)))}) atTop (𝓝 0) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hQ h hμ₀
  exact tendsto_compProd_relative_collar_failure P κ (h.aemeasurable_lqgMeasure hμ₀)
    (hV.mono fun _ hv => hv.1) (3*r) (5*r) hd
    (ae_compProd_zero_annulus_regular_at_singular_roots hgrowth hγ hγ2 hα h hμ hμ₀ κ hac hr)

end HarmonicBalls.Section6
