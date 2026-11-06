import HarmonicBalls.Proofs.Sec6.SingularRootRelativeCollar
import HarmonicBalls.Proofs.Sec6.RelativeCollarTransferProbability
import HarmonicBalls.Proofs.Sec6.PhaseGridApprox
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Fixed relative displacement from summable rooted collar failures

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology
universe u

/-- A summable relative-collar failure bound at prescribed scales implies a
single relative displacement works eventually at almost every singular-mass
sampled root. The summability assumption is an explicit quantitative premise. -/
theorem exists_singularRoot_zero_eventually_fixed_displacement
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) [IsFiniteMeasure (P ⊗ₘ κ)] (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    {η : ℝ} (hη : 0 < η) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℕ → ℝ), (∀ n, 0 < r n) →
      ∀ a a' amid b b' : ℝ, ∀ d : ℝ≥0∞,
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal amid →
      (∑' n, (P ⊗ₘ κ) {p | d * μ₀ p.1 (annulus p.2 (3*r n) (5*r n)) <
        μ₀ p.1 (annulus p.2 (3*r n-η*r n) (5*r n+η*r n) \
          annulus p.2 (3*r n+η*r n) (5*r n-η*r n))}) ≠ ∞ →
      ∀ᵐ p ∂(P ⊗ₘ κ), ∀ᶠ n in atTop, ∀ w : ℂ,
        dist w p.2 < δ * r n → IsGoodAnnulus (μ₀ p.1) (r n) p.2 a b →
        IsGoodAnnulus (μ₀ p.1) (r n) w a' b' := by
  obtain ⟨δ, hδ, ht⟩ := exists_scale_uniform_goodAnnulus_of_relative_collar hη hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr a a' amid b b' d hbudget hmid hslack hsum
  have hreg : ∀ᵐ p ∂(P ⊗ₘ κ), ∀ n, 0 < μ₀ p.1 (annulus p.2 (3*r n) (5*r n)) := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [ae_compProd_zero_annulus_regular_at_singular_roots
      hgrowth hγ hγ2 hα h hμ hμ₀ κ hac (hr n)] with p hp
    exact hp.2.2
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hQ h hμ₀
  have hloc : ∀ᵐ p ∂(P ⊗ₘ κ), IsLocallyFiniteMeasure (μ₀ p.1) :=
    (quasiMeasurePreserving_fst_compProd P κ).ae (hV.mono fun _ hv => hv.1)
  filter_upwards [ae_eventually_notMem hsum, hreg, hloc] with p hc hp hl
  let : IsLocallyFiniteMeasure (μ₀ p.1) := hl
  filter_upwards [hc] with n hn w hw hg
  have hfin : μ₀ p.1 (annulus p.2 (3*r n) (5*r n)) ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset)
  exact ht (μ₀ p.1) (r n) (hr n) p.2 w hw a a' amid b b' d
    (hp n) hfin hg hbudget hmid hslack (le_of_not_gt hn)

/-- A fixed displacement estimate transfers to a prescribed dyadic mesh at
all phases whenever twice the mesh is eventually smaller than the displacement.
The same lattice point works for any good annulus at the given scale. -/
theorem ae_eventually_phase_lattice_of_fixed_displacement
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (z : Ω → ℂ) (r : ℕ → ℝ) (m : ℕ → ℕ) (δ a a' b b' : ℝ)
    (hmesh : ∀ᶠ n in atTop, 2 * dyadicScale (m n) < δ * r n)
    (ht : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ w : ℂ,
      dist w (z ω) < δ * r n → IsGoodAnnulus (μ ω) (r n) (z ω) a b →
      IsGoodAnnulus (μ ω) (r n) w a' b') :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ phase : ℂ, ∃ y : ℂ,
      y - phase ∈ scaledLattice (dyadicScale (m n)) ∧
      dist (z ω) y < 2 * dyadicScale (m n) ∧
      (IsGoodAnnulus (μ ω) (r n) (z ω) a b →
        IsGoodAnnulus (μ ω) (r n) y a' b') := by
  filter_upwards [ht] with ω hω
  filter_upwards [hω, hmesh] with n hn hm phase
  obtain ⟨y, hy, hd⟩ := exists_phase_scaledLattice_dist_lt (z ω) phase (dyadicScale_pos (m n))
  refine ⟨y, hy, hd, ?_⟩
  intro hg
  apply hn y ?_ hg
  rw [dist_comm]
  exact hd.trans hm

end HarmonicBalls.Section6
