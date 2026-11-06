import HarmonicBalls.Proofs.Sec6.SingularRootCollarDiagonal

/-! # Deterministic nearby-centre moduli at singular LQG roots

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology
universe u

/-- Along any prescribed positive radii, deterministic displacement moduli
make good-annulus transfer hold eventually at almost every root sampled from a
kernel dominated by singular LQG mass. The moduli can depend on the radius
sequence and are not asserted to have a uniform positive lower bound. -/
theorem exists_singularRoot_zero_eventually_goodAnnulus_transfer
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) [IsFiniteMeasure (P ⊗ₘ κ)] (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    {a a' amid b b' : ℝ} {d ε : ℝ≥0∞} (hd : 0 < d) (hε : 0 < ε)
    (hbudget : ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b')
    (hmid : ENNReal.ofReal amid < ENNReal.ofReal a)
    (hslack : ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal amid) :
    ∃ δ : ℕ → ℝ, (∀ n, 0 < δ n) ∧
      ∀ᵐ p ∂(P ⊗ₘ κ), ∀ᶠ n in atTop, ∀ w : ℂ,
        dist w p.2 < δ n * r n → IsGoodAnnulus (μ₀ p.1) (r n) p.2 a b →
        IsGoodAnnulus (μ₀ p.1) (r n) w a' b' := by
  classical
  obtain ⟨m, _, hcollar⟩ := exists_singularRoot_zero_eventually_relative_collar
    hgrowth hγ hγ2 hα h hμ hμ₀ κ hac r hr (fun _ => d) (fun _ => hd)
  let η : ℕ → ℝ := fun n => (1 / ((m n : ℝ) + 1)) / r n
  have hη (n : ℕ) : 0 < η n := by
    dsimp [η]
    exact div_pos (one_div_pos.mpr (by positivity)) (hr n)
  have hex (n : ℕ) := exists_scale_uniform_goodAnnulus_of_relative_collar (hη n) hε
  choose δ hδ htransfer using hex
  refine ⟨δ, hδ, ?_⟩
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
  filter_upwards [hcollar, hreg, hloc] with p hc hp hl
  let : IsLocallyFiniteMeasure (μ₀ p.1) := hl
  filter_upwards [hc] with n hc w hw hg
  have hfin : μ₀ p.1 (annulus p.2 (3*r n) (5*r n)) ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset)
  have hηr : η n * r n = 1 / ((m n : ℝ) + 1) := by
    dsimp [η]
    exact div_mul_cancel₀ _ (hr n).ne'
  apply htransfer n (μ₀ p.1) (r n) (hr n) p.2 w hw a a' amid b b' d
    (hp n) hfin hg hbudget hmid hslack
  simpa only [hηr] using hc

end HarmonicBalls.Section6
