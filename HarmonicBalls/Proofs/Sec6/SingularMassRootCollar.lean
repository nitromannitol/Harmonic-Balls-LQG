import HarmonicBalls.Proofs.Sec6.FiniteWindowRootCollar

/-! # Singular-mass collars at singular LQG roots

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology
universe u

/-- For a singular-mass dominated root law, singular LQG annuli have null
boundary and positive mass at a fixed positive scale. -/
theorem ae_compProd_singular_annulus_regular
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (κ : Kernel Ω ℂ) (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ p ∂(P ⊗ₘ κ), μ p.1 (sphere p.2 (3*r)) = 0 ∧
      μ p.1 (sphere p.2 (5*r)) = 0 ∧ 0 < μ p.1 (annulus p.2 (3*r) (5*r)) := by
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα h hμ
  apply ae_compProd_annulus_regular P κ (h.aemeasurable_lqgMeasure hμ)
    (hV.mono fun _ hv => hv.1) r
  filter_upwards [hac, ae_lqg_ae_root_annulus_regular hgrowth hγ hγ2 hα h hμ] with ω ha hreg
  filter_upwards [hreg (κ ω) ha] with z hz
  exact hz r hr

/-- At a fixed positive scale, singular relative-collar failure can be made
arbitrarily unlikely under a finite singular-mass dominated rooted law. -/
theorem exists_singularRoot_singular_relative_collar_failure_lt
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (κ : Kernel Ω ℂ) [IsFiniteMeasure (P ⊗ₘ κ)] (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    {r c : ℝ} (hr : 0 < r) (hc : 0 < c) {d q : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q) :
    ∃ η : ℝ, 0 < η ∧ η < c ∧
      (P ⊗ₘ κ) {p | d * μ p.1 (annulus p.2 (3*r) (5*r)) <
        μ p.1 (annulus p.2 (3*r-η*r) (5*r+η*r) \
          annulus p.2 (3*r+η*r) (5*r-η*r))} < q := by
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα h hμ
  have ht := tendsto_compProd_relative_collar_failure P κ (h.aemeasurable_lqgMeasure hμ)
    (hV.mono fun _ hv => hv.1) (3*r) (5*r) hd
    (ae_compProd_singular_annulus_regular hgrowth hγ hγ2 hα h hμ κ hac hr)
  have hw := tendsto_one_div_add_atTop_nhds_zero_nat.eventually
    (Iio_mem_nhds (mul_pos hc hr))
  obtain ⟨n, hn, hwidth⟩ := ((ht.eventually_lt_const hq).and hw).exists
  refine ⟨(1 / ((n : ℝ) + 1)) / r, div_pos (one_div_pos.mpr (by positivity)) hr,
    (div_lt_iff₀ hr).2 hwidth, ?_⟩
  have heq : (1 / ((n : ℝ) + 1)) / r * r = 1 / ((n : ℝ) + 1) :=
    div_mul_cancel₀ _ hr.ne'
  simpa only [heq] using hn

open Classical in
/-- One deterministic positive width controls singular relative-collar
failure at each radius in a prescribed finite family. -/
theorem exists_singularRoot_finite_singular_relative_collar_failure_lt
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (κ : Kernel Ω ℂ) [IsFiniteMeasure (P ⊗ₘ κ)] (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (s : Finset ℕ)
    {c : ℝ} (hc : 0 < c) {d q : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q) :
    ∃ η : ℝ, 0 < η ∧ η < c ∧ ∀ i ∈ s,
      (P ⊗ₘ κ) {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} < q := by
  induction s using Finset.induction_on with
  | empty => exact ⟨c / 2, by linarith, by linarith, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨η, hη, hηc, hs⟩ := ih
    obtain ⟨η', hη', hη'η, hi⟩ :=
      exists_singularRoot_singular_relative_collar_failure_lt hgrowth hγ hγ2 hα h hμ κ hac
        (hr i) hη hd hq
    refine ⟨η', hη', hη'η.trans hηc, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact (measure_relative_collar_failure_mono (P ⊗ₘ κ) μ (hr j).le hη'η.le d).trans_lt (hs j hj)

end HarmonicBalls.Section6
