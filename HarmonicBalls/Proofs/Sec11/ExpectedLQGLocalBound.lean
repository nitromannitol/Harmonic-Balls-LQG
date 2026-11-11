import HarmonicBalls.Proofs.Sec11.FixedSquareFrontierNull
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-!
# Expectation-level local domination of the zero-charge LQG measure

Let `P` be a measure on `Ω`, let `IsWholePlaneGFF P hC hcirc` be the whole-plane Gaussian free field with circle
averages `hcirc` (zero-charge normalization `h^ℂ_1(0) = 0`), and let `μ : Ω → Measure ℂ` satisfy
`IsLQGMeasureOfField P γ 0 hcirc μ`, i.e. `μ = μ_{h^ℂ}` is the γ-LQG area measure of the zero-charge field
`h = h^ℂ` (`α₀ = 0`; eq:measure-lim, paper line 396; Duplantier-Sheffield 2011, Prop. 1.1). These two hypotheses
are the only ones used. No bound `0 < γ < 2` and no normalization of `P` is assumed.

Main results. For every real `R` and every Borel set `A ⊆ ball 0 R`, with the deterministic constant
`zeroChargeLocalConst γ R = (max R 0 + 1)^{γ²}`:

* `IsWholePlaneGFF.lintegral_lqgMeasure_le_volume_of_isCompact`: for compact `K ⊆ ball 0 R`,
  `∫⁻ ω, μ ω K ∂P ≤ zeroChargeLocalConst γ R * volume K`;
* `IsWholePlaneGFF.lintegral_lqgMeasure_le_volume_of_measurableSet`: for Borel `A ⊆ ball 0 R`,
  `∫⁻ ω, μ ω A ∂P ≤ zeroChargeLocalConst γ R * volume A`.

This is expectation-level domination: it bounds the first moment `E[μ(A)]` by Lebesgue measure. It does not assert
`μ ω ≪ volume` for any `ω`, and no null set depends on `A`: each bound is proved for a fixed `A` and holds with the
same constant for all `A ⊆ ball 0 R`. The statements are `lintegral`s, so no Bochner integrability is needed.

Argument.

* Compact `K ⊆ ball 0 R`. Let `R₀ = max R 0` and `δ₀ > 0` with `cthickening δ₀ K ⊆ ball 0 R₀`
  (`IsCompact.exists_cthickening_subset_open`). For `0 < δ ≤ δ₀`, the Urysohn cutoff `f` of `cthickening δ K`
  (`exists_cutoff_of_isCompact`) vanishes off `ball 0 R₀`, so the first-moment cutoff bound
  `IsWholePlaneGFF.lintegral_lqgMeasure_le_of_cutoff` gives `E μ(K) ≤ (R₀ + 1)^{γ²} ∫ f ≤ (R₀ + 1)^{γ²} vol(cthickening δ K)`.
  Letting `δ → 0` (`tendsto_measure_cthickening_of_isCompact`) gives `E μ(K) ≤ (R₀ + 1)^{γ²} vol K`.
* Borel `A ⊆ ball 0 R`. Let `ν = P.bind μ`, the measure `ν B = ∫⁻ ω, μ ω B ∂P` (`Measure.bind_apply`, which needs
  `AEMeasurable μ P`, `IsWholePlaneGFF.aemeasurable_lqgMeasure`). Then `ν` is finite on compact sets by the compact
  bound, hence regular (`Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure`), so `ν A` is the supremum of `ν K`
  over compact `K ⊆ A` (`MeasurableSet.measure_eq_iSup_isCompact_of_ne_top`, as `ν A ≤ ν (closedBall 0 R) < ∞`).
  Each such `ν K` is at most `zeroChargeLocalConst γ R * volume K ≤ zeroChargeLocalConst γ R * volume A`.

Credit: the import closure of this module contains code by Leonardo Bonanno. It reaches the external LatticeProb
module `LatticeProb.Prob.Birkhoff` (his LatticeProb formalization of the ergodic theorem) through
`HarmonicBalls/Proofs/Sec8/BirkhoffPort.lean`; this module does not cite that code directly.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Metric Topology
open scoped ENNReal NNReal

/-- The deterministic constant `(max R 0 + 1)^{γ²}` of the local domination bound on `ball 0 R`. It is the first-moment
constant `exp (γ² log (R + 1))` of `IsWholePlaneGFF.lintegral_lqgMeasure_le_of_cutoff` at `max R 0 ≥ 0`. -/
noncomputable def zeroChargeLocalConst (γ R : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (max R 0 + 1)))

theorem zeroChargeLocalConst_ne_top (γ R : ℝ) : zeroChargeLocalConst γ R ≠ ∞ :=
  ENNReal.ofReal_ne_top

/-- Expectation-level domination on compact sets: for a compact `K ⊆ ball 0 R`, the first moment of the zero-charge
LQG measure of `K` is at most `(max R 0 + 1)^{γ²} vol K`. -/
theorem IsWholePlaneGFF.lintegral_lqgMeasure_le_volume_of_isCompact {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {K : Set ℂ} (hK : IsCompact K) {R : ℝ} (hKR : K ⊆ Metric.ball (0 : ℂ) R) :
    ∫⁻ ω, μ ω K ∂P ≤ zeroChargeLocalConst γ R * volume K := by
  have hR₀ : 0 ≤ max R 0 := le_max_right R 0
  have hKR₀ : K ⊆ Metric.ball (0 : ℂ) (max R 0) :=
    hKR.trans (Metric.ball_subset_ball (le_max_left R 0))
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open Metric.isOpen_ball hKR₀
  -- the cutoff bound at a fixed small thickening `δ`
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∫⁻ ω, μ ω K ∂P ≤ zeroChargeLocalConst γ R * volume (Metric.cthickening δ K) := by
    intro δ hδ hδle
    obtain ⟨f, hf, hfc, hf01, hK1, hfout, hfint⟩ := exists_cutoff_of_isCompact hK hδ
    have hsubδ : Metric.cthickening δ K ⊆ Metric.ball (0 : ℂ) (max R 0) :=
      (Metric.cthickening_mono hδle K).trans hsub
    have hfR : ∀ z : ℂ, max R 0 < ‖z‖ → f z = 0 := by
      intro z hz
      apply hfout
      intro hzc
      have h1 : ‖z‖ < max R 0 := mem_ball_zero_iff.mp (hsubδ hzc)
      linarith
    calc ∫⁻ ω, μ ω K ∂P
        ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (max R 0 + 1))) * ∫⁻ z, ENNReal.ofReal (f z) :=
          hgff.lintegral_lqgMeasure_le_of_cutoff hμ hK.isClosed.measurableSet hf hfc hf01 hK1 hR₀ hfR
      _ ≤ zeroChargeLocalConst γ R * volume (Metric.cthickening δ K) :=
          mul_le_mul_of_nonneg_left hfint zero_le
  -- let `δ → 0`: `vol (cthickening δ K) → vol K` for compact `K`
  have hlim : Tendsto (fun δ : ℝ => zeroChargeLocalConst γ R * volume (Metric.cthickening δ K))
      (𝓝[>] (0 : ℝ)) (𝓝 (zeroChargeLocalConst γ R * volume K)) :=
    ENNReal.Tendsto.const_mul
      ((tendsto_measure_cthickening_of_isCompact hK).mono_left nhdsWithin_le_nhds)
      (Or.inr (zeroChargeLocalConst_ne_top γ R))
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ∫⁻ ω, μ ω K ∂P ≤ zeroChargeLocalConst γ R * volume (Metric.cthickening δ K) := by
    filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
    exact key δ hδ.1 hδ.2.le
  exact ge_of_tendsto hlim hev

/-- The expectation measure `P.bind μ` of the zero-charge LQG measure is finite on compact sets. The bound is the
compact bound of `IsWholePlaneGFF.lintegral_lqgMeasure_le_volume_of_isCompact`. -/
theorem IsWholePlaneGFF.isFiniteMeasureOnCompacts_bind {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    IsFiniteMeasureOnCompacts (P.bind μ) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  rw [Measure.bind_apply hK.isClosed.measurableSet (hgff.aemeasurable_lqgMeasure hμ)]
  exact (hgff.lintegral_lqgMeasure_le_volume_of_isCompact hμ hK hR).trans_lt
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (zeroChargeLocalConst_ne_top γ R)) hK.measure_lt_top)

/-- Expectation-level local domination (the main statement): for every real `R` and every Borel set `A ⊆ ball 0 R`,
`∫⁻ ω, μ ω A ∂P ≤ (max R 0 + 1)^{γ²} vol A`, from the zero-charge GFF and the zero-charge LQG-limit hypothesis alone. -/
theorem IsWholePlaneGFF.lintegral_lqgMeasure_le_volume_of_measurableSet {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {R : ℝ} {A : Set ℂ} (hA : MeasurableSet A) (hAR : A ⊆ Metric.ball (0 : ℂ) R) :
    ∫⁻ ω, μ ω A ∂P ≤ zeroChargeLocalConst γ R * volume A := by
  have hfin : IsFiniteMeasureOnCompacts (P.bind μ) := hgff.isFiniteMeasureOnCompacts_bind hμ
  have hmeas : AEMeasurable μ P := hgff.aemeasurable_lqgMeasure hμ
  rw [← Measure.bind_apply hA hmeas]
  have hAfin : (P.bind μ) A ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
      (measure_mono (hAR.trans Metric.ball_subset_closedBall))
  refine (le_of_eq (hA.measure_eq_iSup_isCompact_of_ne_top hAfin)).trans ?_
  refine iSup_le fun K => iSup_le fun hKA => iSup_le fun hK => ?_
  rw [Measure.bind_apply hK.isClosed.measurableSet hmeas]
  exact (hgff.lintegral_lqgMeasure_le_volume_of_isCompact hμ hK (hKA.trans hAR)).trans
    (mul_le_mul_of_nonneg_left (measure_mono hKA) zero_le)

end HarmonicBalls
