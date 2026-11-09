import HarmonicBalls.FirstPass.S11h.ThirdEventMeasurable

/-!
# First pass, Section 11: measurability of the third pinch event for insertion `α₀ < Q` (fp-S11h, owner n2)

Alpha-general measurability (operator decision B1, 2026-11-09 21:12 UTC, with the corrected GFF hypothesis of the
operator truth check 21:18 UTC) of `aemeasurable_internalDiam`, `ae_continuous_metric` and `nullMeasurableSet_pinchThirdEvent`
for an LQG metric `D` of the log-singular field `h^ℂ - α₀ log|·|`, with `0 < γ < 2` and `α₀ < lqgQ γ` (corrected context
`h^α`, paper lines 3236-3238, correction `[C43]`). The α = 0 theorems that used the false inputs were removed from
`ThirdEventMeasurable.lean`.

Frozen inputs (`FirstPass/Frozen`): `LQGInternalMetricWeylAeMeasurableFrozen` (`S11d.lean`, alpha-general),
`LQGInternalMetricContinuousAlphaGFFFrozen` and `LQGMetricLengthIdentityAlphaGFFFrozen` (`S11g.lean`); each takes the
hypothesis `∃ hcirc, IsWholePlaneGFF P hC hcirc`, which the caller supplies from `hgff`.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

universe u

/-- Field-level a.s. measurability of `ω ↦ D^W(q, q')` for an LQG metric `D` of `hC` with insertion `α₀ < Q`
(`LQGInternalMetricWeylAeMeasurableFrozen` at `f = 0`, with `D = toReal (weylScaling 𝔇(hC))` almost surely). -/
theorem aemeasurable_internalMetric_alpha {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hAe : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hgff : IsWholePlaneGFF P hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    {W : Set ℂ} (hW : IsOpen W) (q q' : ℂ) :
    AEMeasurable (fun ω => internalMetric (D ω) W q q') P := by
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  obtain ⟨Φ, hΦm, hΦ⟩ := hAe γ ξ α₀ Ω P hC hcirc 𝔇 hgff hγ hγ2 hα h𝔇 W hW q q'
  have hDeq : ∀ᵐ ω ∂P, D ω = fun u v =>
      (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
    filter_upwards [hDae] with ω hω
    funext u v
    obtain ⟨hnn, heq⟩ := hω u v
    rw [← heq, ENNReal.toReal_ofReal hnn]
  have h0 : ∀ᵐ ω ∂P, Φ (hC ω) =
      internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) W q q' := by
    filter_upwards [hΦ (fun _ => 0) continuous_const] with ω hω
    rw [addFunPairing_const_zero] at hω
    exact hω
  have hmeasΦ : Measurable fun ω => Φ (hC ω) := hΦm.comp (measurable_hC_distribution hgff)
  refine hmeasΦ.aemeasurable.congr ?_
  filter_upwards [h0, hDeq] with ω h0ω hDω
  show Φ (hC ω) = internalMetric (D ω) W q q'
  rw [hDω, h0ω]

/-- Field-level a.s. measurability of the internal diameter `diam^δ(A)` of an LQG metric with insertion `α₀ < Q`. -/
theorem aemeasurable_internalDiam_alpha {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ α₀ δ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hAe : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hint : LQGInternalMetricContinuousAlphaGFFFrozen.{u})
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) (hδ : 0 < δ) (A : Set ℂ) :
    AEMeasurable (fun ω => internalDiam (D ω) δ A) P := by
  unfold internalDiam
  refine aemeasurable_iSup_pair P A (fun ω x y => internalMetric (D ω) (thickening δ A) x y) ?_ ?_
  · intro x y
    exact aemeasurable_internalMetric_alpha hAe hgff hγ hγ2 hα hD isOpen_thickening x y
  · filter_upwards [hint γ ξ α₀ Ω P hC D ⟨hcirc, hgff⟩ hγ hγ2 hα hD (thickening δ A) isOpen_thickening] with ω hω
    exact hω.mono (prod_mono (self_subset_thickening hδ A) (self_subset_thickening hδ A))

/-- The metric `ω ↦ D ω` of an LQG metric with insertion `α₀ < Q` is a.s. jointly continuous on `ℂ × ℂ`. -/
theorem ae_continuous_metric_alpha {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hint : LQGInternalMetricContinuousAlphaGFFFrozen.{u}) (hlen : LQGMetricLengthIdentityAlphaGFFFrozen.{u})
    (hGFF : ∃ hcirc : Ω → ℝ → ℂ → ℝ, IsWholePlaneGFF P hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D) :
    ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℂ => D ω p.1 p.2) := by
  have hnn : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v := by
    obtain ⟨𝔇, -, h⟩ := hD
    filter_upwards [h] with ω hω u v
    exact (hω u v).1
  filter_upwards [hint γ ξ α₀ Ω P hC D hGFF hγ hγ2 hα hD univ isOpen_univ,
    hlen γ ξ α₀ Ω P hC D hGFF hγ hγ2 hα hD, hnn] with ω hcont hlω hnnω
  rw [univ_prod_univ] at hcont
  have hg : Continuous (fun p : ℂ × ℂ => ENNReal.ofReal (D ω p.1 p.2)) := by
    have hfun : (fun p : ℂ × ℂ => ENNReal.ofReal (D ω p.1 p.2)) =
        fun p => internalMetric (D ω) univ p.1 p.2 := funext fun p => hlω p.1 p.2
    rw [hfun]
    exact continuousOn_univ.mp hcont
  have hreal : (fun p : ℂ × ℂ => D ω p.1 p.2) =
      fun p => (ENNReal.ofReal (D ω p.1 p.2)).toReal :=
    funext fun p => (ENNReal.toReal_ofReal (hnnω p.1 p.2)).symm
  rw [hreal]
  exact ENNReal.continuousOn_toReal.comp_continuous hg fun p => ENNReal.ofReal_ne_top

/-- The third pinch event `Ẽ₃` (`pinchThirdEvent`) for an LQG metric `D` of `hC` with insertion `α₀ < Q` is a
null-measurable set of `ω` (step N2 of the alpha-general `firstPass_11_17_corrected`, paper lines 3630-3633). -/
theorem nullMeasurableSet_pinchThirdEvent_alpha {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ α₀ δ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hAe : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hint : LQGInternalMetricContinuousAlphaGFFFrozen.{u})
    (hlen : LQGMetricLengthIdentityAlphaGFFFrozen.{u})
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) (hδ : 0 < δ) (V W : Set ℂ) :
    NullMeasurableSet {ω | pinchThirdEvent (D ω) V W δ} P := by
  have : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  have hI := aemeasurable_internalDiam_alpha hAe hint hgff hγ hγ2 hα hD hδ (thickening (3 * δ) W \ V)
  have hmeas : ∀ z w, AEMeasurable (fun ω => ENNReal.ofReal (D ω z w)) P := by
    intro z w
    refine (aemeasurable_internalMetric_alpha hAe hgff hγ hγ2 hα hD isOpen_univ z w).congr ?_
    filter_upwards [hlen γ ξ α₀ Ω P hC D ⟨hcirc, hgff⟩ hγ hγ2 hα hD] with ω hω
    exact (hω z w).symm
  have hR := aemeasurable_ofReal_setDist P D hmeas
    (ae_continuous_metric_alpha hint hlen ⟨hcirc, hgff⟩ hγ hγ2 hα hD)
    (isCompact_sphere (0 : ℂ) (2 * δ)) (isCompact_sphere (0 : ℂ) (3 * δ))
    (NormedSpace.sphere_nonempty.mpr (by linarith)) (NormedSpace.sphere_nonempty.mpr (by linarith))
  unfold pinchThirdEvent
  exact nullMeasurableSet_lt hI hR

end HarmonicBalls
