import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstLawTransfer
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstMeasurable

/-!
# Lemma 11.15: measurability of the open certificate on the field

Paper `lemma:first-event-proof` (line 3277) needs a measurable event inside the open certificate
`correctedOpenFirstCertificate` (`Proofs/Sec11/CorrectedPinchFirstLawTransfer.lean`). Here the certificate is measurable
for the field σ-algebra `distributionMeasurableSpace` (`Defs/LQGMetric.lean:117`) once the internal metric on the whole
plane is field-measurable: this is the FROZEN input `LQGInternalMetricWeylMeasurableFrozen` (`FirstPass/Frozen/S11d.lean`,
reused, with `W = univ`, `α₀ = 0`). Off a measurable exceptional set `N` the metric is a Euclidean length metric; on `N` it
is replaced by the Euclidean distance, so that the length property holds for every `ω`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- The real metric of the Weyl scaling at exponent `ξ` with `α₀ = 0`: `D_T(u,v) = (weylScaling (𝔇 T) ξ 0 u v).toReal`. -/
noncomputable def zeroShiftMetric (ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (T : (ℂ → ℝ) → ℝ) : ℂ → ℂ → ℝ :=
  fun u v => (weylScaling (𝔇 T) ξ (fun z => -(0 : ℝ) * Real.log ‖z‖) u v).toReal

open scoped Classical in
/-- The modified metric of the certificate: the internal whole-plane metric of `zeroShiftMetric` off `N`, and the
Euclidean distance on `N`. Both pieces are measurable in `ω`. -/

noncomputable def certMetricOn {Ω : Type*} (N : Set Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (ξ : ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ω : Ω) : ℂ → ℂ → ℝ :=
  fun u v => if ω ∈ N then dist u v else (internalMetric (zeroShiftMetric ξ 𝔇 (hC ω)) univ u v).toReal

/-- Measurability of the open certificate on the field: `{ω | correctedOpenFirstCertificate (certMetricOn N …) …}` is
measurable, for a measurable `N` off which the zero-shift metric is a Euclidean length metric. -/
theorem measurableSet_certificate_certMetricOn
    {Ω : Type*} [MeasurableSpace Ω] (hC : Ω → (ℂ → ℝ) → ℝ)
    (hCm : @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace hC)
    (hfr : LQGInternalMetricWeylMeasurableFrozen)
    {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (N : Set Ω) (hN : MeasurableSet N)
    (hgood : ∀ ω, ω ∉ N → IsEuclideanLengthMetric (zeroShiftMetric ξ 𝔇 (hC ω)))
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) :
    MeasurableSet {ω | correctedOpenFirstCertificate (certMetricOn N hC ξ 𝔇 ω) W T Q' Q δ} := by
  have hfr' : ∀ x y : ℂ, @Measurable ((ℂ → ℝ) → ℝ) ℝ≥0∞ distributionMeasurableSpace ENNReal.measurableSpace
      (fun T => internalMetric (zeroShiftMetric ξ 𝔇 T) univ x y) :=
    fun x y => hfr γ ξ 0 𝔇 h𝔇 univ isOpen_univ x y
  have hDm : ∀ x y : ℂ, Measurable fun ω => certMetricOn N hC ξ 𝔇 ω x y := by
    intro x y
    have hm1 : Measurable fun ω => internalMetric (zeroShiftMetric ξ 𝔇 (hC ω)) univ x y :=
      (hfr' x y).comp hCm
    have hm2 : Measurable fun ω => (internalMetric (zeroShiftMetric ξ 𝔇 (hC ω)) univ x y).toReal :=
      ENNReal.measurable_toReal.comp hm1
    exact Measurable.ite hN measurable_const hm2
  have hlen : ∀ ω, IsEuclideanLengthMetric (certMetricOn N hC ξ 𝔇 ω) := by
    intro ω
    by_cases hω : ω ∈ N
    · have hfun : certMetricOn N hC ξ 𝔇 ω = fun u v => dist u v := by
        funext u v
        simp [certMetricOn, hω]
      rw [hfun]
      exact isEuclideanLengthMetric_dist
    · have hg := hgood ω hω
      have hfun : certMetricOn N hC ξ 𝔇 ω = zeroShiftMetric ξ 𝔇 (hC ω) := by
        funext u v
        have hnn : 0 ≤ zeroShiftMetric ξ 𝔇 (hC ω) u v := ENNReal.toReal_nonneg
        simp only [certMetricOn, hω, ↓reduceIte]
        rw [← hg.ofReal_eq_internalMetric u v, ENNReal.toReal_ofReal hnn]
      rw [hfun]
      exact hg
  exact h.measurableSet_open_first_certificate hDm hlen


end HarmonicBalls
