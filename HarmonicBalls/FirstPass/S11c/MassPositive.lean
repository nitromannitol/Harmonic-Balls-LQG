import HarmonicBalls.FirstPass.S11c.ShiftMass
import HarmonicBalls.FirstPass.S11c.CutoffShift
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Proposition 11.10, positive probability of a large mass on a dyadic square

(assembly of compiled steps, with the Cameron-Martin event transfer as a hypothesis of the frozen form
`CameronMartinEventTransferFrozen`). For a closed dyadic square `S₁` and any finite positive level `C₀`, the event
`{μ_h(S₁) ≥ C₀}` has positive probability. Proof (paper line 3050): the mass is at least `C₁` with probability at least `1/2`
(`exists_lower_of_ae_pos`, from the almost-sure positivity of the mass); the Weyl shift by the constant `a` on `S₁`
(`exists_const_shift_on`, `weylShiftPair_fst_apply_of_const`) multiplies the mass by `e^{γa} = C₀/C₁` on the event; the
Cameron-Martin event transfer gives positivity for the unshifted event.
-/

namespace HarmonicBalls

universe u

open MeasureTheory Set Metric
open scoped ENNReal

theorem mass_event_pos_of_shift {γ α₀ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hCM : CameronMartinEventTransferFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {S₁ S₂ : Set ℂ} (hS₁ : IsClosedDyadicSquare S₁) (hS₂ : IsClosedDyadicSquare S₂) (hS12 : S₁ ⊆ S₂)
    (hdisj : Disjoint S₂ (sphere (0 : ℂ) 1))
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hsup : AEMeasurable (fun ω => ⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (D ω) S₂ u v) P)
    (hmass : AEMeasurable (fun ω => μ ω S₁) P) (hpos : ∀ᵐ ω ∂P, 0 < μ ω S₁)
    {C₀ : ℝ≥0∞} (hC₀ : 0 < C₀) (hC₀t : C₀ ≠ ⊤) :
    0 < P {ω | C₀ ≤ μ ω S₁} := by
  have hcompact : IsCompact S₁ := by
    obtain ⟨n, j, k, rfl⟩ := hS₁
    exact isCompact_Icc.reProdIm isCompact_Icc
  have hS₁m : MeasurableSet S₁ := hcompact.isClosed.measurableSet
  have hdisj₁ : Disjoint S₁ (sphere (0 : ℂ) 1) := hdisj.mono_left hS12
  obtain ⟨C₁, hC₁pos, hC₁top, hhalf⟩ := exists_lower_of_aemeasurable P hmass hpos
  set m : ℝ := (C₀ / C₁).toReal with hm_def
  have hdivpos : 0 < C₀ / C₁ := ENNReal.div_pos_iff.2 ⟨hC₀.ne', hC₁top⟩
  have hdivtop : C₀ / C₁ ≠ ⊤ := ENNReal.div_ne_top hC₀t hC₁pos.ne'
  have hm : 0 < m := ENNReal.toReal_pos hdivpos.ne' hdivtop
  have hmC : ENNReal.ofReal m = C₀ / C₁ := ENNReal.ofReal_toReal hdivtop
  set a : ℝ := Real.log m / γ with ha_def
  have hexp : Real.exp (γ * a) = m := by
    rw [show γ * a = Real.log m by rw [ha_def]; field_simp]
    exact Real.exp_log hm
  obtain ⟨f, hfs, hfc, hf0, hfa⟩ := exists_const_shift_on hcompact hdisj₁ a
  have hprem : 0 < P {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤ ⊤ ∧
      C₀ ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁} := by
    have hpos1 : 0 < P {ω | C₁ ≤ μ ω S₁} := lt_of_lt_of_le (by norm_num) hhalf
    refine lt_of_lt_of_le hpos1 (measure_mono ?_)
    · intro ω hω
      refine ⟨le_top, ?_⟩
      rw [weylShiftPair_fst_apply_of_const hS₁m (fun z hz => hfa z hz) (μ ω) (D ω), hexp, hmC]
      calc C₀ = C₀ / C₁ * C₁ := (ENNReal.div_mul_cancel hC₁pos.ne' hC₁top).symm
        _ ≤ C₀ / C₁ * μ ω S₁ := mul_le_mul_of_nonneg_left hω zero_le
  have hset : {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤ ⊤ ∧
      C₀ ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁} = {ω | C₀ ≤ ENNReal.ofReal m * μ ω S₁} := by
    ext ω
    simp only [Set.mem_ofPred_eq, le_top, true_and]
    rw [weylShiftPair_fst_apply_of_const hS₁m (fun z hz => hfa z hz) (μ ω) (D ω), hexp]
  have hmeasShift : NullMeasurableSet {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤ ⊤ ∧
      C₀ ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁} P := by
    rw [hset]
    exact nullMeasurableSet_le aemeasurable_const (hmass.const_mul _)
  have hcm := hCM γ α₀ ξ f hγ hγ2 hα hfs hfc hf0 Ω P hC hcirc μ D S₁ S₂ ⊤ C₀ hGFF hμ hD hS₁ hS₂ hsup
    hmass hmeasShift hprem
  simpa using hcm

end HarmonicBalls
