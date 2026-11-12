import HarmonicBalls.FirstPass.Phase2.CountableClearanceChainDerived
import HarmonicBalls.FirstPass.Phase2.WeylContinuousShiftDerived
import HarmonicBalls.FirstPass.Phase2.WeylScalingCompositionDerived

/-!
# A measurable decoder for the internal metric of the singular LQG metric

For a γ-LQG metric `𝔇` (`IsLQGMetric`), the metric of `h - α₀ log |·|` is the Weyl scaling
`D = e^{-ξ α₀ log |·|} · 𝔇(h)`. This file builds one functional `Φ` on distributions, measurable for the σ-algebra of
pairings, which recovers the internal metric `D^W(q, q')` on an open set `W` from the field:

* the logarithmic cutoff `-α₀ log max(|·|, e^{-k})` is continuous, so `𝔇(T + cutoff_k)` is the LQG metric of a
  continuously shifted field; `singularCutoffLimsup` is `limsup_k 𝔇(T + cutoff_k)(a, b)`, measurable in `T`;
* `singularMetricDecoder` is the countable clearance-chain infimum (`countableClearanceChainInf`) of that limsup, which is
  measurable for every distribution, with no regularity assumption off the support of the field.

`singularMetricDecoder_eq` identifies the decoder with `D^W(q, q')` at every distribution `T` at which the cutoff metrics
converge to a Euclidean length metric. `ae_weylScaling_singularShift_regular` gives the regularity of the target metric:
almost surely, for a whole-plane GFF `h^ℂ` and continuous `f`, the singular metric of `h^ℂ + f` is finite, a Euclidean
length metric, and continuous at `0`.
-/

namespace HarmonicBalls

universe u

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- The pairing with a test function, `T ↦ T φ`, is measurable for the σ-algebra of pairings. -/
theorem measurable_testPairing_distribution {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ => T φ :=
  measurable_iff_comap_le.2 (le_iSup₂ (f := fun (φ : ℂ → ℝ) (_ : IsTestFunction univ φ) =>
    MeasurableSpace.comap (fun T : (ℂ → ℝ) → ℝ => T φ) inferInstance) φ hφ)

/-- The shift `T ↦ T + g` of distributions by a function (`addFunPairing`) is measurable for the σ-algebra of pairings
on both sides. -/
theorem measurable_addFunPairing_distribution_self (g : ℂ → ℝ) :
    @Measurable ((ℂ → ℝ) → ℝ) ((ℂ → ℝ) → ℝ) distributionMeasurableSpace distributionMeasurableSpace
      fun T => addFunPairing T g := by
  refine measurable_iff_comap_le.2 ?_
  unfold distributionMeasurableSpace
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun φ => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun hφ => ?_
  rw [MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 ((measurable_testPairing_distribution hφ).add_const _)

/-- The logarithmic cutoff `-α₀ log max(|z|, e^{-k})` of the singularity `-α₀ log |z|` at radius `e^{-k}`. -/
noncomputable def logCutoffWeight (α₀ : ℝ) (k : ℕ) (z : ℂ) : ℝ :=
  -α₀ * Real.log (max ‖z‖ (Real.exp (-(k : ℝ))))

theorem continuous_logCutoffWeight (α₀ : ℝ) (k : ℕ) : Continuous (logCutoffWeight α₀ k) :=
  continuous_const.mul ((continuous_norm.max continuous_const).log fun _ =>
    (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)).ne')

/-- The limsup of the LQG metrics of the cutoff fields: `limsup_k 𝔇(T - α₀ log max(|·|, e^{-k}))(a, b)`. -/
noncomputable def singularCutoffLimsup (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (α₀ : ℝ) (T : (ℂ → ℝ) → ℝ)
    (a b : ℂ) : ℝ≥0∞ :=
  limsup (fun k : ℕ => ENNReal.ofReal (𝔇 (addFunPairing T (logCutoffWeight α₀ k)) a b)) atTop

theorem measurable_singularCutoffLimsup {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (α₀ : ℝ) (a b : ℂ) :
    Measurable[distributionMeasurableSpace] fun T => singularCutoffLimsup 𝔇 α₀ T a b :=
  Measurable.limsup fun k => ENNReal.measurable_ofReal.comp
    ((h𝔇.measurable_apply a b).comp (measurable_addFunPairing_distribution_self (logCutoffWeight α₀ k)))

open Classical in
/-- The decoder of the internal metric `D^W(q, q')` of the singular metric: the countable clearance-chain infimum of
`singularCutoffLimsup` (vertices in the countable set `S`, clearance tested against the countable set `C ⊆ Wᶜ`), and `∞`
when `q ∉ W`. -/
noncomputable def singularMetricDecoder (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (α₀ : ℝ) (S C W : Set ℂ) (q q' : ℂ)
    (T : (ℂ → ℝ) → ℝ) : ℝ≥0∞ :=
  if q ∈ W then countableClearanceChainInf S C (fun a b => (singularCutoffLimsup 𝔇 α₀ T a b).toReal) q q' else ⊤

theorem measurable_singularMetricDecoder {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (α₀ : ℝ) {S C : Set ℂ} [Countable S] (hC : C.Countable) (W : Set ℂ)
    (q q' : ℂ) : Measurable[distributionMeasurableSpace] (singularMetricDecoder 𝔇 α₀ S C W q q') := by
  unfold singularMetricDecoder
  by_cases hq : q ∈ W
  · simp only [hq, ↓reduceIte]
    exact @measurable_countableClearanceChainInf _ distributionMeasurableSpace
      (fun T a b => (singularCutoffLimsup 𝔇 α₀ T a b).toReal) S C _ hC q q'
      (fun a b => (measurable_singularCutoffLimsup h𝔇 α₀ a b).ennreal_toReal)
  · simp only [hq, ↓reduceIte]
    exact measurable_const

/-- The internal metric of a set not containing the starting point is `∞`. -/
theorem internalMetric_eq_top_of_not_mem {D : ℂ → ℂ → ℝ} {W : Set ℂ} {q : ℂ} (hq : q ∉ W) (q' : ℂ) :
    internalMetric D W q q' = ⊤ := by
  rw [← top_le_iff]
  unfold internalMetric
  exact le_iInf fun P => le_iInf fun hP => absurd (by simpa using hP 0) hq

/-- Identification of the decoder. If at the distribution `T` the cutoff metrics `𝔇(T - α₀ log max(|·|, e^{-k}))(a, b)`
converge to `E(a, b)` for all `a, b`, and `E` is (the extended form of) a Euclidean length metric, then the decoder is
the internal metric of `E` on the open set `W`. -/
theorem singularMetricDecoder_eq {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {α₀ : ℝ} {S C W : Set ℂ} (hS : Dense S)
    (hW : IsOpen W) (hCW : C ⊆ Wᶜ) (hWC : Wᶜ ⊆ closure C) {T : (ℂ → ℝ) → ℝ} {E : ℂ → ℂ → ℝ≥0∞}
    (hE : IsEuclideanLengthMetric fun a b => (E a b).toReal)
    (hlim : ∀ a b, Tendsto (fun k : ℕ => ENNReal.ofReal (𝔇 (addFunPairing T (logCutoffWeight α₀ k)) a b))
      atTop (𝓝 (E a b)))
    (q q' : ℂ) :
    singularMetricDecoder 𝔇 α₀ S C W q q' T = internalMetric (fun a b => (E a b).toReal) W q q' := by
  have hN : (fun a b => (singularCutoffLimsup 𝔇 α₀ T a b).toReal) = fun a b => (E a b).toReal := by
    funext a b
    rw [singularCutoffLimsup, (hlim a b).limsup_eq]
  unfold singularMetricDecoder
  split_ifs with hq
  · rw [hN, hE.internalMetric_eq_countableClearanceChainInf hS hW hCW hWC hq q']
  · exact (internalMetric_eq_top_of_not_mem hq q').symm

/-- Regularity of the singular metric of a shifted field. Under the field axioms of the LQG metric of
`h^ℂ - α₀ log |·|` (`LQGMetricFieldAxiomsUnivFrozen`), for a whole-plane GFF `h^ℂ` and a continuous function `f`, almost
surely the metric `E = e^{-ξ α₀ log |·|} · 𝔇(h^ℂ + f)` of `h^ℂ + f - α₀ log |·|` is finite, its real form is a
Euclidean length metric, and `E(x, 0) → 0` as `x → 0`. Route: `E = e^{ξ f} · D_h` by the Weyl scaling composition
(`weylScalingCompositionFrozen_holds`) and axiom III, and `D_h` is a Euclidean length metric by axiom I. -/
theorem ae_weylScaling_singularShift_regular (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) {γ ξ α₀ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hW : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) {f : ℂ → ℝ} (hf : Continuous f) :
    ∀ᵐ ω ∂P,
      (∀ u v, weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α₀ * Real.log ‖z‖) u v < ⊤) ∧
      IsEuclideanLengthMetric (fun u v =>
        (weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α₀ * Real.log ‖z‖) u v).toReal) ∧
      Tendsto (fun x => weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α₀ * Real.log ‖z‖) x 0)
        (𝓝 0) (𝓝 0) := by
  have hAxω := hAx Ω P γ ξ α₀ hC hcirc hW hγ0 hγ2 hα 𝔇 h𝔇
  filter_upwards [hAxω.1, hAxω.2.2.1,
    weylScalingCompositionFrozen_holds γ ξ α₀ Ω P hC hcirc hW hγ0 hγ2 hα 𝔇 h𝔇 f hf] with ω hI hIII hcomp
  have hfun : weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α₀ * Real.log ‖z‖) =
      weylScaling (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ξ f := by
    funext u v
    exact (hcomp u v).trans (hIII f hf u v)
  rw [hfun]
  obtain ⟨hfin, hE⟩ := hI.2.weylScaling_continuous_isEuclideanLengthMetric ξ hf
  refine ⟨hfin, hE, ?_⟩
  have h00 : weylScaling (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) ξ f
      0 0 = 0 := by
    have h := hE.self_eq_zero 0
    rcases ENNReal.toReal_eq_zero_iff _ |>.mp h with h | h
    · exact h
    · exact absurd h (hfin 0 0).ne
  have hc := (ENNReal.continuous_ofReal.comp (hE.continuous_left 0)).tendsto 0
  simp only [Function.comp_def, ENNReal.ofReal_toReal (hfin _ _).ne, h00, ENNReal.toReal_zero,
    ENNReal.ofReal_zero] at hc
  exact hc

end HarmonicBalls
