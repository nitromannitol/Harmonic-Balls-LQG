import HarmonicBalls.Draft.Section11
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.S11e.Include
import HarmonicBalls.FirstPass.S11e.FirstPositive
import HarmonicBalls.FirstPass.Frozen.S11e

/-!
# First pass, Section 11 pinch positivity (fp-S11e, owner n2)

Results of this file: Lemmas 11.12, 11.15, 11.16, 11.17 of the paper (`lemma:mu_h-pinch-positive-probability`,
`lemma:first-event-proof`, `lemma:second-event-proof`, `lemma:third-event-proof`). Current state:

* `firstPass_11_16` is PROVED-FP: Lemma 11.17 (`PinchThirdEventPositiveStmt`) implies Lemma 11.16
  (`PinchSecondEventPositiveStmt`) with the same configuration and the same witnesses, since `Ẽ₁ ∩ Ẽ₂ ∩ Ẽ₃ ⊆ Ẽ₁ ∩ Ẽ₂`
  (paper lines 3281-3285).
* Lemmas 11.15 and 11.17 and Lemma 11.12 remain OPEN (their NEW local-certificate steps are not yet formalized; see
  `reports/n2.md`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Lemma 11.16 (`lemma:second-event-proof`, paper line 3281), first-pass form. It follows from Lemma 11.17
(`PinchThirdEventPositiveStmt`, paper line 3285): the same configuration `U, V, W, T, Q', Q, δ₀` and the same
measurable witnesses `A`, because `Ẽ₁ ∩ Ẽ₂ ∩ Ẽ₃ ⊆ Ẽ₁ ∩ Ẽ₂` and `P A > 0` is unchanged. -/
theorem firstPass_11_16 (h : PinchThirdEventPositiveStmt.{u}) : PinchSecondEventPositiveStmt.{u} := by
  obtain ⟨U, V, W, T, Q', Q, δ, hconfig, hpos⟩ := h
  refine ⟨U, V, W, T, Q', Q, δ, hconfig, ?_⟩
  intro γ ξ hγ hγ₂ Ω inst P hC hcirc μ D hgff hμ hD M hM
  obtain ⟨A, hA, hmeas, hp⟩ := hpos γ ξ hγ hγ₂ Ω P hC hcirc μ D hgff hμ hD M hM
  exact ⟨A, fun ω hω => ⟨(hA hω).1, (hA hω).2.1⟩, hmeas, hp⟩

/-- Lemma 11.12 (`PinchEventPositiveProbabilityStmt`, `Draft/Section11.lean:246`, the `α₀ = 0` inner-measure form),
first-pass form. Hypotheses: Lemma 11.17 (`PinchThirdEventPositiveStmt`, paper line 3285) and the Proposed input
`LQGMetricFieldAxioms` (Fact 2.2 I, the a.s. length-metric property of the LQG metric; `Proposed/LQG.lean:199-204`), for
every carrier `Ω : Type u` and every exponent. Proof: on the event where `D ω` is a Euclidean length metric with
nonnegative values, `Ẽ₁ ∩ Ẽ₂(M) ∩ Ẽ₃ ⊆ Ĝ₁(0; M)` by `pinchPointEvent_of_auxiliary_events`; the bad set is contained in a
measurable null set `N`, so `A \ N` is measurable with `P (A \ N) = P A > 0`. -/
theorem firstPass_11_12
    (hAx : ∀ (γ ξ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ 0 hC hcirc)
    (h : PinchThirdEventPositiveStmt.{u}) : PinchEventPositiveProbabilityStmt.{u} := by
  obtain ⟨U, V, W, T, Q', Q, δ, hconfig, hpos⟩ := h
  refine ⟨U, T, Q', Q, hconfig.toIsPinchPointConfiguration, ?_⟩
  intro γ ξ hγ hγ₂ Ω inst P hC hcirc μ D hgff hμ hD M hM
  obtain ⟨A, hA, hmeas, hp⟩ := hpos γ ξ hγ hγ₂ Ω P hC hcirc μ D hgff hμ hD M hM
  obtain ⟨𝔇, h𝔇, hDω⟩ := hD
  have hQ : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    positivity
  have hgood : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) ∧ ∀ u v, 0 ≤ D ω u v := by
    filter_upwards [((hAx γ ξ Ω P hC hcirc) hgff hγ hγ₂ hQ 𝔇 h𝔇).1, hDω] with ω hω hDωω
    have hEq : (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -0 * Real.log ‖x‖) u v).toReal) = D ω := by
      funext u v
      rw [← (hDωω u v).2, ENNReal.toReal_ofReal (hDωω u v).1]
    refine ⟨?_, fun u v => (hDωω u v).1⟩
    rw [← hEq]
    exact hω.2
  obtain ⟨N, hNm, hsub, hN0⟩ : ∃ N : Set Ω, MeasurableSet N ∧
      {ω | ¬ (IsEuclideanLengthMetric (D ω) ∧ ∀ u v, 0 ≤ D ω u v)} ⊆ N ∧ P N = 0 :=
    ⟨toMeasurable P _, measurableSet_toMeasurable _ _, subset_toMeasurable _ _, by
      rw [measure_toMeasurable]
      exact ae_iff.1 hgood⟩
  refine ⟨A \ N, ?_, hmeas.diff hNm, ?_⟩
  · intro ω hω
    have hgoodω : IsEuclideanLengthMetric (D ω) ∧ ∀ u v, 0 ≤ D ω u v := by
      by_contra hbad
      exact hω.2 (hsub hbad)
    have hA' := hA hω.1
    exact pinchPointEvent_of_auxiliary_events hconfig hgoodω.1 hgoodω.2 (μ ω) M hA'.1 hA'.2.1 hA'.2.2
  · rw [measure_sdiff_null hN0]
    exact hp

/-- Lemma 11.15 (`lemma:first-event-proof`, paper line 3277), first-pass form: `P[Ẽ₁] > 0` for the fixed corrected pinch
configuration (`isCorrectedPinchConfiguration_fixed`). The only hypothesis is the frozen field-level measurability
`LQGMetricPointwiseAEMeasurableFrozen` (`FirstPass/Frozen/S11e.lean`, EXTERNAL, a.e. form on realized LQG metrics). Proof:
`pinchFirst_positive_of_frozen` (`FirstPass/S11e/FirstPositive.lean`). -/
theorem firstPass_11_15 (hfr : LQGMetricPointwiseAEMeasurableFrozen) : PinchFirstEventPositiveStmt.{u} := by
  unfold PinchFirstEventPositiveStmt
  refine ⟨_, _, _, _, _, _, _, isCorrectedPinchConfiguration_fixed.toIsPinchPointProofConfiguration, ?_⟩
  intro γ ξ hγ hγ2 Ω _ P hC hcirc D hgff hD
  exact pinchFirst_positive_of_frozen hfr isCorrectedPinchConfiguration_fixed hγ hγ2 P hC hcirc D hgff hD

#print axioms firstPass_11_15

#print axioms firstPass_11_16
#print axioms firstPass_11_12

end HarmonicBalls
