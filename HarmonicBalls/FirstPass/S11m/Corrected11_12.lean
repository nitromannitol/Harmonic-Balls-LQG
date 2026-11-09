import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11j.Geometry
import HarmonicBalls.FirstPass.S11e.Include
import HarmonicBalls.Proposed.LQG

/-!
# Assembly of the corrected Lemma 11.12 from its local decoder and its positivity (fp-S11m, owner z4)

Route of `notes/fp-gaps/CHATGPT-11-12-11-13-fixes.md`: the local event `E^α(M) = {ω : h^α|_{B₇} mod constants ∈ E}` is
built from one Borel set `E` (Step 3.6, l.319-332) and the inclusion and positivity are read off the auxiliary events
`Ẽ₁`, `Ẽ₂(M)`, `Ẽ₃` of the true pair `(μ, D)` (Step 4.2 l.359-379, Step 4.3-4.5 l.380-467).

* `PinchLocalDecoderStmt` is the NEW step: one Borel `E` decides almost surely the three auxiliary events of the true pair.
  Its written argument is route Step 3.6 with the identifications of ambient and internal distances; it is not yet proved.
* `PinchThirdEventFaithfulStmt` (`FirstPass/S11h/Faithful.lean`, n2's corrected Lemma 11.17 with all three events) gives
  the positive probability of the auxiliary events. It is used as a numbered result of another worker. It is stated only for
  the exponent `ξ = γ / d_γ`, so this assembly needs `0 < ξ` (see `CorrectedLemma11_12PosXiStmt`).
* The length property of the true metric at insertion `α` is `LQGMetricFieldAxioms` (`Proposed/LQG.lean`, Fact 2.2 I, pending
  operator source-check), used at `α₀ = α`.
* The inclusion is `pinchPointEvent_of_auxiliary_events` (`FirstPass/S11e/Include.lean`), already proved.

`firstPass_11_12_corrected_posXi_of_steps` proves the restriction of `CorrectedLemma11_12Stmt` to `0 < ξ` from these inputs.
It is NOT `firstPass_11_12_corrected`: the full statement quantifies over every real `ξ` (`S11i/Faithful.lean:56`).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

universe u

/-- NEW step (route Step 3.6 with Step 4.2, `notes/fp-gaps/CHATGPT-11-12-11-13-fixes.md` l.319-332, l.359-379): one Borel
set `E` of local fields modulo constants on `B₇(0)`, chosen before `α`, such that for every insertion `α < Q` and every model,
almost surely `h^α|_{B₇} mod constants ∈ E` if and only if the three auxiliary events of the true pair `(μ, D)` hold.

UNVERIFIED (z4, round 8): the two-sided form is stronger than Lemma 11.12 (corrected, paper lines 3236-3244) needs, which
asks only for `E ⊂ Ĝ₁` almost surely and `P[E] > 0`. `pinchFirstEvent` (`Draft/Section11.lean:95`) uses
`internalMetric (thickening (2δ) (Q ∪ W))ᶜ 0 x` for `x ∈ sphere 0 5`, an unbounded set, and the whole-plane `setDist`s of
`pinchSecondEvent`/`pinchThirdEvent`. No written argument gives almost-sure `σ(h|_{B₇})`-determination of these events.
Replace by a one-sided local certificate (inclusion plus positivity) before relying on `firstPass_11_12_corrected_posXi_of_steps`. -/
def PinchLocalDecoderStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ M : ℝ, 0 < M →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), MeasurableSet E ∧
  ∀ α : ℝ, α < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
    ∀ᵐ ω ∂P, (localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E ↔
      (pinchFirstEvent (D ω) W T Q' Q δ ∧ pinchSecondEvent (μ ω) (D ω) U V δ M ∧ pinchThirdEvent (D ω) V W δ))

/-- Lemma 11.12 in the corrected form (`CorrectedLemma11_12Stmt`, `FirstPass/S11i/Faithful.lean:56`) restricted to
`0 < ξ`. This is an intermediate statement; the full statement is `CorrectedLemma11_12Stmt`. -/
def CorrectedLemma11_12PosXiStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ M : ℝ, 0 < M →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), MeasurableSet E ∧
  ∀ α : ℝ, α < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
    MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball (0 : ℂ) 7)]
      {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    0 < P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    ∀ᵐ ω ∂P, localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E →
      pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0

/-- The restriction to `0 < ξ` of Lemma 11.12 (corrected), from the local decoder `PinchLocalDecoderStmt`, the faithful
positivity of the auxiliary events `PinchThirdEventFaithfulStmt` (with `dγ = γ / ξ`), and the length property
`LQGMetricFieldAxioms` (Fact 2.2 I, Proposed) at `α₀ = α`. -/
theorem firstPass_11_12_corrected_posXi_of_steps
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hThird : PinchThirdEventFaithfulStmt.{u}) (hDec : PinchLocalDecoderStmt.{u}) :
    CorrectedLemma11_12PosXiStmt.{u} := by
  intro U V W T Q' Q δ hgeo γ ξ hγ hγ2 hξ M hM
  obtain ⟨E, hEm, hE⟩ := hDec U V W T Q' Q δ hgeo γ ξ hγ hγ2 M hM
  refine ⟨E, hEm, ?_⟩
  intro α hα Ω _ P hC hcirc μ D hgff hμ hD
  have hiff := hE α hα Ω P hC hcirc μ D hgff hμ hD
  have hmeas : MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball (0 : ℂ) 7)]
      {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} :=
    localModConstField_measurable α hC (ball (0 : ℂ) 7) hEm
  have hξeq : γ / (γ / ξ) = ξ := by
    field_simp
  have hDξ : IsLQGMetricOfField P γ (γ / (γ / ξ)) α hC D := by
    rw [hξeq]
    exact hD
  obtain ⟨A, hAsub, hAm, hAp⟩ := hThird U V W T Q' Q δ hgeo γ α (γ / ξ) hγ hγ2 hα (div_pos hγ hξ)
    Ω P hC hcirc μ D hgff hμ hDξ M hM
  have hNull := ae_iff.mp hiff
  have hSpos : 0 < P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} := by
    by_contra hcon
    have h0 : P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp hcon)
    have hsub : A ⊆ {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∪
        {ω | ¬ (localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E ↔
          (pinchFirstEvent (D ω) W T Q' Q δ ∧ pinchSecondEvent (μ ω) (D ω) U V δ M ∧
            pinchThirdEvent (D ω) V W δ))} := by
      intro ω hω
      by_cases hS : localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E
      · exact Or.inl hS
      · refine Or.inr ?_
        intro hiffω
        exact hS (hiffω.mpr (hAsub hω))
    have hle : P A ≤ 0 :=
      (measure_mono hsub).trans ((measure_union_le _ _).trans (by simp [h0, hNull]))
    exact absurd hAp (not_lt.mpr hle)
  refine ⟨hmeas, hSpos, ?_⟩
  have hgood : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) ∧ ∀ x y, 0 ≤ D ω x y := by
    obtain ⟨𝔇, h𝔇, hDω⟩ := hD
    filter_upwards [((hAx γ ξ α Ω P hC hcirc) hgff hγ hγ2 hα 𝔇 h𝔇).1, hDω] with ω hω hDωω
    have hEq : (fun x y => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal) = D ω := by
      funext x y
      rw [← (hDωω x y).2, ENNReal.toReal_ofReal (hDωω x y).1]
    refine ⟨?_, fun x y => (hDωω x y).1⟩
    rw [← hEq]
    exact hω.2
  filter_upwards [hiff, hgood] with ω hω hgoodω hmem
  have haux := hω.mp hmem
  exact pinchPointEvent_of_auxiliary_events (hgeo.toPinchPointProofConfiguration hgeo.U_nonempty)
    hgoodω.1 hgoodω.2 (μ ω) M haux.1 haux.2.1 haux.2.2

end HarmonicBalls
