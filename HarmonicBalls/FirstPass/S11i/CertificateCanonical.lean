import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.S11i.AlphaCanonical
import HarmonicBalls.FirstPass.S11i.CanonicalLawUniversal
import HarmonicBalls.FirstPass.S11i.RootedLocality

/-!
# Positivity of the canonical certificate probability (write-up Step 7 / Section 4, B1 of `notes/fp-gaps/CHATGPT-n3-step12-gaps.md`)

For one whole-plane GFF realization `(Ω, P, hC, hcirc)` and the canonical field `alphaCanon γ hC`, the event
`A_F = {ω | ballRestrictPairing 7 (alphaCanon γ hC ω) ∈ F}` has probability independent of the realization
(`canonicalLaw_eq_of_isWholePlaneGFF`). The positivity clause `0 < P(A_F)` of the corrected Lemma 11.12 (`[C43]`,
`CorrectedLemma11_12Stmt`, `Faithful.lean:56`) at insertion `α = γ` therefore transfers to every realization.

Inputs: `CorrectedLemma11_12Stmt` (Lemma 11.12, corrected form; the certificate `E` is its output) and one realization
`(Ω₀, P₀, hC₀, hcirc₀, μ₀, D₀)` carrying an LQG measure and an LQG metric at insertion `γ` (existence input, see the
report). The argument uses no further inputs.
-/

namespace HarmonicBalls.S11iCert

open MeasureTheory Metric Set Filter

universe u

/-- The restriction to `B_7(0)` of the canonical field equals the restricted local field modulo constants
(definitional: both are the pairings `φ ↦ hC φ - α ∫ φ log|·|` on the test functions of `B_7(0)`). -/
theorem ballRestrict_alphaCanon_eq (α : ℝ) {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) :
    ballRestrictPairing 7 (alphaCanon α hC ω) = localModConstField α hC (ball (0 : ℂ) 7) ω := by
  funext i
  rfl

/-- The event `{x | ballRestrictPairing 7 (transl (logDrift α) x) ∈ E}` on the canonical pairing space. -/
def canonEvent (α : ℝ) (E : Set (ModConstTestPairings (ball (0 : ℂ) 7))) :
    Set (ModConstTestPairings (univ : Set ℂ)) :=
  {x | ballRestrictPairing 7 (transl (logDrift α) x) ∈ E}

/-- The canonical event `A_F` has the same probability in every whole-plane GFF realization. -/
theorem prob_ballRestrict_alphaCanon_indep {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P' hC' hcirc') (α : ℝ)
    (E : Set (ModConstTestPairings (ball (0 : ℂ) 7))) (hE : MeasurableSet E) :
    P {ω | ballRestrictPairing 7 (alphaCanon α hC ω) ∈ E} =
      P' {ω | ballRestrictPairing 7 (alphaCanon α hC' ω) ∈ E} := by
  -- the deterministic map from the pairings to the canonical field, and the restriction to `B_7`
  have hvec : Measurable (fun ω (i : {φ : ℂ → ℝ // IsTestFunction (univ : Set ℂ) φ ∧ ∫ x, φ x = 0}) => hC ω i.1) :=
    Measurable.of_eval (fun i => hh.measurable_pairing i.1 i.2.1)
  have hvec' : Measurable (fun ω (i : {φ : ℂ → ℝ // IsTestFunction (univ : Set ℂ) φ ∧ ∫ x, φ x = 0}) => hC' ω i.1) :=
    Measurable.of_eval (fun i => hh'.measurable_pairing i.1 i.2.1)
  have hT : Measurable (transl (logDrift α)) := by
    unfold transl
    exact Measurable.of_eval (fun i => (measurable_pi_apply i).add_const _)
  have hR : Measurable (ballRestrictPairing 7) :=
    Measurable.of_eval (fun i => measurable_pi_apply _)
  have hS : MeasurableSet (canonEvent α E) := (hR.comp hT) hE
  have e1 : {ω | ballRestrictPairing 7 (alphaCanon α hC ω) ∈ E} =
      (fun ω (i : {φ : ℂ → ℝ // IsTestFunction (univ : Set ℂ) φ ∧ ∫ x, φ x = 0}) => hC ω i.1) ⁻¹' canonEvent α E := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_preimage, canonEvent, Set.mem_ofPred_eq, alphaCanon_eq]
  have e2 : {ω | ballRestrictPairing 7 (alphaCanon α hC' ω) ∈ E} =
      (fun ω (i : {φ : ℂ → ℝ // IsTestFunction (univ : Set ℂ) φ ∧ ∫ x, φ x = 0}) => hC' ω i.1) ⁻¹' canonEvent α E := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_preimage, canonEvent, Set.mem_ofPred_eq, alphaCanon_eq]
  rw [e1, e2, ← Measure.map_apply hvec hS, ← Measure.map_apply hvec' hS,
    canonicalLaw_eq_of_isWholePlaneGFF hh hh']

/-- Positivity of the canonical certificate probability at insertion `γ`, from the positivity clause of the corrected
Lemma 11.12 for one realization and the model-independence of the canonical law. Output: the certificate `E` of
Lemma 11.12 (measurable) and `0 < P(A_F)` for every whole-plane GFF realization `P` (write-up (17)-(18)). -/
theorem certificate_canonical_pos (hCert : CorrectedLemma11_12Stmt.{u})
    (U V W T Q' Q : Set ℂ) (δ₀ : ℝ) (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ₀)
    (hOmega : insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ₀)
    {γ ξ M : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M)
    (hmodel : ∃ (Ω₀ : Type u) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ) (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ) (D₀ : Ω₀ → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧ IsLQGMeasureOfField P₀ γ γ hcirc₀ μ₀ ∧
        IsLQGMetricOfField P₀ γ ξ γ hC₀ D₀) :
    ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), MeasurableSet E ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        0 < (P {ω | ballRestrictPairing 7 (alphaCanon γ hC ω) ∈ E}).toReal := by
  obtain ⟨E, hEm, hEclause⟩ := hCert U V W T Q' Q δ₀ hgeom hOmega γ ξ hγ0 hγ2 M hM
  refine ⟨E, hEm, ?_⟩
  intro Ω _ P _ hC hcirc hGFF
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, hC₀, hcirc₀, μ₀, D₀, hGFF₀, hμ₀, hD₀⟩ := hmodel
  have hQ : γ < lqgQ γ := by
    have h1 : γ / 2 < 2 / γ := by
      rw [div_lt_div_iff₀ (by norm_num) hγ0]
      nlinarith
    unfold lqgQ
    linarith
  obtain ⟨-, hpos₀, -⟩ := hEclause γ hQ Ω₀ P₀ hC₀ hcirc₀ μ₀ D₀ hGFF₀ hμ₀ hD₀
  have hpos₀' : 0 < P₀ {ω | ballRestrictPairing 7 (alphaCanon γ hC₀ ω) ∈ E} := by
    simpa only [ballRestrict_alphaCanon_eq] using hpos₀
  have htr := prob_ballRestrict_alphaCanon_indep hGFF₀ hGFF γ E hEm
  have hpos : 0 < P {ω | ballRestrictPairing 7 (alphaCanon γ hC ω) ∈ E} := by
    rw [← htr]
    exact hpos₀'
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top P _)

end HarmonicBalls.S11iCert
