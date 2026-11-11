import HarmonicBalls.FirstPass.S11i.Assembly13
import HarmonicBalls.FirstPass.S11i.CanonicalLawUniversal
import HarmonicBalls.FirstPass.S11ap

/-!
# The 11.12 event at the insertion `γ` and the model-independent probability

Two route-independent pieces of `Step8IdentityStmt` (Corrected11_13.lean) for the Lemma 11.12 event `E`:

* `pinchEventGamma_exists`: `CorrectedLemma11_12Stmt` (Faithful.lean) gives, for every buffered geometry and
  `0 < γ < 2`, `0 < M`, an event `E` with `PinchEventGammaStmt U T Q' Q γ ξ M E`. The insertion `α = γ` is admissible
  because `γ < Q(γ) = 2/γ + γ/2` (`lqgQ`, Defs/Notation.lean:19). No new input.
* `exists_localModConstField_prob`: for a measurable `E`, the probability `P{h^α|_{B₇} mod const ∈ E}` of a
  whole-plane GFF model is the same for every whole-plane GFF model. Proof: the field modulo constants is a fixed
  measurable function of the canonical law (`modConstOfCanon`), the probability of its preimage is the canonical law
  of `E`, and the canonical law is model-independent (`canonicalLaw_eq_of_isWholePlaneGFF`, CanonicalLawUniversal.lean:59).
  A whole-plane GFF is a probability measure (`isProbabilityMeasure_of_isWholePlaneGFF`, via the Gaussian process
  property on the empty family and `HasGaussianLaw.isProbabilityMeasure`).
-/

universe u

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- The field `h^α` modulo constants on `B₇`, as a function of the canonical coordinates `x = (⟨h^ℂ, φ⟩)_φ` of the
mean-zero test functions on `ℂ`: `φ ↦ x(φ) - α ∫ φ(x) log|x| dx`. -/
noncomputable def modConstOfCanon (α : ℝ) (x : CanonIdx → ℝ) : ModConstTestPairings (ball (0 : ℂ) 7) :=
  fun φ => x ⟨φ.1, ⟨⟨φ.2.1.1, φ.2.1.2.1, Set.subset_univ _⟩, φ.2.2⟩⟩ - α * ∫ t, φ.1 t * Real.log ‖t‖

lemma localModConstField_eq_modConstOfCanon (α : ℝ) {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) :
    localModConstField α hC (ball (0 : ℂ) 7) ω = modConstOfCanon α (fun i : CanonIdx => hC ω i.1) :=
  rfl

lemma measurable_modConstOfCanon (α : ℝ) : Measurable (modConstOfCanon α) :=
  Measurable.of_eval (fun _ => (measurable_pi_apply _).sub measurable_const)

/-- A whole-plane GFF is a probability measure: the Gaussian process property on the empty family gives a Gaussian law
of the zero-dimensional vector, which is a probability measure. -/
lemma isProbabilityMeasure_of_isWholePlaneGFF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) :
    IsProbabilityMeasure P :=
  ((hh.isGaussianProcess).hasGaussianLaw ∅).isProbabilityMeasure

/-- The probability of the event `{h^α|_{B₇} mod const ∈ E}` is the canonical law of `modConstOfCanon α ⁻¹' E`. -/
lemma prob_localModConstField_mem_eq_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (α : ℝ)
    {E : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hE : MeasurableSet E) :
    P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} =
      P.map (fun ω (i : CanonIdx) => hC ω i.1) (modConstOfCanon α ⁻¹' E) := by
  have hX : Measurable (fun ω (i : CanonIdx) => hC ω i.1) :=
    Measurable.of_eval (fun i : CanonIdx => hh.measurable_pairing i.1 i.2.1)
  rw [Measure.map_apply hX ((measurable_modConstOfCanon α) hE)]
  rfl

/-- **Model-independence of the probability of a measurable event.** For two whole-plane GFF models (on possibly different
probability spaces) the probabilities of `{h^α|_{B₇} mod const ∈ E}` agree. -/
theorem localModConstField_prob_indep {Ω Ω' : Type u} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P' hC' hcirc') (α : ℝ)
    {E : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hE : MeasurableSet E) :
    (P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E}).toReal =
      (P' {ω | localModConstField α hC' (ball (0 : ℂ) 7) ω ∈ E}).toReal := by
  have := isProbabilityMeasure_of_isWholePlaneGFF hh
  have := isProbabilityMeasure_of_isWholePlaneGFF hh'
  rw [prob_localModConstField_mem_eq_map hh α hE, prob_localModConstField_mem_eq_map hh' α hE,
    canonicalLaw_eq_of_isWholePlaneGFF hh hh']

/-- **The constant `q` of the first conjunct of `Step8IdentityStmt`.** For a measurable event `E` there is a real `q`
such that every whole-plane GFF model gives `P{h^α|_{B₇} mod const ∈ E}.toReal = q`. (If no model exists, `q = 0` is
vacuous.) -/
theorem exists_localModConstField_prob (α : ℝ) {E : Set (ModConstTestPairings (ball (0 : ℂ) 7))}
    (hE : MeasurableSet E) :
    ∃ q : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      (P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E}).toReal = q := by
  by_cases h : ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc
  · obtain ⟨Ω₀, m₀, P₀, hC₀, hc₀, hh₀⟩ := h
    exact ⟨(P₀ {ω | localModConstField α hC₀ (ball (0 : ℂ) 7) ω ∈ E}).toReal,
      fun Ω m P hC hcirc hh => localModConstField_prob_indep hh hh₀ α hE⟩
  · exact ⟨0, fun Ω m P hC hcirc hh => absurd ⟨Ω, m, P, hC, hcirc, hh⟩ h⟩

/-- **The 11.12 event at the insertion `γ`.** `CorrectedLemma11_12Stmt` gives `PinchEventGammaStmt` for every buffered
geometry, `0 < γ < 2` and `M > 0` (the insertion `α = γ` satisfies `α < lqgQ γ`). -/
theorem pinchEventGamma_exists (h12 : CorrectedLemma11_12Stmt.{u}) {U V W T Q' Q : Set ℂ} {δ₀ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ₀) {γ ξ M : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hM : 0 < M) :
    ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaStmt.{u} U T Q' Q γ ξ M E := by
  have hQ : γ < lqgQ γ := by
    unfold lqgQ
    have h2 : γ / 2 < 2 / γ := by
      rw [lt_div_iff₀ hγ]
      nlinarith
    linarith
  obtain ⟨E, hEm, hE⟩ := h12 U V W T Q' Q δ₀ hgeo
    (FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom hgeo) γ ξ hγ hγ2 M hM
  exact ⟨E, hEm, fun Ω _ P hC hcirc μ D hh hμ hD => hE γ hQ Ω P hC hcirc μ D hh hμ hD⟩

end HarmonicBalls
