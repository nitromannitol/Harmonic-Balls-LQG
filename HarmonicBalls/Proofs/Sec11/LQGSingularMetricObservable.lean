import HarmonicBalls.Proofs.Sec11.LQGBaseMetricObservable
import HarmonicBalls.Steps.Sec11.PinchMetricMeasure

/-! # A singular LQG metric as a field observable

The staged metric locality input gives a measurable decoder for each field
realization. Its construction may depend on that realization.
-/

namespace HarmonicBalls

open Set MeasureTheory ProbabilityTheory

/-- A standard Borel observable measurable in the full field sigma algebra
is a measurable function of the GFF observable process. -/
theorem exists_observable_of_field_measurable
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [StandardBorelSpace E] [Nonempty E] {α₀ : ℝ}
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (f : Ω → E) (hf : Measurable[fieldSigmaAlgebra α₀ hC univ] f) :
    ∃ F : (GFFObservable.Admissible → ℝ) → E, Measurable F ∧
      ∀ ω, F (fun o => o.1.eval (hC ω) (hcirc ω)) = f ω := by
  rw [fieldSigmaAlgebra_eq, fieldSigmaAlgebra_eq_comap_localFieldPairings] at hf
  obtain ⟨g, hg, heq⟩ := hf.exists_eq_measurable_comp
  let r : (GFFObservable.Admissible → ℝ) → LocalFieldTest univ → ℝ :=
    fun v φ => v ⟨.pairing φ.1, φ.2⟩
  have hr : Measurable r := by
    apply measurable_pi_iff.mpr
    intro φ
    exact measurable_pi_apply (⟨.pairing φ.1, φ.2⟩ : GFFObservable.Admissible)
  refine ⟨g ∘ r, hg.comp hr, ?_⟩
  intro ω
  have hpr : r (fun o => o.1.eval (hC ω) (hcirc ω)) = localFieldPairings 0 hC univ ω := by
    funext φ
    simp [r, localFieldPairings, fieldPairing, GFFObservable.eval]
  rw [Function.comp_apply, hpr, heq]
  rfl

/-- Pointwise field-measurable distance representatives that almost surely
agree with a continuous distance observation yield a measurable field decoder. -/
theorem exists_continuous_observable_of_field_representative
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → C(ℂ × ℂ, ℝ)) (G : Ω → ℂ → ℂ → ℝ)
    (hG : ∀ x y, Measurable[fieldSigmaAlgebra α₀ hC univ] fun ω => G ω x y)
    (hEq : ∀ᵐ ω ∂P, ∀ x y, G ω x y = D ω (x, y)) :
    ∃ F : (GFFObservable.Admissible → ℝ) → C(ℂ × ℂ, ℝ), Measurable F ∧
      ∀ᵐ ω ∂P, F (fun o => o.1.eval (hC ω) (hcirc ω)) = D ω := by
  let d : ℕ → ℂ × ℂ := TopologicalSpace.denseSeq (ℂ × ℂ)
  let e : C(ℂ × ℂ, ℝ) → ℕ → ℝ := fun D n => D (d n)
  have he : Measurable e := measurable_pi_iff.mpr fun n =>
    (continuous_eval_const (d n)).measurable
  have hinj : Function.Injective e := by
    intro D D' h
    apply ContinuousMap.ext
    have hd := (TopologicalSpace.denseRange_denseSeq (ℂ × ℂ)).equalizer
      D.continuous D'.continuous
    apply congrFun (hd ?_)
    funext n
    exact congrFun h n
  have hemb : MeasurableEmbedding e := he.measurableEmbedding hinj
  obtain ⟨decode, hdecode, hdecode_eq⟩ :=
    hemb.exists_measurable_extend (g := id) measurable_id (fun _ => inferInstance)
  let f : Ω → ℕ → ℝ := fun ω n => G ω (d n).1 (d n).2
  have hf : Measurable[fieldSigmaAlgebra α₀ hC univ] f := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC univ
    exact measurable_pi_iff.mpr fun n => hG (d n).1 (d n).2
  obtain ⟨g, hg, hg_eq⟩ := exists_observable_of_field_measurable hC hcirc f hf
  refine ⟨decode ∘ g, hdecode.comp hg, ?_⟩
  filter_upwards [hEq] with ω hω
  rw [Function.comp_apply, hg_eq]
  have heq : f ω = e (D ω) := by
    funext n
    exact hω (d n).1 (d n).2
  rw [heq]
  exact congrFun hdecode_eq _

/-- Under the staged singular-field metric axioms, each continuous version of
the singular metric has a measurable field decoder, almost surely. -/
theorem IsWholePlaneGFF.exists_singularMetric_observable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → C(ℂ × ℂ, ℝ)}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC (fun ω x y => D ω (x, y))) :
    ∃ F : (GFFObservable.Admissible → ℝ) → C(ℂ × ℂ, ℝ), Measurable F ∧
      ∀ᵐ ω ∂P, F (fun o => o.1.eval (hC ω) (hcirc ω)) = D ω := by
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  obtain ⟨hmetric, hlocal, _, _⟩ := haxioms hgff hγ hγ₂ hα 𝔇 h𝔇
  obtain ⟨G, hG, hGeq⟩ := hlocal univ isOpen_univ
  apply exists_continuous_observable_of_field_representative hC hcirc D
    (fun ω x y => (G ω x y).toReal)
  · intro x y
    exact (hG x y).ennreal_toReal
  · filter_upwards [hrepr, hmetric, hGeq] with ω hrepr hmetric hGeq
    intro x y
    have hbase : (fun u v => D ω (u, v)) = fun u v =>
        (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      funext u v
      rw [← (hrepr u v).2, ENNReal.toReal_ofReal (hrepr u v).1]
    have hlength : IsEuclideanLengthMetric (fun u v => D ω (u, v)) := by
      rw [hbase]
      exact hmetric.2
    have heq := hGeq x (mem_univ x) y (mem_univ y)
    rw [← hbase, ← hlength.ofReal_eq_internalMetric] at heq
    rw [← heq, ENNReal.toReal_ofReal (hrepr x y).1]

/-- The joint law of the LQG measure and a singular metric has a measurable
field-observable version on every other whole-plane GFF realization.  Identifying
that version with the other realization's singular metric is a separate step. -/
theorem IsWholePlaneGFF.identDistrib_lqgMeasure_singularMetric_observable
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    {D : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ α₀ hcirc' μ')
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC (fun ω x y => D ω (x, y))) :
    ∃ F : (GFFObservable.Admissible → ℝ) → C(ℂ × ℂ, ℝ), Measurable F ∧
      (∀ᵐ ω ∂P, F (fun o => o.1.eval (hC ω) (hcirc ω)) = D ω) ∧
      IdentDistrib (fun ω => (μ ω, D ω))
        (fun ω => (μ' ω, F (fun o => o.1.eval (hC' ω) (hcirc' ω)))) P P' := by
  obtain ⟨F, hF, hEq⟩ := h.exists_singularMetric_observable haxioms hγ hγ₂ hα hD
  refine ⟨F, hF, hEq, ?_⟩
  have hd := h.identDistrib_lqgMeasure_with_standardBorel_observable h' hμ hμ' F hF
  have heq : ∀ᵐ ω ∂P, (μ ω, F (fun o => o.1.eval (hC ω) (hcirc ω))) = (μ ω, D ω) :=
    hEq.mono fun ω hω => congrArg (Prod.mk (μ ω)) hω
  exact (IdentDistrib.of_ae_eq hd.aemeasurable_fst heq).symm.trans hd

#print axioms exists_observable_of_field_measurable
#print axioms exists_continuous_observable_of_field_representative
#print axioms IsWholePlaneGFF.exists_singularMetric_observable
#print axioms IsWholePlaneGFF.identDistrib_lqgMeasure_singularMetric_observable

end HarmonicBalls
