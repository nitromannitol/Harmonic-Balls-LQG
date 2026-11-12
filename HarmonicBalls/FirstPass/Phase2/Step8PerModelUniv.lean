import HarmonicBalls.FirstPass.Phase2.LQGMetricAxiomsUniv
import HarmonicBalls.FirstPass.Phase2.Step8PerModelWholePlane
import HarmonicBalls.FirstPass.Phase2.Lemma1110LeafForms

/-!
# Step 8 of Lemma 11.13 on probability spaces of every universe

`Step8CertificateFrequencyPerModelStmt` quantifies over models `(P, h^ℂ, h_·(·), μ, D)` on a sample space
`Ω : Type u`. Its proof from the seed inputs is written on spaces in `Type`. This file transfers it to every universe.

Proof. A model on `Ω : Type u` is represented on a sample space in `Type`: the range of
`X : ω ↦ (h^ℂ(ω), h_·(·)(ω), μ(ω), D(ω))` (`ModelRange`), with the σ-algebra of the sets whose preimage under `X` is
`P`-null-measurable and the push-forward of the completion of `P` (`modelRangeMeasure`), as in
`Phase2/LQGMetricAxiomsUniv.lean`. An almost sure statement holds on the range if and only if it holds on `Ω`
(`ae_modelRangeMeasure_iff`). The range model is a whole-plane GFF (`isWholePlaneGFF_modelRangeMeasure`); the LQG
measure and the LQG metric of the field are almost sure properties of `(h_·(·), μ)` and `(h^ℂ, D)`, so they hold on the
range. The statement on the range gives zoom families on the range; their composites with `X` are the zoom families of
the model, and both conclusions are almost sure statements about the sample point `X ω`.

## Main results

* `step8CertificateFrequencyPerModel_univ_of_zero`: `Step8CertificateFrequencyPerModelStmt.{0}` implies
  `Step8CertificateFrequencyPerModelStmt.{u}`.
* `firstPass_11_13_canonical_univ_of_seedInputs_metricInputs`: Lemma 11.13 at the canonical exponent at every universe,
  from the field axioms of the LQG metric and the literature inputs `hN2`, `hfr`, `hDC`, `hFin` (in `Type`).
-/

universe u

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

namespace Step8PerModelUniv

open LQGMetricUniv

/-- A sample point of a whole-plane model: the pairings of the field, its circle averages, the LQG measure and the
LQG metric. -/
structure ModelPoint : Type where
  /-- The pairings `φ ↦ (h^ℂ, φ)`. -/
  pairing : (ℂ → ℝ) → ℝ
  /-- The circle averages `(r, z) ↦ h^ℂ_r(z)`. -/
  circle : ℝ → ℂ → ℝ
  /-- The LQG measure. -/
  measure : Measure ℂ
  /-- The LQG metric. -/
  metric : ℂ → ℂ → ℝ

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The sample point of the model at `ω`. -/
def modelPoint (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (ω : Ω) : ModelPoint :=
  ⟨hC ω, hcirc ω, μ ω, D ω⟩

/-- The range of `X : Ω → ModelPoint`, a type in `Type`. The measure `P` only enters through the σ-algebra. -/
def ModelRange (_P : Measure Ω) (X : Ω → ModelPoint) : Type := {y : ModelPoint // ∃ ω, X ω = y}

/-- The map of `Ω` to the range of `X`, on the completion `NullMeasurableSpace Ω P`. -/
def toModelRange (P : Measure Ω) (X : Ω → ModelPoint) : NullMeasurableSpace Ω P → ModelRange P X :=
  fun ω => ⟨X ω, ω, rfl⟩

/-- The σ-algebra of the range: the sets whose preimage is `P`-null-measurable. -/
instance (P : Measure Ω) (X : Ω → ModelPoint) : MeasurableSpace (ModelRange P X) :=
  MeasurableSpace.map (toModelRange P X) inferInstance

/-- The law of the model on the range: the push-forward of the completion of `P`. -/
noncomputable def modelRangeMeasure (P : Measure Ω) (X : Ω → ModelPoint) : Measure (ModelRange P X) :=
  P.completion.map (toModelRange P X)

variable {P : Measure Ω} {X : Ω → ModelPoint}

theorem measurable_toModelRange : Measurable (toModelRange P X) := fun _ hs => hs

/-- A function on the range whose composite with `X` is null-measurable is measurable. -/
theorem measurable_of_nullMeasurable_modelRange {β : Type*} [MeasurableSpace β] {g : ModelRange P X → β}
    (hg : NullMeasurable (fun ω : Ω => g (toModelRange P X ω)) P) : Measurable g := fun _ hs => hg hs

/-- Almost sure statements on the range are almost sure statements on `Ω`. -/
theorem ae_modelRangeMeasure_iff {p : ModelRange P X → Prop} :
    (∀ᵐ y ∂modelRangeMeasure P X, p y) ↔ ∀ᵐ ω ∂P, p (toModelRange P X ω) := by
  constructor
  · intro h
    exact ae_of_ae_map measurable_toModelRange.aemeasurable h
  · intro h
    have hnull : P {ω | ¬p (toModelRange P X ω)} = 0 := ae_iff.1 h
    have hms : MeasurableSet {y | p y} := by
      change NullMeasurableSet {ω : Ω | p (toModelRange P X ω)} P
      have h1 : NullMeasurableSet {ω : Ω | ¬p (toModelRange P X ω)} P := NullMeasurableSet.of_null hnull
      convert h1.compl using 1
      ext ω
      simp
    exact (ae_map_iff measurable_toModelRange.aemeasurable hms).2 h

/-- The range of a whole-plane GFF model is a whole-plane GFF under `modelRangeMeasure`. -/
theorem isWholePlaneGFF_modelRangeMeasure {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (μ : Ω → Measure ℂ)
    (D : Ω → ℂ → ℂ → ℝ) (hG : IsWholePlaneGFF P hC hcirc) :
    IsWholePlaneGFF (modelRangeMeasure P (modelPoint hC hcirc μ D)) (fun y => y.1.pairing)
      (fun y => y.1.circle) := by
  have hGc : IsWholePlaneGFF P.completion (hC ∘ fromNull P) (hcirc ∘ fromNull P) :=
    hG.comp_measurePreserving measurePreserving_fromNull
  have hmeasO : ∀ o : GFFObservable, o.IsAdmissible →
      Measurable fun y : ModelRange P (modelPoint hC hcirc μ D) => o.eval y.1.pairing y.1.circle := by
    intro o ho
    refine measurable_of_nullMeasurable_modelRange ?_
    cases o with
    | pairing φ => exact (hG.measurable_pairing φ ho).nullMeasurable
    | circle r z => exact (hG.measurable_circle r z ho).nullMeasurable
  have hint : ∀ g : ModelRange P (modelPoint hC hcirc μ D) → ℝ, Measurable g →
      ∫ y, g y ∂modelRangeMeasure P (modelPoint hC hcirc μ D) =
        ∫ ω, g (toModelRange P (modelPoint hC hcirc μ D) ω) ∂P.completion := fun g hg =>
    integral_map measurable_toModelRange.aemeasurable hg.aestronglyMeasurable
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ hφ
    exact hmeasO (.pairing φ) hφ
  · intro r z hr
    exact hmeasO (.circle r z) hr
  · refine ⟨fun I => ?_⟩
    have hI : Measurable (fun y : ModelRange P (modelPoint hC hcirc μ D) =>
        I.restrict fun o : GFFObservable.Admissible => o.1.eval y.1.pairing y.1.circle) :=
      measurable_pi_iff.mpr fun i => hmeasO i.1.1 i.1.2
    refine ⟨hI.aemeasurable, ?_⟩
    have hlaw : (modelRangeMeasure P (modelPoint hC hcirc μ D)).map
        (fun y : ModelRange P (modelPoint hC hcirc μ D) =>
          I.restrict fun o : GFFObservable.Admissible => o.1.eval y.1.pairing y.1.circle) =
        P.completion.map (fun ω : NullMeasurableSpace Ω P =>
          I.restrict fun o : GFFObservable.Admissible => o.1.eval ((hC ∘ fromNull P) ω) ((hcirc ∘ fromNull P) ω)) := by
      rw [modelRangeMeasure, Measure.map_map hI measurable_toModelRange]
      rfl
    rw [hlaw]
    exact (hGc.isGaussianProcess.hasGaussianLaw I).isGaussian_map
  · intro o ho
    rw [hint _ (hmeasO o ho)]
    exact hGc.integral_eq_zero o ho
  · intro o o' ho ho'
    rw [modelRangeMeasure, covariance_map_fun (hmeasO o ho).aestronglyMeasurable
      (hmeasO o' ho').aestronglyMeasurable measurable_toModelRange.aemeasurable]
    exact hGc.covariance_eq o o' ho ho'
  · exact ae_modelRangeMeasure_iff.2 hG.ae_continuousOn_circle

end Step8PerModelUniv

open Step8PerModelUniv

/-- **Step 8 of Lemma 11.13 at every universe.** The per-model certificate frequency on sample spaces in `Type`
implies it on sample spaces in `Type u`: the model is represented on the range of its sample point
`(h^ℂ, h_·(·), μ, D)`, and the zoom families of the range model, composed with the sample point, are zoom families of
the model. -/
theorem step8CertificateFrequencyPerModel_univ_of_zero (h0 : Step8CertificateFrequencyPerModelStmt.{0}) :
    Step8CertificateFrequencyPerModelStmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM Ω _ P hC hcirc μ D hG hμ hD
  have hG' := isWholePlaneGFF_modelRangeMeasure (P := P) μ D hG
  have hμ' : IsLQGMeasureOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ α₀ (fun y => y.1.circle)
      (fun y => y.1.measure) := by
    unfold IsLQGMeasureOfField IsLQGMeasure at hμ ⊢
    exact ae_modelRangeMeasure_iff.2 hμ
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  have hD' : IsLQGMetricOfField (modelRangeMeasure P (modelPoint hC hcirc μ D)) γ (lqgXi γ) α₀
      (fun y => y.1.pairing) (fun y => y.1.metric) :=
    ⟨𝔇, h𝔇, ae_modelRangeMeasure_iff.2 hDae⟩
  obtain ⟨q, hq, μk, Dk, hsc, hstep⟩ := h0 U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM
    (ModelRange P (modelPoint hC hcirc μ D)) (modelRangeMeasure P (modelPoint hC hcirc μ D)) _ _ _ _ hG' hμ' hD'
  refine ⟨q, hq, fun k ω => μk k (toModelRange P (modelPoint hC hcirc μ D) ω),
    fun k ω => Dk k (toModelRange P (modelPoint hC hcirc μ D) ω), fun k => ?_, fun k => ?_⟩
  · exact ae_modelRangeMeasure_iff.1 (hsc k)
  · exact ae_modelRangeMeasure_iff.1 (hstep k)

open FirstPassPhase2Step8WholePlaneFromSeed in
/-- **Lemma 11.13 (canonical exponent) at every universe, from the literature inputs.** Step 8 on sample spaces in
`Type` from the seed inputs (`step8CertificateFrequencyWholePlane_of_seedInputs`, with Proposition 11.9 from the field
axioms and Lemma 11.10 from `hDC` and `hFin`), transferred to `Type u` by
`step8CertificateFrequencyPerModel_univ_of_zero`. Inputs: the field axioms of the LQG metric (`hAx` in `Type u`,
`hAx0` in `Type`), the local metric replacement `hN2`, the continuity of the rooted physical metric at the insertion
`hfr`, and the dyadic diameter inputs `hDC`, `hFin`. -/
theorem firstPass_11_13_canonical_univ_of_seedInputs_metricInputs
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hAx0 : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hDC : DyadicCellDiamSmallFrozen.{0})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{0}) :
    CorrectedLemma11_13CanonicalStmt.{u} :=
  firstPass_11_13_canonical_of_perModelFrequency hAx
    (step8CertificateFrequencyPerModel_univ_of_zero
      (step8CertificateFrequencyPerModel_of_wholePlane
        (step8CertificateFrequencyWholePlane_of_seedInputs hAx0 hN2 hfr
          (firstPass_11_9_derivedInputsFieldAxioms (fun γ ξ α₀ Ω _ P hC hcirc => hAx0 Ω P γ ξ α₀ hC hcirc)
            (S11c.firstPass_11_10_derivedInputsSquarePositive hDC hFin
              fun γ ξ α₀ Ω _ P hC hcirc => hAx0 Ω P γ ξ α₀ hC hcirc)))))

end HarmonicBalls
