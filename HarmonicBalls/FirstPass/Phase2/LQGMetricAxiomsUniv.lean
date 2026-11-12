import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Proofs.GFF.CoordinateModification

/-!
# The axioms of an LQG metric on probability spaces of every universe

`IsLQGMetric γ ξ 𝔇` (`Defs/LQGMetric.lean`) asks for the axioms I-IV (`SatisfiesLQGMetricAxioms`) whenever
`h = h^ℂ + f`, with `h^ℂ` a whole-plane GFF and `f` a random continuous function, on a probability space in `Type`.
The axioms only involve the joint law of `h^ℂ`, of its circle averages and of `f`, so they hold on probability spaces in
every universe (`IsLQGMetric.satisfiesLQGMetricAxioms_univ`).

Proof. A model `(Ω, P, h^ℂ, h_·(·), f)` with `Ω : Type u` is represented on a sample space in `Type`: the range of
`X : ω ↦ (h^ℂ(ω), h_·(·)(ω), f(ω))` (`RangeSpace`), with the σ-algebra of the sets whose preimage under `X` is
`P`-null-measurable and the push-forward of the completion of `P` (`rangeMeasure`). Because the completion is
complete, an almost sure statement holds on the range if and only if it holds on `Ω` (`ae_rangeMeasure_iff`), and a
function on the range is measurable as soon as its composite with `X` is null-measurable (`measurable_of_nullMeasurable`).
The range model is again a whole-plane GFF plus a continuous function (`isWholePlaneGFF_rangeMeasure`); the axioms of
`𝔇` on the range pull back to `Ω`, the locality σ-algebra `σ(h|_U)` of `Ω` being the comap of that of the range.
-/

universe u

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LQGMetricUniv

/-- A sample point of the canonical space: the pairings of a field, its circle averages and a function on `ℂ`. -/
structure SamplePoint : Type where
  /-- The pairings `φ ↦ (h^ℂ, φ)`. -/
  pairing : (ℂ → ℝ) → ℝ
  /-- The circle averages `(r, z) ↦ h^ℂ_r(z)`. -/
  circle : ℝ → ℂ → ℝ
  /-- The added function `f`. -/
  shift : ℂ → ℝ

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The range of `X : Ω → SamplePoint`, a type in `Type`. The measure `P` only enters through the σ-algebra. -/
def RangeSpace (_P : Measure Ω) (X : Ω → SamplePoint) : Type := {y : SamplePoint // ∃ ω, X ω = y}

/-- The map of `Ω` to the range of `X`, on the completion `NullMeasurableSpace Ω P`. -/
def toRange (P : Measure Ω) (X : Ω → SamplePoint) : NullMeasurableSpace Ω P → RangeSpace P X :=
  fun ω => ⟨X ω, ω, rfl⟩

/-- The σ-algebra of the range: the sets whose preimage is `P`-null-measurable. -/
instance (P : Measure Ω) (X : Ω → SamplePoint) : MeasurableSpace (RangeSpace P X) :=
  MeasurableSpace.map (toRange P X) inferInstance

/-- The law of the model on the range: the push-forward of the completion of `P`. -/
noncomputable def rangeMeasure (P : Measure Ω) (X : Ω → SamplePoint) : Measure (RangeSpace P X) :=
  P.completion.map (toRange P X)

variable {P : Measure Ω} {X : Ω → SamplePoint}

theorem measurable_toRange : Measurable (toRange P X) := fun _ hs => hs

/-- A function on the range whose composite with `X` is null-measurable is measurable. -/
theorem measurable_of_nullMeasurable {β : Type*} [MeasurableSpace β] {g : RangeSpace P X → β}
    (hg : NullMeasurable (fun ω : Ω => g (toRange P X ω)) P) : Measurable g := fun _ hs => hg hs

/-- Almost sure statements on the range are almost sure statements on `Ω`. -/
theorem ae_rangeMeasure_iff {p : RangeSpace P X → Prop} :
    (∀ᵐ y ∂rangeMeasure P X, p y) ↔ ∀ᵐ ω ∂P, p (toRange P X ω) := by
  constructor
  · intro h
    exact ae_of_ae_map measurable_toRange.aemeasurable h
  · intro h
    have hnull : P {ω | ¬p (toRange P X ω)} = 0 := ae_iff.1 h
    have hms : MeasurableSet {y | p y} := by
      change NullMeasurableSet {ω : Ω | p (toRange P X ω)} P
      have h1 : NullMeasurableSet {ω : Ω | ¬p (toRange P X ω)} P := NullMeasurableSet.of_null hnull
      convert h1.compl using 1
      ext ω
      simp
    exact (ae_map_iff measurable_toRange.aemeasurable hms).2 h

/-- The identity map from the completion `NullMeasurableSpace Ω P` to `Ω`. -/
def fromNull (P : Measure Ω) : NullMeasurableSpace Ω P → Ω := fun ω => ω

/-- The identity is measure preserving from the completion of `P` to `P`. -/
theorem measurePreserving_fromNull : MeasurePreserving (fromNull P) P.completion P := by
  have hm : Measurable (fromNull P) := fun _ hs => hs.nullMeasurableSet
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs]
  rfl

/-- The sample point of a model `(h^ℂ, h_·(·), f)` at `ω`. -/
def samplePoint (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (f : Ω → ℂ → ℝ) (ω : Ω) : SamplePoint :=
  ⟨hC ω, hcirc ω, f ω⟩

/-- The range of a whole-plane GFF model is a whole-plane GFF under `rangeMeasure`. -/
theorem isWholePlaneGFF_rangeMeasure {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (f : Ω → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc) :
    IsWholePlaneGFF (rangeMeasure P (samplePoint hC hcirc f)) (fun y => y.1.pairing) (fun y => y.1.circle) := by
  -- the model on the completion
  have hGc : IsWholePlaneGFF P.completion (hC ∘ fromNull P) (hcirc ∘ fromNull P) :=
    hG.comp_measurePreserving measurePreserving_fromNull
  have hmeasO : ∀ o : GFFObservable, o.IsAdmissible →
      Measurable fun y : RangeSpace P (samplePoint hC hcirc f) => o.eval y.1.pairing y.1.circle := by
    intro o ho
    refine measurable_of_nullMeasurable ?_
    cases o with
    | pairing φ => exact (hG.measurable_pairing φ ho).nullMeasurable
    | circle r z => exact (hG.measurable_circle r z ho).nullMeasurable
  have hint : ∀ g : RangeSpace P (samplePoint hC hcirc f) → ℝ, Measurable g →
      ∫ y, g y ∂rangeMeasure P (samplePoint hC hcirc f) =
        ∫ ω, g (toRange P (samplePoint hC hcirc f) ω) ∂P.completion := fun g hg =>
    integral_map measurable_toRange.aemeasurable hg.aestronglyMeasurable
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ hφ
    exact hmeasO (.pairing φ) hφ
  · intro r z hr
    exact hmeasO (.circle r z) hr
  · refine ⟨fun I => ?_⟩
    have hI : Measurable (fun y : RangeSpace P (samplePoint hC hcirc f) =>
        I.restrict fun o : GFFObservable.Admissible => o.1.eval y.1.pairing y.1.circle) :=
      measurable_pi_iff.mpr fun i => hmeasO i.1.1 i.1.2
    refine ⟨hI.aemeasurable, ?_⟩
    have hlaw : (rangeMeasure P (samplePoint hC hcirc f)).map (fun y : RangeSpace P (samplePoint hC hcirc f) =>
        I.restrict fun o : GFFObservable.Admissible => o.1.eval y.1.pairing y.1.circle) =
        P.completion.map (fun ω : NullMeasurableSpace Ω P =>
          I.restrict fun o : GFFObservable.Admissible => o.1.eval ((hC ∘ fromNull P) ω) ((hcirc ∘ fromNull P) ω)) := by
      rw [rangeMeasure, Measure.map_map hI measurable_toRange]
      rfl
    rw [hlaw]
    exact (hGc.isGaussianProcess.hasGaussianLaw I).isGaussian_map
  · intro o ho
    rw [hint _ (hmeasO o ho)]
    exact hGc.integral_eq_zero o ho
  · intro o o' ho ho'
    rw [rangeMeasure, covariance_map_fun (hmeasO o ho).aestronglyMeasurable
      (hmeasO o' ho').aestronglyMeasurable measurable_toRange.aemeasurable]
    exact hGc.covariance_eq o o' ho ho'
  · exact ae_rangeMeasure_iff.2 hG.ae_continuousOn_circle

end LQGMetricUniv

open LQGMetricUniv in
/-- **The axioms of an LQG metric hold on probability spaces of every universe.** For a γ-LQG metric `𝔇` with Weyl
exponent `ξ` (`IsLQGMetric`, whose axioms are required on probability spaces in `Type`), a whole-plane GFF `h^ℂ` on a
probability space `Ω : Type u` and a random continuous function `f` (measurable in `ω` at each point), `D_{h^ℂ + f}`
satisfies the axioms I-IV. -/
theorem IsLQGMetric.satisfiesLQGMetricAxioms_univ {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hM : IsLQGMetric γ ξ 𝔇) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (f : Ω → ℂ → ℝ) (hG : IsWholePlaneGFF P hC hcirc)
    (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ x, Measurable fun ω => f ω x) :
    SatisfiesLQGMetricAxioms P γ ξ 𝔇 fun ω => addFunPairing (hC ω) (f ω) := by
  let X : Ω → SamplePoint := samplePoint hC hcirc f
  have hG0 : IsWholePlaneGFF (rangeMeasure P X) (fun y => y.1.pairing) (fun y => y.1.circle) :=
    isWholePlaneGFF_rangeMeasure f hG
  have hcont : ∀ y : RangeSpace P X, Continuous y.1.shift := by
    rintro ⟨y, ω, rfl⟩
    exact hf ω
  have hmeas : ∀ x, Measurable fun y : RangeSpace P X => y.1.shift x := fun x =>
    measurable_of_nullMeasurable ((hfm x).nullMeasurable)
  have hA := hM.satisfiesLQGMetricAxioms (RangeSpace P X) (rangeMeasure P X) (fun y => y.1.pairing)
    (fun y => y.1.circle) (fun y => y.1.shift) hG0 hcont hmeas
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ae_rangeMeasure_iff.1 hA.ae_isEuclideanLengthMetric
  · intro U hU
    obtain ⟨G, hGm, hGae⟩ := hA.locality U hU
    refine ⟨fun ω => G (toRange P X ω), fun z w => ?_, ae_rangeMeasure_iff.1 hGae⟩
    have hcomap : pairingSigmaAlgebra (fun ω => addFunPairing (hC ω) (f ω)) U =
        MeasurableSpace.comap (toRange P X)
          (pairingSigmaAlgebra (fun y : RangeSpace P X => addFunPairing y.1.pairing y.1.shift) U) := by
      simp only [pairingSigmaAlgebra, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
      rfl
    rw [hcomap]
    exact (hGm z w).comp (comap_measurable _)
  · exact ae_rangeMeasure_iff.1 hA.ae_weylScaling
  · intro r hr z
    exact ae_rangeMeasure_iff.1 (hA.coordChange r hr z)

end HarmonicBalls
