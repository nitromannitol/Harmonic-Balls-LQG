import HarmonicBalls.Proofs.GFF.ContinuousCircleVersion
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! # Measurable continuous circle-average versions

The GFF and continuous circle-average construction used here are due to Leonardo Bonanno.
-/

noncomputable section
open MeasureTheory Filter Topology
namespace HarmonicBalls

/-- The parameter space of positive radii and complex centers. -/
abbrev CircleParameter := Set.Ioi (0 : ℝ) × ℂ

private instance : LocallyCompactSpace (Set.Ioi (0 : ℝ)) :=
  isOpen_Ioi.locallyCompactSpace

/-- Coordinatewise almost-everywhere measurability gives an almost-everywhere
measurable continuous-map-valued function. -/
theorem aemeasurable_circle_map_of_evaluations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {F : Ω → C(CircleParameter, ℝ)}
    (hF : ∀ p, AEMeasurable (fun ω => F ω p) P) : AEMeasurable F P := by
  have hn : NullMeasurable F P := by
    change @Measurable (NullMeasurableSpace Ω P) _ _ _ F
    apply ContinuousMap.measurable_iff_eval.mpr
    intro p
    exact (hF p).nullMeasurable.measurable'
  exact hn.aemeasurable

/-- Leonardo Bonanno's continuous circle-average version can be chosen jointly
measurable and normalized at the unit circle for every sample. -/
theorem IsWholePlaneGFF.exists_measurable_continuous_circle_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ F : Ω → C(CircleParameter, ℝ),
      Measurable F ∧ (∀ ω, F ω (⟨1, by simp⟩, 0) = 0) ∧
      ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2 := by
  obtain ⟨H, hHc, hHz, hHm, hHr⟩ := hh.exists_continuous_circle_version
  let K : Ω → C(CircleParameter, ℝ) := fun ω =>
    ⟨fun p => H p.1 p.2 ω,
      continuousOn_univ.mp ((hHc ω).comp
        (continuous_subtype_val.prodMap continuous_id).continuousOn
        (by intro p hp; exact ⟨p.1.2, Set.mem_univ _⟩))⟩
  have hKm : AEMeasurable K P := aemeasurable_circle_map_of_evaluations
    (fun p => hHm p.1 p.1.2 p.2)
  let L := hKm.mk K
  have hLm : Measurable L := hKm.measurable_mk
  have hLK : K =ᵐ[P] L := hKm.ae_eq_mk
  let q : CircleParameter := (⟨1, by simp⟩, 0)
  refine ⟨fun ω => L ω - ContinuousMap.const CircleParameter (L ω q), ?_, ?_, ?_⟩
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro p
    exact ((ContinuousMap.measurable_eval p).comp hLm).sub
      ((ContinuousMap.measurable_eval q).comp hLm)
  · intro ω
    change L ω q - L ω q = 0
    exact sub_self _
  · intro p
    filter_upwards [hLK, hHr p.1 p.1.2 p.2] with ω hk hr
    change L ω p - L ω q = hcirc ω p.1 p.2
    rw [← hk]
    change H p.1 p.2 ω - H 1 0 ω = _
    rw [hHz ω, sub_zero, hr]

/-- Evaluation of a continuous circle-average-valued map is jointly measurable. -/
theorem measurable_circle_evaluation :
    Measurable (fun q : C(CircleParameter, ℝ) × CircleParameter => q.1 q.2) :=
  continuous_eval.measurable

/-- A measurable continuous version can be evaluated at a measurable random parameter. -/
theorem measurable_circle_evaluation_random
    {Ω : Type*} [MeasurableSpace Ω] {F : Ω → C(CircleParameter, ℝ)}
    {p : Ω → CircleParameter} (hF : Measurable F) (hp : Measurable p) :
    Measurable (fun ω => F ω (p ω)) :=
  measurable_circle_evaluation.comp (hF.prodMk hp)

/-- Evaluation of a measurable continuous version is jointly measurable in the
sample and the circle parameter. -/
theorem measurable_circle_version_joint
    {Ω : Type*} [MeasurableSpace Ω] {F : Ω → C(CircleParameter, ℝ)}
    (hF : Measurable F) : Measurable (fun q : Ω × CircleParameter => F q.1 q.2) :=
  measurable_circle_evaluation.comp ((hF.comp measurable_fst).prodMk measurable_snd)

/-- A measurable positive random radius and center give a measurable evaluation. -/
theorem measurable_circle_evaluation_random_radius_center
    {Ω : Type*} [MeasurableSpace Ω] {F : Ω → C(CircleParameter, ℝ)}
    {r : Ω → Set.Ioi (0 : ℝ)} {z : Ω → ℂ}
    (hF : Measurable F) (hr : Measurable r) (hz : Measurable z) :
    Measurable (fun ω => F ω (r ω, z ω)) :=
  measurable_circle_evaluation_random hF (hr.prodMk hz)

/-- Continuous versions agreeing at every fixed circle agree as functions on one event. -/
theorem ae_continuous_circle_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F G : Ω → C(CircleParameter, ℝ)}
    (hF : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2)
    (hG : ∀ p : CircleParameter, (fun ω => G ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) :
    F =ᵐ[P] G := by
  let : Nonempty CircleParameter := ⟨⟨⟨1, by simp⟩, 0⟩⟩
  let d : ℕ → CircleParameter := TopologicalSpace.denseSeq CircleParameter
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq CircleParameter
  have he : ∀ᵐ ω ∂P, ∀ n, F ω (d n) = G ω (d n) := by
    apply ae_all_iff.mpr
    intro n
    exact (hF (d n)).trans (hG (d n)).symm
  filter_upwards [he] with ω hω
  apply ContinuousMap.ext
  intro p
  exact congrFun (hd.equalizer (F ω).continuous (G ω).continuous (funext hω)) p

#print axioms aemeasurable_circle_map_of_evaluations
#print axioms IsWholePlaneGFF.exists_measurable_continuous_circle_version
#print axioms measurable_circle_evaluation
#print axioms measurable_circle_evaluation_random
#print axioms measurable_circle_version_joint
#print axioms measurable_circle_evaluation_random_radius_center
#print axioms ae_continuous_circle_map_eq
