import HarmonicBalls.Proofs.GFF.MeasurableContinuousCircleVersion
import HarmonicBalls.Defs.LQG

/-! # Common continuous circle version and LQG approximations

The GFF and continuous circle-average construction used here are due to Leonardo Bonanno.
-/

noncomputable section
open MeasureTheory Filter Topology
namespace HarmonicBalls

/-- Extend a continuous positive-radius profile arbitrarily to nonpositive radii. -/
def circleProfile (F : C(CircleParameter, ℝ)) (r : ℝ) (z : ℂ) : ℝ :=
  if hr : 0 < r then F (⟨r, hr⟩, z) else 0

/-- Fixed-circle agreement and raw sample continuity imply agreement at every
positive circle on one common event. -/
theorem ae_circle_map_eq_raw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ))
    (hF : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) :
    ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2 := by
  let : Nonempty CircleParameter := ⟨⟨⟨1, by simp⟩, 0⟩⟩
  let d : ℕ → CircleParameter := TopologicalSpace.denseSeq CircleParameter
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq CircleParameter
  have he : ∀ᵐ ω ∂P, ∀ n, F ω (d n) = hcirc ω (d n).1 (d n).2 :=
    ae_all_iff.mpr fun n => hF (d n)
  filter_upwards [he, hcont] with ω hω hc
  have hraw : Continuous (fun p : CircleParameter => hcirc ω p.1 p.2) :=
    continuousOn_univ.mp (hc.comp
      (continuous_subtype_val.prodMap continuous_id).continuousOn
      (by intro p hp; exact ⟨p.1.2, Set.mem_univ _⟩))
  exact fun p => congrFun (hd.equalizer (F ω).continuous hraw (funext hω)) p

/-- A whole-plane GFF and any of its coordinatewise continuous versions agree
on every positive circle simultaneously. -/
theorem IsWholePlaneGFF.ae_circle_map_eq_raw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {F : Ω → C(CircleParameter, ℝ)} (hh : IsWholePlaneGFF P hC hcirc)
    (hF : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) :
    ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2 :=
  HarmonicBalls.ae_circle_map_eq_raw hh.ae_continuousOn_circle hF

/-- The approximation measures agree for all positive scales and parameters on
one common event. -/
theorem ae_lqgApprox_circleProfile_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (h : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2) :
    ∀ᵐ ω ∂P, ∀ γ α r, 0 < r →
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) r =
        lqgApprox γ (fieldCircleAverage α (circleProfile (F ω))) r := by
  filter_upwards [h] with ω hω γ α r hr
  unfold lqgApprox
  congr 1
  funext z
  simp only [fieldCircleAverage, circleProfile, dite_eq_left hr, hω (⟨r, hr⟩, z)]

/-- The LQG measure predicate is invariant under this common continuous version. -/
theorem isLQGMeasureOfField_circleProfile_iff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (h : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2)
    (γ α : ℝ) (μ : Ω → Measure ℂ) :
    IsLQGMeasureOfField P γ α hcirc μ ↔
      IsLQGMeasureOfField P γ α (fun ω => circleProfile (F ω)) μ := by
  have he := ae_lqgApprox_circleProfile_eq h
  constructor <;> intro hm
  all_goals
    filter_upwards [he, hm] with ω hω hlim
    refine ⟨hlim.isLocallyFiniteMeasure, ?_⟩
    intro f hf hfc
    have hs : (fun k : ℕ => lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k)) =
        (fun k : ℕ => lqgApprox γ (fieldCircleAverage α (circleProfile (F ω))) (dyadicScale k)) :=
      funext fun k => hω γ α _ (dyadicScale_pos k)
    have hi := congrArg (fun g : ℕ → Measure ℂ => fun k => ∫ z, f z ∂(g k)) hs
    first | rw [← hi]; exact hlim.tendsto_integral f hf hfc
          | rw [hi]; exact hlim.tendsto_integral f hf hfc

/-- Dependent measurable positive-radius and center evaluations of the raw
process are almost-everywhere measurable. -/
theorem aemeasurable_raw_circle_random
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (hF : Measurable F)
    (h : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2)
    {r : Ω → Set.Ioi (0 : ℝ)} {z : Ω → ℂ} (hr : Measurable r) (hz : Measurable z) :
    AEMeasurable (fun ω => hcirc ω (r ω) (z ω)) P := by
  apply (measurable_circle_evaluation_random_radius_center hF hr hz).aemeasurable.congr
  filter_upwards [h] with ω hω
  exact hω (r ω, z ω)

#print axioms IsWholePlaneGFF.ae_circle_map_eq_raw
#print axioms ae_circle_map_eq_raw
#print axioms ae_lqgApprox_circleProfile_eq
#print axioms isLQGMeasureOfField_circleProfile_iff
#print axioms aemeasurable_raw_circle_random
end HarmonicBalls
