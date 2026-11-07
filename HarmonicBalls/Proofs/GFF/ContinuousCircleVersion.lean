import HarmonicBalls.Proofs.GFF.BonannoNormalizedVersion
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm

/-! # Continuous versions of circle averages

The distribution-valued GFF and the continuous circle-average construction used
here are due to Leonardo Bonanno. Fixed-coordinate agreement is distinguished
from agreement on one event at every coordinate. -/

noncomputable section
open MeasureTheory Filter Topology
namespace HarmonicBalls

/-- Leonardo Bonanno's continuous circle-average version, normalized at the unit
circle for every sample, and equal to the raw process at each fixed coordinate. -/
theorem IsWholePlaneGFF.exists_continuous_circle_version
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ H : ℝ → ℂ → Ω → ℝ,
      (∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Set.Ioi 0 ×ˢ Set.univ)) ∧
      (∀ ω, H 1 0 ω = 0) ∧
      (∀ r, 0 < r → ∀ z, AEMeasurable (H r z) P) ∧
      (∀ r, 0 < r → ∀ z, H r z =ᵐ[P] fun ω => hcirc ω r z) := by
  obtain ⟨K, hKcont, hK⟩ := LQGMetric.CircleAvg.exists_continuous_version_circleAvg
    hh.reconstructedGFF_normalized.1
  have hKraw : ∀ r, 0 < r → ∀ z, K r z =ᵐ[P] fun ω => hcirc ω r z := by
    intro r hr z
    filter_upwards [hK r hr z, hh.reconstructedGFF_normalized.2,
      hh.ae_circleAvg_reconstructedGFF hr z] with ω hk hz hc
    rw [hk, hz, sub_zero, hc]
  have hzero : ∀ᵐ ω ∂P, K 1 0 ω = 0 := by
    filter_upwards [hKraw 1 one_pos 0, hh.ae_circleAverage_one_zero] with ω h₁ h₂
    rw [h₁, h₂]
  refine ⟨fun r z ω => K r z ω - K 1 0 ω, ?_, ?_, ?_, ?_⟩
  · intro ω
    exact (hKcont ω).sub continuousOn_const
  · intro ω
    exact sub_self _
  · intro r hr z
    apply (hh.measurable_circle r z hr).aemeasurable.congr
    filter_upwards [hKraw r hr z, hzero] with ω he hz
    simp only [hz, sub_zero, he]
  · intro r hr z
    filter_upwards [hKraw r hr z, hzero] with ω he hz
    simp only [hz, sub_zero, he]

/-- Coordinatewise versions agree on one event on any countable family. -/
theorem ae_circle_version_eq_on_countable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {H : ℝ → ℂ → Ω → ℝ}
    (hH : ∀ r, 0 < r → ∀ z, H r z =ᵐ[P] fun ω => hcirc ω r z)
    (s : Set (Set.Ioi (0 : ℝ) × ℂ)) (hs : s.Countable) :
    ∀ᵐ ω ∂P, ∀ p ∈ s, H p.1 p.2 ω = hcirc ω p.1 p.2 := by
  let : Countable s := hs.to_subtype
  have h : ∀ᵐ ω ∂P, ∀ p : s, H p.1.1 p.1.2 ω = hcirc ω p.1.1 p.1.2 :=
    ae_all_iff.mpr fun p => hH p.1.1 p.1.1.2 p.1.2
  filter_upwards [h] with ω hω p hp
  exact hω ⟨p, hp⟩

/-- Two continuous coordinatewise versions are indistinguishable on all
positive radii and centers. -/
theorem ae_continuous_circle_versions_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {H K : ℝ → ℂ → Ω → ℝ}
    (hHc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Set.Ioi 0 ×ˢ Set.univ))
    (hKc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => K p.1 p.2 ω) (Set.Ioi 0 ×ˢ Set.univ))
    (hH : ∀ r, 0 < r → ∀ z, H r z =ᵐ[P] fun ω => hcirc ω r z)
    (hK : ∀ r, 0 < r → ∀ z, K r z =ᵐ[P] fun ω => hcirc ω r z) :
    ∀ᵐ ω ∂P, ∀ r, 0 < r → ∀ z, H r z ω = K r z ω := by
  let S := Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ)
  let : Nonempty S := ⟨⟨(1, 0), by simp [S]⟩⟩
  let d : ℕ → S := TopologicalSpace.denseSeq S
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq S
  have he : ∀ᵐ ω ∂P, ∀ n, H (d n).1.1 (d n).1.2 ω = K (d n).1.1 (d n).1.2 ω := by
    apply ae_all_iff.mpr
    intro n
    exact (hH _ (d n).2.1 _).trans (hK _ (d n).2.1 _).symm
  filter_upwards [he] with ω hω r hr z
  have hcH : Continuous (fun p : S => H p.1.1 p.1.2 ω) := (hHc ω).domRestrict
  have hcK : Continuous (fun p : S => K p.1.1 p.1.2 ω) := (hKc ω).domRestrict
  have eqfun : (fun p : S => H p.1.1 p.1.2 ω) = fun p : S => K p.1.1 p.1.2 ω :=
    hd.equalizer hcH hcK (funext hω)
  exact congrFun eqfun ⟨(r, z), ⟨hr, Set.mem_univ _⟩⟩

#print axioms IsWholePlaneGFF.exists_continuous_circle_version
#print axioms ae_circle_version_eq_on_countable
#print axioms ae_continuous_circle_versions_eq
