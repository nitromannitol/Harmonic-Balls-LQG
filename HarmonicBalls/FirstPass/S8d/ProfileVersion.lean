import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.GFF.MeasurableContinuousCircleVersion

/-! # FIRST-PASS helper (fp-S8d, owner n4): universe-free continuous circle-average version

`IsWholePlaneGFF.exists_measurable_continuous_circle_version` (Proofs/GFF/MeasurableContinuousCircleVersion.lean:34)
is stated for `Ω : Type`, although its proof uses only universe-free ingredients. This file states and proves the
`Ω : Type*` version. The a.s. continuity of the circle-average process (`IsWholePlaneGFF.ae_continuousOn_circle`)
gives a measurable full-measure set `Nᶜ` on which the process is continuous; the version is the process on `Nᶜ`
(and `0` on `N`), normalized at the unit circle as in the Type proof. Measurability uses
`aemeasurable_circle_map_of_evaluations` (universe-free).
-/

open MeasureTheory Filter Set Metric
open scoped Classical

namespace HarmonicBalls

theorem IsWholePlaneGFF.exists_measurable_continuous_circle_version_univ
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ F : Ω → C(CircleParameter, ℝ),
      Measurable F ∧ (∀ ω, F ω (⟨1, by simp⟩, 0) = 0) ∧
      ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2 := by
  have hae := hh.ae_continuousOn_circle
  rw [ae_iff] at hae
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hae
  have hcont : ∀ ω, ω ∉ N → ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) := by
    intro ω hω
    by_contra h
    exact hω (hsub h)
  have hKc : ∀ ω, Continuous fun p : CircleParameter => if ω ∈ Nᶜ then hcirc ω p.1.1 p.2 else 0 := by
    intro ω
    by_cases hω : ω ∈ Nᶜ
    · simp only [hω, ite_true]
      have h1 : ContinuousOn ((fun p : ℝ × ℂ => hcirc ω p.1 p.2) ∘ (fun p : CircleParameter => (p.1.1, p.2))) univ :=
        ContinuousOn.comp (hcont ω hω) (Continuous.continuousOn (continuous_subtype_val.prodMap continuous_id))
          (fun p _ => ⟨p.1.2, Set.mem_univ _⟩)
      exact continuousOn_univ.mp h1
    · simp only [hω, ite_false]
      exact continuous_const
  let K : Ω → C(CircleParameter, ℝ) := fun ω =>
    ⟨fun p => if ω ∈ Nᶜ then hcirc ω p.1.1 p.2 else 0, hKc ω⟩
  have hKev : ∀ p : CircleParameter, AEMeasurable (fun ω => K ω p) P := by
    intro p
    have hm : Measurable fun ω => K ω p := by
      show Measurable fun ω => if ω ∈ Nᶜ then hcirc ω p.1.1 p.2 else 0
      exact Measurable.ite hNm.compl (hh.measurable_circle _ _ p.1.2) measurable_const
    exact hm.aemeasurable
  have hKm : AEMeasurable K P := aemeasurable_circle_map_of_evaluations hKev
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
    have h0 : ∀ᵐ ω ∂P, hcirc ω 1 0 = 0 := hh.ae_circleAverage_one_zero
    have hN : ∀ᵐ ω ∂P, ω ∉ N := by
      rw [ae_iff]
      simpa using hN0
    filter_upwards [hLK, hN, h0] with ω hk hω h1
    have hω' : ω ∈ Nᶜ := hω
    have hp : L ω p = hcirc ω p.1.1 p.2 := by
      rw [← hk]
      show (if ω ∈ Nᶜ then hcirc ω p.1.1 p.2 else 0) = _
      simp only [hω', ↓reduceIte]
    have hq : L ω q = 0 := by
      rw [← hk]
      show (if ω ∈ Nᶜ then hcirc ω q.1.1 q.2 else 0) = 0
      simp only [hω', ↓reduceIte]
      exact h1
    change L ω p - L ω q = hcirc ω p.1 p.2
    rw [hp, hq, sub_zero]

#print axioms IsWholePlaneGFF.exists_measurable_continuous_circle_version_univ

end HarmonicBalls
