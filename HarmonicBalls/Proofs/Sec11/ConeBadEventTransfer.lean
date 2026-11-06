import HarmonicBalls.Proofs.Sec8.WholePlaneSmoothShift

/-!
# Positivity of cone events transfers along smooth shifts (Lemma 11.8, Step 1)

Lemma 11.8 (`ConeBadEventProbabilityStmt`, lemma:positive-probability) proves its base case by adding a bump
function to the whole-plane GFF and using mutual absolute continuity of the pairing laws. This file proves the
transfer step. A cone event that holds on a set of positive probability for the shifted field holds with positive
probability for the original field.

The smooth-shift law `IsWholePlaneGFF.local_smooth_shift_pairing_law` (module
`HarmonicBalls.Proofs.Sec8.WholePlaneSmoothShift`, commit 854fb81, by h3) rests on Leonardo Bonanno's Gaussian
Cameron-Martin theorem (`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`). This file uses it, so the credit is
Leonardo Bonanno's.

Not established here: the a.s. representation of the cone events by the local pairing processes (the LQG measure is
a function of the circle averages, not of the pairings), the pointwise bump inclusion, and the uniform probability bound
for all centres, scales and exponents. These remain explicit hypotheses of `cone_event_pos_of_smooth_shift`.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal ContDiff

universe u

/-- Positivity transfers along an absolutely continuous image: if `P.map X' ≪ P.map X` and `X'` puts positive
probability on a measurable set `B`, then `X` does too. -/
theorem measure_preimage_pos_of_map_absolutelyContinuous
    {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] {P : Measure Ω} {X X' : Ω → Y}
    (hX : Measurable X) (hX' : Measurable X') (hAC : P.map X' ≪ P.map X)
    {B : Set Y} (hB : MeasurableSet B) (hpos : 0 < P (X' ⁻¹' B)) :
    0 < P (X ⁻¹' B) := by
  by_contra h
  have h0 : P (X ⁻¹' B) = 0 := le_antisymm (not_lt.mp h) zero_le
  have h1 : P.map X B = 0 := by rw [Measure.map_apply hX hB]; exact h0
  have h2 : P.map X' B = 0 := hAC h1
  rw [Measure.map_apply hX' hB] at h2
  exact hpos.ne' h2

/-- Lemma 11.8, Step 1, transfer form. Let `hC` be the pairings of a whole-plane GFF and let `g` be smooth on
`ball c R` with `r < R`. Let `E` be an event of the original field and `E'` an event of the shifted field `h + g`,
each represented almost surely by the local pairing process of `hC` (with insertion `k`) and by a measurable set `B`
of processes: `X w = (φ ↦ hC w φ + k φ)` and `X' w = (φ ↦ hC w φ + ∫ φ g + k φ)`. If the shifted event contains a set
`G` of positive probability, the original event has positive probability. -/
theorem cone_event_pos_of_smooth_shift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {g : ℂ → ℝ} (hg : ContDiffOn ℝ ∞ g (ball c R))
    (k : Section6.LocalTest (ball c r) → ℝ)
    {B : Set (Section6.LocalTest (ball c r) → ℝ)} (hB : MeasurableSet B)
    (E Ep : Ω → Prop)
    (hE : ∀ᶠ w in ae P, (E w ↔
      (fun φ : Section6.LocalTest (ball c r) => hC w φ.1.1 + k φ) ∈ B))
    (hEp : ∀ᶠ w in ae P, (Ep w ↔
      (fun φ : Section6.LocalTest (ball c r) => hC w φ.1.1 + (∫ x, φ.1.1 x * g x) + k φ) ∈ B))
    (G : Set Ω) (hGpos : 0 < P G) (hG : ∀ᶠ w in ae P, (w ∈ G → Ep w)) :
    0 < P {w | E w} := by
  have hAC := hh.local_smooth_shift_pairing_law hr hrR hg k
  have hX : Measurable (fun w (φ : Section6.LocalTest (ball c r)) => hC w φ.1.1 + k φ) :=
    measurable_pi_iff.mpr fun φ =>
      ((hh.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).add_const _)
  have hX' : Measurable
      (fun w (φ : Section6.LocalTest (ball c r)) => hC w φ.1.1 + (∫ x, φ.1.1 x * g x) + k φ) :=
    measurable_pi_iff.mpr fun φ =>
      (((hh.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).add_const _).add_const _)
  set X := fun w (φ : Section6.LocalTest (ball c r)) => hC w φ.1.1 + k φ with hXdef
  set X' := fun w (φ : Section6.LocalTest (ball c r)) => hC w φ.1.1 + (∫ x, φ.1.1 x * g x) + k φ
    with hX'def
  have hsub : G ≤ᵐ[P] (X' ⁻¹' B) := by
    filter_upwards [hG, hEp] with w hwG hwE
    exact fun hGw => hwE.1 (hwG hGw)
  have hpos' : 0 < P (X' ⁻¹' B) := lt_of_lt_of_le hGpos (measure_mono_ae hsub)
  have hXpos : 0 < P (X ⁻¹' B) :=
    measure_preimage_pos_of_map_absolutelyContinuous hX hX' hAC hB hpos'
  have hEq : {w | E w} =ᵐ[P] (X ⁻¹' B) := by
    filter_upwards [hE] with w hw
    exact propext hw
  rw [measure_congr hEq]
  exact hXpos

end HarmonicBalls

#print axioms HarmonicBalls.cone_event_pos_of_smooth_shift
#print axioms HarmonicBalls.measure_preimage_pos_of_map_absolutelyContinuous
