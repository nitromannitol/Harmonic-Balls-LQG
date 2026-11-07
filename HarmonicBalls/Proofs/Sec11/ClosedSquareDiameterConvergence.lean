import HarmonicBalls.Proofs.Sec11.DyadicClosedSquareTail
import HarmonicBalls.Proofs.Sec11.MassDiameterDyadicAsymptotic

/-! # Convergence of dyadic internal diameters

The uniform closed-square tail estimate is an explicit hypothesis. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- Unit-circle normalization removes the circle-average factor from any
diameter-tail event, simultaneously for arbitrary thresholds and observables. -/
theorem IsWholePlaneGFF.measure_tail_with_unit_circle_factor
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (ξ : ℝ) (b : ℝ≥0∞)
    (X : Ω → ℝ≥0∞) :
    P {ω | b * ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) < X ω} =
      P {ω | b < X ω} := by
  apply measure_congr
  filter_upwards [h.ae_circleAverage_one_zero] with ω hω
  simp [hω]

/-- A closed-square diameter tail with exponent greater than two implies
that all enlarged dyadic-tile diameters are simultaneously small in
probability. The random circle-average normalization is handled jointly. -/
theorem IsWholePlaneGFF.tendsto_intermediate_diameters_of_closed_square_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (D : Ω → ℂ → ℂ → ℝ)
    (a : ℂ) (L : ℝ) (hL : 0 < L) (c s ξ p : ℝ)
    (hs : 0 < s) (hp : 2 < p) (e : ℝ → ℝ)
    (he : Tendsto e (𝓝[>] 0) (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      P {ω | ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) *
          ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) <
        ⨆ x ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
          ⨆ y ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
            internalMetric (D ω) (complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i) x y} ≤
      ENNReal.ofReal ((3 * L / (2 * (2 : ℝ) ^ n)) ^
        (p + e (3 * L / (2 * (2 : ℝ) ^ n)))))
    (d : ℝ) (hd : 0 < d) :
    Tendsto (fun n => P {ω | ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      dyadicIntermediateInternalDiameter D a L n i ω < ENNReal.ofReal d}ᶜ)
      atTop (𝓝 0) := by
  let p' : ℝ := (2 + p) / 2
  have hp' : 2 < p' := by dsimp [p']; linarith
  have hpp : p' < p := by dsimp [p']; linarith
  obtain ⟨hsmall, htail⟩ := dyadicIntermediateInternalDiameter_thresholds_of_closed_square
    P D a L hL c s ξ hs hcirc p p' hp' hpp e he hbound
  let b : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s)
  let b' : ℕ → ℝ≥0∞ := fun n => if b n < ENNReal.ofReal d then b n else 0
  have hd' : 0 < ENNReal.ofReal d := ENNReal.ofReal_pos.mpr hd
  have hb' : ∀ n, b' n < ENNReal.ofReal d := by
    intro n
    by_cases hn : b n < ENNReal.ofReal d <;> simp [b', hn, hd']
  apply h.tendsto_all_tiles_failure_of_pinned_circle_factor ξ
    (fun n => Fin (2 ^ n) × Fin (2 ^ n))
    (dyadicIntermediateInternalDiameter D a L)
    b' (ENNReal.ofReal d) hb' ?_
  · apply tendsto_dyadic_square_failure_sum_of_power_error P _ p' hp' (fun _ => 0)
      tendsto_const_nhds
    filter_upwards [hsmall d hd, htail] with n hn ht
    simpa [b', b, hn] using ht

#print axioms IsWholePlaneGFF.tendsto_intermediate_diameters_of_closed_square_tail
#print axioms IsWholePlaneGFF.measure_tail_with_unit_circle_factor
end HarmonicBalls
