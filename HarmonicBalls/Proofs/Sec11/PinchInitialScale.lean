import HarmonicBalls.Proofs.Sec11.PinchFixedPointBirkhoff

/-! # From unit-scale positivity to fixed-point pinch frequency

The pointwise ergodic theorem used through the fixed-point bridge is due to
Leonardo Bonanno, `LatticeProb.Prob.Birkhoff`. Stationarity and germ
triviality remain explicit assumptions, as do the staged locality inputs.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter

/-- Full stationarity of a measurable real sequence identifies the laws at
scales zero and one and also the laws of its positive tails. -/
theorem stationary_sequence_first_law_and_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n))
    (hs : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω)) :
    P.map (X 1) = P.map (X 0) ∧
    P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω) := by
  have hm : Measurable (fun ω n => X n ω) := Measurable.of_eval hXm
  have hm' : Measurable (fun ω n => X (n + 1) ω) := Measurable.of_eval fun n => hXm (n + 1)
  constructor
  · have hh := congrArg (fun Q : Measure (ℕ → ℝ) => Q.map (fun x => x 0)) hs
    rw [Measure.map_map (measurable_pi_apply 0) hm',
      Measure.map_map (measurable_pi_apply 0) hm] at hh
    change P.map (X 1) = P.map (X 0) at hh
    exact hh
  · have hh := congrArg (fun Q : Measure (ℕ → ℝ) => Q.map (fun x n => x (n + 1))) hs
    rw [Measure.map_map measurable_sequence_shift hm', Measure.map_map measurable_sequence_shift hm] at hh
    change P.map (fun ω n => X ((n + 1) + 1) ω) =
      P.map (fun ω n => X (n + 1) ω) at hh
    simpa only [Nat.add_assoc] using hh

open Classical in
/-- Stationarity propagates positivity at unit scale to scale one half,
and the Birkhoff and germ bridge then gives positive fixed-point density. -/
theorem ae_positive_pinchBlockDensity_of_unitScale_stationary_lqg_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {U T Q' Q : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q' Q)
    (M : ℝ) (z : ℂ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hmloc : LQGMeasureLocality P γ α₀ hC hcirc)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (htrivial : ∀ A : Set Ω,
      (∀ ε, 0 < ε → MeasurableSet[fieldSigmaAlgebra α₀ hC (ball z ε)] A) →
      P A = 0 ∨ P A = 1)
    (hstat : P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + 1)) z then (1 : ℝ) else 0) =
      P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ n) z then (1 : ℝ) else 0))
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M 1 z}) :
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  obtain ⟨X, hXm, _, hX, _⟩ :=
    exists_germ_measurable_pinchIndicators hconfig M z hγ hγ₂ hα hgff hμ hD hmloc haxioms
  have hmap (k : ℕ) : P.map (fun ω n => X (n + k) ω) =
      P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + k)) z then (1 : ℝ) else 0) := by
    apply Measure.map_congr
    filter_upwards [hX] with ω hω
    funext n
    exact hω (n + k)
  have hsX : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω) := by
    calc
      _ = _ := hmap 1
      _ = _ := hstat
      _ = _ := by simpa only [add_zero] using (hmap 0).symm
  obtain ⟨hfirst, htail⟩ := stationary_sequence_first_law_and_tail P X hXm hsX
  have hstat' : P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + 2)) z then (1 : ℝ) else 0) =
      P.map (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
        ((2 : ℝ)⁻¹ ^ (n + 1)) z then (1 : ℝ) else 0) := by
    rwa [hmap 2, hmap 1] at htail
  have hE (n : ℕ) : P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
      ((2 : ℝ)⁻¹ ^ n) z} = P (X n ⁻¹' ({1} : Set ℝ)) := by
    apply measure_congr
    filter_upwards [hX] with ω hω
    simp only [mem_preimage, mem_singleton_iff, hω n]
    split_ifs <;> simp_all
  have hmeas : P (X 1 ⁻¹' ({1} : Set ℝ)) = P (X 0 ⁻¹' ({1} : Set ℝ)) := by
    have hh := congrArg (fun Q : Measure ℝ => Q ({1} : Set ℝ)) hfirst
    rwa [Measure.map_apply (hXm 1) (measurableSet_singleton 1),
      Measure.map_apply (hXm 0) (measurableSet_singleton 1)] at hh
  have hpos' : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Q M
      ((2 : ℝ)⁻¹ ^ 1) z} := by
    rw [hE 1, hmeas, ← hE 0]
    simpa only [pow_zero] using hpos
  exact ae_positive_pinchBlockDensity_of_stationary_lqg_event_birkhoff hconfig M z
    hγ hγ₂ hα hgff hμ hD hmloc haxioms htrivial hstat' hpos'

#print axioms stationary_sequence_first_law_and_tail
#print axioms ae_positive_pinchBlockDensity_of_unitScale_stationary_lqg_event

end HarmonicBalls
