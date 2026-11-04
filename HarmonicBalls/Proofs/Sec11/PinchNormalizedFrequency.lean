import HarmonicBalls.Proofs.Sec11.PinchAEGermFrequency
import HarmonicBalls.Proofs.Sec11.PinchModConstTailVersions
import HarmonicBalls.Proofs.Sec8.AEStationaryFrequency

/-! # Normalized local data and pinch frequency

The Section 8 ergodic theorem used here is from Leonardo Bonanno's
LatticeProb formalization. Normalized metric locality and stationarity are
explicit hypotheses. -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

open Classical in
/-- Normalized internal metric locality and stationarity give a pinch block
frequency at every rate below the half-scale event probability. -/
theorem IsWholePlaneGFF.ae_internal_pinch_frequency_of_normalized_metric
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ)
    (hmetric : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
        (∀ᵐ ω ∂P, 0 < c ω) ∧
        (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)]
          (fun ω => G ω x y)) ∧
        (∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
          internalMetric (fun x y => c ω * D ω x y)
            (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y))
    (hstat : IdentDistrib
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0)
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
        ((2 : ℝ)⁻¹ ^ (n + 1)) 0 then (1 : ℝ) else 0) P P)
    (δ : ℝ) (hδ : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q V M ((2 : ℝ)⁻¹ ^ 1) 0}).toReal) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let F : Ω → ℕ → ℝ := fun ω n =>
    if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q V M
      ((2 : ℝ)⁻¹ ^ n) 0 then 1 else 0
  obtain ⟨X, hXm, hX, hs⟩ := exists_measurable_stationary_version P F hstat
  have hlocal := hGFF.exists_modConst_local_pinch_tail_versions P hμ hfull hD hconfig M hmetric
  have hlocal' : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → Measurable[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] (Y n)) ∧
      (∀ n, K ≤ n → X n =ᵐ[P] Y n) := by
    intro ε hε
    obtain ⟨K, Y, hYm, hY⟩ := hlocal ε hε
    exact ⟨K, Y, hYm, fun n hn => (hX n).trans (hY n hn)⟩
  have hs' : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω) := by
    let shift : (ℕ → ℝ) → (ℕ → ℝ) := fun x n => x (n + 1)
    have hm := congrArg (Measure.map shift) hs
    rw [Measure.map_map measurable_sequence_shift (Measurable.of_eval (fun n => hXm (n + 1))),
      Measure.map_map measurable_sequence_shift (Measurable.of_eval hXm)] at hm
    simpa [shift, Function.comp_def, Nat.add_assoc] using hm
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, le_of_lt hn⟩
  have hrmono : Antitone r := by
    intro a b hab
    dsimp [r]
    apply one_div_le_one_div_of_le (by positivity)
    simpa only [add_comm] using add_le_add_right (Nat.cast_le.mpr hab : (a : ℝ) ≤ b) (1 : ℝ)
  have hgmono : Monotone (fun ε => Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) := by
    intro a b hab
    exact fieldSigmaAlgebraModConst_mono α₀ hC (ball_subset_ball hab)
  exact ae_internal_pinch_block_density_of_ae_local_versions P μ D U T Q V M 0 X
    _ r hr hcofinal hrmono hgmono hlocal' (hGFF.origin_germ_trivial α₀)
    hXm hX hs' δ hδ

#print axioms IsWholePlaneGFF.ae_internal_pinch_frequency_of_normalized_metric

end HarmonicBalls
