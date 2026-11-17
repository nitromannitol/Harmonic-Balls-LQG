import HarmonicBalls.Proofs.Potential.LQGClockUniformAnnularTail

/-! # Supremum estimates from increments

An expected supremum can be bounded by the initial value and the expected
sum of consecutive increments.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HarmonicBalls

/-- The expected supremum of a real sequence is bounded by its initial
absolute value and the sum of its expected absolute increments. -/
theorem lintegral_iSup_ofReal_abs_le_initial_add_increments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX : ∀ i, AEMeasurable (X i) μ) :
    (∫⁻ ω, ⨆ i : ℕ, ENNReal.ofReal |X i ω| ∂μ) ≤
      (∫⁻ ω, ENNReal.ofReal |X 0 ω| ∂μ) +
        ∑' i : ℕ, ∫⁻ ω, ENNReal.ofReal |X (i+1) ω - X i ω| ∂μ := by
  have hpoint (ω : Ω) (i : ℕ) :
      |X i ω| ≤ |X 0 ω| + ∑ j ∈ Finset.range i, |X (j+1) ω - X j ω| := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Finset.sum_range_succ]
      have h := abs_add_le (X i ω) (X (i+1) ω - X i ω)
      have heq : X i ω + (X (i+1) ω - X i ω) = X (i+1) ω := by ring
      rw [heq] at h
      linarith
  have hbound (ω : Ω) :
      (⨆ i : ℕ, ENNReal.ofReal |X i ω|) ≤
        ENNReal.ofReal |X 0 ω| + ∑' i : ℕ, ENNReal.ofReal |X (i+1) ω - X i ω| := by
    apply iSup_le
    intro i
    calc
      _ ≤ ENNReal.ofReal (|X 0 ω| + ∑ j ∈ Finset.range i, |X (j+1) ω - X j ω|) :=
        ENNReal.ofReal_le_ofReal (hpoint ω i)
      _ = ENNReal.ofReal |X 0 ω| + ∑ j ∈ Finset.range i, ENNReal.ofReal |X (j+1) ω - X j ω| := by
        rw [ENNReal.ofReal_add (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _),
          ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
      _ ≤ _ := add_le_add_right (ENNReal.sum_le_tsum _) _
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal |X 0 ω| +
        ∑' i : ℕ, ENNReal.ofReal |X (i+1) ω - X i ω|) ∂μ := lintegral_mono hbound
    _ = _ := by
      rw [lintegral_add_left' (hX 0).abs.ennreal_ofReal, lintegral_tsum]
      intro i
      exact ((hX (i+1)).sub (hX i)).abs.ennreal_ofReal

/-- Vanishing expected initial values and increment sums imply a vanishing
expected supremum. -/
theorem tendsto_lintegral_iSup_ofReal_abs_zero_of_increments
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (hX : ∀ n i, AEMeasurable (X n i) μ)
    (hinit : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal |X n 0 ω| ∂μ) atTop (𝓝 0))
    (hinc : Tendsto (fun n => ∑' i : ℕ,
      ∫⁻ ω, ENNReal.ofReal |X n (i+1) ω - X n i ω| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, ⨆ i : ℕ, ENNReal.ofReal |X n i ω| ∂μ) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => (∫⁻ ω, ENNReal.ofReal |X n 0 ω| ∂μ) +
      ∑' i : ℕ, ∫⁻ ω, ENNReal.ofReal |X n (i+1) ω - X n i ω| ∂μ) atTop (𝓝 0) := by
    simpa using hinit.add hinc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun n => lintegral_iSup_ofReal_abs_le_initial_add_increments μ (X n) (hX n))

end HarmonicBalls
