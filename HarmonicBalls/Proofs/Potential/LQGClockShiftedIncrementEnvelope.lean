import HarmonicBalls.Proofs.Potential.LQGClockSupremumIncrement

/-! # Shifted increment envelopes

A summable envelope for shifted increments controls expected suprema.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A summable envelope indexed by the initial scale plus the increment index,
together with vanishing initial values, yields vanishing expected suprema. -/
theorem tendsto_lintegral_iSup_ofReal_abs_zero_of_shifted_envelope
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → ℕ → Ω → ℝ)
    (hX : ∀ n i, AEMeasurable (X n i) μ) (B : ℕ → ℝ≥0∞)
    (hB : (∑' j, B j) ≠ ∞)
    (hinit : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal |X n 0 ω| ∂μ) atTop (𝓝 0))
    (hinc : ∀ n i, (∫⁻ ω, ENNReal.ofReal |X n (i+1) ω - X n i ω| ∂μ) ≤ B (n+i)) :
    Tendsto (fun n => ∫⁻ ω, ⨆ i : ℕ, ENNReal.ofReal |X n i ω| ∂μ) atTop (𝓝 0) := by
  apply tendsto_lintegral_iSup_ofReal_abs_zero_of_increments μ X hX hinit
  have htail := (ENNReal.tendsto_tsum_compl_atTop_zero hB).comp tendsto_finset_range
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
    (fun _ => bot_le) ?_
  intro n
  calc
    _ ≤ ∑' i : ℕ, B (n+i) := ENNReal.tsum_le_tsum (hinc n)
    _ ≤ ∑' j : {j : ℕ // j ∉ Finset.range n}, B j.1 := by
      let f : ℕ → {j : ℕ // j ∉ Finset.range n} :=
        fun i => ⟨n+i, by simp⟩
      have hf : Function.Injective f := by
        intro a b h
        exact Nat.add_left_cancel (congrArg Subtype.val h)
      exact ENNReal.tsum_comp_le_tsum_of_injective hf (fun j => B j.1)

end HarmonicBalls
