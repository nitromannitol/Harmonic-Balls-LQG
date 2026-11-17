import HarmonicBalls.Proofs.Potential.LQGClockInnerUniformTime
import HarmonicBalls.Proofs.Potential.LQGClockInnerProduct

/-! # Bounded expected inner occupations

The bounded expected uniform inner occupation vanishes as the cutoff shrinks.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The expected inner occupation, capped at a finite level, vanishes uniformly
in dyadic smoothing scale and unit time. -/
theorem tendsto_lintegral_min_iSup_time_inner_inserted_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α))
    (K : ℝ≥0∞) (hK : K ≠ ∞) :
    Tendsto (fun n : ℕ => ∫⁻ q : Ω × ContinuousPath ℂ,
      min (⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal))) K
        ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let X (n : ℕ) (q : Ω × ContinuousPath ℂ) := ⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
    let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
    ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => ε^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal))
  have hδ (n : ℕ) : (2 : ℝ)⁻¹ ^ (n+2) ≤ 1/2 := by
    rw [show n+2 = (n+1)+1 by omega, pow_succ]
    have h : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hX (n : ℕ) : AEMeasurable (X n) (P.prod (planarBrownianMotion x)) := by
    have heq : X n = fun q => ⨆ i : ℕ,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2)}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)) := by
      funext q
      apply iSup_congr
      intro i
      have hset : {z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2} =
          {z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2)} := by
        ext z
        simp only [mem_ofPred_eq]
        exact ⟨And.left, fun hz => ⟨hz, (le_of_lt hz).trans (hδ n)⟩⟩
      simp only [hset]
      apply le_antisymm
      · apply iSup_le
        intro t
        exact lintegral_mono_set (Ioc_subset_Ioc le_rfl t.2.2)
      · exact le_iSup_of_le ⟨1, by simp⟩ le_rfl
    rw [heq]
    apply AEMeasurable.iSup
    intro i
    exact aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x)
      (by positivity) γ α _ 0 1
  have hlim : ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
      Tendsto (fun n => min (X n q) K) atTop (𝓝 0) := by
    filter_upwards [ae_prod_tendsto_iSup_time_inner_inserted_zero hh x hq0 hq2 hγ hsub] with q hq
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hq
    · intro n; exact zero_le
    · intro n; exact min_le_left _ _
  have h := tendsto_lintegral_of_dominated_convergence' (μ := P.prod (planarBrownianMotion x))
    (fun _ => K) (fun n => (hX n).min aemeasurable_const)
    (fun n => Filter.Eventually.of_forall fun q => min_le_right _ _) (by simp [hK]) hlim
  simpa [X] using h

end HarmonicBalls
