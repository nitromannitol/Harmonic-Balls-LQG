import HarmonicBalls.Proofs.Potential.LQGClockAnnularSummability

/-! # Countable-time annular clock increments

Expected uniform bounds imply almost-sure summability on countable time sets.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Uniform increments over any countable collection of unit times are summable
almost surely under the product law. -/
theorem exists_ae_tsum_countable_stoppedAnnularClock_iSup_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {ι : Type*} [Countable ι] (t : ι → Icc (0 : ℝ) 1) :
    ∃ K : ℕ, ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      (∑' j : ℕ, ⨆ i : ι, ENNReal.ofReal (|stoppedAnnularClock (fun z =>
        (dyadicScale (j+K+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K+1)) z)) δ
            (fun _ => ((t i : ℝ).toNNReal)) p.2 -
        stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
            (fun _ => ((t i : ℝ).toNNReal)) p.2|)) < ⊤ := by
  obtain ⟨K, hK⟩ := exists_tsum_lintegral_prod_stoppedAnnularClock_iSup_lt_top hh x hγ hγ2 α hδ
  let S (j : ℕ) (p : Ω × ContinuousPath ℂ) := ⨆ i : ι, ENNReal.ofReal (|stoppedAnnularClock (fun z =>
        (dyadicScale (j+K+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K+1)) z)) δ
            (fun _ => ((t i : ℝ).toNNReal)) p.2 -
        stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
            (fun _ => ((t i : ℝ).toNNReal)) p.2|)
  have hS (j : ℕ) : AEMeasurable (S j) (P.prod (planarBrownianMotion x)) := by
    apply AEMeasurable.iSup
    intro i
    exact ((aemeasurable_stoppedAnnularClock_sub hh x γ α δ
      (fun _ => ((t i : ℝ).toNNReal)) measurable_const (j+K)).abs).ennreal_ofReal
  have hint : (∫⁻ p, ∑' j, S j p ∂(P.prod (planarBrownianMotion x))) < ⊤ := by
    rw [lintegral_tsum hS]
    apply lt_of_le_of_lt _ hK
    apply ENNReal.tsum_le_tsum
    intro j
    apply lintegral_mono
    intro p
    dsimp only [S]
    apply iSup_le
    intro i
    exact le_iSup (fun u : Icc (0 : ℝ) 1 => ENNReal.ofReal (|stoppedAnnularClock (fun z =>
        (dyadicScale (j+K+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K+1)) z)) δ
            (fun _ => ((u : ℝ).toNNReal)) p.2 -
        stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
            (fun _ => ((u : ℝ).toNNReal)) p.2|)) (t i)
  refine ⟨K, ?_⟩
  exact ae_lt_top' (AEMeasurable.tsum hS) hint.ne

end HarmonicBalls
