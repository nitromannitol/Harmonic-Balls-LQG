import HarmonicBalls.Proofs.Potential.LQGClockInnerProduct

/-! # Lower limits of inner clock occupations

A uniform first-moment bound passes to lower limits along smoothing sequences.
-/

open MeasureTheory MarkovProcess Set Filter
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The product-law expected lower limit of the actual inserted inner occupations
obeys the same uniform bound as each occupation. -/
theorem exists_lintegral_liminf_brownian_inner_inserted_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (ε : ℕ → ℝ), (∀ i, 0 < ε i) →
      (∀ i, ε i ≤ 1 / 2) → ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 / 2 →
      (∫⁻ q : Ω × ContinuousPath ℂ, liminf (fun i : ℕ =>
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < δ}.indicator (fun z => (ε i) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε i) z)) (q.2 s.toNNReal)))
          atTop ∂(P.prod (planarBrownianMotion x))) ≤
        (ENNReal.ofReal δ) ^ (p - γ * α) * C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_prod_brownian_inner_inserted_le hh x γ α p hq hqp hp
  refine ⟨C, hC, ?_⟩
  intro ε hε hεhalf δ hδ hδhalf
  exact (lintegral_liminf_le' (fun i =>
    aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x)
      (hε i) γ α δ 0 1)).trans
    (liminf_le_of_frequently_le' (.of_forall fun i =>
      hbound (hε i) (hεhalf i) hδ hδhalf))

end HarmonicBalls
