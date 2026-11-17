import HarmonicBalls.Proofs.Potential.LQGClockInsertedOccupationIncrement
import HarmonicBalls.Proofs.Potential.LQGClockUniformAnnularTail
import HarmonicBalls.Proofs.Potential.LQGClockUniformInnerExpectation

/-! # Expected inserted cutoff increments

A summable bound controls expected cutoff increments uniformly in the cutoff.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The expected absolute increment of an inserted closed-cutoff occupation
admits a summable bound independent of the outer cutoff. -/
theorem exists_summable_uniform_inserted_cutoff_increment_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hq1 : γ * α < 1) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2*(1-γ*α)) :
    ∃ B : ℕ → ℝ≥0∞, (∑' n, B n) < ∞ ∧ ∀ (n : ℕ) (δ : ℝ),
      let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
      (∫⁻ q : ContinuousPath ℂ × Ω, ENNReal.ofReal |(∫ z,
        {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => (ε/2)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (ε/2) z)) z
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))) -
        ∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) ε z)) z
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))|
        ∂((planarBrownianMotion x).prod P)) ≤ B n := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨A, hAs, hA⟩ := exists_summable_uniform_inserted_annular_increment_bound hh x hq0 hq1 hγ hsub
  obtain ⟨C, hCs, hC⟩ := exists_summable_uniform_inner_inserted_expectation_bound hh x γ α 1 hq0 hq1 (by norm_num)
  obtain ⟨q₂, β, d, θ, hqq, hq₂, hβ, hβ₂, hd0, hd, hγθ, hθ, _⟩ :=
    exists_annealed_singular_clock_exponents hq0 hq1 hγ hsub
  refine ⟨fun n => ENNReal.ofReal (A n) + C n + C n, ?_, ?_⟩
  · rw [ENNReal.tsum_add, ENNReal.tsum_add]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hAs.tsum_ofReal_ne_top.lt_top, hCs⟩, hCs⟩
  · intro n δ
    let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεhalf : ε ≤ 1/2 := by
      dsimp [ε]
      rw [pow_succ]
      have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    let I (q : ContinuousPath ℂ × Ω) : ℝ := ∫ z,
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc q.2 (ε/2) z - hcirc q.2 1 0 -
          α*Real.log (max (ε/2) ‖z‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc q.2 ε z - hcirc q.2 1 0 -
          α*Real.log (max ε ‖z‖)))) z
        ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))))
    let K (r : ℝ) (q : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < ε}.indicator (fun z => r^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) r z)) (q.2 s.toNNReal))
    have hI : Integrable I ((planarBrownianMotion x).prod P) :=
      (inserted_annular_increment_annealed_bound hh x hq0 hqq hq₂ hβ hβ₂ hd0 hd
        hγθ.le hθ.le hε hεhalf δ).1
    have hK (r : ℝ) (hr : 0 < r) : AEMeasurable (K r) (P.prod (planarBrownianMotion x)) :=
      aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x) hr γ α ε 0 1
    have hKa (r : ℝ) (hr : 0 < r) :
        AEMeasurable (fun q : ContinuousPath ℂ × Ω => K r (q.2,q.1))
          ((planarBrownianMotion x).prod P) := (hK r hr).prod_swap
    have hpoint : ∀ᵐ q : ContinuousPath ℂ × Ω ∂((planarBrownianMotion x).prod P),
        ENNReal.ofReal |(∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => (ε/2)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (ε/2) z)) z
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))) -
          ∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) ε z)) z
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))| ≤
          ENNReal.ofReal |I q| + K (ε/2) (q.2,q.1) + K ε (q.2,q.1) := by
      filter_upwards [(Measure.quasiMeasurePreserving_snd
        (μ := planarBrownianMotion x) (ν := P)).ae
          (ae_inserted_closedBall_occupation_increment_le hh γ α)] with q hq
      exact hq q.1 ε δ hε hεhalf
    calc
      _ ≤ ∫⁻ q, (ENNReal.ofReal |I q| + K (ε/2) (q.2,q.1) + K ε (q.2,q.1))
          ∂((planarBrownianMotion x).prod P) := lintegral_mono_ae hpoint
      _ = (∫⁻ q, ENNReal.ofReal |I q| ∂((planarBrownianMotion x).prod P)) +
          (∫⁻ q, K (ε/2) (q.2,q.1) ∂((planarBrownianMotion x).prod P)) +
          ∫⁻ q, K ε (q.2,q.1) ∂((planarBrownianMotion x).prod P) := by
        change (∫⁻ q, ((fun q : ContinuousPath ℂ × Ω => ENNReal.ofReal |I q|) +
          (fun q : ContinuousPath ℂ × Ω => K (ε/2) (q.2,q.1))) q + K ε (q.2,q.1)
          ∂((planarBrownianMotion x).prod P)) = _
        rw [lintegral_add_left' (hI.abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal.add
          (hKa (ε/2) (half_pos hε)))]
        change (∫⁻ q, ENNReal.ofReal |I q| + K (ε/2) (q.2,q.1)
          ∂((planarBrownianMotion x).prod P)) + _ = _
        rw [lintegral_add_left' hI.abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
      _ ≤ ENNReal.ofReal (A n) + C n + C n := by
        have hIA : (∫⁻ q, ENNReal.ofReal |I q| ∂((planarBrownianMotion x).prod P)) ≤
            ENNReal.ofReal (A n) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hI.abs
            (Filter.Eventually.of_forall fun _ => abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hA n δ)
        have hK1 : (∫⁻ q, K (ε/2) (q.2,q.1) ∂((planarBrownianMotion x).prod P)) ≤ C n := by
          change (∫⁻ q, K (ε/2) q.swap ∂((planarBrownianMotion x).prod P)) ≤ C n
          rw [lintegral_prod_swap]
          exact hC n (ε/2) (half_pos hε) (by linarith)
        have hK2 : (∫⁻ q, K ε (q.2,q.1) ∂((planarBrownianMotion x).prod P)) ≤ C n := by
          change (∫⁻ q, K ε q.swap ∂((planarBrownianMotion x).prod P)) ≤ C n
          rw [lintegral_prod_swap]
          exact hC n ε hε hεhalf
        exact add_le_add (add_le_add hIA hK1) hK2

end HarmonicBalls
