import HarmonicBalls.Proofs.Potential.LQGClockInsertedUniformAnnularBound

/-! # Uniform annealed annular tails

Expected tails of inserted annular increments vanish uniformly over deterministic
outer-radius sequences.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- A single vanishing bound controls the expected sum of annular increments
for every deterministic choice of outer radii. -/
theorem exists_uniform_inserted_annular_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq1 : γ*α < 1) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2*(1-γ*α)) :
    ∃ T : ℕ → ℝ≥0∞, Tendsto T atTop (𝓝 0) ∧ ∀ (δ : ℕ → ℝ) (k : ℕ),
      (∫⁻ q : ContinuousPath ℂ × Ω,
        ∑' n : {n : ℕ // n ∉ Finset.range k}, ENNReal.ofReal |∫ w,
          {w : ℂ | (2 : ℝ)⁻¹ ^ (n.1+1) ≤ ‖w‖ ∧ ‖w‖ ≤ δ n.1 ∧ ‖w‖ ≤ 1/2}.indicator
            (fun w =>
              (((2 : ℝ)⁻¹ ^ (n.1+1))/2)^(γ^2/2) * Real.exp
                (γ*(hcirc q.2 (((2 : ℝ)⁻¹ ^ (n.1+1))/2) w-hcirc q.2 1 0 -
                  α*Real.log (max (((2 : ℝ)⁻¹ ^ (n.1+1))/2) ‖w‖))) -
              ((2 : ℝ)⁻¹ ^ (n.1+1))^(γ^2/2) * Real.exp
                (γ*(hcirc q.2 ((2 : ℝ)⁻¹ ^ (n.1+1)) w-hcirc q.2 1 0 -
                  α*Real.log (max ((2 : ℝ)⁻¹ ^ (n.1+1)) ‖w‖)))) w
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))| ∂((planarBrownianMotion x).prod P)) ≤ T k := by
  obtain ⟨B, hBs, hB⟩ := exists_summable_uniform_inserted_annular_increment_bound hh x hq0 hq1 hγ hsub
  obtain ⟨q₂, β, d, θ, hqq, hq₂, hβ, hβ₂, hd0, hd, hγθ, hθ, _⟩ :=
    exists_annealed_singular_clock_exponents hq0 hq1 hγ hsub
  refine ⟨fun k => ∑' n : {n : ℕ // n ∉ Finset.range k}, ENNReal.ofReal (B n.1), ?_, ?_⟩
  · exact (ENNReal.tendsto_tsum_compl_atTop_zero hBs.tsum_ofReal_ne_top).comp tendsto_finset_range
  · intro δ k
    let I (n : ℕ) (q : ContinuousPath ℂ × Ω) : ℝ := ∫ w,
      {w : ℂ | (2 : ℝ)⁻¹ ^ (n+1) ≤ ‖w‖ ∧ ‖w‖ ≤ δ n ∧ ‖w‖ ≤ 1/2}.indicator
        (fun w =>
          (((2 : ℝ)⁻¹ ^ (n+1))/2)^(γ^2/2) * Real.exp
            (γ*(hcirc q.2 (((2 : ℝ)⁻¹ ^ (n+1))/2) w-hcirc q.2 1 0 -
              α*Real.log (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖w‖))) -
          ((2 : ℝ)⁻¹ ^ (n+1))^(γ^2/2) * Real.exp
            (γ*(hcirc q.2 ((2 : ℝ)⁻¹ ^ (n+1)) w-hcirc q.2 1 0 -
              α*Real.log (max ((2 : ℝ)⁻¹ ^ (n+1)) ‖w‖)))) w
      ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))
    have hI (n : ℕ) : Integrable (I n) ((planarBrownianMotion x).prod P) := by
      have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
      have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
        rw [pow_succ]
        have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith
      exact (inserted_annular_increment_annealed_bound hh x hq0 hqq hq₂ hβ hβ₂ hd0 hd
        hγθ.le hθ.le hpos hhalf (δ n)).1
    change (∫⁻ q, ∑' n : {n : ℕ // n ∉ Finset.range k}, ENNReal.ofReal |I n.1 q|
      ∂((planarBrownianMotion x).prod P)) ≤ _
    rw [lintegral_tsum (fun n : {n : ℕ // n ∉ Finset.range k} =>
      (hI n.1).abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    apply ENNReal.tsum_le_tsum
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hI n.1).abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hB n.1 (δ n.1))

end HarmonicBalls
