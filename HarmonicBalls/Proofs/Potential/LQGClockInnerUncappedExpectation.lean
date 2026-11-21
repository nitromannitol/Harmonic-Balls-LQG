import HarmonicBalls.Proofs.Potential.LQGClockEnvelopeAnnularIncrement
import HarmonicBalls.Proofs.Potential.LQGClockFineInnerExpectation
import HarmonicBalls.Proofs.Potential.LQGClockFullInnerExpectation

/-! # Expected inner occupations without truncation

For a fixed Brownian start, the product-law expected supremum of the actual inner
occupations over unit times and all dyadic smoothing scales tends to zero as the inner
cutoff shrinks, whenever `0 < γ * α` and `γ ^ 2 / 2 < 2 - γ * α`. This range contains the
almost sure range `γ ^ 2 / 2 < 2 * (2 - γ * α) / (2 + γ * α)` of the pathwise statement.
The annular increments are controlled through the weighted pair energy with a Riesz kernel.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The expected absolute increment of an inserted closed-cutoff occupation
admits a summable bound independent of the outer cutoff. -/
theorem exists_summable_uniform_inserted_cutoff_increment_bound_of_lt_two_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2 - γ*α) :
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
  have hq2 : γ*α < 2 := by linarith [sq_nonneg γ]
  obtain ⟨A, hAs, hA⟩ :=
    exists_summable_uniform_inserted_annular_increment_bound_of_lt_two_sub hh x hq0 hγ hsub
  obtain ⟨C, hCs, hC⟩ := exists_summable_uniform_inner_inserted_expectation_bound hh x γ α
    ((γ*α+2)/2) hq0 (by linarith) (by linarith)
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
    have hAn := hA n δ
    dsimp only at hAn
    have hI : Integrable I ((planarBrownianMotion x).prod P) := hAn.1
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
          exact ENNReal.ofReal_le_ofReal hAn.2
        have hK1 : (∫⁻ q, K (ε/2) (q.2,q.1) ∂((planarBrownianMotion x).prod P)) ≤ C n := by
          change (∫⁻ q, K (ε/2) q.swap ∂((planarBrownianMotion x).prod P)) ≤ C n
          rw [lintegral_prod_swap]
          exact hC n (ε/2) (half_pos hε) (by linarith)
        have hK2 : (∫⁻ q, K ε (q.2,q.1) ∂((planarBrownianMotion x).prod P)) ≤ C n := by
          change (∫⁻ q, K ε q.swap ∂((planarBrownianMotion x).prod P)) ≤ C n
          rw [lintegral_prod_swap]
          exact hC n ε hε hεhalf
        exact add_le_add (add_le_add hIA hK1) hK2

/-- For a fixed Brownian start, expected closed-ball occupations vanish uniformly
over finer dyadic smoothing scales in the displayed parameter regime. -/
theorem tendsto_lintegral_iSup_inserted_inner_closed_occupation_zero_of_lt_two_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2 - γ*α) :
    Tendsto (fun n : ℕ => ∫⁻ q : ContinuousPath ℂ × Ω, ⨆ i : ℕ,
      let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+i+1)
      ENNReal.ofReal |∫ z,
        {z : ℂ | ‖z‖ ≤ (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) ε z)) z
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))|
      ∂((planarBrownianMotion x).prod P)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hq2 : γ*α < 2 := by linarith [sq_nonneg γ]
  let d : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdhalf (n : ℕ) : d n ≤ 1/2 := by
    dsimp [d]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hdstep (n : ℕ) : d (n+1) = d n / 2 := by
    dsimp [d]
    rw [show n+1+1 = (n+1)+1 by omega, pow_succ]
    ring
  have hdlt (n : ℕ) : d (n+1) < d n := by rw [hdstep]; linarith [hd n]
  let X (n i : ℕ) (q : ContinuousPath ℂ × Ω) : ℝ := ∫ z,
    {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator
      (fun z => (d (n+i))^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d (n+i)) z)) z
      ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))
  have hX (n i : ℕ) : AEMeasurable (X n i) ((planarBrownianMotion x).prod P) :=
    aemeasurable_inserted_closedBall_occupation hh (planarBrownianMotion x) γ α
      (d (n+1)) (d (n+i)) (hd _)
  obtain ⟨A, hAs, hA⟩ :=
    exists_summable_uniform_inserted_cutoff_increment_bound_of_lt_two_sub hh x hq0 hγ hsub
  obtain ⟨C, hCs, hC⟩ := exists_summable_uniform_inner_inserted_expectation_bound hh x γ α
    ((γ*α+2)/2) hq0 (by linarith) (by linarith)
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hpoint : ∀ᵐ q : ContinuousPath ℂ × Ω ∂((planarBrownianMotion x).prod P),
      ∀ n : ℕ, ENNReal.ofReal |X n 0 q| ≤
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < d n}.indicator (fun z => (d n)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d n) z)) (q.1 s.toNNReal)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd
      (μ := planarBrownianMotion x) (ν := P)).ae hcont,
      (Measure.quasiMeasurePreserving_snd
      (μ := planarBrownianMotion x) (ν := P)).ae
        (ae_recentered_inserted_circle_average hh α)] with q hc hr n
    let f : ℂ → ℝ := fun z => (d n)^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d n) z)
    have hfeq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d n) z) =
        fun z => hcirc q.2 (d n) z - hcirc q.2 1 0 - α * Real.log (max (d n) ‖z‖) := by
      funext z
      exact (hr (d n) z (hd n)).symm
    have hf : Continuous f := by
      have hfc : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d n) z) := by
        rw [hfeq]
        exact ((hc (d n) (hd n)).sub continuous_const).sub (continuous_const.mul
          ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (hd n)).ne')))
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hfc))
    have hf0 (z : ℂ) : 0 ≤ f z :=
      mul_nonneg (Real.rpow_nonneg (hd n).le _) (Real.exp_pos _).le
    simpa [X, f] using closed_unit_occupation_le_lintegral_inner_time q.1 f hf hf0 (hdlt n) (hdhalf n)
  have hinit : Tendsto (fun n => ∫⁻ q, ENNReal.ofReal |X n 0 q|
      ∂((planarBrownianMotion x).prod P)) atTop (𝓝 0) := by
    have ht : Tendsto C atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hCs.ne
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    intro n
    calc
      _ ≤ ∫⁻ q : ContinuousPath ℂ × Ω, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < d n}.indicator (fun z => (d n)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d n) z)) (q.1 s.toNNReal)))
          ∂((planarBrownianMotion x).prod P) := lintegral_mono_ae (hpoint.mono fun q hq => hq n)
      _ = ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < d n}.indicator (fun z => (d n)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d n) z)) (q.2 s.toNNReal)))
          ∂(P.prod (planarBrownianMotion x)) := by
            let F (q : Ω × ContinuousPath ℂ) := ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
              ({z : ℂ | ‖z‖ < d n}.indicator (fun z => (d n)^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d n) z)) (q.2 s.toNNReal))
            change (∫⁻ q, F q.swap ∂((planarBrownianMotion x).prod P)) =
              ∫⁻ q, F q ∂(P.prod (planarBrownianMotion x))
            exact lintegral_prod_swap F
      _ ≤ C n := hC n (d n) (hd n) (hdhalf n)
  have hinc (n i : ℕ) : (∫⁻ q, ENNReal.ofReal |X n (i+1) q - X n i q|
      ∂((planarBrownianMotion x).prod P)) ≤ A (n+i) := by
    have h := hA (n+i) (d (n+1))
    simpa only [X, ← Nat.add_assoc, hdstep, d] using h
  have h := tendsto_lintegral_iSup_ofReal_abs_zero_of_shifted_envelope
    ((planarBrownianMotion x).prod P) X hX A hAs.ne hinit hinc
  simpa only [X, d, Nat.add_assoc] using h

/-- The product-law expected supremum of actual inner occupations over all
unit times and dyadic smoothing scales tends to zero. -/
theorem tendsto_lintegral_iSup_time_inner_inserted_zero_of_lt_two_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2 - γ*α) :
    Tendsto (fun n : ℕ => ∫⁻ q : Ω × ContinuousPath ℂ,
      (⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hq2 : γ*α < 2 := by linarith [sq_nonneg γ]
  let d : ℕ → ℝ := fun i => (2 : ℝ)⁻¹ ^ (i+1)
  have hd (i : ℕ) : 0 < d i := by dsimp [d]; positivity
  have hdlt (i : ℕ) : d (i+1) < d i := by
    dsimp [d]
    rw [show i+1+1 = (i+1)+1 by omega, pow_succ]
    have h : 0 < (2 : ℝ)⁻¹ ^ (i+1) := by positivity
    nlinarith
  let F (q : Ω × ContinuousPath ℂ) (i : ℕ) (z : ℂ) := (d i)^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z)
  let C (n : ℕ) (q : Ω × ContinuousPath ℂ) :=
    ∑ i ∈ Finset.range (n+1), ∫⁻ s in Ioc (0 : ℝ) 1,
      ENNReal.ofReal ({z : ℂ | ‖z‖ < d n}.indicator (F q i) (q.2 s.toNNReal))
  let J (n : ℕ) (q : Ω × ContinuousPath ℂ) := ⨆ i : ℕ, ENNReal.ofReal |∫ z,
    {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator (F q (n+i)) z
      ∂(Measure.map (fun t => q.2 t) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))|
  have hCmeas (n : ℕ) : AEMeasurable (C n) (P.prod (planarBrownianMotion x)) := by
    apply Finset.aemeasurable_fun_sum
    intro i hi
    exact aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x) (hd i) γ α (d n) 0 1
  let p : ℝ := (2+γ*α)/2
  have hqp : γ*α < p := by dsimp [p]; linarith
  have hp : p < 2 := by dsimp [p]; linarith
  have hC : Tendsto (fun n => ∫⁻ q, C n q ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
    simpa only [C, F, d] using
      tendsto_lintegral_sum_inner_inserted_coarse_dyadic_zero hh x γ α p hq0 hqp hp
  have hJ : Tendsto (fun n => ∫⁻ q, J n q ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
    have heq (n : ℕ) : (∫⁻ q, J n q ∂(P.prod (planarBrownianMotion x))) =
        ∫⁻ q : ContinuousPath ℂ × Ω, J n q.swap ∂((planarBrownianMotion x).prod P) := by
      symm
      exact lintegral_prod_swap (J n)
    simp_rw [heq]
    simpa only [J, F, d, Nat.add_assoc, Nat.reduceAdd, Prod.swap] using
      tendsto_lintegral_iSup_inserted_inner_closed_occupation_zero_of_lt_two_sub hh x hq0 hγ hsub
  have hsum : Tendsto (fun n => (∫⁻ q, C n q ∂(P.prod (planarBrownianMotion x))) +
      (∫⁻ q, J n q ∂(P.prod (planarBrownianMotion x)))) atTop (𝓝 0) := by
    simpa only [add_zero] using hC.add hJ
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hbound (n : ℕ) : ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      (⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1, ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator (F q i) (q.2 s.toNNReal))) ≤ C n q + J n q := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hcont,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_recentered_inserted_circle_average hh α)] with q hc hr
    have hF (i : ℕ) : Continuous (F q i) := by
      have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z) =
          fun z => hcirc q.1 (d i) z - hcirc q.1 1 0 - α * Real.log (max (d i) ‖z‖) := by
        funext z
        exact (hr (d i) z (hd i)).symm
      have hi : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z) := by
        rw [heq]
        exact ((hc _ (hd i)).sub continuous_const).sub (continuous_const.mul
          ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (hd i)).ne')))
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hi))
    have hF0 (i : ℕ) (z : ℂ) : 0 ≤ F q i z :=
      mul_nonneg (Real.rpow_nonneg (hd i).le _) (Real.exp_pos _).le
    apply iSup_le
    intro i
    apply iSup_le
    intro t
    by_cases hi : i < n+1
    · calc
        _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
            ({z : ℂ | ‖z‖ < d n}.indicator (F q i) (q.2 s.toNNReal)) := by
          calc
            _ ≤ ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
                ({z : ℂ | ‖z‖ < d n}.indicator (F q i) (q.2 s.toNNReal)) := by
              apply lintegral_mono
              intro s
              apply ENNReal.ofReal_le_ofReal
              apply Set.indicator_le_indicator_of_subset _ (hF0 i)
              intro z hz
              exact lt_trans hz.1 (hdlt n)
            _ ≤ _ := lintegral_mono_set (Ioc_subset_Ioc le_rfl t.2.2)
        _ ≤ C n q := by
          dsimp only [C]
          exact Finset.single_le_sum (f := fun j : ℕ => ∫⁻ s in Ioc (0 : ℝ) 1,
            ENNReal.ofReal ({z : ℂ | ‖z‖ < d n}.indicator (F q j) (q.2 s.toNNReal)))
            (fun _ _ => zero_le) (Finset.mem_range.mpr hi)
        _ ≤ C n q + J n q := le_add_right le_rfl
    · have hni : n ≤ i := by omega
      calc
        _ ≤ ENNReal.ofReal (∫ z, {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator
            (F q i) z ∂(Measure.map (fun u => q.2 u) (Measure.map Real.toNNReal
              (volume.restrict (Icc (0 : ℝ) 1))))) :=
          lintegral_inner_time_le_closed_unit_occupation q.2 (F q i) (hF i) (hF0 i)
            (d (n+1)) t.1 t.2.2
        _ ≤ ENNReal.ofReal |∫ z, {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator
            (F q i) z ∂(Measure.map (fun u => q.2 u) (Measure.map Real.toNNReal
              (volume.restrict (Icc (0 : ℝ) 1))))| := ENNReal.ofReal_le_ofReal (le_abs_self _)
        _ ≤ J n q := by
          simpa only [J, Nat.add_sub_of_le hni] using
            le_iSup (fun j : ℕ => ENNReal.ofReal |∫ z,
              {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator (F q (n+j)) z
                ∂(Measure.map (fun u => q.2 u) (Measure.map Real.toNNReal
                  (volume.restrict (Icc (0 : ℝ) 1))))|) (i-n)
        _ ≤ C n q + J n q := le_add_left le_rfl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
  · intro n
    exact zero_le
  · intro n
    calc
      _ ≤ ∫⁻ q, C n q + J n q ∂(P.prod (planarBrownianMotion x)) := by
        apply lintegral_mono_ae
        simpa only [F, d, Nat.add_assoc, Nat.reduceAdd] using hbound n
      _ = _ := lintegral_add_left' (hCmeas n) (J n)

/-- In the almost sure parameter range of the pathwise inner statement, the product-law
expected supremum of the actual inner occupations over unit times and all dyadic smoothing
scales tends to zero. -/
theorem tendsto_lintegral_iSup_time_inner_inserted_zero_of_lt_two_mul_div
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    Tendsto (fun n : ℕ => ∫⁻ q : Ω × ContinuousPath ℂ,
      (⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
  have hpos : 0 < 2 + γ*α := by linarith
  have hle : 2 * (2-γ*α) / (2+γ*α) ≤ 2 - γ*α := by
    rw [div_le_iff₀ hpos]
    nlinarith
  exact tendsto_lintegral_iSup_time_inner_inserted_zero_of_lt_two_sub hh x hq0 hγ
    (lt_of_lt_of_le hsub hle)

end HarmonicBalls
