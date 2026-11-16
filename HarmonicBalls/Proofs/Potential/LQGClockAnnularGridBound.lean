import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformIntegrability
import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformIncrement

/-! # Annular clock increments under the product law

The product-law expectation of an annular increment agrees with its iterated
field and Brownian expectation.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The joint nonnegative integral of the annular increment is the annealed
expectation of its field-averaged absolute value. -/
theorem lintegral_prod_annularIncrementSample_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    (∫⁻ p : Ω × ContinuousPath ℂ,
      ENNReal.ofReal |annularIncrementSample hcirc γ α δ ε τ p.2 p.1|
      ∂(P.prod (planarBrownianMotion x))) =
      ENNReal.ofReal (∫ b, stoppedAnnularIncrement P hcirc γ α δ ε τ b
        ∂(planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨F, hFm, _, hFae⟩ :=
    exists_integrable_annularIncrementSample hh hγ0 hγ2 α x hε hεhalf hεδ τ hτ
  have heq : (fun p : Ω × ContinuousPath ℂ =>
      ENNReal.ofReal |annularIncrementSample hcirc γ α δ ε τ p.2 p.1|) =ᵐ[
        P.prod (planarBrownianMotion x)]
      (fun p => ENNReal.ofReal |F (p.2,p.1)|) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae hFae] with p hp
    rw [hp p.2]
  rw [lintegral_congr_ae heq]
  have hmeas : Measurable (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal |F (p.2,p.1)|) :=
    ENNReal.measurable_ofReal.comp ((hFm.comp measurable_swap).abs)
  rw [lintegral_prod_symm _ hmeas.aemeasurable]
  have hfield (b : ContinuousPath ℂ) : Integrable (fun ω => F (b, ω)) P := by
    apply (integrable_stopped_annular_increment_field hh hε hεhalf hεδ γ α τ b).congr
    filter_upwards [hFae] with ω hω
    exact (hω b).symm
  have hinner (b : ContinuousPath ℂ) :
      (∫⁻ ω, ENNReal.ofReal |F (b,ω)| ∂P) =
        ENNReal.ofReal (stoppedAnnularIncrement P hcirc γ α δ ε τ b) := by
    simp_rw [← Real.norm_eq_abs]
    rw [← ofReal_integral_eq_lintegral_ofReal (hfield b).norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))]
    congr 1
    unfold stoppedAnnularIncrement
    apply integral_congr_ae
    filter_upwards [hFae] with ω hω
    rw [hω b]
    rfl
  simp_rw [hinner]
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_stopped_annular_inserted_increment_annealed_le hh hγ0 hγ2 α x
      (hε.trans_le hεδ) τ hτ
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · exact (hb ε hε hεhalf hεδ).1
  · exact Filter.Eventually.of_forall (fun b => integral_nonneg (fun ω => abs_nonneg _))

/-- The annealed increment bound has constants independent of the measurable horizon. -/
theorem brownian_stopped_annular_inserted_increment_annealed_le_uniform_horizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    : ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        Integrable (stoppedAnnularIncrement P hcirc γ α δ ε τ) (planarBrownianMotion x) ∧
        (∫ b, stoppedAnnularIncrement P hcirc γ α δ ε τ b ∂(planarBrownianMotion x)) ≤
          ((Real.exp (γ^2*Real.log 2)-1) *
            (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂(planarBrownianMotion x)) * 2^d)+1)/2 *
              Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
          2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    ae_brownian_stopped_annular_inserted_increment_le_riesz_energy hh hγ0 hγ2 α x hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro τ hτ ε hε hεhalf hεδ
  let E : ContinuousPath ℂ → ℝ := unitOccupationRieszEnergy d
  let a : ℝ := Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2))
  let c : ℝ := Real.exp (Real.log ε * ((θ-γ)^2/2))
  let B : ℝ := Real.exp (γ^2*Real.log 2)-1
  let G : ContinuousPath ℂ → ℝ := fun b => ((B*(M^2 * E b * 2^d)+1)/2)*a + 2*M*c
  have hE : Integrable E (planarBrownianMotion x) := integrable_unitOccupationRieszEnergy x hd0 hd2
  have hG : Integrable G (planarBrownianMotion x) := by
    dsimp [G]
    fun_prop
  have hm : Measurable (stoppedAnnularIncrement P hcirc γ α δ ε τ) :=
    measurable_stopped_annular_inserted_field_expectation hh hε γ α δ τ hτ
  have hle : ∀ᵐ b ∂(planarBrownianMotion x), stoppedAnnularIncrement P hcirc γ α δ ε τ b ≤ G b := by
    filter_upwards [hb] with b hb
    exact hb (τ b) ε hε hεhalf hεδ
  have hnonneg : ∀ b, 0 ≤ stoppedAnnularIncrement P hcirc γ α δ ε τ b := by
    intro b
    apply integral_nonneg
    intro ω
    exact abs_nonneg _
  have hi : Integrable (stoppedAnnularIncrement P hcirc γ α δ ε τ) (planarBrownianMotion x) := by
    apply hG.mono' hm.aestronglyMeasurable
    filter_upwards [hle] with b hb
    simpa [Real.norm_eq_abs, abs_of_nonneg (hnonneg b)] using hb
  refine ⟨hi, (integral_mono_ae hi hG hle).trans ?_⟩
  change (∫ b, G b ∂(planarBrownianMotion x)) ≤
    ((B*(M^2 * (∫ b, E b ∂(planarBrownianMotion x)) * 2^d)+1)/2)*a + 2*M*c
  have hGeq : G = fun b => (B*M^2*2^d*a/2)*E b + (a/2 + 2*M*c) := by
    funext b
    dsimp [G]
    ring
  rw [hGeq, integral_add (hE.const_mul _) (integrable_const _), integral_const_mul]
  simp only [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
  ring_nf
  exact le_rfl


/-- The product-law increment estimate is uniform over measurable horizons. -/
theorem lintegral_prod_annular_increment_le_uniform_horizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    : ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal
          |annularIncrementSample hcirc γ α δ ε τ p.2 p.1|
          ∂(P.prod (planarBrownianMotion x))) ≤ ENNReal.ofReal (
          ((Real.exp (γ^2*Real.log 2)-1) *
            (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂(planarBrownianMotion x)) * 2^d)+1)/2 *
              Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
          2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_stopped_annular_inserted_increment_annealed_le_uniform_horizon
      hh hγ0 hγ2 α x hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro τ hτ ε hε hεhalf hεδ
  rw [lintegral_prod_annularIncrementSample_eq hh hγ0 hγ2 α x hε hεhalf hεδ τ hτ]
  exact ENNReal.ofReal_le_ofReal (hb τ hτ ε hε hεhalf hεδ).2

/-- The grid reduction remains valid when monotonicity and the cell bound hold
almost everywhere and the grid differences arealmost everywhere measurable. -/
theorem lintegral_iSup_abs_sub_le_grid_of_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    (hmono : ∀ᵐ ω ∂μ, MonotoneOn (f ω) (Set.Icc 0 T) ∧
      MonotoneOn (g ω) (Set.Icc 0 T))
    (hgrid : ∀ j : ℕ, AEMeasurable (fun ω => |f ω (j * T / m) - g ω (j * T / m)|) μ)
    (K : Ω → ℝ) (hK : ∀ᵐ ω ∂μ, 0 ≤ K ω ∧
      ∀ j, j < m → g ω ((j + 1) * T / m) - g ω (j * T / m) ≤ K ω) :
    (∫⁻ ω, ⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |f ω t - g ω t| ∂μ) ≤
      (∑ j ∈ Finset.range (m + 1), ∫⁻ ω, ENNReal.ofReal |f ω (j * T / m) - g ω (j * T / m)| ∂μ) +
        ∫⁻ ω, ENNReal.ofReal (K ω) ∂μ := by
  let D : Ω → ℝ := fun ω => ∑ j ∈ Finset.range (m + 1),
    |f ω (j * T / m) - g ω (j * T / m)|
  have hD0 (ω : Ω) : 0 ≤ D ω := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hDm : AEMeasurable D μ := by
    convert Finset.aemeasurable_sum (Finset.range (m + 1)) (fun j _ => hgrid j) using 1
    ext ω
    simp [D]
  have hpoint : ∀ᵐ ω ∂μ,
      (⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |f ω t - g ω t|) ≤
        ENNReal.ofReal (D ω) + ENNReal.ofReal (K ω) := by
    filter_upwards [hmono, hK] with ω hω hκ
    apply iSup_le
    intro t
    rw [← ENNReal.ofReal_add (hD0 ω) hκ.1]
    apply ENNReal.ofReal_le_ofReal
    apply LatticeProb.abs_sub_le_of_grid hm hT hω.1 hω.2 ?_ hκ.2 t t.property
    intro j hj
    change |f ω (j * T / m) - g ω (j * T / m)| ≤
      ∑ i ∈ Finset.range (m + 1), |f ω (i * T / m) - g ω (i * T / m)|
    exact Finset.single_le_sum (s := Finset.range (m + 1)) (a := j)
      (f := fun i : ℕ => |f ω (i * T / m) - g ω (i * T / m)|)
      (fun i _ => abs_nonneg (f ω (i * T / m) - g ω (i * T / m)))
      (Finset.mem_range.mpr (by omega))
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (D ω) + ENNReal.ofReal (K ω)) ∂μ := lintegral_mono_ae hpoint
    _ = (∫⁻ ω, ENNReal.ofReal (D ω) ∂μ) + ∫⁻ ω, ENNReal.ofReal (K ω) ∂μ :=
      lintegral_add_left' hDm.ennreal_ofReal _
    _ = _ := by
      congr 1
      simp only [D, ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
      exact lintegral_finsetSum' (Finset.range (m + 1)) (fun j _ => (hgrid j).ennreal_ofReal)

private theorem grid_integrable_annular_density (f : ℂ → ℝ) (hf : Continuous f) (δ : ℝ)
    (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f) μ := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.norm.continuousOn
  apply (integrable_const (max K 0)).mono' (hf.measurable.indicator hA).aestronglyMeasurable
  filter_upwards with z
  by_cases hz : z ∈ A
  · have hzk : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
    rw [show A.indicator f z = f z from Set.indicator_of_mem hz _]
    exact (hK ⟨z, hzk, rfl⟩).trans (le_max_left K 0)
  · rw [show A.indicator f z = 0 from Set.indicator_of_notMem hz _, norm_zero]
    exact le_max_right K 0

private theorem grid_continuous_inserted_density (hcirc : ℝ → ℂ → ℝ) (γ α r : ℝ)
    (hr : 0 < r) (hc : Continuous (hcirc r))
    (hrec : ∀ z, hcirc r z - hcirc 1 0 - α * Real.log (max r ‖z‖) =
      LatticeProb.Gauss.fieldCircleAverage α hcirc r z) :
    Continuous (fun z => r^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α hcirc r z)) := by
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α hcirc r z) =
      fun z => hcirc r z - hcirc 1 0 - α * Real.log (max r ‖z‖) := by
    funext z
    exact (hrec z).symm
  have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α hcirc r z) := by
    rw [heq]
    exact (hc.sub continuous_const).sub
      (continuous_const.mul ((continuous_const.max continuous_norm).log
        (fun _ => (lt_max_of_lt_left hr).ne')))
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))

private theorem grid_annular_clock_increment_eq
    (hcirc : ℝ → ℂ → ℝ) (γ α δ : ℝ) (τ : ContinuousPath ℂ → ℝ≥0)
    (hcont : ∀ r, 0 < r → Continuous (hcirc r))
    (hrec : ∀ r z, 0 < r → hcirc r z - hcirc 1 0 - α * Real.log (max r ‖z‖) =
      LatticeProb.Gauss.fieldCircleAverage α hcirc r z)
    (k : ℕ) (b : ContinuousPath ℂ) :
    stoppedAnnularClock (fun z => (dyadicScale (k+1))^(γ^2/2) *
      Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α hcirc (dyadicScale (k+1)) z)) δ τ b -
    stoppedAnnularClock (fun z => (dyadicScale k)^(γ^2/2) *
      Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α hcirc (dyadicScale k) z)) δ τ b =
    annularIncrementSample (fun _ : Unit => hcirc) γ α δ (dyadicScale k) τ b () := by
  let D : ℕ → ℂ → ℝ := fun k z => (dyadicScale k)^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α hcirc (dyadicScale k) z)
  have hD (j : ℕ) : Continuous (D j) := grid_continuous_inserted_density hcirc γ α _
    (dyadicScale_pos j) (hcont _ (dyadicScale_pos j)) (fun z => hrec _ z (dyadicScale_pos j))
  have hscale : dyadicScale (k+1) = dyadicScale k / 2 := by
    simp only [dyadicScale, pow_succ]
    ring
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic (τ b)))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hμ : μ ≤ Measure.map (fun t => b t) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le (Measure.map (fun t => b t) ν) hμ
  change (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (D (k+1)) z ∂μ) -
    (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (D k) z ∂μ) = _
  rw [← integral_sub (grid_integrable_annular_density _ (hD (k+1)) δ μ)
    (grid_integrable_annular_density _ (hD k) δ μ)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Set.indicator_apply]
  split_ifs
  · dsimp [D]
    rw [hscale, ← hrec _ z (half_pos (dyadicScale_pos k)),
      ← hrec _ z (dyadicScale_pos k)]
  · ring

/-- On one full-measure field event, every dyadic clock difference equals its
annular increment sample, simultaneously for all paths and horizons. -/
theorem ae_stoppedAnnularClock_sub_eq_annularIncrementSample
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α δ : ℝ) :
    ∀ᵐ ω ∂P, ∀ (τ : ContinuousPath ℂ → ℝ≥0) (k : ℕ) (b : ContinuousPath ℂ),
      stoppedAnnularClock (fun z => (dyadicScale (k+1))^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z)) δ τ b -
      stoppedAnnularClock (fun z => (dyadicScale k)^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)) δ τ b =
      annularIncrementSample hcirc γ α δ (dyadicScale k) τ b ω := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
  have hcont : ∀ r, 0 < r → Continuous (hcirc ω r) := by
    intro r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  intro τ k b
  exact grid_annular_clock_increment_eq (hcirc ω) γ α δ τ hcont hrec k b

/-- Each actual dyadic clock difference at a measurable horizon is almost
 everywhere measurable under the field-path product law. -/
theorem aemeasurable_stoppedAnnularClock_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) (γ α δ : ℝ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) (k : ℕ) :
    AEMeasurable (fun p : Ω × ContinuousPath ℂ =>
      stoppedAnnularClock (fun z => (dyadicScale (k+1))^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) δ τ p.2 -
      stoppedAnnularClock (fun z => (dyadicScale k)^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale k) z)) δ τ p.2)
      (P.prod (planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨F, hF, hFae⟩ := exists_measurable_annularIncrementSample hh (dyadicScale_pos k) γ α δ τ hτ
  apply (hF.comp measurable_swap).aemeasurable.congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_stoppedAnnularClock_sub_eq_annularIncrementSample hh γ α δ),
    (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae hFae] with p hp hq
  exact (hq p.2).trans (hp τ k p.2).symm

/-- The actual dyadic annular clock differences have an annealed bound with
constants uniform over measurable horizons. -/
theorem lintegral_prod_stoppedAnnularClock_sub_le_uniform_horizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ k : ℕ, dyadicScale k ≤ 1/2 → dyadicScale k ≤ δ →
        (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal (|stoppedAnnularClock (fun z => (dyadicScale (k+1))^(γ^2/2) *
            Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) δ τ p.2 -
          stoppedAnnularClock (fun z => (dyadicScale k)^(γ^2/2) *
            Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale k) z)) δ τ p.2|)
          ∂(P.prod (planarBrownianMotion x))) ≤ ENNReal.ofReal (
          ((Real.exp (γ^2*Real.log 2)-1) *
            (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂(planarBrownianMotion x)) * 2^d)+1)/2 *
              Real.exp (Real.log (dyadicScale k) * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
          2*M*Real.exp (Real.log (dyadicScale k) * ((θ-γ)^2/2))) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hbound⟩ :=
    lintegral_prod_annular_increment_le_uniform_horizon hh hγ0 hγ2 α x hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro τ hτ k hhalf hδk
  have heq : (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal (|stoppedAnnularClock (fun z => (dyadicScale (k+1))^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) δ τ p.2 -
      stoppedAnnularClock (fun z => (dyadicScale k)^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale k) z)) δ τ p.2|)) =ᵐ[
        P.prod (planarBrownianMotion x)]
      (fun p => ENNReal.ofReal |annularIncrementSample hcirc γ α δ (dyadicScale k) τ p.2 p.1|) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_stoppedAnnularClock_sub_eq_annularIncrementSample hh γ α δ)] with p hp
    rw [hp τ k p.2]
  rw [lintegral_congr_ae heq]
  exact hbound τ hτ (dyadicScale k) (dyadicScale_pos k) hhalf hδk

/-- A nonnegative continuous annular density has nonnegative clock increments,
and their extended values equal the corresponding time-cell integrals. -/
theorem stoppedAnnularClock_sub_nonneg_and_ofReal_eq_lintegral (f : ℂ → ℝ) (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z)
    (δ : ℝ) (b : ContinuousPath ℂ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    0 ≤ stoppedAnnularClock f δ (fun _ => v.toNNReal) b -
      stoppedAnnularClock f δ (fun _ => u.toNNReal) b ∧
    ENNReal.ofReal (stoppedAnnularClock f δ (fun _ => v.toNNReal) b -
      stoppedAnnularClock f δ (fun _ => u.toNNReal) b) =
      ∫⁻ s in Ioc u v, ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let g : ℝ → ℝ := fun s => A.indicator f (b s.toNNReal)
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hgm : Measurable g := (hf.measurable.indicator hA).comp
    (b.continuous.measurable.comp continuous_real_toNNReal.measurable)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.norm.continuousOn
  have hgK : ∀ s, ‖g s‖ ≤ max K 0 := by
    intro s
    by_cases hs : b s.toNNReal ∈ A
    · have hs' : b s.toNNReal ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hs.2
      rw [show g s = f (b s.toNNReal) from Set.indicator_of_mem hs _]
      exact (hK ⟨_, hs', rfl⟩).trans (le_max_left K 0)
    · rw [show g s = 0 from Set.indicator_of_notMem hs _, norm_zero]
      exact le_max_right K 0
  have hgi (a c : ℝ) : IntervalIntegrable g volume a c := by
    have hc : IntervalIntegrable (fun _ : ℝ => max K 0) volume a c := intervalIntegrable_const
    apply hc.mono_fun' hgm.aestronglyMeasurable.restrict
    exact Filter.Eventually.of_forall hgK
  have hg0 (s : ℝ) : 0 ≤ g s := by
    simp only [g, Set.indicator_apply]
    split_ifs with hs
    · exact hf0 _
    · exact le_rfl
  have hv0 : 0 ≤ v := hu.trans huv
  rw [stoppedAnnularClock_eq_time_integral _ hf.measurable,
    stoppedAnnularClock_eq_time_integral _ hf.measurable]
  simp only [NNReal.coe_one, Real.coe_toNNReal', max_eq_left hu, max_eq_left hv0,
    min_eq_right hv, min_eq_right (huv.trans hv)]
  change 0 ≤ (∫ s in (0 : ℝ)..v, g s) - (∫ s in (0 : ℝ)..u, g s) ∧
    ENNReal.ofReal ((∫ s in (0 : ℝ)..v, g s) - (∫ s in (0 : ℝ)..u, g s)) = _
  rw [intervalIntegral.integral_interval_sub_left (hgi 0 v) (hgi 0 u)]
  refine ⟨intervalIntegral.integral_nonneg_of_forall huv hg0, ?_⟩
  rw [intervalIntegral.integral_of_le huv,
    ofReal_integral_eq_lintegral_ofReal (hgi u v).1 (Filter.Eventually.of_forall hg0)]

/-- A nonnegative continuous density gives a nondecreasing annular clock. -/
theorem monotoneOn_stoppedAnnularClock (f : ℂ → ℝ) (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) (δ : ℝ) (b : ContinuousPath ℂ) :
    MonotoneOn (fun t : ℝ => stoppedAnnularClock f δ (fun _ => t.toNNReal) b)
      (Icc (0 : ℝ) 1) := by
  intro u hu v hv huv
  exact sub_nonneg.mp (stoppedAnnularClock_sub_nonneg_and_ofReal_eq_lintegral
    f hf hf0 δ b hu.1 huv hv.2).1


/-- On one full-measure field event, each actual dyadic annular clock is
nondecreasing and its increments are the corresponding density-cell integrals. -/
theorem ae_dyadic_stoppedAnnularClock_monotone_and_cell
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α δ : ℝ) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (b : ContinuousPath ℂ),
      let f : ℂ → ℝ := fun z => (dyadicScale k)^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)
      MonotoneOn (fun t : ℝ => stoppedAnnularClock f δ (fun _ => t.toNNReal) b) (Icc 0 1) ∧
      ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ 1 →
        ENNReal.ofReal (stoppedAnnularClock f δ (fun _ => v.toNNReal) b -
          stoppedAnnularClock f δ (fun _ => u.toNNReal) b) =
        ∫⁻ s in Ioc u v, ENNReal.ofReal
          ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
  intro k b
  let f : ℂ → ℝ := fun z => (dyadicScale k)^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)
  have hc : Continuous (hcirc ω (dyadicScale k)) := by
    rw [← funext (hω (dyadicScale k))]
    exact hHc ω (dyadicScale k) (dyadicScale_pos k)
  have hf : Continuous f := grid_continuous_inserted_density (hcirc ω) γ α (dyadicScale k)
    (dyadicScale_pos k) hc (fun z => hrec _ z (dyadicScale_pos k))
  have hf0 : ∀ z, 0 ≤ f z := by
    intro z
    dsimp [f]
    exact mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
  refine ⟨monotoneOn_stoppedAnnularClock f hf hf0 δ b, ?_⟩
  intro u v hu huv hv
  exact (stoppedAnnularClock_sub_nonneg_and_ofReal_eq_lintegral f hf hf0 δ b hu huv hv).2

end HarmonicBalls
