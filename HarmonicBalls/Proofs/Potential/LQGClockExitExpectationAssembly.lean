import HarmonicBalls.Proofs.Potential.LQGClockInnerStoppedIncrement
import HarmonicBalls.Proofs.Potential.LQGClockExitIncrementUniformIntegrability
import HarmonicBalls.Proofs.Potential.LQGClockOfLocallyUniformLimit

/-! # Expected exit times of the inserted clock from regional increment bounds

Split the plane into the inner disc `‖z‖ < δ`, the annulus `δ ≤ ‖z‖ ≤ 1/2` and the exterior
`1/2 < ‖z‖`. For the clocks stopped at the exit time from a smooth bounded domain and capped
at time one, the inner increments have a summable bound uniform over the start whenever
`0 < γ * α` and `γ ^ 2 / 2 < 2 - γ * α`. Given summable bounds of the same kind for the
annular and the exterior increments, uniform over starts in the domain, the exit-time clock
approximations are uniformly integrable for almost every field, and every LQG clock that is
almost surely a time-change clock has finite expected exit time equal to the limit of the
expected Green integrals of the approximating measures.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- An interval integral along a path up to a time at most one is the integral against the
occupation measure of the path up to that time. -/
theorem intervalIntegral_path_eq_integral_occupation (F : ℂ → ℝ) (hF : Measurable F)
    (b : ContinuousPath ℂ) {u : ℝ≥0} (hu : u ≤ 1) :
    (∫ s in (0 : ℝ)..(u : ℝ), F (b s.toNNReal)) =
      ∫ z, F z ∂(Measure.map (fun t => b t)
        ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic u))) := by
  rw [integral_map b.continuous.measurable.aemeasurable hF.aestronglyMeasurable]
  rw [Measure.restrict_map continuous_real_toNNReal.measurable measurableSet_Iic]
  rw [Measure.restrict_restrict (continuous_real_toNNReal.measurable measurableSet_Iic)]
  rw [integral_map (f := fun t : ℝ≥0 => F (b t)) continuous_real_toNNReal.measurable.aemeasurable
    (hF.comp b.continuous.measurable).aestronglyMeasurable]
  rw [intervalIntegral.integral_of_le u.coe_nonneg, ← integral_Icc_eq_integral_Ioc]
  congr 1
  congr 1
  ext s
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc]
  constructor
  · rintro ⟨h0, hT⟩
    exact ⟨(Real.toNNReal_le_iff_le_coe).mpr hT, h0, le_trans hT (by exact_mod_cast hu)⟩
  · rintro ⟨hs, h0, _⟩
    exact ⟨h0, (Real.toNNReal_le_iff_le_coe).mp hs⟩


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Integrals of the inserted density over a region against stopped occupation measures are
almost everywhere measurable under the product law. -/
theorem aemeasurable_region_stopped_occupation
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ) (k : ℕ) {S : Set ℂ}
    (hS : MeasurableSet S) (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ)
    (ν' : Measure (ContinuousPath ℂ)) [SFinite ν'] :
    AEMeasurable (fun p : Ω × ContinuousPath ℂ => ∫ z, S.indicator (fun z =>
      (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale k) z)) z
      ∂(Measure.map (fun t => p.2 t) ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ p.2))))) (P.prod ν') := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let d : ℝ := dyadicScale k
  have hd : 0 < d := dyadicScale_pos k
  let FH : Ω × ℂ → ℝ := fun q => S.indicator (fun z => d ^ (γ ^ 2 / 2) * Real.exp (γ *
    (H q.1 d z - H q.1 1 0 - α * Real.log (max d ‖z‖)))) q.2
  have hFH : Measurable FH := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 d q.2) := (hHm d hd).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 one_pos).comp ((measurable_const : Measurable fun _ : Ω × ℂ => (0 : ℂ)).prodMk
        measurable_fst)
    have h3 : Measurable (fun q : Ω × ℂ => d ^ (γ ^ 2 / 2) * Real.exp (γ *
        (H q.1 d q.2 - H q.1 1 0 - α * Real.log (max d ‖q.2‖)))) :=
      measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul ((h1.sub h2).sub
        (measurable_const.mul (Real.measurable_log.comp
          (measurable_const.max (measurable_norm.comp measurable_snd)))))))
    have heq : FH = (Prod.snd ⁻¹' S).indicator (fun q : Ω × ℂ => d ^ (γ ^ 2 / 2) * Real.exp (γ *
        (H q.1 d q.2 - H q.1 1 0 - α * Real.log (max d ‖q.2‖)))) := by
      funext q
      by_cases hq : q.2 ∈ S
      · rw [Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' S from hq)]
        exact Set.indicator_of_mem hq _
      · rw [Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' S from hq)]
        exact Set.indicator_of_notMem hq _
    rw [heq]
    exact h3.indicator (measurable_snd hS)
  have hm := (measurable_stopped_path_integral FH hFH τ hτ).comp measurable_swap
  refine hm.aemeasurable.congr ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν')).ae
    (hHae.and (ae_recentered_inserted_circle_average hh α))] with p hp
  obtain ⟨hω, hrec⟩ := hp
  simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
  congr 1
  funext z
  simp only [FH]
  by_cases hz : z ∈ S
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hω, hω, hrec d z hd]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]


private theorem integrable_of_le_unit_occupation' (b : ContinuousPath ℂ) {μ : Measure ℂ}
    (hμ : μ ≤ Measure.map (fun t => b t) (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))))
    {f : ℂ → ℝ} (hf : Continuous f) : Integrable f μ := by
  have ht : Integrable (fun s : ℝ => f (b s.toNNReal))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hf.comp (b.continuous.comp continuous_real_toNNReal)).integrableOn_Icc
  have hν : Integrable (fun t : ℝ≥0 => f (b t)) (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
    (integrable_map_measure (hf.comp b.continuous).aestronglyMeasurable
      continuous_real_toNNReal.measurable.aemeasurable).2 ht
  exact ((integrable_map_measure hf.aestronglyMeasurable
    b.continuous.measurable.aemeasurable).2 hν).mono_measure hμ

/-- A clock approximation up to a time at most one splits into its inner, annular and exterior
occupation parts. -/
theorem lqgClockApprox_eq_regions {γ δ : ℝ} (hδ : δ ≤ 1/2) (h : ℝ → ℂ → ℝ) (j : ℕ)
    (hc : Continuous (h (dyadicScale j))) (b : ContinuousPath ℂ) {τ : ℝ≥0} (hτ : τ ≤ 1) :
    lqgClockApprox γ h (dyadicScale j) b τ =
      (∫ z, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          (dyadicScale j) ^ (γ ^ 2 / 2) * Real.exp (γ * h (dyadicScale j) z)) z
        ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic τ)))) +
      (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale j) ^ (γ ^ 2 / 2) * Real.exp (γ * h (dyadicScale j) z)) z
        ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic τ)))) +
      (∫ z, {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
          (dyadicScale j) ^ (γ ^ 2 / 2) * Real.exp (γ * h (dyadicScale j) z)) z
        ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic τ)))) := by
  let f : ℂ → ℝ := fun z => (dyadicScale j) ^ (γ ^ 2 / 2) * Real.exp (γ * h (dyadicScale j) z)
  have hf : Continuous f := continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))
  let μ : Measure ℂ := Measure.map (fun t => b t) ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic τ))
  have hμ : μ ≤ Measure.map (fun t => b t) (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  have hS1 : MeasurableSet {z : ℂ | ‖z‖ < δ} := measurableSet_lt measurable_norm measurable_const
  have hS2 : MeasurableSet {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hS3 : MeasurableSet {z : ℂ | 1/2 < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hi (S : Set ℂ) (hS : MeasurableSet S) : Integrable (S.indicator f) μ :=
    (integrable_of_le_unit_occupation' b hμ hf).indicator hS
  have hconv := intervalIntegral_path_eq_integral_occupation f hf.measurable b hτ
  show (∫ s in (0 : ℝ)..(τ : ℝ), f (b s.toNNReal)) =
    (∫ z, {z : ℂ | ‖z‖ < δ}.indicator f z ∂μ) +
    (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f z ∂μ) +
    (∫ z, {z : ℂ | 1/2 < ‖z‖}.indicator f z ∂μ)
  have hi12 : Integrable (fun z => {z : ℂ | ‖z‖ < δ}.indicator f z +
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f z) μ := (hi _ hS1).add (hi _ hS2)
  rw [hconv, ← integral_add (hi _ hS1) (hi _ hS2), ← integral_add hi12 (hi _ hS3)]
  congr 1
  funext z
  by_cases h1 : ‖z‖ < δ
  · have h2 : z ∉ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} := fun h => (not_le.mpr h1) h.1
    have h3 : z ∉ {z : ℂ | 1/2 < ‖z‖} := fun h => by
      have : ‖z‖ < 1/2 := lt_of_lt_of_le h1 hδ
      exact (lt_asymm h this)
    rw [Set.indicator_of_mem (show z ∈ {z : ℂ | ‖z‖ < δ} from h1), Set.indicator_of_notMem h2,
      Set.indicator_of_notMem h3]
    ring
  · by_cases h4 : ‖z‖ ≤ 1/2
    · have h2 : z ∈ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} := ⟨not_lt.mp h1, h4⟩
      have h3 : z ∉ {z : ℂ | 1/2 < ‖z‖} := fun h => (not_lt.mpr h4) h
      rw [Set.indicator_of_notMem (show z ∉ {z : ℂ | ‖z‖ < δ} from h1),
        Set.indicator_of_mem h2, Set.indicator_of_notMem h3]
      ring
    · have h2 : z ∉ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} := fun h => h4 h.2
      have h3 : z ∈ {z : ℂ | 1/2 < ‖z‖} := lt_of_not_ge h4
      rw [Set.indicator_of_notMem (show z ∉ {z : ℂ | ‖z‖ < δ} from h1),
        Set.indicator_of_notMem h2, Set.indicator_of_mem h3]
      ring


private theorem abs_sub_three_le (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ) :
    |(a₁ + b₁ + c₁) - (a₂ + b₂ + c₂)| ≤ |a₁ - a₂| + |b₁ - b₂| + |c₁ - c₂| := by
  rw [show (a₁ + b₁ + c₁) - (a₂ + b₂ + c₂) = (a₁ - a₂) + (b₁ - b₂) + (c₁ - c₂) by ring]
  exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)

/-- Expected exit times of the inserted clock from annular and exterior increment bounds:
for `0 < γ * α` and `γ ^ 2 / 2 < 2 - γ * α`, summable bounds on the expected annular and
exterior increments of the clocks stopped at the exit time from a smooth bounded domain and
capped at time one, uniform over starts in the domain, make every LQG clock from a fixed start
in the domain that is almost surely a time-change clock have, for almost every field, finite
expected LBM exit time equal to the limit of the expected Green integrals of the approximating
measures. -/
theorem ae_tendsto_clockApprox_green_expectedLBMExitTime_of_annular_exterior_increments
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hγ : 0 < γ) (hsub : γ ^ 2 / 2 < 2 - γ * α) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ ≤ 1/2) {D : Set ℂ} (hD : IsSmoothBoundedOpen D) {x : ℂ} (hx : x ∈ D)
    (cA cE : ℕ → ℝ≥0∞) (hcA : (∑' k, cA k) ≠ ⊤) (hcE : (∑' k, cE k) ≠ ⊤)
    (hA : ∀ (k : ℕ), ∀ y ∈ D, (∫⁻ p, ENNReal.ofReal
      |stoppedAnnularClock (fun z => (dyadicScale (k+2)) ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+2)) z)) δ (fun b => (min 1 (ContinuousPath.exitTime D b).toReal).toNNReal) p.2 -
        stoppedAnnularClock (fun z => (dyadicScale (k+1)) ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) δ (fun b => (min 1 (ContinuousPath.exitTime D b).toReal).toNNReal) p.2|
      ∂(P.prod (planarBrownianMotion y))) ≤ cA k)
    (hE : ∀ (k : ℕ), ∀ y ∈ D, (∫⁻ p, ENNReal.ofReal
      |(∫ z, {z : ℂ | 1/2 < ‖z‖}.indicator (fun z => (dyadicScale (k+2)) ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+2)) z)) z
          ∂(Measure.map (fun t => p.2 t) ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic ((min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal))))) -
        ∫ z, {z : ℂ | 1/2 < ‖z‖}.indicator (fun z => (dyadicScale (k+1)) ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) z
          ∂(Measure.map (fun t => p.2 t) ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic ((min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal))))|
      ∂(P.prod (planarBrownianMotion y))) ≤ cE k)
    (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hclock : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω))
    (hF : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω b)) :
    ∀ᵐ ω ∂P, expectedLBMExitTime (F ω) D x ≠ ⊤ ∧
      Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) y)))
        atTop (𝓝 (expectedLBMExitTime (F ω) D x)) := by
  have hDo : IsOpen D := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  obtain ⟨cI, hcI, hI⟩ :=
    exists_summable_uniform_inner_suboccupation_increment_bound hh hq0 hγ hsub hδ0 hδ
  let τD : ContinuousPath ℂ → ℝ≥0 := (fun b => (min 1 (ContinuousPath.exitTime D b).toReal).toNNReal)
  have hτD : Measurable τD :=
    (measurable_const.min (ContinuousPath.measurable_exitTime D hDo).ennreal_toReal).real_toNNReal
  have hτD1 (b : ContinuousPath ℂ) : τD b ≤ 1 := by
    have h := Real.toNNReal_le_toNNReal (min_le_left (1 : ℝ) (ContinuousPath.exitTime D b).toReal)
    simpa [τD] using h
  let μD : ContinuousPath ℂ → Measure ℂ := fun b =>
    Measure.map (fun t => b t) ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τD b)))
  have hμD (b : ContinuousPath ℂ) : μD b ≤ Measure.map (fun t => b t) (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  have hcont := ae_continuous_fieldCircleAverage hh α
  refine ae_tendsto_clockApprox_green_expectedLBMExitTime_fieldCircleAverage_of_unit_increments
    hh hD hx (fun k => cI k + cA k + cE k) ?_ ?_ F hclock hF
  · rw [ENNReal.tsum_add, ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hcI, hcA⟩, hcE⟩
  · intro k y hy
    have hS1 : MeasurableSet {z : ℂ | ‖z‖ < δ} := measurableSet_lt measurable_norm measurable_const
    have hS2 : MeasurableSet {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} :=
      (measurableSet_le measurable_const measurable_norm).inter
        (measurableSet_le measurable_norm measurable_const)
    let ΔI : Ω × ContinuousPath ℂ → ℝ := fun p =>
      (∫ z, {z : ℂ | ‖z‖ < δ}.indicator (fun z => (dyadicScale (k+2)) ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+2)) z)) z ∂(μD p.2)) -
        ∫ z, {z : ℂ | ‖z‖ < δ}.indicator (fun z => (dyadicScale (k+1)) ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) z ∂(μD p.2)
    let ΔA : Ω × ContinuousPath ℂ → ℝ := fun p =>
      stoppedAnnularClock (fun z => (dyadicScale (k+2)) ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+2)) z)) δ τD p.2 -
        stoppedAnnularClock (fun z => (dyadicScale (k+1)) ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) δ τD p.2
    let ΔE : Ω × ContinuousPath ℂ → ℝ := fun p =>
      (∫ z, {z : ℂ | 1/2 < ‖z‖}.indicator (fun z => (dyadicScale (k+2)) ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+2)) z)) z ∂(μD p.2)) -
        ∫ z, {z : ℂ | 1/2 < ‖z‖}.indicator (fun z => (dyadicScale (k+1)) ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) z ∂(μD p.2)
    have hmI : AEMeasurable (fun p => ENNReal.ofReal |ΔI p|) (P.prod (planarBrownianMotion y)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable
        ((aemeasurable_region_stopped_occupation hh γ α (k+2) hS1 τD hτD _).sub
          (aemeasurable_region_stopped_occupation hh γ α (k+1) hS1 τD hτD _)))
    have hmA : AEMeasurable (fun p => ENNReal.ofReal |ΔA p|) (P.prod (planarBrownianMotion y)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable
        ((aemeasurable_region_stopped_occupation hh γ α (k+2) hS2 τD hτD _).sub
          (aemeasurable_region_stopped_occupation hh γ α (k+1) hS2 τD hτD _)))
    have hmIA : AEMeasurable (fun p => ENNReal.ofReal |ΔI p| + ENNReal.ofReal |ΔA p|)
        (P.prod (planarBrownianMotion y)) := hmI.add hmA
    have hpt : ∀ᵐ p ∂(P.prod (planarBrownianMotion y)), ENNReal.ofReal
        |lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1)) (dyadicScale (k+2)) p.2
            (min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal -
          lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1)) (dyadicScale (k+1)) p.2
            (min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal| ≤
        (ENNReal.ofReal |ΔI p| + ENNReal.ofReal |ΔA p|) + ENNReal.ofReal |ΔE p| := by
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
        (ν := planarBrownianMotion y)).ae hcont] with p hp
      rw [lqgClockApprox_eq_regions hδ _ (k+2) (hp _ (dyadicScale_pos _)) p.2 (hτD1 p.2),
        lqgClockApprox_eq_regions hδ _ (k+1) (hp _ (dyadicScale_pos _)) p.2 (hτD1 p.2),
        ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
        ← ENNReal.ofReal_add (by positivity) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (abs_sub_three_le _ _ _ _ _ _)
    refine (lintegral_mono_ae hpt).trans ?_
    rw [lintegral_add_left' hmIA, lintegral_add_left' hmI]
    exact add_le_add (add_le_add (hI k y μD hμD) (hA k y hy)) (hE k y hy)

end HarmonicBalls
