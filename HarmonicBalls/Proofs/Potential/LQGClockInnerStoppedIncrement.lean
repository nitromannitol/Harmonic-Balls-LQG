import HarmonicBalls.Proofs.Potential.LQGClockInnerUniformStartCore
import HarmonicBalls.Proofs.Potential.LQGClockEnvelopeAnnularIncrement

/-! # Inner clock increments under sub-occupation measures, uniformly over the start

Fix a disc `‖z‖ < δ` around the insertion. For the inserted circle-average densities at the
dyadic scales `ε` and `ε / 2`, the difference of their integrals against any measure below
the unit-time occupation measure of a path splits into a field increment with the
singularly dominated weight `max (ε / 2) ‖z‖ ^ (-γ α)` and a nonnegative core supported in
`‖z‖ < ε`. The truncated second-moment estimate bounds the first part through the weighted
pair energy and the singular occupation, and the core is bounded by the uniform first-moment
estimate. All Brownian constants are uniform over the start, so the expected increments have
one summable bound for every start and every family of sub-occupation measures, whenever
`0 < γ * α` and `γ ^ 2 / 2 < 2 - γ * α`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

private theorem integrable_of_le_unit_occupation (b : ContinuousPath ℂ) {μ : Measure ℂ}
    (hμ : μ ≤ Measure.map (fun t => b t)
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))))
    {f : ℂ → ℝ} (hf : Continuous f) : Integrable f μ := by
  have ht : Integrable (fun s : ℝ => f (b s.toNNReal))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hf.comp (b.continuous.comp continuous_real_toNNReal)).integrableOn_Icc
  have hν : Integrable (fun t : ℝ≥0 => f (b t))
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
    (integrable_map_measure (hf.comp b.continuous).aestronglyMeasurable
      continuous_real_toNNReal.measurable.aemeasurable).2 ht
  exact ((integrable_map_measure hf.aestronglyMeasurable
    b.continuous.measurable.aemeasurable).2 hν).mono_measure hμ

set_option maxHeartbeats 400000 in
/-- The inner dyadic increments of the inserted field have a summable expected bound that is
uniform over the Brownian start and over families of sub-occupation measures. -/
theorem exists_summable_uniform_inner_suboccupation_increment_bound
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hγ : 0 < γ) (hsub : γ ^ 2 / 2 < 2 - γ * α)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1/2) :
    ∃ c : ℕ → ℝ≥0∞, (∑' k, c k) ≠ ⊤ ∧ ∀ (k : ℕ) (y : ℂ) (μ : ContinuousPath ℂ → Measure ℂ),
      (∀ b, μ b ≤ Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) →
      (∫⁻ p, ENNReal.ofReal |(∫ z, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          (dyadicScale (k+2)) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+2)) z)) z
            ∂(μ p.2)) -
        ∫ z, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          (dyadicScale (k+1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) z
            ∂(μ p.2)| ∂(P.prod (planarBrownianMotion y))) ≤ c k := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  set q : ℝ := γ * α with hqdef
  have hq2 : q < 2 := by linarith [sq_nonneg γ]
  obtain ⟨β, hβl, hβu⟩ := exists_between hsub
  have hβ0 : 0 < β := lt_of_le_of_lt (by positivity) hβl
  have hqβ : q + β < 2 := by linarith
  obtain ⟨θ, hγθ, hθ, hdecay⟩ := exists_annular_moment_exponent hγ hβl
  let pe : ℝ := (q + 2) / 2
  have hqpe : q < pe := by dsimp [pe]; linarith
  have hpe2 : pe < 2 := by dsimp [pe]; linarith
  obtain ⟨CW, hCW, hCWle⟩ := exists_planarBrownianMotion_unitSingularWeightedPairEnergy_le hq0 hβ0 hqβ
  obtain ⟨Co, hCo, hCole⟩ := exists_planarBrownianMotion_unit_singular_occupation_le hq0 hq2
  obtain ⟨C₂, hC₂, hC₂le⟩ := exists_uniform_inner_inserted_density_le hh γ α pe hq0 hqpe hpe2
  let κ₁ : ℝ := (β - γ ^ 2 + (2 * γ - θ) ^ 2 / 2) / 2
  let κ₂ : ℝ := (θ - γ) ^ 2 / 2
  have hκ₁ : 0 < κ₁ := by dsimp [κ₁]; positivity
  have hκ₂ : 0 < κ₂ := by
    have : 0 < θ - γ := by linarith
    dsimp [κ₂]; positivity
  let L : ℝ := Real.exp (γ ^ 2 * Real.log 2) - 1
  have hL : 0 ≤ L := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  let ε : ℕ → ℝ := fun k => dyadicScale (k+1)
  have hεpos (k : ℕ) : 0 < ε k := dyadicScale_pos _
  have hεhalf (k : ℕ) : ε k ≤ 1/2 := by
    dsimp [ε, dyadicScale]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hεstep (k : ℕ) : dyadicScale (k+2) = ε k / 2 := by
    dsimp [ε, dyadicScale]
    rw [show k + 2 = (k+1) + 1 by omega, pow_succ]
    ring
  let e₁ : ℕ → ℝ := fun k => Real.exp (Real.log (ε k) * κ₁)
  let e₂ : ℕ → ℝ := fun k => Real.exp (Real.log (ε k) * κ₂)
  let e₃ : ℕ → ℝ := fun k => Real.exp (Real.log (ε k) * (pe - q))
  have hsum (κ : ℝ) (hκ : 0 < κ) :
      Summable (fun k : ℕ => Real.exp (Real.log (ε k) * κ)) :=
    (summable_nat_add_iff 1).2 (LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hκ)
  let c : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (L * 2 ^ β / 2) * CW * ENNReal.ofReal (e₁ k) +
      ENNReal.ofReal (1/2) * ENNReal.ofReal (e₁ k) + 2 * Co * ENNReal.ofReal (e₂ k) +
      2 ^ q * C₂ * ENNReal.ofReal (e₃ k)
  have htsum (κ : ℝ) (hκ : 0 < κ) :
      (∑' k : ℕ, ENNReal.ofReal (Real.exp (Real.log (ε k) * κ))) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) (hsum κ hκ)]
    exact ENNReal.ofReal_ne_top
  have hq2top : (2 : ℝ≥0∞) ^ q ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq0.le (by norm_num)
  refine ⟨c, ?_, ?_⟩
  · simp only [c]
    rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left,
      ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCW.ne) (htsum κ₁ hκ₁)
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (htsum κ₁ hκ₁)
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hCo.ne) (htsum κ₂ hκ₂)
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hq2top hC₂.ne)
        (htsum (pe - q) (by linarith))
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let Sδ : Set ℂ := {z : ℂ | ‖z‖ < δ}
  have hSδ : MeasurableSet Sδ := measurableSet_lt measurable_norm measurable_const
  let E : ℝ → Ω → ℂ → ℝ := fun s ω z => s ^ (γ ^ 2 / 2) * Real.exp (γ * (H ω s z - H ω 1 0))
  let m : ℝ → ℂ → ℝ := fun s z => Real.exp (-q * Real.log (max s ‖z‖))
  let fH : ℝ → Ω → ℂ → ℝ := fun s ω z => E s ω z * m s z
  have hEc (s : ℝ) (hs : 0 < s) (ω : Ω) : Continuous (E s ω) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((hHc ω s hs).sub continuous_const)))
  have hmc (s : ℝ) (hs : 0 < s) : Continuous (m s) :=
    Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hs).ne')))
  have hEm (s : ℝ) (hs : 0 < s) : Measurable (fun p : Ω × ℂ => E s p.1 p.2) := by
    have h1 : Measurable (fun p : Ω × ℂ => H p.1 s p.2) := (hHm s hs).comp measurable_swap
    have h2 : Measurable (fun p : Ω × ℂ => H p.1 1 0) :=
      (hHm 1 one_pos).comp ((measurable_const : Measurable fun _ : Ω × ℂ => (0 : ℂ)).prodMk
        measurable_fst)
    exact measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul (h1.sub h2)))
  have hmm (s : ℝ) (hs : 0 < s) : Measurable (m s) := (hmc s hs).measurable
  have hE0 (s : ℝ) (hs : 0 ≤ s) (ω : Ω) (z : ℂ) : 0 ≤ E s ω z :=
    mul_nonneg (Real.rpow_nonneg hs _) (Real.exp_pos _).le
  have hm0 (s : ℝ) (z : ℂ) : 0 ≤ m s z := (Real.exp_pos _).le
  have hgood : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → ∀ z : ℂ, s ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z) = fH s ω z := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec s hs z
    rw [← hrec s z hs, ← hω s z, ← hω 1 0]
    simp only [fH, E, m]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    rw [hqdef]
    ring
  have hmle (s : ℝ) (hs : 0 < s) (z : ℂ) : m s z ≤ s ^ (-q) := by
    simp only [m]
    rw [Real.rpow_def_of_pos hs]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log s ≤ Real.log (max s ‖z‖) :=
      Real.log_le_log hs (le_max_left _ _)
    nlinarith
  have hm_half (s : ℝ) (hs : 0 < s) (z : ℂ) : m (s/2) z ≤ 2 ^ q * m s z := by
    simp only [m]
    have h2 : (2 : ℝ) ^ q = Real.exp (q * Real.log 2) := by
      rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    rw [h2, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hpos : 0 < max (s/2) ‖z‖ := lt_max_of_lt_left (by linarith)
    have hle : max s ‖z‖ ≤ 2 * max (s/2) ‖z‖ := by
      rcases le_total (s/2) ‖z‖ with h | h
      · rw [max_eq_right h]
        exact max_le (by linarith) (by linarith [norm_nonneg z])
      · rw [max_eq_left h]
        exact max_le (by linarith) (by linarith)
    have hlog : Real.log (max s ‖z‖) ≤ Real.log 2 + Real.log (max (s/2) ‖z‖) := by
      rw [← Real.log_mul (by norm_num) hpos.ne']
      exact Real.log_le_log (lt_max_of_lt_left hs) hle
    nlinarith
  have hm_mono (s : ℝ) (hs : 0 < s) (z : ℂ) : m s z ≤ m (s/2) z := by
    simp only [m]
    apply Real.exp_le_exp.mpr
    have hlog : Real.log (max (s/2) ‖z‖) ≤ Real.log (max s ‖z‖) :=
      Real.log_le_log (lt_max_of_lt_left (by linarith)) (max_le_max (by linarith) le_rfl)
    nlinarith
  have hm_eq (s : ℝ) (z : ℂ) (hz : s ≤ ‖z‖) : m (s/2) z = m s z := by
    have hs2 : s/2 ≤ ‖z‖ := by
      rcases le_or_gt 0 s with h | h
      · linarith
      · linarith [norm_nonneg z]
    simp only [m, max_eq_right hz, max_eq_right hs2]
  have hscale : ∀ r : ℝ, 0 < r → r ≤ 1/2 → ∀ (y : ℂ) (μ : ContinuousPath ℂ → Measure ℂ),
      (∀ b, μ b ≤ Measure.map (fun t => b t) (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) →
      (∫⁻ p, ENNReal.ofReal |(∫ z, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          (r/2) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (r/2) z)) z ∂(μ p.2)) -
        ∫ z, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          r ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) z ∂(μ p.2)|
          ∂(P.prod (planarBrownianMotion y))) ≤
        ENNReal.ofReal (L * 2 ^ β / 2) * CW * ENNReal.ofReal (Real.exp (Real.log r * κ₁)) +
          ENNReal.ofReal (1/2) * ENNReal.ofReal (Real.exp (Real.log r * κ₁)) +
          2 * Co * ENNReal.ofReal (Real.exp (Real.log r * κ₂)) +
          2 ^ q * C₂ * ENNReal.ofReal (Real.exp (Real.log r * (pe - q))) := by
    intro r hr hr2 y μ hμ
    have hr2' : 0 < r / 2 := by linarith
    have hfin (b : ContinuousPath ℂ) : IsFiniteMeasure (μ b) := by
      let : IsProbabilityMeasure (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
        ⟨by simp [Measure.map_apply continuous_real_toNNReal.measurable]⟩
      have : IsProbabilityMeasure (Measure.map (fun t => b t) (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) := inferInstance
      exact isFiniteMeasure_of_le _ (hμ b)
    let Sr : Set ℂ := {z : ℂ | ‖z‖ < r}
    have hSr : MeasurableSet Sr := measurableSet_lt measurable_norm measurable_const
    -- the increment in terms of the jointly measurable version
    let JH : Ω → ContinuousPath ℂ → ℝ := fun ω b =>
      (∫ z, Sδ.indicator (fH (r/2) ω) z ∂(μ b)) - ∫ z, Sδ.indicator (fH r ω) z ∂(μ b)
    have hJ : ∀ᵐ p ∂(P.prod (planarBrownianMotion y)),
        ENNReal.ofReal |(∫ z, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          (r/2) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (r/2) z)) z ∂(μ p.2)) -
        ∫ z, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          r ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) z ∂(μ p.2)| =
        ENNReal.ofReal |JH p.1 p.2| := by
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
        (ν := planarBrownianMotion y)).ae hgood] with p hp
      rw [show (fun z => (r/2) ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (r/2) z)) = fH (r/2) p.1 from
          funext (hp _ hr2'),
        show (fun z => r ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) = fH r p.1 from
          funext (hp _ hr)]
    -- envelopes at the start y
    let W : ContinuousPath ℂ → ℝ≥0∞ := unitSingularWeightedPairEnergy 0 q β
    have hWm : Measurable W := measurable_unitSingularWeightedPairEnergy 0 q β
    have hWi : (∫⁻ b, W b ∂(planarBrownianMotion y)) ≠ ⊤ :=
      ((hCWle y 0).trans_lt hCW).ne
    obtain ⟨-, hHenv⟩ := integrable_toReal_pair_envelope_of_lintegral y 0 (q := q) (β := β) W
      hWm.aemeasurable hWi (Filter.Eventually.of_forall fun b r' hr' _ =>
        (unitSingularPairNear_le_rpow_mul_weightedPairEnergy 0 hβ0 hr' b).trans_eq
          (mul_comm _ _))
    have h4 := ae_brownian_singular_submeasure_field_increment_le_of_envelope hh y 0 hq0 hq2
      (fun b => (W b).toReal) hHenv
    let R : ContinuousPath ℂ → ℝ := fun b =>
      ((Real.exp (γ^2*Real.log 2)-1)*
        Real.exp (Real.log 1 * (2*γ^2-(2*γ-θ)^2/2))*
        (2^β * (W b).toReal)+1)/2 *
        Real.exp (Real.log r * ((β-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope 0 q b *
        Real.exp (Real.log 1 * (γ^2/2-(θ-γ)^2/2))*
        Real.exp (Real.log r * ((θ-γ)^2/2))
    let X : ContinuousPath ℂ → ℝ≥0∞ := fun b => ∫⁻ ω, ∫⁻ z, Sr.indicator
      (fun z => ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z))) z ∂(μ b) ∂P
    have hpath : ∀ᵐ b ∂(planarBrownianMotion y),
        (∫⁻ ω, ENNReal.ofReal |JH ω b| ∂P) ≤ ENNReal.ofReal (R b) + 2 ^ q * X b := by
      filter_upwards [h4] with b hb4
      have : IsFiniteMeasure (μ b) := hfin b
      have hint (F : ℂ → ℝ) (hF : Continuous F) (S : Set ℂ) (hS : MeasurableSet S) :
          Integrable (S.indicator F) (μ b) :=
        (integrable_of_le_unit_occupation b (hμ b) hF).indicator hS
      have hfc (s : ℝ) (hs : 0 < s) (ω : Ω) : Continuous (fH s ω) := (hEc s hs ω).mul (hmc s hs)
      have hEle (s : ℝ) (hs : 0 < s) (hs2 : s ≤ 1/2) (ω : Ω) (z : ℂ) (hz : z ∈ Sδ) :
          E s ω z ≤ fH s ω z := by
        have hmax : max s ‖z‖ ≤ 1/2 := max_le hs2 (le_trans (le_of_lt hz) hδ)
        have hpos : 0 < max s ‖z‖ := lt_max_of_lt_left hs
        have hlog : Real.log (max s ‖z‖) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
        have hm1 : 1 ≤ m s z := Real.one_le_exp (by nlinarith)
        calc E s ω z = E s ω z * 1 := (mul_one _).symm
          _ ≤ E s ω z * m s z := mul_le_mul_of_nonneg_left hm1 (hE0 s hs.le ω z)
      let F₁ : Ω → ℝ := fun ω =>
        ∫ z, Sδ.indicator (fun z => m (r/2) z * (E (r/2) ω z - E r ω z)) z ∂(μ b)
      let F₂ : Ω → ℝ := fun ω =>
        ∫ z, Sδ.indicator (fun z => E r ω z * (m (r/2) z - m r z)) z ∂(μ b)
      let Core : Ω → ℝ := fun ω => ∫ z, Sr.indicator (fH r ω) z ∂(μ b)
      have hi1 (ω : Ω) : Integrable (Sδ.indicator
          (fun z => m (r/2) z * (E (r/2) ω z - E r ω z))) (μ b) :=
        hint (fun z => m (r/2) z * (E (r/2) ω z - E r ω z))
          ((hmc _ hr2').mul ((hEc _ hr2' ω).sub (hEc _ hr ω))) Sδ hSδ
      have hi2 (ω : Ω) : Integrable (Sδ.indicator
          (fun z => E r ω z * (m (r/2) z - m r z))) (μ b) :=
        hint (fun z => E r ω z * (m (r/2) z - m r z))
          ((hEc _ hr ω).mul ((hmc _ hr2').sub (hmc _ hr))) Sδ hSδ
      have hsplit (ω : Ω) : JH ω b = F₁ ω + F₂ ω := by
        simp only [JH, F₁, F₂]
        rw [← integral_sub (hint _ (hfc _ hr2' ω) Sδ hSδ) (hint _ (hfc _ hr ω) Sδ hSδ),
          ← integral_add (hi1 ω) (hi2 ω)]
        congr 1
        funext z
        by_cases hz : z ∈ Sδ
        · simp only [Set.indicator_of_mem hz, fH]
          ring
        · simp only [Set.indicator_of_notMem hz]
          ring
      have hF₂0 (ω : Ω) : 0 ≤ F₂ ω := by
        apply integral_nonneg
        intro z
        by_cases hz : z ∈ Sδ
        · rw [Set.indicator_of_mem hz]
          exact mul_nonneg (hE0 r hr.le ω z) (sub_nonneg.mpr (hm_mono r hr z))
        · simp [Set.indicator_of_notMem hz]
      have hF₂le (ω : Ω) : F₂ ω ≤ 2 ^ q * Core ω := by
        simp only [F₂, Core]
        rw [← integral_const_mul]
        apply integral_mono (hi2 ω) ((hint _ (hfc _ hr ω) Sr hSr).const_mul _)
        intro z
        have h3 := hE0 r hr.le ω z
        have h2 := hm0 r z
        have h1 := hm_half r hr z
        have hq2pos : 0 < (2 : ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) _
        simp only [Set.indicator_apply, fH]
        by_cases hzr : ‖z‖ < r
        · have hz' : z ∈ Sr := hzr
          by_cases hz : z ∈ Sδ
          · simp only [hz, hz', ↓reduceIte]
            nlinarith [mul_nonneg h3 (sub_nonneg.mpr h1), mul_nonneg h3 h2]
          · simp only [hz, hz', ↓reduceIte]
            positivity
        · have hz' : z ∉ Sr := hzr
          by_cases hz : z ∈ Sδ
          · simp only [hz, hz', ↓reduceIte, hm_eq r z (not_lt.mp hzr), sub_self, mul_zero, le_refl]
          · simp only [hz, hz', ↓reduceIte, mul_zero, le_refl]
      -- measurability in the field
      have hGm (f : Ω → ℂ → ℝ) (hf : Measurable (fun p : Ω × ℂ => f p.1 p.2)) (S : Set ℂ)
          (hS : MeasurableSet S) :
          StronglyMeasurable (fun ω => ∫ z, S.indicator (f ω) z ∂(μ b)) := by
        have h : (fun p : Ω × ℂ => S.indicator (f p.1) p.2) =
            (Prod.snd ⁻¹' S).indicator (fun p : Ω × ℂ => f p.1 p.2) := by
          funext p
          by_cases hp : p.2 ∈ S
          · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' S from hp)]
          · rw [Set.indicator_of_notMem hp,
              Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' S from hp)]
        have hm : Measurable (fun p : Ω × ℂ => S.indicator (f p.1) p.2) := by
          rw [h]
          exact hf.indicator (measurable_snd hS)
        exact hm.stronglyMeasurable.integral_prod_right'
      have hfHm (t : ℝ) (ht : 0 < t) : Measurable (fun p : Ω × ℂ => fH t p.1 p.2) :=
        (hEm t ht).mul ((hmm t ht).comp measurable_snd)
      -- the expected inserted occupations are finite
      let T : ℝ → Ω → ℝ := fun t ω => ∫ z, Sδ.indicator (fH t ω) z ∂(μ b)
      have hTi (t : ℝ) (ht : 0 < t) (ht2 : t ≤ 1/2) : Integrable (T t) P := by
        refine ⟨(hGm (fH t) (hfHm t ht) Sδ hSδ).aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_enorm]
        have hT0 (ω : Ω) : 0 ≤ T t ω := integral_nonneg (fun z => by
          by_cases hz : z ∈ Sδ
          · rw [Set.indicator_of_mem hz]
            exact mul_nonneg (hE0 t ht.le ω z) (hm0 t z)
          · simp [Set.indicator_of_notMem hz])
        have heq1 : (∫⁻ ω, ‖T t ω‖ₑ ∂P) = ∫⁻ ω, ∫⁻ z, Sδ.indicator
            (fun z => ENNReal.ofReal (t ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z))) z ∂(μ b) ∂P := by
          apply lintegral_congr_ae
          filter_upwards [hgood] with ω hω
          rw [Real.enorm_of_nonneg (hT0 ω), ofReal_integral_eq_lintegral_ofReal
            (hint _ (hfc t ht ω) Sδ hSδ) (Filter.Eventually.of_forall fun z => by
              by_cases hz : z ∈ Sδ
              · rw [Set.indicator_of_mem hz]
                exact mul_nonneg (hE0 t ht.le ω z) (hm0 t z)
              · simp [Set.indicator_of_notMem hz])]
          apply lintegral_congr
          intro z
          by_cases hz : z ∈ Sδ
          · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hω t ht z]
          · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, ENNReal.ofReal_zero]
        rw [heq1, lintegral_inner_inserted_density_eq hh ht ht2 hδ γ α (μ b)]
        refine lt_of_le_of_lt (b := ∫⁻ _z, ENNReal.ofReal (t ^ (-q)) ∂(μ b)) ?_ ?_
        · apply lintegral_mono
          intro z
          by_cases hz : z ∈ Sδ
          · rw [Set.indicator_of_mem hz]
            apply ENNReal.ofReal_le_ofReal
            have := hmle t ht z
            simpa [m, hqdef, neg_mul] using this
          · rw [Set.indicator_of_notMem hz]
            exact zero_le
        · rw [lintegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
      have hr2'' : r/2 ≤ 1/2 := by linarith
      have hF₁m : StronglyMeasurable F₁ :=
        hGm (fun ω z => m (r/2) z * (E (r/2) ω z - E r ω z))
          (((hmm _ hr2').comp measurable_snd).mul ((hEm _ hr2').sub (hEm _ hr))) Sδ hSδ
      have hF₁i : Integrable F₁ P := by
        refine Integrable.mono' (((hTi (r/2) hr2' hr2'').add (hTi r hr hr2)).const_mul
          ((r/2) ^ (-q))) hF₁m.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
        calc ‖F₁ ω‖ ≤ ∫ z, ‖Sδ.indicator (fun z => m (r/2) z * (E (r/2) ω z - E r ω z)) z‖
              ∂(μ b) := norm_integral_le_integral_norm _
          _ ≤ ∫ z, (r/2) ^ (-q) * (Sδ.indicator (fH (r/2) ω) z + Sδ.indicator (fH r ω) z)
              ∂(μ b) := by
            apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              (((hint _ (hfc _ hr2' ω) Sδ hSδ).add (hint _ (hfc _ hr ω) Sδ hSδ)).const_mul _)
            filter_upwards with z
            simp only [Pi.add_apply]
            by_cases hz : z ∈ Sδ
            · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Set.indicator_of_mem hz,
                Real.norm_eq_abs, abs_mul, abs_of_nonneg (hm0 _ z)]
              have hE1 := hE0 (r/2) hr2'.le ω z
              have hE2 := hE0 r hr.le ω z
              have habs : |E (r/2) ω z - E r ω z| ≤ E (r/2) ω z + E r ω z :=
                abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
              calc m (r/2) z * |E (r/2) ω z - E r ω z| ≤ m (r/2) z * (E (r/2) ω z + E r ω z) :=
                    mul_le_mul_of_nonneg_left habs (hm0 _ z)
                _ ≤ (r/2) ^ (-q) * (E (r/2) ω z + E r ω z) :=
                    mul_le_mul_of_nonneg_right (hmle _ hr2' z) (by linarith)
                _ ≤ (r/2) ^ (-q) * (fH (r/2) ω z + fH r ω z) :=
                    mul_le_mul_of_nonneg_left (add_le_add (hEle _ hr2' hr2'' ω z hz)
                      (hEle _ hr hr2 ω z hz)) (Real.rpow_nonneg hr2'.le _)
            · simp [Set.indicator_of_notMem hz]
          _ = (r/2) ^ (-q) * (T (r/2) ω + T r ω) := by
            rw [integral_const_mul, integral_add (hint _ (hfc _ hr2' ω) Sδ hSδ)
              (hint _ (hfc _ hr ω) Sδ hSδ)]
      have hgm : Measurable (Sδ.indicator (m (r/2))) := (hmm _ hr2').indicator hSδ
      have hgq : ∀ y, ENNReal.ofReal |Sδ.indicator (m (r/2)) y| ≤
          (ENNReal.ofReal ‖y - 0‖) ^ (-q) := by
        intro y
        by_cases hy : y ∈ Sδ
        · rw [Set.indicator_of_mem hy, abs_of_nonneg (hm0 _ y), sub_zero]
          by_cases hy0 : y = 0
          · rw [hy0, norm_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith)]
            exact le_top
          · have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
            rw [ENNReal.ofReal_rpow_of_pos hpos]
            apply ENNReal.ofReal_le_ofReal
            simp only [m]
            rw [Real.rpow_def_of_pos hpos]
            apply Real.exp_le_exp.mpr
            have := Real.log_le_log hpos (le_max_right (r/2) ‖y‖)
            nlinarith
        · rw [Set.indicator_of_notMem hy, abs_zero, ENNReal.ofReal_zero]
          exact zero_le
      have hgs : ∀ y, Sδ.indicator (m (r/2)) y ≠ 0 → ‖y‖ ≤ 1 - 1/2 := by
        intro y hy
        by_contra h
        apply hy
        apply Set.indicator_of_notMem
        intro hyS
        have : ‖y‖ < δ := hyS
        linarith
      have h4b := hb4 (Sδ.indicator (m (r/2))) hgm hgq (μ b) (hμ b) (R := 1) (γ := γ) (θ := θ)
        one_pos hγθ.le hθ.le hgs r hr hr2
      have hF₁int : (∫ ω, |F₁ ω| ∂P) ≤ R b := by
        refine le_trans (le_of_eq ?_) h4b
        apply integral_congr_ae
        filter_upwards [hHae] with ω hω
        simp only [F₁]
        congr 1
        congr 1
        funext y
        by_cases hy : y ∈ Sδ
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
          simp only [E, hω]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
      have hCore0 (ω : Ω) : 0 ≤ Core ω := integral_nonneg (fun z => by
        by_cases hz : z ∈ Sr
        · rw [Set.indicator_of_mem hz]
          exact mul_nonneg (hE0 r hr.le ω z) (hm0 r z)
        · simp [Set.indicator_of_notMem hz])
      have hCoreX : (∫⁻ ω, ENNReal.ofReal (Core ω) ∂P) = X b := by
        apply lintegral_congr_ae
        filter_upwards [hgood] with ω hω
        rw [ofReal_integral_eq_lintegral_ofReal (hint _ (hfc r hr ω) Sr hSr)
          (Filter.Eventually.of_forall fun z => by
            by_cases hz : z ∈ Sr
            · rw [Set.indicator_of_mem hz]
              exact mul_nonneg (hE0 r hr.le ω z) (hm0 r z)
            · simp [Set.indicator_of_notMem hz])]
        apply lintegral_congr
        intro z
        by_cases hz : z ∈ Sr
        · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hω r hr z]
        · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, ENNReal.ofReal_zero]
      have hptw (ω : Ω) : ENNReal.ofReal |JH ω b| ≤ ENNReal.ofReal |F₁ ω| +
          ENNReal.ofReal ((2 : ℝ) ^ q) * ENNReal.ofReal (Core ω) := by
        have hq2pos : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
        rw [← ENNReal.ofReal_mul hq2pos,
          ← ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hq2pos (hCore0 ω))]
        apply ENNReal.ofReal_le_ofReal
        rw [hsplit ω]
        calc |F₁ ω + F₂ ω| ≤ |F₁ ω| + |F₂ ω| := abs_add_le _ _
          _ = |F₁ ω| + F₂ ω := by rw [abs_of_nonneg (hF₂0 ω)]
          _ ≤ |F₁ ω| + 2 ^ q * Core ω := by linarith [hF₂le ω]
      have h2q : ENNReal.ofReal ((2 : ℝ) ^ q) = (2 : ℝ≥0∞) ^ q := by
        rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      calc (∫⁻ ω, ENNReal.ofReal |JH ω b| ∂P) ≤ ∫⁻ ω, (ENNReal.ofReal |F₁ ω| +
            ENNReal.ofReal ((2 : ℝ) ^ q) * ENNReal.ofReal (Core ω)) ∂P := lintegral_mono hptw
        _ = (∫⁻ ω, ENNReal.ofReal |F₁ ω| ∂P) +
            ENNReal.ofReal ((2 : ℝ) ^ q) * ∫⁻ ω, ENNReal.ofReal (Core ω) ∂P := by
          rw [lintegral_add_left hF₁m.measurable.abs.ennreal_ofReal,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (R b) + 2 ^ q * X b := by
          rw [hCoreX, h2q, ← ofReal_integral_eq_lintegral_ofReal hF₁i.abs
            (Filter.Eventually.of_forall fun _ => abs_nonneg _)]
          exact add_le_add (ENNReal.ofReal_le_ofReal hF₁int) le_rfl
    let e₁r : ℝ := Real.exp (Real.log r * κ₁)
    let e₂r : ℝ := Real.exp (Real.log r * κ₂)
    let occ : ContinuousPath ℂ → ℝ≥0∞ := fun b =>
      ∫⁻ t : ℝ≥0, (ENNReal.ofReal ‖b t - 0‖) ^ (-q) ∂(Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
    have hoccm : Measurable occ := by
      have hf : Measurable (fun p : ContinuousPath ℂ × ℝ≥0 =>
          (ENNReal.ofReal ‖p.1 p.2 - 0‖) ^ (-q)) := by fun_prop
      exact Measurable.lintegral_prod_right hf
    have hRb (b : ContinuousPath ℂ) : R b = (L * 2 ^ β / 2) * (W b).toReal * e₁r +
        (1/2) * e₁r + 2 * (occ b).toReal * e₂r := by
      simp only [R, Real.log_one, zero_mul, Real.exp_zero, mul_one, unitSingularOccupationEnvelope,
        e₁r, e₂r, occ, L, κ₁, κ₂]
      ring
    have hR_le (b : ContinuousPath ℂ) : ENNReal.ofReal (R b) ≤
        ENNReal.ofReal (L * 2 ^ β / 2) * W b * ENNReal.ofReal e₁r +
          ENNReal.ofReal (1/2) * ENNReal.ofReal e₁r + 2 * occ b * ENNReal.ofReal e₂r := by
      have hA : 0 ≤ L * 2 ^ β / 2 := by positivity
      have he₁ : 0 ≤ e₁r := (Real.exp_pos _).le
      have he₂ : 0 ≤ e₂r := (Real.exp_pos _).le
      rw [hRb, ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hA,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by norm_num)]
      gcongr
      · exact ENNReal.ofReal_toReal_le
      · norm_num
      · exact ENNReal.ofReal_toReal_le
    have hRm : Measurable (fun b => ENNReal.ofReal (R b)) := by
      have : Measurable R := by
        simp only [R, unitSingularOccupationEnvelope]
        fun_prop
      exact this.ennreal_ofReal
    have hRint : (∫⁻ b, ENNReal.ofReal (R b) ∂(planarBrownianMotion y)) ≤
        ENNReal.ofReal (L * 2 ^ β / 2) * CW * ENNReal.ofReal e₁r +
          ENNReal.ofReal (1/2) * ENNReal.ofReal e₁r + 2 * Co * ENNReal.ofReal e₂r := by
      calc
        _ ≤ ∫⁻ b, (ENNReal.ofReal (L * 2 ^ β / 2) * W b * ENNReal.ofReal e₁r +
            ENNReal.ofReal (1/2) * ENNReal.ofReal e₁r + 2 * occ b * ENNReal.ofReal e₂r)
              ∂(planarBrownianMotion y) := lintegral_mono hR_le
        _ = ENNReal.ofReal (L * 2 ^ β / 2) * (∫⁻ b, W b ∂(planarBrownianMotion y)) *
              ENNReal.ofReal e₁r + ENNReal.ofReal (1/2) * ENNReal.ofReal e₁r +
            2 * (∫⁻ b, occ b ∂(planarBrownianMotion y)) * ENNReal.ofReal e₂r := by
          rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
            lintegral_const, measure_univ, mul_one, lintegral_mul_const _ (by fun_prop),
            lintegral_const_mul _ hWm, lintegral_mul_const _ (by fun_prop),
            lintegral_const_mul _ hoccm]
        _ ≤ _ := by
          gcongr
          · exact hCWle y 0
          · exact hCole y 0
    have hXint : (∫⁻ b, X b ∂(planarBrownianMotion y)) ≤
        C₂ * ENNReal.ofReal (Real.exp (Real.log r * (pe - q))) := by
      have h := hC₂le y hr hr2 hr hr2 μ (fun b => by have := hfin b; infer_instance) hμ
      have hconv : ENNReal.ofReal r ^ (pe - γ * α) =
          ENNReal.ofReal (Real.exp (Real.log r * (pe - q))) := by
        rw [ENNReal.ofReal_rpow_of_pos hr, Real.rpow_def_of_pos hr, hqdef]
      rw [hconv, mul_comm] at h
      exact h
    calc
      _ = ∫⁻ p, ENNReal.ofReal |JH p.1 p.2| ∂(P.prod (planarBrownianMotion y)) :=
        lintegral_congr_ae hJ
      _ ≤ ∫⁻ b, ∫⁻ ω, ENNReal.ofReal |JH ω b| ∂P ∂(planarBrownianMotion y) := by
        rw [← lintegral_prod_swap]
        exact lintegral_prod_le _
      _ ≤ ∫⁻ b, (ENNReal.ofReal (R b) + 2 ^ q * X b) ∂(planarBrownianMotion y) :=
        lintegral_mono_ae hpath
      _ = (∫⁻ b, ENNReal.ofReal (R b) ∂(planarBrownianMotion y)) +
          2 ^ q * ∫⁻ b, X b ∂(planarBrownianMotion y) := by
        rw [lintegral_add_left hRm, lintegral_const_mul' _ _ hq2top]
      _ ≤ (ENNReal.ofReal (L * 2 ^ β / 2) * CW * ENNReal.ofReal e₁r +
          ENNReal.ofReal (1/2) * ENNReal.ofReal e₁r + 2 * Co * ENNReal.ofReal e₂r) +
          2 ^ q * (C₂ * ENNReal.ofReal (Real.exp (Real.log r * (pe - q)))) :=
        add_le_add hRint (mul_le_mul_of_nonneg_left hXint zero_le)
      _ = _ := by ring
  intro k y μ hμ
  have h := hscale (ε k) (hεpos k) (hεhalf k) y μ hμ
  rw [hεstep k]
  exact h

end HarmonicBalls
