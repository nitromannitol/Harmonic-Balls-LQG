import Mathlib
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proposed.DuplantierMillerSheffield
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedFirstMoment
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedFatou
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmTotalMass
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleAverageJointMeasurable

/-! # Route (A), Palm identity: the marked LQG mass has the Lebesgue first moment

For the γ-LQG measure `μ_g` of the whole-plane GFF (`α₀ = 0`), `E μ_g(η) = ∫ η` for `0 ≤ η ∈ C_c(B_1)`. The upper bound
is the Fatou bound `lintegral_lqgMeasure_le` (MarkedFatou.lean). For the lower bound, the cut-offs
`χ_m(z) = min 1 (max 0 (m (1 - |z|) - 1))` increase to `1_{B_1}`; the total mass `E μ_g(B_1) = π`
(`integral_measure_ball_eq_pi`, from the staged printed unnormalized Prop) gives `E μ_g(χ_m) → π = ∫ χ_m`, and Fatou
applied to `c χ_m - η ≥ 0` gives `E μ_g(η) ≥ ∫ η - c (∫ χ_m - E μ_g(χ_m))`. This is the step "ν = d²z on B_1" of
r10 `l:r9-marked` (sentence "Both measures have total mass π, so their nonnegative difference has mass zero").
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HarmonicBalls

/-- The cut-off `χ_m(z) = min 1 (max 0 (m (1 - |z|) - 1))`: equal to `1` on `|z| ≤ 1 - 2/m`, to `0` on
`|z| ≥ 1 - 1/m`, increasing in `m`. -/
noncomputable def cutoffBall (m : ℕ) (z : ℂ) : ℝ := min 1 (max 0 ((m : ℝ) * (1 - ‖z‖) - 1))

theorem cutoffBall_continuous (m : ℕ) : Continuous (cutoffBall m) := by
  unfold cutoffBall
  fun_prop

theorem cutoffBall_nonneg (m : ℕ) (z : ℂ) : 0 ≤ cutoffBall m z :=
  le_min zero_le_one (le_max_left _ _)

theorem cutoffBall_le_one (m : ℕ) (z : ℂ) : cutoffBall m z ≤ 1 :=
  min_le_left _ _

theorem cutoffBall_eq_zero_of_one_le (m : ℕ) {z : ℂ} (hz : 1 ≤ ‖z‖) : cutoffBall m z = 0 := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (m : ℝ) * (1 - ‖z‖) ≤ 0 := by nlinarith
  unfold cutoffBall
  rw [max_eq_left (show (m : ℝ) * (1 - ‖z‖) - 1 ≤ 0 by linarith), min_eq_right zero_le_one]

theorem cutoffBall_eq_zero_of_ge {m : ℕ} (hm : 1 ≤ m) {z : ℂ} (hz : 1 - 1 / (m : ℝ) ≤ ‖z‖) :
    cutoffBall m z = 0 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < m := by linarith
  have h1 : (m : ℝ) * (1 - ‖z‖) ≤ 1 := by
    have h2 : 1 - ‖z‖ ≤ 1 / (m : ℝ) := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hpos.le
    rwa [mul_one_div_cancel hpos.ne'] at h3
  unfold cutoffBall
  rw [max_eq_left (show (m : ℝ) * (1 - ‖z‖) - 1 ≤ 0 by linarith), min_eq_right zero_le_one]

theorem cutoffBall_eq_one_of_le (m : ℕ) {z : ℂ} (hz : 2 ≤ (m : ℝ) * (1 - ‖z‖)) :
    cutoffBall m z = 1 := by
  unfold cutoffBall
  rw [min_eq_left (le_max_of_le_right (show (1 : ℝ) ≤ (m : ℝ) * (1 - ‖z‖) - 1 by linarith))]

theorem cutoffBall_monotone (z : ℂ) : Monotone fun m : ℕ => cutoffBall m z := by
  intro m m' hmm
  by_cases hz : 1 ≤ ‖z‖
  · simp only [cutoffBall_eq_zero_of_one_le m hz, cutoffBall_eq_zero_of_one_le m' hz, le_refl]
  · have hz' : ‖z‖ < 1 := not_le.1 hz
    have h : (m : ℝ) * (1 - ‖z‖) ≤ (m' : ℝ) * (1 - ‖z‖) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmm) (by linarith)
    unfold cutoffBall
    exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

theorem tendsto_cutoffBall (z : ℂ) :
    Tendsto (fun m : ℕ => cutoffBall m z) atTop
      (𝓝 ((ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ) z)) := by
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · rw [indicator_of_mem hz, Pi.one_apply]
    have hz' : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
    have hpos : 0 < 1 - ‖z‖ := by linarith
    obtain ⟨N, hN⟩ := exists_nat_ge (2 / (1 - ‖z‖))
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with m hm
    have h2 : 2 / (1 - ‖z‖) ≤ (m : ℝ) := le_trans hN (by exact_mod_cast hm)
    exact (cutoffBall_eq_one_of_le m ((div_le_iff₀ hpos).1 h2)).symm
  · rw [indicator_of_notMem hz]
    have hz' : 1 ≤ ‖z‖ := by simpa [mem_ball_zero_iff] using hz
    have hfun : (fun m : ℕ => cutoffBall m z) = fun _ => (0 : ℝ) :=
      funext fun m => cutoffBall_eq_zero_of_one_le m hz'
    rw [hfun]
    exact tendsto_const_nhds

theorem cutoffBall_hasCompactSupport (m : ℕ) : HasCompactSupport (cutoffBall m) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) 1) fun _ hz =>
    cutoffBall_eq_zero_of_one_le m
      (le_of_lt (not_le.1 (fun h => hz (mem_closedBall_zero_iff.2 h))))

theorem cutoffBall_le_indicator (m : ℕ) (z : ℂ) :
    cutoffBall m z ≤ (ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ) z := by
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · rw [indicator_of_mem hz, Pi.one_apply]
    exact cutoffBall_le_one m z
  · rw [indicator_of_notMem hz]
    have hz' : 1 ≤ ‖z‖ := by simpa [mem_ball_zero_iff] using hz
    exact le_of_eq (cutoffBall_eq_zero_of_one_le m hz')

/-- The support of `c χ_m - η` lies in `closedBall (1 - 1/m) ∪ tsupport η`, hence in the open unit ball. -/
theorem tsupport_cutoff_sub_subset {η : ℂ → ℝ} (htsupp : tsupport η ⊆ ball (0 : ℂ) 1) (c : ℝ) {m : ℕ}
    (hm : 1 ≤ m) : tsupport (fun z => c * cutoffBall m z - η z) ⊆ ball (0 : ℂ) 1 := by
  have hsub : Function.support (fun z => c * cutoffBall m z - η z) ⊆
      closedBall (0 : ℂ) (1 - 1 / (m : ℝ)) ∪ tsupport η := by
    intro z hz
    rw [Function.mem_support] at hz
    by_cases hzt : z ∈ tsupport η
    · exact Or.inr hzt
    · left
      have hη0z : η z = 0 := image_eq_zero_of_notMem_tsupport hzt
      rw [mem_closedBall_zero_iff]
      by_contra hcon
      have hcz : cutoffBall m z = 0 :=
        cutoffBall_eq_zero_of_ge hm (le_of_lt (not_le.1 hcon))
      apply hz
      simp [hcz, hη0z]
  have hpos : (0 : ℝ) < 1 / (m : ℝ) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    positivity
  have hclosed : closedBall (0 : ℂ) (1 - 1 / (m : ℝ)) ∪ tsupport η ⊆ ball (0 : ℂ) 1 :=
    Set.union_subset (closedBall_subset_ball (by linarith)) htsupp
  exact (closure_minimal hsub ((isClosed_closedBall).union (isClosed_tsupport η))).trans hclosed

/-- Measurability (in `ω`) of the marked LQG masses of a continuous compactly supported test function. -/
theorem aemeasurable_lqgMeasure_test (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {η : ℂ → ℝ} (hη : Continuous η) (hηs : HasCompactSupport η) :
    AEMeasurable (fun ω => ∫ z, η z ∂(μ ω)) P := by
  have hver : ∀ k : ℕ, ∃ g : Ω → ℂ → ℝ, Measurable (fun p : Ω × ℂ => g p.1 p.2) ∧
      ∃ N : Set Ω, P N = 0 ∧ ∀ ω, ω ∉ N → ∀ z, g ω z = hcirc ω (dyadicScale k) z := fun k => by
    obtain ⟨g, hgm, _, N, _, hN0, hgN⟩ :=
      exists_measurable_circleAverage_version hG (dyadicScale_pos k)
    exact ⟨g, hgm, N, hN0, hgN⟩
  choose g hgm N hN0 hgN using hver
  have hAm : ∀ k : ℕ, AEMeasurable (fun ω => ∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ)) P := by
    intro k
    have hF : Measurable (fun p : Ω × ℂ =>
        η p.2 * (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * g k p.1 p.2))) :=
      (hη.measurable.comp measurable_snd).mul
        (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul (hgm k))))
    have hS := hF.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℂ))
    refine (hS.aestronglyMeasurable.congr ?_).aemeasurable
    filter_upwards [(ae_iff (p := fun ω => ω ∉ N k)).2 (by simpa using hN0 k)] with ω hω
    simp only [hgN k ω hω]
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ ω) := hμ
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ∫ z, η z * (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂(volume : Measure ℂ)) atTop
      (𝓝 (∫ z, η z ∂(μ ω))) := by
    filter_upwards [hμ', hG.ae_continuousOn_circle] with ω hω hcont
    have hT := hω.tendsto_integral η hη hηs
    have hcontk : ∀ k : ℕ, Continuous (fun z => fieldCircleAverage 0 (hcirc ω) (dyadicScale k) z) := by
      intro k
      simp only [fieldCircleAverage_zero_eq]
      exact hcont.comp_continuous (continuous_const.prodMk continuous_id)
        (fun z => ⟨dyadicScale_pos k, Set.mem_univ z⟩)
    refine Tendsto.congr (fun k => ?_) hT
    rw [integral_lqgApprox_of_continuous (dyadicScale_pos k) (hcontk k) η]
    simp only [fieldCircleAverage_zero_eq]
  exact aemeasurable_of_tendsto_metrizable_ae atTop hAm hconv

/-- Integrability of the marked LQG masses of a nonnegative test function. -/
theorem integrable_lqgMeasure_test_of_nonneg (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {η : ℂ → ℝ} (hη : Continuous η) (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z)
    (htsupp : tsupport η ⊆ ball (0 : ℂ) 1) :
    Integrable (fun ω => ∫ z, η z ∂(μ ω)) P := by
  refine ⟨(aemeasurable_lqgMeasure_test γ hG hμ hη hηs).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hle := lintegral_lqgMeasure_le γ hG hμ hη hηs hη0 htsupp
  calc ∫⁻ ω, ‖∫ z, η z ∂(μ ω)‖ₑ ∂P
      = ∫⁻ ω, ENNReal.ofReal (∫ z, η z ∂(μ ω)) ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (integral_nonneg hη0)]
    _ ≤ ENNReal.ofReal (∫ z, η z) := hle
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The upper bound `E μ_g(η) ≤ ∫ η` as a real inequality. -/
theorem integral_lqgMeasure_le_of_nonneg (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {η : ℂ → ℝ} (hη : Continuous η) (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z)
    (htsupp : tsupport η ⊆ ball (0 : ℂ) 1) :
    ∫ ω, ∫ z, η z ∂(μ ω) ∂P ≤ ∫ z, η z := by
  have hint := integrable_lqgMeasure_test_of_nonneg γ hG hμ hη hηs hη0 htsupp
  have hle := lintegral_lqgMeasure_le γ hG hμ hη hηs hη0 htsupp
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => integral_nonneg hη0)] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hη0)).1 hle

/-- The integrals of the cut-offs against a locally finite measure converge to its mass of the unit ball. -/
theorem tendsto_integral_cutoffBall_of_locallyFinite (μ' : Measure ℂ) [IsLocallyFiniteMeasure μ'] :
    Tendsto (fun m : ℕ => ∫ z, cutoffBall m z ∂μ') atTop (𝓝 (μ'.real (ball (0 : ℂ) 1))) := by
  have hF : Integrable ((ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ)) μ' :=
    (integrableOn_const (measure_ball_lt_top).ne).integrable_indicator measurableSet_ball
  have hlim := integral_tendsto_of_tendsto_of_monotone
    (fun m => (cutoffBall_continuous m).integrable_of_hasCompactSupport (cutoffBall_hasCompactSupport m))
    hF (ae_of_all _ fun z => cutoffBall_monotone z) (ae_of_all _ fun z => tendsto_cutoffBall z)
  rw [integral_indicator_one measurableSet_ball] at hlim
  exact hlim

/-- The integrals of the cut-offs against Lebesgue measure converge to `π`. -/
theorem tendsto_integral_cutoffBall_volume :
    Tendsto (fun m : ℕ => ∫ z, cutoffBall m z ∂(volume : Measure ℂ)) atTop (𝓝 Real.pi) := by
  have hint : Integrable ((ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ)) (volume : Measure ℂ) :=
    (integrableOn_const (measure_ball_lt_top).ne).integrable_indicator measurableSet_ball
  have hlim := tendsto_integral_of_dominated_convergence
    ((ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ))
    (fun m => (cutoffBall_continuous m).aestronglyMeasurable) hint
    (fun m => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cutoffBall_nonneg m z)]
      exact cutoffBall_le_indicator m z)
    (ae_of_all _ fun z => tendsto_cutoffBall z)
  rw [integral_indicator_one measurableSet_ball] at hlim
  simpa [Measure.real, Complex.volume_ball, Real.pi_nonneg] using hlim

/-- **Lebesgue first moment of the marked LQG mass** (r10 `l:r9-marked`, "Both measures have total mass π"):
`E μ_g(η) = ∫ η` for `0 ≤ η` continuous with compact support in the unit ball, `α₀ = 0`, under the staged printed
unnormalized whole-plane identity `hU` of [DMS, Lemma A.10, p. 184] (through `integral_measure_ball_eq_pi`). -/
theorem integral_lqgMeasure_eq_of_nonneg (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ)
    {η : ℂ → ℝ} (hη : Continuous η) (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z)
    (htsupp : tsupport η ⊆ ball (0 : ℂ) 1) :
    ∫ ω, ∫ z, η z ∂(μ ω) ∂P = ∫ z, η z := by
  have hup := integral_lqgMeasure_le_of_nonneg γ hG hμ hη hηs hη0 htsupp
  obtain ⟨M, hM1, hMsup⟩ := exists_margin_of_tsupport_subset_ball hηs htsupp
  obtain ⟨c0, hc0⟩ := hη.bounded_above_of_compact_support hηs
  have hc_nonneg : 0 ≤ max c0 0 := le_max_right _ _
  have hcη : ∀ z, η z ≤ max c0 0 := fun z => by
    have h := hc0 z
    rw [Real.norm_eq_abs] at h
    have h1 := le_abs_self (η z)
    have h2 := le_max_left c0 0
    linarith
  obtain ⟨m0, hm0⟩ := exists_nat_gt (2 / (1 - M))
  have hMpos : 0 < 1 - M := by linarith
  have hm0pos : (0 : ℝ) < m0 := lt_trans (div_pos (by norm_num) hMpos) hm0
  have hm0one : 1 ≤ m0 := by
    have : (0 : ℕ) < m0 := by exact_mod_cast hm0pos
    omega
  -- for `m ≥ m0`, `c χ_m ≥ η` with `c = max c0 0`
  have hdom : ∀ m : ℕ, m0 ≤ m → ∀ z, η z ≤ max c0 0 * cutoffBall m z := by
    intro m hm z
    by_cases hz : ‖z‖ ≤ M
    · have hm' : (m0 : ℝ) ≤ m := by exact_mod_cast hm
      have h3 : 2 / (1 - M) ≤ (m : ℝ) := le_trans hm0.le hm'
      have h4 : 2 ≤ (m : ℝ) * (1 - M) := (div_le_iff₀ hMpos).1 h3
      have h5 : (m : ℝ) * (1 - M) ≤ (m : ℝ) * (1 - ‖z‖) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg m)
      rw [cutoffBall_eq_one_of_le (z := z) m (by linarith), mul_one]
      exact hcη z
    · have hzt : z ∉ tsupport η := fun h => hz (hMsup z h)
      rw [image_eq_zero_of_notMem_tsupport hzt]
      exact mul_nonneg hc_nonneg (cutoffBall_nonneg m z)
  -- the total mass of the cut-offs: `E μ_g(χ_m) → π` (dominated convergence in ω)
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ ω) := hμ
  have hQ2 : Tendsto (fun m : ℕ => ∫ ω, ∫ z, cutoffBall m z ∂(μ ω) ∂P) atTop (𝓝 Real.pi) := by
    have hpi := integral_measure_ball_eq_pi hU hG hμ
    have hbd : Integrable (fun ω => (μ ω (ball (0 : ℂ) 1)).toReal) P := by
      by_contra h
      rw [integral_undef h] at hpi
      linarith [Real.pi_pos]
    rw [← hpi]
    refine tendsto_integral_of_dominated_convergence (fun ω => (μ ω (ball (0 : ℂ) 1)).toReal)
      (fun m => (aemeasurable_lqgMeasure_test γ hG hμ (cutoffBall_continuous m)
        (cutoffBall_hasCompactSupport m)).aestronglyMeasurable) hbd ?_ ?_
    · intro m
      filter_upwards [hμ'] with ω hω
      have := hω.isLocallyFiniteMeasure
      have hχi : Integrable (cutoffBall m) (μ ω) :=
        (cutoffBall_continuous m).integrable_of_hasCompactSupport (cutoffBall_hasCompactSupport m)
      have hBi : Integrable ((ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ)) (μ ω) :=
        (integrableOn_const (measure_ball_lt_top).ne).integrable_indicator measurableSet_ball
      have h1 : 0 ≤ ∫ z, cutoffBall m z ∂(μ ω) := integral_nonneg fun z => cutoffBall_nonneg m z
      have h2 : ∫ z, cutoffBall m z ∂(μ ω)
          ≤ ∫ z, (ball (0 : ℂ) 1).indicator (1 : ℂ → ℝ) z ∂(μ ω) :=
        integral_mono hχi hBi fun z => cutoffBall_le_indicator m z
      rw [integral_indicator_one measurableSet_ball] at h2
      rw [Real.norm_of_nonneg h1]
      exact h2
    · filter_upwards [hμ'] with ω hω
      have := hω.isLocallyFiniteMeasure
      exact tendsto_integral_cutoffBall_of_locallyFinite (μ ω)
  -- the Lebesgue total mass of the cut-offs
  have hQ1 := tendsto_integral_cutoffBall_volume
  have hlimit : Tendsto (fun m : ℕ => max c0 0 * (∫ ω, ∫ z, cutoffBall m z ∂(μ ω) ∂P)
      - max c0 0 * (∫ z, cutoffBall m z ∂(volume : Measure ℂ)) + ∫ z, η z ∂(volume : Measure ℂ))
      atTop (𝓝 (max c0 0 * Real.pi - max c0 0 * Real.pi + ∫ z, η z ∂(volume : Measure ℂ))) :=
    ((hQ2.const_mul _).sub (hQ1.const_mul _)).add_const _
  rw [sub_self, zero_add] at hlimit
  -- the lower bound for `m ≥ m0`, from Fatou applied to `c χ_m - η ≥ 0`
  have hkey : ∀ m : ℕ, m0 ≤ m →
      max c0 0 * (∫ ω, ∫ z, cutoffBall m z ∂(μ ω) ∂P)
        - max c0 0 * (∫ z, cutoffBall m z ∂(volume : Measure ℂ)) + ∫ z, η z ∂(volume : Measure ℂ)
        ≤ ∫ ω, ∫ z, η z ∂(μ ω) ∂P := by
    intro m hm
    have hm1 : 1 ≤ m := le_trans hm0one hm
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = max c0 0 := ⟨_, rfl⟩
    rw [← hc]
    obtain ⟨f, hf⟩ : ∃ f : ℂ → ℝ, f = fun z => c * cutoffBall m z - η z := ⟨_, rfl⟩
    have hf0 : ∀ z, 0 ≤ f z := by
      intro z
      have h := hdom m hm z
      rw [← hc] at h
      rw [hf]
      exact sub_nonneg.2 h
    have hfc : Continuous f := by
      rw [hf]
      exact (continuous_const.mul (cutoffBall_continuous m)).sub hη
    have hfs : HasCompactSupport f := by
      rw [hf]
      exact ((cutoffBall_hasCompactSupport m).mul_left).sub hηs
    have hft : tsupport f ⊆ ball (0 : ℂ) 1 := by
      rw [hf]
      exact tsupport_cutoff_sub_subset htsupp c hm1
    have hF := integral_lqgMeasure_le_of_nonneg γ hG hμ hfc hfs hf0 hft
    have hFi := integrable_lqgMeasure_test_of_nonneg γ hG hμ hfc hfs hf0 hft
    have hηi := integrable_lqgMeasure_test_of_nonneg γ hG hμ hη hηs hη0 htsupp
    have hsplit : (∫ ω, ∫ z, c * cutoffBall m z ∂(μ ω) ∂P)
        = (∫ ω, ∫ z, f z ∂(μ ω) ∂P) + ∫ ω, ∫ z, η z ∂(μ ω) ∂P := by
      rw [← integral_add hFi hηi]
      refine integral_congr_ae ?_
      filter_upwards [hμ'] with ω hω
      have := hω.isLocallyFiniteMeasure
      have hfi : Integrable f (μ ω) := hfc.integrable_of_hasCompactSupport hfs
      have hηi' : Integrable η (μ ω) := hη.integrable_of_hasCompactSupport hηs
      rw [← integral_add hfi hηi']
      congr 1
      funext z
      simp [hf]
    have hcs : (∫ ω, ∫ z, c * cutoffBall m z ∂(μ ω) ∂P)
        = c * ∫ ω, ∫ z, cutoffBall m z ∂(μ ω) ∂P := by
      rw [← integral_const_mul]
      congr 1
      funext ω
      rw [integral_const_mul]
    have hχc : Integrable (fun z => c * cutoffBall m z) (volume : Measure ℂ) :=
      ((cutoffBall_continuous m).const_mul c).integrable_of_hasCompactSupport
        ((cutoffBall_hasCompactSupport m).mul_left)
    have hηc : Integrable η (volume : Measure ℂ) := hη.integrable_of_hasCompactSupport hηs
    have hlebf : ∫ z, f z ∂(volume : Measure ℂ)
        = c * ∫ z, cutoffBall m z ∂(volume : Measure ℂ) - ∫ z, η z ∂(volume : Measure ℂ) := by
      rw [hf]
      show ∫ z, (c * cutoffBall m z - η z) ∂(volume : Measure ℂ) = _
      rw [integral_sub hχc hηc, integral_const_mul]
    linarith [hF, hsplit, hcs, hlebf]
  have hlow : ∫ z, η z ∂(volume : Measure ℂ) ≤ ∫ ω, ∫ z, η z ∂(μ ω) ∂P :=
    le_of_tendsto hlimit (eventually_atTop.2 ⟨m0, fun m hm => hkey m hm⟩)
  exact le_antisymm hup hlow

end HarmonicBalls

end
