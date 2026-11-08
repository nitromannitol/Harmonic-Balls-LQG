import HarmonicBalls.Proofs.Sec11.FixedSquareFrontierNull
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

/-!
# Singular LQG measures (`α < Q`) do not charge deterministic compact sets avoiding the origin

Let `h = h^ℂ - α log|·|` be the field of the paper, with circle averages `fieldCircleAverage α hcirc` built from a
whole-plane GFF `IsWholePlaneGFF P hC hcirc`, and let `μ` be its γ-LQG measure `IsLQGMeasureOfField P γ α hcirc μ`.
The source scope is `0 < γ < 2` and `α < Q = lqgQ γ`; both are kept as hypotheses of the statements. For every
deterministic compact `K ⊆ ℂ` with `0 ∉ K` and `Leb K = 0`, almost surely `μ ω K = 0`. The quantifier order is the
task's: `K` is fixed before `ω`, and no samplewise absolute continuity `μ ω ≪ volume` is used.

Argument (first moment, as in `FixedSquareFrontierNull`, with one extra deterministic weight).

* The circle average of `log ‖·‖` over `∂B_ε(z)` equals `log (max ε ‖z‖)` (Jensen's formula; Mathlib's
  `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`). Hence `fieldCircleAverage α h ε z = h_ε(z) - α log
  (max ε ‖z‖)`. For `ε ≤ ‖z‖` the approximating density is the zero-charge density times the radial weight
  `radialWeight γ α z = ‖z‖^{-γα}`; for smaller `ε` it differs, so only the dyadic scales below the inner radius of
  the cutoff support are used.
* Let `C₀ = cthickening δ₀ K` with `δ₀ > 0` and `C₀ ⊆ ℂ ∖ {0}` (`IsCompact.exists_cthickening_subset_open`). On the
  compact `C₀` the norm has a positive lower bound `ρ` and the radial weight a bound `M`, and `C₀ ⊆ closedBall 0 R`.
* For a continuous `0 ≤ f ≤ 1` equal to `1` on `K`, vanishing off `C₀`, the Gaussian first moment
  `E[ε^{γ²/2} exp(γ h_ε(z))] ≤ (R + 1)^{γ²}` (`IsWholePlaneGFF.lintegral_density_le`), Tonelli, Fatou and the dyadic
  vague convergence give `E μ(K) ≤ (R + 1)^{γ²} M ∫ f`.
* Urysohn cutoffs of `cthickening δ K` with `δ → 0` and `Leb K = 0` give `E μ(K) = 0`.

The square frontier `frontier (closedSquare a L)` is compact and Lebesgue-null (it lies on four lines), so it is
singular-LQG-null almost surely whenever it avoids the origin.

Credit: the import closure of this module contains code by Leonardo Bonanno. It reaches the external LatticeProb
module `LatticeProb.Prob.Birkhoff` (his LatticeProb formalization of the ergodic theorem) through
`HarmonicBalls/Proofs/Sec8/BirkhoffPort.lean`; this module does not cite that code directly. The closure check is
recorded in `docs/campaign/audits/SingularCompactNull.md`.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Metric Topology
open scoped ENNReal NNReal

/-- The circle average of `log ‖·‖` over `∂B_ε(z)` is `log (max ε ‖z‖)` (mean value property of `log |·|`, which is
harmonic off `0`; Jensen's formula). -/
theorem circleAverage_log_norm_eq_log_max {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Real.circleAverage (fun x => Real.log ‖x‖) z ε = Real.log (max ε ‖z‖) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := z) (R := ε) hε.ne'
  simp only [sub_zero] at h
  rw [h]
  rcases le_total ε ‖z‖ with hle | hle
  · have h1 : 1 ≤ ε⁻¹ * ‖z‖ := by
      rw [← div_eq_inv_mul]
      exact (one_le_div hε).2 hle
    have hz0 : ‖z‖ ≠ 0 := (lt_of_lt_of_le hε hle).ne'
    rw [max_eq_right hle]
    simp only [Real.posLog]
    rw [max_eq_right (Real.log_nonneg h1), Real.log_mul (inv_ne_zero hε.ne') hz0, Real.log_inv]
    ring
  · have h1 : ε⁻¹ * ‖z‖ ≤ 1 := by
      rw [← div_eq_inv_mul]
      exact (div_le_one hε).2 hle
    rw [max_eq_left hle]
    simp only [Real.posLog]
    rw [max_eq_left (Real.log_nonpos (mul_nonneg (inv_nonneg.2 hε.le) (norm_nonneg z)) h1), add_zero]

/-- The circle average form of the field: `fieldCircleAverage α h ε z = h_ε(z) - α log (max ε ‖z‖)`. -/
theorem fieldCircleAverage_eq_sub_log_max (α : ℝ) (hc : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    fieldCircleAverage α hc ε z = hc ε z - α * Real.log (max ε ‖z‖) := by
  unfold fieldCircleAverage
  rw [circleAverage_log_norm_eq_log_max hε z]

/-- The deterministic radial weight `‖z‖^{-γα} = exp(-γα log ‖z‖)` of a singular γ-LQG density (`α` the charge). -/
noncomputable def radialWeight (γ α : ℝ) (z : ℂ) : ℝ :=
  Real.exp (-(γ * α) * Real.log ‖z‖)

/-- Off the inner disc of radius `ε`, the approximating density of the singular field is the zero-charge density
`ε^{γ²/2} e^{γ h_ε(z)}` times the deterministic radial weight. -/
theorem lqgDensity_eq_mul_radialWeight {γ α : ℝ} (hc : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : ε ≤ ‖z‖) :
    ε ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage α hc ε z) =
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hc ε z)) * radialWeight γ α z := by
  rw [fieldCircleAverage_eq_sub_log_max α hc hε z, max_eq_right hz, radialWeight,
    show γ * (hc ε z - α * Real.log ‖z‖) = γ * hc ε z + -(γ * α) * Real.log ‖z‖ by ring, Real.exp_add]
  ring

/-- **First moment with a radial weight.** For a continuous cutoff `0 ≤ f ≤ 1` equal to `1` on `K`, vanishing off
`B_R`, and supported where `‖z‖ ≥ ρ` and the radial weight is at most `M`:
`E μ(K) ≤ (R + 1)^{γ²} M ∫ f dLeb`. -/
theorem IsWholePlaneGFF.lintegral_lqgMeasure_le_of_cutoff_weight {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {K : Set ℂ} (hKm : MeasurableSet K) {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hf01 : ∀ z, 0 ≤ f z ∧ f z ≤ 1) (hK1 : ∀ z ∈ K, f z = 1) {R : ℝ} (hR : 0 ≤ R)
    (hfR : ∀ z, R < ‖z‖ → f z = 0) {ρ M : ℝ} (hρ : 0 < ρ)
    (hsupp : ∀ z, f z ≠ 0 → ρ ≤ ‖z‖ ∧ radialWeight γ α z ≤ M) :
    ∫⁻ ω, μ ω K ∂P ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ENNReal.ofReal M *
        ∫⁻ z, ENNReal.ofReal (f z) := by
  have := hgff.isProbabilityMeasure
  obtain ⟨H, hHcont, hHmeas, hHae⟩ := hgff.exists_jointlyMeasurable_circleAverage
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  have hfeM : Measurable fun z => ENNReal.ofReal (f z) := hf.measurable.ennreal_ofReal
  have hwmeas : Measurable (radialWeight γ α) := by
    unfold radialWeight
    exact Real.measurable_exp.comp (measurable_const.mul (Real.measurable_log.comp measurable_norm))
  have hwM : Measurable fun z => ENNReal.ofReal (radialWeight γ α z) := hwmeas.ennreal_ofReal
  -- the total mass of the cutoff is finite (it vanishes off `B_R` and is at most `1`)
  have hfint : ∫⁻ z, ENNReal.ofReal (f z) ≠ ∞ := by
    have hpt : ∀ z, ENNReal.ofReal (f z) ≤ (closedBall (0 : ℂ) R).indicator 1 z := by
      intro z
      by_cases hz : ‖z‖ ≤ R
      · rw [indicator_of_mem (mem_closedBall_zero_iff.2 hz), Pi.one_apply]
        exact ENNReal.ofReal_le_one.2 (hf01 z).2
      · rw [hfR z (lt_of_not_ge hz), ENNReal.ofReal_zero]
        exact zero_le
    have hle : ∫⁻ z, ENNReal.ofReal (f z) ≤ volume (closedBall (0 : ℂ) R) :=
      calc ∫⁻ z, ENNReal.ofReal (f z) ≤ ∫⁻ z, (closedBall (0 : ℂ) R).indicator 1 z := lintegral_mono hpt
        _ = volume (closedBall (0 : ℂ) R) := lintegral_indicator_one measurableSet_closedBall
    exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne hle
  -- the dyadic approximations evaluated on `f`
  set A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    ∫⁻ z, ENNReal.ofReal (f z) ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k)) with hAdef
  have hAmeas : ∀ k, AEMeasurable (A k) P := fun k =>
    (Measure.measurable_lintegral hfeM).comp_aemeasurable (hgff.aemeasurable_lqgApprox γ α k)
  -- the joint integrand, written with the jointly measurable version `H` of the circle averages
  set F : ℕ → Ω → ℂ → ℝ≥0∞ := fun k ω z =>
    ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H ω (dyadicScale k) z)) *
      (ENNReal.ofReal (radialWeight γ α z) * ENNReal.ofReal (f z)) with hFdef
  -- for the scales below `min ρ 1`, the approximation integral is the joint-density integral
  have hsmall : ∀ k, dyadicScale k ≤ min ρ 1 → ∀ᵐ ω ∂P, A k ω = ∫⁻ z, F k ω z := by
    intro k hk
    have hε := dyadicScale_pos k
    have hερ : dyadicScale k ≤ ρ := le_trans hk (min_le_left _ _)
    filter_upwards [hHae] with ω hω
    have hdens : ∀ z, fieldCircleAverage α (hcirc ω) (dyadicScale k) z =
        H ω (dyadicScale k) z - α * Real.log (max (dyadicScale k) ‖z‖) := fun z => by
      rw [fieldCircleAverage_eq_sub_log_max α _ hε z, hω]
    have hcontD : Continuous fun z => H ω (dyadicScale k) z - α * Real.log (max (dyadicScale k) ‖z‖) :=
      (hHcont ω _ hε).sub (continuous_const.mul
        (Continuous.log (continuous_const.max continuous_norm) fun z => (lt_max_of_lt_left hε).ne'))
    have hmeas : Measurable fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α (hcirc ω) (dyadicScale k) z)) := by
      simp only [hdens]
      exact (ENNReal.continuous_ofReal.comp (continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul hcontD)))).measurable
    have hA : A k ω = ∫⁻ z, ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α (hcirc ω) (dyadicScale k) z)) * ENNReal.ofReal (f z) := by
      show ∫⁻ z, ENNReal.ofReal (f z) ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k)) = _
      unfold lqgApprox
      exact lintegral_withDensity_eq_lintegral_mul _ hmeas hfeM
    rw [hA]
    refine lintegral_congr fun z => ?_
    by_cases hfz : f z = 0
    · simp [hFdef, hfz]
    · have hz : dyadicScale k ≤ ‖z‖ := le_trans hερ (hsupp z hfz).1
      simp only [hFdef]
      rw [lqgDensity_eq_mul_radialWeight (hcirc ω) hε hz, ← hω,
        ENNReal.ofReal_mul (p := dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H ω (dyadicScale k) z))
          (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)]
      ring
  -- the uniform first-moment bound for the scales below `min ρ 1`
  have hbound : ∀ k, dyadicScale k ≤ min ρ 1 →
      ∫⁻ ω, A k ω ∂P ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ENNReal.ofReal M *
        ∫⁻ z, ENNReal.ofReal (f z) := by
    intro k hk
    have hε := dyadicScale_pos k
    have hε1 : dyadicScale k ≤ 1 := le_trans hk (min_le_right _ _)
    have hHk : Measurable fun p : Ω × ℂ => H p.1 (dyadicScale k) p.2 :=
      (hHmeas _ hε).comp measurable_swap
    have hFm : Measurable fun p : Ω × ℂ => F k p.1 p.2 := by
      simp only [hFdef]
      exact ((measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hHk))).ennreal_ofReal).mul
        ((hwM.comp measurable_snd).mul (hfeM.comp measurable_snd))
    have hpt : ∀ z, ∫⁻ ω, F k ω z ∂P ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * (ENNReal.ofReal M * ENNReal.ofReal (f z)) := by
      intro z
      by_cases hz : ‖z‖ ≤ R
      · by_cases hfz : f z = 0
        · simp [hFdef, hfz]
        · have hGle : ∫⁻ ω, ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H ω (dyadicScale k) z)) ∂P
              ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) := by
            have hae : (fun ω => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H ω (dyadicScale k) z)))
                =ᵐ[P] (fun ω => ENNReal.ofReal
                  (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω (dyadicScale k) z))) :=
              hHae.mono fun ω hω => by simp only [hω]
            rw [lintegral_congr_ae hae]
            exact hgff.lintegral_density_le γ hR hε hε1 hz
          have hwz : radialWeight γ α z ≤ M := (hsupp z hfz).2
          simp only [hFdef]
          rw [lintegral_mul_const' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
          calc (∫⁻ ω, ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * H ω (dyadicScale k) z)) ∂P) *
                (ENNReal.ofReal (radialWeight γ α z) * ENNReal.ofReal (f z))
              ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) *
                (ENNReal.ofReal (radialWeight γ α z) * ENNReal.ofReal (f z)) := mul_le_mul_of_nonneg_right hGle zero_le
            _ ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) *
                (ENNReal.ofReal M * ENNReal.ofReal (f z)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hwz) zero_le)
                  zero_le
      · have hf0 : f z = 0 := hfR z (lt_of_not_ge hz)
        simp [hFdef, hf0]
    calc ∫⁻ ω, A k ω ∂P = ∫⁻ ω, ∫⁻ z, F k ω z ∂volume ∂P := lintegral_congr_ae (hsmall k hk)
      _ = ∫⁻ z, ∫⁻ ω, F k ω z ∂P ∂volume := lintegral_lintegral_swap hFm.aemeasurable
      _ ≤ ∫⁻ z, ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) *
            (ENNReal.ofReal M * ENNReal.ofReal (f z)) ∂volume := lintegral_mono hpt
      _ = ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ENNReal.ofReal M *
            ∫⁻ z, ENNReal.ofReal (f z) ∂volume := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            mul_assoc]
  -- the scales used below are the tail `k ≥ k₀` of the dyadic sequence
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → dyadicScale k ≤ min ρ 1 := by
    have hmpos : 0 < min ρ 1 := lt_min hρ one_pos
    have hT : Tendsto (fun k : ℕ => (2 : ℝ)⁻¹ ^ k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 ((tendsto_order.1 hT).2 (min ρ 1) hmpos)
    exact ⟨k₀, fun k hk => (hk₀ k hk).le⟩
  have hfinA : ∀ j : ℕ, ∀ᵐ ω ∂P, A (j + k₀) ω < ∞ := fun j =>
    ae_lt_top' (hAmeas (j + k₀))
      (ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hfint)
        (hbound (j + k₀) (hk₀ _ (Nat.le_add_left _ _))))
  have hpt : ∀ᵐ ω ∂P, μ ω K ≤ liminf (fun j : ℕ => A (j + k₀) ω) atTop := by
    filter_upwards [hμ', ae_all_iff.2 hfinA] with ω hω hωfin
    have := hω.isLocallyFiniteMeasure
    have hle : ∀ z, K.indicator 1 z ≤ ENNReal.ofReal (f z) := by
      intro z
      by_cases hz : z ∈ K
      · rw [indicator_of_mem hz, Pi.one_apply, hK1 z hz, ENNReal.ofReal_one]
      · rw [indicator_of_notMem hz]
        exact zero_le
    have key := lintegral_eq_liminf_of_tendsto (m := μ ω)
      (ν := fun j : ℕ => lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale (j + k₀)))
      hf hfc (fun z => (hf01 z).1) (fun j => (hωfin j).ne)
      ((hω.tendsto_integral f hf hfc).comp (tendsto_add_atTop_nat k₀))
    calc μ ω K = ∫⁻ z, K.indicator 1 z ∂(μ ω) := (lintegral_indicator_one hKm).symm
      _ ≤ ∫⁻ z, ENNReal.ofReal (f z) ∂(μ ω) := lintegral_mono hle
      _ = liminf (fun j : ℕ => A (j + k₀) ω) atTop := key
  have hfat : ∫⁻ ω, liminf (fun j : ℕ => A (j + k₀) ω) atTop ∂P ≤
      liminf (fun j : ℕ => ∫⁻ ω, A (j + k₀) ω ∂P) atTop :=
    lintegral_liminf_le' fun j => hAmeas (j + k₀)
  have hlim : liminf (fun j : ℕ => ∫⁻ ω, A (j + k₀) ω ∂P) atTop ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ENNReal.ofReal M *
        ∫⁻ z, ENNReal.ofReal (f z) :=
    liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall fun j =>
      hbound (j + k₀) (hk₀ _ (Nat.le_add_left _ _))))
  exact (lintegral_mono_ae hpt).trans (hfat.trans hlim)

/-- **Singular LQG measures do not charge deterministic compact sets avoiding the origin.** Let `h^ℂ` be a whole-plane
GFF and `μ` the γ-LQG measure of `h = h^ℂ - α log|·|` with `0 < γ < 2` and `α < Q` (the scope of the paper, kept as
hypotheses). If `K ⊆ ℂ` is compact, `0 ∉ K` and `Leb K = 0`, then almost surely `μ ω K = 0`. The compact set `K` is fixed
before `ω`; no samplewise absolute continuity is used. -/
theorem IsWholePlaneGFF.ae_lqgMeasure_eq_zero_of_isCompact_not_mem_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (_hγ : 0 < γ) (_hγ2 : γ < 2) (_hα : α < lqgQ γ) {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) {K : Set ℂ} (hK : IsCompact K) (h0 : (0 : ℂ) ∉ K)
    (hKv : volume K = 0) :
    ∀ᵐ ω ∂P, μ ω K = 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact Eventually.of_forall fun ω => measure_empty
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hK0 : K ⊆ ({0} : Set ℂ)ᶜ := fun z hz hz0 => h0 (Set.mem_singleton_iff.1 hz0 ▸ hz)
  -- a compact neighbourhood `C₀ = cthickening δ₀ K` of `K` avoiding `0`
  obtain ⟨δ₀, hδ₀, hC₀⟩ := hK.exists_cthickening_subset_open isOpen_compl_singleton hK0
  have hC₀cpt : IsCompact (cthickening δ₀ K) := hK.cthickening
  have hC₀ne : (cthickening δ₀ K).Nonempty := hne.mono (self_subset_cthickening K)
  have hC₀0 : (0 : ℂ) ∉ cthickening δ₀ K := fun h => hC₀ h (Set.mem_singleton 0)
  -- a positive lower bound `ρ` for the norm on `C₀`
  obtain ⟨z₀, hz₀, hmin⟩ := hC₀cpt.exists_isMinOn hC₀ne continuous_norm.continuousOn
  obtain ⟨ρ, hρ, hρle⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ cthickening δ₀ K, ρ ≤ ‖z‖ :=
    ⟨‖z₀‖, norm_pos_iff.2 fun h => hC₀0 (h ▸ hz₀), fun z hz => isMinOn_iff.1 hmin z hz⟩
  -- a bound `M₀` for the radial weight on `C₀`
  have hwC : ContinuousOn (radialWeight γ α) (cthickening δ₀ K) := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    have hz0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 fun h => hC₀0 (h ▸ hz)
    unfold radialWeight
    exact Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul (ContinuousAt.log continuous_norm.continuousAt hz0))
  obtain ⟨zM, -, hmax⟩ := hC₀cpt.exists_isMaxOn hC₀ne hwC
  obtain ⟨M₀, hwle⟩ : ∃ M₀ : ℝ, ∀ z ∈ cthickening δ₀ K, radialWeight γ α z ≤ M₀ :=
    ⟨radialWeight γ α zM, fun z hz => isMaxOn_iff.1 hmax z hz⟩
  -- a radius `R` with `C₀ ⊆ closedBall 0 R`
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hC₀cpt.isBounded
  obtain ⟨R, hR, hRbd⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ z ∈ cthickening δ₀ K, ‖z‖ ≤ R :=
    ⟨max R₀ 0, le_max_right _ _,
      fun z hz => (mem_closedBall_zero_iff.1 (hR₀ hz)).trans (le_max_left _ _)⟩
  have hkey : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∫⁻ ω, μ ω K ∂P ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ENNReal.ofReal M₀ *
        volume (cthickening δ K) := by
    intro δ hδ hδle
    obtain ⟨f, hf, hfc, hf01, hK1, hfδ, hfint⟩ := exists_cutoff_of_isCompact hK hδ
    have hsub : cthickening δ K ⊆ cthickening δ₀ K := cthickening_mono hδle K
    have hfsupp : ∀ z, f z ≠ 0 → z ∈ cthickening δ₀ K := fun z hz =>
      hsub (Classical.byContradiction fun h => hz (hfδ z h))
    have hfR : ∀ z, R < ‖z‖ → f z = 0 := fun z hz =>
      hfδ z fun hzc => absurd (hRbd z (hsub hzc)) (not_le.2 hz)
    have hsupp : ∀ z, f z ≠ 0 → ρ ≤ ‖z‖ ∧ radialWeight γ α z ≤ M₀ := fun z hz =>
      ⟨hρle z (hfsupp z hz), hwle z (hfsupp z hz)⟩
    refine (hgff.lintegral_lqgMeasure_le_of_cutoff_weight hμ hKm hf hfc hf01 hK1 hR hfR hρ hsupp).trans ?_
    gcongr
  have hc_top : ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) * ENNReal.ofReal M₀ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun δ : ℝ => ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log (R + 1))) *
      ENNReal.ofReal M₀ * volume (cthickening δ K)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun δ : ℝ => volume (cthickening δ K)) (𝓝[>] 0) (𝓝 (volume K)) :=
      (tendsto_measure_cthickening_of_isCompact hK (μ := volume)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [hKv] at h
    have h2 := ENNReal.Tendsto.const_mul h (Or.inr hc_top)
    rwa [mul_zero] at h2
  have hzero : ∫⁻ ω, μ ω K ∂P = 0 := by
    refine le_antisymm (ge_of_tendsto hlim ?_) zero_le
    filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
    exact hkey δ hδ.1 hδ.2.le
  have hAE : AEMeasurable (fun ω => μ ω K) P :=
    (Measure.measurable_coe hKm).comp_aemeasurable (hgff.aemeasurable_lqgMeasure hμ)
  exact (lintegral_eq_zero_iff' hAE).1 hzero

/-- **The fixed square frontier avoiding the origin is singular-LQG-null.** For a deterministic square
`frontier (closedSquare a L)` (corner `a`, side `L ≥ 0`) with `0 ∉` the frontier, almost surely
`μ ω (frontier (closedSquare a L)) = 0`, for `0 < γ < 2`, `α < Q`. The square is fixed before `ω`. -/
theorem IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero_of_not_mem_zero {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) (a : ℂ) {L : ℝ} (hL : 0 ≤ L)
    (h0 : (0 : ℂ) ∉ frontier (closedSquare a L)) :
    ∀ᵐ ω ∂P, μ ω (frontier (closedSquare a L)) = 0 := by
  have hcpt : IsCompact (closedSquare a L) := IsCompact.reProdIm isCompact_Icc isCompact_Icc
  have hfr_sub : frontier (closedSquare a L) ⊆ closedSquare a L := by
    rw [hcpt.isClosed.frontier_eq]
    exact sdiff_subset
  have hfr_cpt : IsCompact (frontier (closedSquare a L)) :=
    hcpt.of_isClosed_subset isClosed_frontier hfr_sub
  have hfr_vol : volume (frontier (closedSquare a L)) = 0 :=
    measure_mono_null (frontier_closedSquare_subset_lines a hL)
      (measure_union_null (measure_union_null (measure_union_null (volume_setOf_re_eq_const _)
        (volume_setOf_re_eq_const _)) (volume_setOf_im_eq_const _)) (volume_setOf_im_eq_const _))
  exact hgff.ae_lqgMeasure_eq_zero_of_isCompact_not_mem_zero hγ hγ2 hα hμ hfr_cpt h0 hfr_vol

end HarmonicBalls
