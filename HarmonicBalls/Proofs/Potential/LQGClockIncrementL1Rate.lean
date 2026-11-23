import HarmonicBalls.Proofs.Potential.LQGClockOneStart
import LatticeProb.LQG.GMCL1Rate

/-! # The `L¹` rate of the dyadic clock increments along a path

For a path `w` bounded by `N` on `(a, b]`, its occupation measure `ν_w(A) = |{v ∈ (a, b] : w_v ∈ A}|`
(`pathOccupation`) and a whole-plane GFF `h`, the consecutive dyadic approximants of the clock
increment, recentred at `h_R(0)` with `R = N + 1`,
`e^{-γ h_R(0)} I^k_{a,b}(w) = ∫_a^b ε^{γ²/2} e^{γ (h_ε(w_v) - h_R(0))} dv`, `ε = 2^{-k}`, satisfy the
`L¹` bound of the thick-point truncation (Duplantier-Sheffield 2011, Section 3; Berestycki 2015,
Section 2, for the occupation measure of a Brownian path), proved in Lattice-Probability for every
reference measure (`LatticeProb.Gauss.IsWholePlaneGFF.integral_abs_integral_increment_le`): for
`γ ≤ α ≤ 2γ` and `τ > 0`,
`E |e^{-γ h_R(0)} (I^{k+1} - I^k)| ≤ ε^{γ²/2} ((B I_ε / τ + τ) / 2 + 2 (b - a) e^{L (γ²/2 - (α - γ)²/2)})`
with `L = log (R / ε)`, `B = (2^{γ²} - 1) e^{L (2γ² - (2γ - α)²/2)}` and `I_ε = ν_w ⊗ ν_w {|z - z'| < 2ε}`.

Here `I_ε ≤ (2ε)^β ∫∫ |w_s - w_t|^{-β}` for every `β > 0` (`pathOccupation_prod_lt_le`), and the
Brownian interval energies `E_x ∫∫ |B_s - B_t|^{-β}` are finite for `β < 2`. With `τ = ε^{(β - p)/2}`,
`p = 2γ² - (2γ - α)²/2`, the bound becomes `K₁ ε^e ∫∫ |w_s - w_t|^{-β} + ε^e / 2 + K₃ ε^{(α - γ)²/2}`,
`e = (β - γ² + (2γ - α)²/2) / 2` (`lintegral_ofReal_abs_integral_dyadicIncrement_le_exp`). This
replaces the quenched second-moment bound of Berestycki 2015, Section 2, with the occupation estimate
of Dembo-Peres-Rosen-Zeitouni, by an annealed `L¹` bound under the joint law of the field and the
path.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The occupation measure `A ↦ |{v ∈ (a, b] : w_v ∈ A}|` of a path on the time interval `(a, b]`. -/
noncomputable def pathOccupation (w : ContinuousPath ℂ) (a b : ℝ) : Measure ℂ :=
  (volume.restrict (Ioc a b)).map fun v => w v.toNNReal

theorem ContinuousPath.continuous_comp_toNNReal (w : ContinuousPath ℂ) :
    Continuous fun v : ℝ => w v.toNNReal :=
  w.continuous.comp continuous_real_toNNReal

instance (w : ContinuousPath ℂ) (a b : ℝ) : IsFiniteMeasure (pathOccupation w a b) := by
  unfold pathOccupation
  infer_instance

/-- An indicator of `‖d‖ < δ` is at most `δ^β ‖d‖^{-β}`. -/
theorem pathOccupation_indicator_norm_lt_le {δ β : ℝ} (hδ : 0 < δ) (hβ : 0 < β) (d : ℂ) :
    ({d : ℂ | ‖d‖ < δ}.indicator (1 : ℂ → ℝ≥0∞) d) ≤
      ENNReal.ofReal (δ ^ β) * (ENNReal.ofReal ‖d‖) ^ (-β) := by
  by_cases hd : ‖d‖ < δ
  · rw [Set.indicator_of_mem (show d ∈ {d : ℂ | ‖d‖ < δ} from hd), Pi.one_apply]
    rcases eq_or_lt_of_le (norm_nonneg d) with h0 | hpos
    · rw [← h0, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith),
        ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ β)).ne']
      exact le_top
    · rw [ENNReal.ofReal_rpow_of_pos hpos, ← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le β)]
      refine ENNReal.one_le_ofReal.mpr ?_
      rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hpos β)]
      exact Real.rpow_le_rpow hpos.le hd.le hβ.le
  · rw [Set.indicator_of_notMem (show d ∉ {d : ℂ | ‖d‖ < δ} from hd)]
    exact zero_le

/-- The pairs of points of the occupation measure at distance less than `δ` have mass at most
`δ^β ∫∫ |w_s - w_t|^{-β}`. -/
theorem pathOccupation_prod_lt_le (w : ContinuousPath ℂ) (a b : ℝ) {δ β : ℝ} (hδ : 0 < δ)
    (hβ : 0 < β) :
    ((pathOccupation w a b).prod (pathOccupation w a b)) {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ} ≤
      ENNReal.ofReal (δ ^ β) * ∫⁻ s in Ioc a b, ∫⁻ t in Ioc a b,
        (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-β) := by
  set f : ℝ → ℂ := fun v => w v.toNNReal with hfdef
  have hf : Measurable f := (ContinuousPath.continuous_comp_toNNReal w).measurable
  have hS : MeasurableSet {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ} :=
    (isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_snd))
      continuous_const).measurableSet
  have hE : Measurable fun q : ℝ × ℝ => (ENNReal.ofReal ‖f q.1 - f q.2‖) ^ (-β) :=
    ((continuous_norm.comp
      (((ContinuousPath.continuous_comp_toNNReal w).comp continuous_fst).sub
        ((ContinuousPath.continuous_comp_toNNReal w).comp
          continuous_snd))).measurable.ennreal_ofReal).pow_const _
  unfold pathOccupation
  rw [Measure.map_prod_map _ _ hf hf, Measure.map_apply (hf.prodMap hf) hS,
    ← lintegral_indicator_one (hS.preimage (hf.prodMap hf))]
  calc ∫⁻ q, (Prod.map f f ⁻¹' {p : ℂ × ℂ | ‖p.1 - p.2‖ < δ}).indicator 1 q
        ∂((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b)))
      ≤ ∫⁻ q, ENNReal.ofReal (δ ^ β) * (ENNReal.ofReal ‖f q.1 - f q.2‖) ^ (-β)
        ∂((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
        refine lintegral_mono fun q => ?_
        have h := pathOccupation_indicator_norm_lt_le hδ hβ (f q.1 - f q.2)
        simpa [Set.indicator, Prod.map] using h
    _ = _ := by
        rw [lintegral_const_mul _ hE, lintegral_prod _ hE.aemeasurable]

/-- The `L¹` bound of the thick-point truncation for the recentred dyadic increments along a path
bounded by `N` on `(a, b]`, with the occupation measure of the path as reference measure. -/
theorem lintegral_ofReal_abs_integral_increment_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε N : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hN : 0 ≤ N) {a b : ℝ} (hab : a ≤ b) {w : ContinuousPath ℂ}
    (hw : ∀ v ∈ Ioc a b, ‖w v.toNNReal‖ ≤ N) {γ α β τ : ℝ} (hγα : γ ≤ α) (hα : α ≤ 2 * γ)
    (hβ : 0 < β) (hτ : 0 < τ) :
    ∫⁻ ω, ENNReal.ofReal |∫ v in Ioc a b, ((ε / 2) ^ (γ ^ 2 / 2) *
        rexp (γ * (hcirc ω (ε / 2) (w v.toNNReal) - hcirc ω (N + 1) 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε (w v.toNNReal) - hcirc ω (N + 1) 0)))| ∂P ≤
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * ((rexp (γ ^ 2 * Real.log 2) - 1) *
          rexp (Real.log ((N + 1) / ε) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) / τ / 2) *
          (2 * ε) ^ β) *
        (∫⁻ s in Ioc a b, ∫⁻ t in Ioc a b,
          (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-β)) +
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * (τ / 2 +
        2 * (b - a) * rexp (Real.log ((N + 1) / ε) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)))) := by
  have hPm := hh.isProbabilityMeasure
  have hR : 0 < N + 1 := by linarith
  set ν := pathOccupation w a b with hνdef
  have hf : Measurable fun v : ℝ => w v.toNNReal :=
    (ContinuousPath.continuous_comp_toNNReal w).measurable
  set g : ℂ → ℝ := (Metric.closedBall (0 : ℂ) N).indicator fun _ => 1 with hgdef
  have hgm : Measurable g := measurable_const.indicator Metric.isClosed_closedBall.measurableSet
  have hgi : Integrable g ν :=
    (integrable_const (1 : ℝ)).indicator Metric.isClosed_closedBall.measurableSet
  have hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ N + 1 := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) N := by
      by_contra hc
      exact hz (Set.indicator_of_notMem hc _)
    rw [mem_closedBall_zero_iff] at hz'
    linarith
  have hgf : ∀ v ∈ Ioc a b, g (w v.toNNReal) = 1 := fun v hv =>
    Set.indicator_of_mem (mem_closedBall_zero_iff.mpr (hw v hv)) _
  have hg01 : ∀ z, |g z| ≤ 1 := by
    intro z
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) N
    · rw [hgdef, Set.indicator_of_mem hz, abs_one]
    · rw [hgdef, Set.indicator_of_notMem hz, abs_zero]
      exact zero_le_one
  have hM := hh.integral_abs_integral_increment_le hε hR ν hgm hgi hgR hγα hα hτ
  have hint := (hh.integrable_integral_increment hε hR ν hgm hgi hgR γ).abs
  -- along a field with continuous circle averages, the integral against `ν` is the time integral
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hh.ae_continuousOn_circle] with ω hω r hr
    exact hω.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hr, mem_univ _⟩
  have heq : ∀ᵐ ω ∂P, ∫ v in Ioc a b, ((ε / 2) ^ (γ ^ 2 / 2) *
        rexp (γ * (hcirc ω (ε / 2) (w v.toNNReal) - hcirc ω (N + 1) 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε (w v.toNNReal) - hcirc ω (N + 1) 0))) =
      ∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (ε / 2) z - hcirc ω (N + 1) 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω (N + 1) 0))) ∂ν := by
    filter_upwards [hcont] with ω hω
    have hc : Continuous fun z => (ε / 2) ^ (γ ^ 2 / 2) *
        rexp (γ * (hcirc ω (ε / 2) z - hcirc ω (N + 1) 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω (N + 1) 0)) :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
        ((hω _ (by linarith)).sub continuous_const)))).sub
        (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
          ((hω _ hε).sub continuous_const))))
    have hm : AEStronglyMeasurable (fun z => g z * ((ε / 2) ^ (γ ^ 2 / 2) *
        rexp (γ * (hcirc ω (ε / 2) z - hcirc ω (N + 1) 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω (N + 1) 0))))
        (Measure.map (fun v : ℝ => w v.toNNReal) (volume.restrict (Ioc a b))) :=
      (hgm.mul hc.measurable).aestronglyMeasurable
    symm
    refine (integral_map hf.aemeasurable hm).trans ?_
    refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
    simp only [hgf v hv, one_mul]
  -- the pair mass and the total mass of `g`
  set S : Set (ℂ × ℂ) := {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε} with hSdef
  have hS : MeasurableSet S :=
    (isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_snd))
      continuous_const).measurableSet
  set I := ∫ p, S.indicator (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν) with hIdef
  have hI0 : 0 ≤ I := integral_nonneg fun p =>
    Set.indicator_nonneg (fun p _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) p
  have hIle : ENNReal.ofReal I ≤ (ν.prod ν) S := by
    by_cases hfi : Integrable (fun p => S.indicator (fun p => |g p.1| * |g p.2|) p) (ν.prod ν)
    · rw [hIdef, ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ fun p =>
        Set.indicator_nonneg (fun p _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) p),
        ← lintegral_indicator_one hS]
      refine lintegral_mono fun p => ?_
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Pi.one_apply]
        exact ENNReal.ofReal_le_one.mpr ((mul_le_mul (hg01 _) (hg01 _) (abs_nonneg _)
          zero_le_one).trans_eq (one_mul 1))
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, ENNReal.ofReal_zero]
    · rw [hIdef, integral_undef hfi, ENNReal.ofReal_zero]
      exact zero_le
  have hA : ∫ z, |g z| ∂ν = b - a := by
    have habs : (fun z => |g z|) = g := by
      funext z
      by_cases hz : z ∈ Metric.closedBall (0 : ℂ) N
      · rw [hgdef, Set.indicator_of_mem hz, abs_one]
      · rw [hgdef, Set.indicator_of_notMem hz, abs_zero]
    rw [habs]
    refine (integral_map (μ := volume.restrict (Ioc a b)) hf.aemeasurable
      hgm.aestronglyMeasurable).trans ?_
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (1 : ℝ)) fun v hv => hgf v hv,
      setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul, mul_one]
  -- assembling the bound
  set L := Real.log ((N + 1) / ε) with hLdef
  set B := (rexp (γ ^ 2 * Real.log 2) - 1) * rexp (L * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2))
    with hBdef
  have hB0 : 0 ≤ B := mul_nonneg (sub_nonneg.mpr (Real.one_le_exp (by positivity)))
    (Real.exp_pos _).le
  have hεγ : 0 ≤ ε ^ (γ ^ 2 / 2) := Real.rpow_nonneg hε.le _
  have hc1 : 0 ≤ ε ^ (γ ^ 2 / 2) * (B / τ / 2) := by positivity
  rw [hA] at hM
  calc ∫⁻ ω, ENNReal.ofReal |∫ v in Ioc a b, ((ε / 2) ^ (γ ^ 2 / 2) *
        rexp (γ * (hcirc ω (ε / 2) (w v.toNNReal) - hcirc ω (N + 1) 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε (w v.toNNReal) - hcirc ω (N + 1) 0)))| ∂P
      = ∫⁻ ω, ENNReal.ofReal |∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) *
          rexp (γ * (hcirc ω (ε / 2) z - hcirc ω (N + 1) 0)) -
          ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω (N + 1) 0))) ∂ν| ∂P :=
        lintegral_congr_ae (heq.mono fun ω hω => congrArg (fun y => ENNReal.ofReal |y|) hω)
    _ = ENNReal.ofReal (∫ ω, |∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) *
          rexp (γ * (hcirc ω (ε / 2) z - hcirc ω (N + 1) 0)) -
          ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω (N + 1) 0))) ∂ν| ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => abs_nonneg _)).symm
    _ ≤ ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * ((B * I / τ + τ) / 2 +
          2 * (b - a) * rexp (L * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)))) :=
        ENNReal.ofReal_le_ofReal hM
    _ = ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * (B / τ / 2) * I + ε ^ (γ ^ 2 / 2) * (τ / 2 +
          2 * (b - a) * rexp (L * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)))) := by
        congr 1
        ring
    _ ≤ ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * (B / τ / 2)) * ENNReal.ofReal I +
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * (τ / 2 +
          2 * (b - a) * rexp (L * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)))) := by
        rw [← ENNReal.ofReal_mul hc1]
        exact ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * (B / τ / 2)) * (ENNReal.ofReal ((2 * ε) ^ β) *
          ∫⁻ s in Ioc a b, ∫⁻ t in Ioc a b,
            (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-β)) +
        ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * (τ / 2 +
          2 * (b - a) * rexp (L * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)))) := by
        gcongr
        exact hIle.trans (pathOccupation_prod_lt_le w a b (by linarith) hβ)
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc1]

/-- The `L¹` bound in exponential form along the dyadic scales `ε = 2^{-k}`: with
`τ = ε^{(β - p)/2}`, `p = 2γ² - (2γ - α)²/2` and `e = (β - γ² + (2γ - α)²/2) / 2`, the expected
recentred increment is at most `K₁ ε^e ∫∫ |w_s - w_t|^{-β} + ε^e / 2 + K₃ ε^{(α - γ)²/2}`. -/
theorem lintegral_ofReal_abs_integral_dyadicIncrement_le_exp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (k : ℕ) {N : ℝ} (hN : 0 ≤ N) {a b : ℝ}
    (hab : a ≤ b) {w : ContinuousPath ℂ} (hw : ∀ v ∈ Ioc a b, ‖w v.toNNReal‖ ≤ N)
    {γ α β : ℝ} (hγα : γ ≤ α) (hα : α ≤ 2 * γ) (hβ : 0 < β) :
    ∫⁻ ω, ENNReal.ofReal |∫ v in Ioc a b, (dyadicScale (k + 1) ^ (γ ^ 2 / 2) *
        rexp (γ * (hcirc ω (dyadicScale (k + 1)) (w v.toNNReal) - hcirc ω (N + 1) 0)) -
        dyadicScale k ^ (γ ^ 2 / 2) *
          rexp (γ * (hcirc ω (dyadicScale k) (w v.toNNReal) - hcirc ω (N + 1) 0)))| ∂P ≤
      ENNReal.ofReal ((rexp (γ ^ 2 * Real.log 2) - 1) *
          rexp (Real.log (N + 1) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) * 2 ^ β / 2 *
          rexp (Real.log (dyadicScale k) * ((β - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2))) *
        (∫⁻ s in Ioc a b, ∫⁻ t in Ioc a b,
          (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-β)) +
      ENNReal.ofReal (rexp (Real.log (dyadicScale k) * ((β - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2)) / 2 +
        2 * (b - a) * rexp (Real.log (N + 1) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)) *
          rexp (Real.log (dyadicScale k) * ((α - γ) ^ 2 / 2))) := by
  have hε : 0 < dyadicScale k := dyadicScale_pos k
  have hk1 : dyadicScale (k + 1) = dyadicScale k / 2 := by
    rw [dyadicScale, dyadicScale, pow_succ, div_eq_mul_inv]
  have hR : 0 < N + 1 := by linarith
  rw [hk1]
  set ε := dyadicScale k with hεdef
  set p := 2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2 with hp
  set q := γ ^ 2 / 2 - (α - γ) ^ 2 / 2 with hq
  set e := (β - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2 with he
  set u := Real.log ε with hu
  set v := Real.log (N + 1) with hv
  have h := lintegral_ofReal_abs_integral_increment_le hh hε (dyadicScale_le_one k) hN hab hw
    hγα hα hβ (τ := rexp (u * ((β - p) / 2))) (Real.exp_pos _)
  refine h.trans (le_of_eq ?_)
  have e1 : ε ^ (γ ^ 2 / 2) = rexp (u * (γ ^ 2 / 2)) := Real.rpow_def_of_pos hε _
  have e2 : (2 * ε) ^ β = rexp (Real.log 2 * β) * rexp (u * β) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_mul two_ne_zero hε.ne', ← Real.exp_add, hu]
    congr 1
    ring
  have e3 : (2 : ℝ) ^ β = rexp (Real.log 2 * β) := Real.rpow_def_of_pos two_pos _
  have e4 : Real.log ((N + 1) / ε) = v - u := Real.log_div hR.ne' hε.ne'
  have k1 : rexp (u * (γ ^ 2 / 2)) * rexp ((v - u) * p) * rexp (u * β) *
      (rexp (u * ((β - p) / 2)))⁻¹ = rexp (v * p) * rexp (u * e) := by
    rw [← Real.exp_neg]
    simp only [← Real.exp_add]
    congr 1
    rw [he, hp]
    ring
  have k2 : rexp (u * (γ ^ 2 / 2)) * rexp (u * ((β - p) / 2)) = rexp (u * e) := by
    rw [← Real.exp_add]
    congr 1
    rw [he, hp]
    ring
  have k3 : rexp (u * (γ ^ 2 / 2)) * rexp ((v - u) * q) =
      rexp (v * q) * rexp (u * ((α - γ) ^ 2 / 2)) := by
    simp only [← Real.exp_add]
    congr 1
    rw [hq]
    ring
  rw [e1, e2, e3, e4]
  congr 1
  · congr 2
    calc _ = (rexp (γ ^ 2 * Real.log 2) - 1) * rexp (Real.log 2 * β) / 2 *
          (rexp (u * (γ ^ 2 / 2)) * rexp ((v - u) * p) * rexp (u * β) *
            (rexp (u * ((β - p) / 2)))⁻¹) := by ring
      _ = _ := by rw [k1]; ring
  · congr 1
    linear_combination (1 / 2 : ℝ) * k2 + 2 * (b - a) * k3

/-- The Brownian inverse-power interval energies over `(a, b]` have finite expectation for
`0 < β < 2`. -/
theorem lintegral_planarBrownianMotion_Ioc_pair_lt_top (x : ℂ) {β : ℝ} (hβ : 0 < β)
    (hβ2 : β < 2) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫⁻ w, (∫⁻ s in Ioc a b, ∫⁻ t in Ioc a b,
      (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-β)) ∂(planarBrownianMotion x) < ⊤ := by
  obtain ⟨C, hC, hCeq⟩ := exists_planarBrownianMotion_interval_pair_enorm_rpow_neg x hβ hβ2
  set ν := Measure.map Real.toNNReal (volume.restrict (Icc a (a + (b - a)))) with hνdef
  have hFle : ∀ w : ContinuousPath ℂ, (∫⁻ s in Ioc a b, ∫⁻ t in Ioc a b,
      (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-β)) ≤
      ∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖w p.1 - w p.2‖) ^ (-β) ∂(ν.prod ν) := by
    intro w
    have hg : Measurable (fun p : ℝ≥0 × ℝ≥0 => (ENNReal.ofReal ‖w p.1 - w p.2‖) ^ (-β)) :=
      ((continuous_norm.comp ((w.continuous.comp continuous_fst).sub
        (w.continuous.comp continuous_snd))).measurable.ennreal_ofReal).pow_const _
    have hab2 : a + (b - a) = b := by ring
    rw [lintegral_prod _ hg.aemeasurable, hνdef, hab2,
      lintegral_map (hg.lintegral_prod_right') measurable_real_toNNReal]
    have hin : ∀ s : ℝ, ∫⁻ t, (ENNReal.ofReal ‖w s.toNNReal - w t‖) ^ (-β)
        ∂(Measure.map Real.toNNReal (volume.restrict (Icc a b))) =
        ∫⁻ t in Icc a b, (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-β) := by
      intro s
      have hgs : Measurable (fun t : ℝ≥0 => (ENNReal.ofReal ‖w s.toNNReal - w t‖) ^ (-β)) :=
        ((continuous_norm.comp (continuous_const.sub w.continuous)).measurable.ennreal_ofReal).pow_const _
      rw [lintegral_map hgs measurable_real_toNNReal]
    simp_rw [hin]
    refine (lintegral_mono fun s => ?_).trans
      (lintegral_mono' (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) le_rfl)
    exact lintegral_mono' (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) le_rfl
  calc _ ≤ ∫⁻ w, ∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖w p.1 - w p.2‖) ^ (-β) ∂(ν.prod ν)
        ∂(planarBrownianMotion x) := lintegral_mono hFle
    _ = (ENNReal.ofReal (b - a)) ^ (2 - β / 2) * C := hCeq a (b - a) ha (sub_pos.mpr hab)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith)
        ENNReal.ofReal_ne_top) hC

end HarmonicBalls
