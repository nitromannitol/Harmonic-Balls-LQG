import HarmonicBalls.Proofs.Potential.LQGClockSquareVisitComparison
import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability
import LatticeProb.Gauss.GFFAffineInvariance

/-! # Scale recursion for stopped annular occupation moments

A moment profile indexed by the smoothing scale that satisfies a contracting
recursion towards larger scales is bounded uniformly on all small scales. For a
subcritical order, the square decomposition of the half disc, combined with a
logarithmic return factor, has a contracting coefficient.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal Topology
open Filter
open HarmonicBalls.Section6

namespace HarmonicBalls

/-- A nonnegative profile on smoothing scales that contracts towards larger
scales and is bounded on one scale window is bounded on all smaller scales. -/
theorem le_of_scale_recursion {M : ℝ → ℝ≥0∞} {ρ η : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hη : 0 < η) {A B θ : ℝ≥0∞} (hθ : θ < 1)
    (hrec : ∀ ε, 0 < ε → ε < η → M ε ≤ A + θ * M (ε / ρ))
    (hbase : ∀ ε, η ≤ ε → ε < η / ρ → M ε ≤ B) :
    ∀ ε, 0 < ε → ε < η / ρ → M ε ≤ A * (1 - θ)⁻¹ + B := by
  set K := A * (1 - θ)⁻¹ + B with hK
  have h1 : (1 - θ) ≠ 0 := (tsub_pos_of_lt hθ).ne'
  have h2 : (1 - θ) ≠ ⊤ := ENNReal.sub_ne_top ENNReal.one_ne_top
  have hinv : (1 - θ)⁻¹ = 1 + θ * (1 - θ)⁻¹ := by
    calc
      (1 - θ)⁻¹ = ((1 - θ) + θ) * (1 - θ)⁻¹ := by rw [tsub_add_cancel_of_le hθ.le, one_mul]
      _ = 1 + θ * (1 - θ)⁻¹ := by rw [add_mul, ENNReal.mul_inv_cancel h1 h2]
  have hstep : A + θ * K ≤ K := by
    calc
      A + θ * K = A * (1 + θ * (1 - θ)⁻¹) + θ * B := by
        rw [hK]
        ring
      _ = A * (1 - θ)⁻¹ + θ * B := by rw [← hinv]
      _ ≤ K := by
        rw [hK]
        exact add_le_add le_rfl (mul_le_of_le_one_left zero_le hθ.le)
  have hBK : B ≤ K := le_add_self
  have hind : ∀ n : ℕ, ∀ ε, η * ρ ^ n ≤ ε → ε < η / ρ → M ε ≤ K := by
    intro n
    induction n with
    | zero =>
      intro ε hε hε2
      simp only [pow_zero, mul_one] at hε
      exact (hbase ε hε hε2).trans hBK
    | succ n ih =>
      intro ε hε hε2
      by_cases hεη : η ≤ ε
      · exact (hbase ε hεη hε2).trans hBK
      · replace hεη : ε < η := not_le.mp hεη
        have hεpos : 0 < ε := lt_of_lt_of_le (by positivity) hε
        have hn : η * ρ ^ n ≤ ε / ρ := by
          rw [le_div_iff₀ hρ, mul_assoc, ← pow_succ]
          exact hε
        have hn2 : ε / ρ < η / ρ := div_lt_div_of_pos_right hεη hρ
        calc
          M ε ≤ A + θ * M (ε / ρ) := hrec ε hεpos hεη
          _ ≤ A + θ * K := by gcongr; exact ih (ε / ρ) hn hn2
          _ ≤ K := hstep
  intro ε hε hε2
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / η by positivity) hρ1
  apply hind n ε _ hε2
  have := (lt_div_iff₀ hη).mp hn
  linarith [mul_comm η (ρ ^ n)]

/-- For a subcritical order there is a grid scale at which the square
coefficient, multiplied by the logarithmic return factor, is below one half. -/
theorem exists_annular_square_return_coefficient_lt_half {γ q : ℝ}
    (hq : 1 < q) (hγq : q * γ ^ 2 < 4) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 10 ∧
      18 * ((LatticeProb.squareIndex r).card : ℝ) * ((4 * r) ^ 2) ^ q *
        Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) *
        (q * (Real.log 2 - Real.log r) / (Real.log (3 * r / 2) - Real.log r)) ^ q < 1 / 2 := by
  let ζ : ℝ := q * (2 + γ ^ 2 / 2) - q ^ 2 * γ ^ 2 / 2
  have hζ : 0 < ζ - 2 := by
    have heq : ζ - 2 = (q - 1) * (4 - q * γ ^ 2) / 2 := by dsimp [ζ]; ring
    rw [heq]
    apply div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)
  have hq0 : 0 < q := by linarith
  have hl32 : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  let K : ℝ := 4608 * (4 : ℝ) ^ (ζ - 2) * (2 * q / Real.log (3 / 2)) ^ q
  have hK : 0 < K := by positivity
  have hlim : Tendsto (fun L : ℝ => L ^ q * Real.exp (-(ζ - 2) * L)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q (ζ - 2) hζ
  obtain ⟨L, hLsmall, hL10⟩ := ((hlim.eventually (gt_mem_nhds
    (show (0 : ℝ) < 1 / (2 * K) by positivity))).and
    (eventually_ge_atTop (Real.log 10))).exists
  have hl2 : Real.log 2 ≤ Real.log 10 := Real.log_le_log (by norm_num) (by norm_num)
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < L := by linarith
  let r : ℝ := Real.exp (-L)
  have hr : 0 < r := Real.exp_pos _
  have hlogr : Real.log r = -L := Real.log_exp _
  have hr10 : r ≤ 1 / 10 := by
    have h10 : Real.exp (-Real.log 10) = 1 / 10 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 10)]
      norm_num
    calc r = Real.exp (-L) := rfl
      _ ≤ Real.exp (-Real.log 10) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 10 := h10
  refine ⟨r, hr, hr10, ?_⟩
  set R : ℝ := 4 * r with hRdef
  have hR : 0 < R := by positivity
  have hR1 : R ≤ 1 := by rw [hRdef]; linarith
  -- the square coefficient
  have hN : ((LatticeProb.squareIndex r).card : ℝ) ≤ 256 / R ^ 2 := by
    have hc := LatticeProb.card_squareIndex_le hr (by linarith : r ≤ 1)
    have heq : 16 / r ^ 2 = 256 / R ^ 2 := by rw [hRdef]; field_simp; ring
    rwa [heq] at hc
  have hid : (R ^ 2) ^ q * Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log R) / 2) = R ^ ζ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    rw [Real.rpow_def_of_pos hR, Real.rpow_def_of_pos hR, ← Real.exp_add]
    congr 1
    dsimp [ζ]
    ring
  have hpow : R ^ ζ = R ^ (ζ - 2) * R ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hR]
    congr 1
    ring
  have hsq : 18 * ((LatticeProb.squareIndex r).card : ℝ) * (R ^ 2) ^ q *
      Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log R) / 2) ≤ 4608 * R ^ (ζ - 2) := by
    calc
      _ = 18 * ((LatticeProb.squareIndex r).card : ℝ) * R ^ ζ := by rw [← hid]; ring
      _ ≤ 18 * (256 / R ^ 2) * R ^ ζ := by gcongr
      _ = 4608 * R ^ (ζ - 2) := by rw [hpow]; field_simp; norm_num
  have hRpow : R ^ (ζ - 2) = (4 : ℝ) ^ (ζ - 2) * Real.exp (-(ζ - 2) * L) := by
    rw [hRdef, Real.mul_rpow (by norm_num) hr.le, Real.rpow_def_of_pos hr, hlogr]
    congr 2
    ring
  -- the return factor
  have hlog32 : Real.log (3 * r / 2) = Real.log (3 / 2) + Real.log r := by
    rw [show 3 * r / 2 = (3 / 2) * r by ring, Real.log_mul (by norm_num) hr.ne']
  have hfac : q * (Real.log 2 - Real.log r) / (Real.log (3 * r / 2) - Real.log r) ≤
      2 * q / Real.log (3 / 2) * L := by
    rw [hlog32, hlogr]
    have h1 : Real.log (3 / 2) + -L - -L = Real.log (3 / 2) := by ring
    rw [h1, div_le_iff₀ hl32]
    have : q * (Real.log 2 - -L) ≤ q * (2 * L) := by
      apply mul_le_mul_of_nonneg_left _ hq0.le
      linarith
    calc q * (Real.log 2 - -L) ≤ q * (2 * L) := this
      _ = 2 * q / Real.log (3 / 2) * L * Real.log (3 / 2) := by field_simp
  have hfac0 : 0 ≤ q * (Real.log 2 - Real.log r) / (Real.log (3 * r / 2) - Real.log r) := by
    rw [hlog32, hlogr]
    apply div_nonneg (mul_nonneg hq0.le (by linarith)) (by linarith)
  have hret : (q * (Real.log 2 - Real.log r) / (Real.log (3 * r / 2) - Real.log r)) ^ q ≤
      (2 * q / Real.log (3 / 2)) ^ q * L ^ q := by
    rw [← Real.mul_rpow (by positivity) hL.le]
    exact Real.rpow_le_rpow hfac0 hfac hq0.le
  have hsq0 : 0 ≤ 18 * ((LatticeProb.squareIndex r).card : ℝ) * (R ^ 2) ^ q *
      Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log R) / 2) := by positivity
  calc
    _ ≤ (4608 * R ^ (ζ - 2)) * ((2 * q / Real.log (3 / 2)) ^ q * L ^ q) :=
      mul_le_mul hsq hret (by positivity) (by positivity)
    _ = K * (L ^ q * Real.exp (-(ζ - 2) * L)) := by rw [hRpow]; ring
    _ < K * (1 / (2 * K)) := mul_lt_mul_of_pos_left hLsmall hK
    _ = 1 / 2 := by field_simp

/-- An occupation integral of a restricted density over a time interval is the
integral over the times at which the path lies in the restriction. -/
theorem lintegral_Ioc_indicator_comp_eq (κ : ℝ → ℂ) (hκ : Measurable κ) (A : Set ℂ)
    (hA : MeasurableSet A) (g : ℂ → ℝ≥0∞) (T : ℝ) :
    (∫⁻ t in Ioc 0 T, A.indicator g (κ t)) = ∫⁻ t in {t | κ t ∈ A} ∩ Ioc 0 T, g (κ t) := by
  have hS : MeasurableSet {t | κ t ∈ A} := hA.preimage hκ
  have heq : (fun t => A.indicator g (κ t)) = {t | κ t ∈ A}.indicator (fun t => g (κ t)) := by
    funext t
    by_cases ht : κ t ∈ A
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ {t | κ t ∈ A} from ht)]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show t ∉ {t | κ t ∈ A} from ht)]
  rw [heq, lintegral_indicator hS, Measure.restrict_restrict hS]

/-- Before a finite time, the occupation of a restricted density is the restricted
integral over a half-open time interval. -/
theorem lintegral_stopped_indicator_eq (b : ContinuousPath ℂ) (g : ℂ → ℝ≥0∞) {T : ℝ≥0∞}
    (hT : T ≠ ⊤) :
    (∫⁻ s, {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T}.indicator (fun s => g (b s.toNNReal)) s) =
      ∫⁻ t in Ioc 0 T.toReal, g (b t.toNNReal) := by
  have hset : {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T} = Ico 0 T.toReal := by
    ext s
    simp only [mem_ofPred_eq, mem_Ico]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h0, (ENNReal.ofReal_lt_iff_lt_toReal h0 hT).mp h1⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h0, (ENNReal.ofReal_lt_iff_lt_toReal h0 hT).mpr h1⟩
  rw [hset, lintegral_indicator measurableSet_Ico, Measure.restrict_congr_set Ico_ae_eq_Ioc]

/-- For a field that agrees with the circle averages, the occupation of a
restricted normalized density before a finite time is the time integral of the
circle-average density over the restricted times. -/
theorem pathOccupationBefore_indicator_normalizedCircleDensity_eq {Ω : Type*}
    {H hcirc : Ω → ℝ → ℂ → ℝ} {ω : Ω} (hω : ∀ ε z, H ω ε z = hcirc ω ε z)
    {ε : ℝ} (hε : 0 < ε) (γ : ℝ) (A : Set ℂ) (hA : MeasurableSet A) (b : ContinuousPath ℂ)
    {T : ℝ≥0∞} (hT : T ≠ ⊤) :
    pathOccupationBefore (A.indicator (normalizedCircleDensity H γ ε ω)) T b =
      ∫⁻ t in {t | b t.toNNReal ∈ A} ∩ Ioc 0 T.toReal,
        ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω) := by
  have hb : Measurable (fun t : ℝ => b t.toNNReal) := by fun_prop
  unfold pathOccupationBefore
  rw [lintegral_stopped_indicator_eq b _ hT, lintegral_Ioc_indicator_comp_eq _ hb A hA]
  apply lintegral_congr
  intro t
  simp only [normalizedCircleDensity, hω]
  rw [gmcDensity_eq_exp_normalized hcirc hε]

/-- The field-Brownian moment of the closed half-disc occupation of the normalized
circle-average density before the exit from the unit disc. -/
noncomputable def stoppedHalfDiscMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : Ω → ℝ → ℂ → ℝ) (γ δ q : ℝ) (y : ℂ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ b, pathOccupationBefore ({z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator
    (normalizedCircleDensity H γ δ ω)) (ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) b) b ^ q
    ∂planarBrownianMotion y ∂P

/-- The stopped half-disc moment only depends on the field up to a null set. -/
theorem stoppedHalfDiscMoment_congr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {H H' : Ω → ℝ → ℂ → ℝ} (hHH : ∀ᵐ ω ∂P, ∀ ε z, H ω ε z = H' ω ε z) (γ δ q : ℝ) (y : ℂ) :
    stoppedHalfDiscMoment P H γ δ q y = stoppedHalfDiscMoment P H' γ δ q y := by
  unfold stoppedHalfDiscMoment
  apply lintegral_congr_ae
  filter_upwards [hHH] with ω hω
  have h : normalizedCircleDensity H γ δ ω = normalizedCircleDensity H' γ δ ω := by
    funext w
    simp only [normalizedCircleDensity, hω]
  rw [h]

/-- The reference square lies in the closed half disc. -/
theorem lqgSquare_subset_halfDisc :
    LatticeProb.LQG.lqgSquare ⊆ {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} := by
  intro w hw
  have h := LatticeProb.LQG.lqgSquare_subset_closedBall hw
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact ⟨norm_nonneg _, by linarith⟩

/-- Exit times of a bounded open set have `q`-th moments bounded uniformly in the
start, for `0 ≤ q ≤ 2`. -/
theorem exists_uniform_lintegral_exitTime_rpow_le {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) {q : ℝ} (hq0 : 0 ≤ q) (hq2 : q ≤ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x : ℂ,
      (∫⁻ b, (ENNReal.ofReal (ContinuousPath.exitTime D b).toReal) ^ q
        ∂planarBrownianMotion x) ≤ C := by
  obtain ⟨lam, hlam, C, hC, hbound⟩ :=
    exists_uniform_planarBrownianMotion_exitTime_exponential_moment hD hDb
  refine ⟨ENNReal.ofReal (1 + 2 / lam ^ 2) * C, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC, ?_⟩
  intro x
  have hK0 : ENNReal.ofReal (1 + 2 / lam ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  calc
    _ ≤ ∫⁻ b, ENNReal.ofReal (1 + 2 / lam ^ 2) *
        ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime D) b
        ∂planarBrownianMotion x := by
      refine lintegral_mono fun b => ?_
      show (ENNReal.ofReal (ContinuousPath.exitTime D b).toReal) ^ q ≤
        ENNReal.ofReal (1 + 2 / lam ^ 2) *
          ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime D) b
      by_cases hb : ContinuousPath.exitTime D b = ⊤
      · rw [ContinuousPath.exponentialStoppingWeight_of_eq_top lam _ hb, ENNReal.mul_top hK0]
        exact le_top
      · rw [ContinuousPath.exponentialStoppingWeight_of_ne_top lam _ hb]
        set τ := (ContinuousPath.exitTime D b).toReal with hτdef
        have hτ : 0 ≤ τ := ENNReal.toReal_nonneg
        rw [ENNReal.ofReal_rpow_of_nonneg hτ hq0, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : τ ^ q ≤ 1 + τ ^ 2 := by
          rcases le_total τ 1 with h | h
          · have := Real.rpow_le_one hτ h hq0
            nlinarith [sq_nonneg τ]
          · have h' : τ ^ q ≤ τ ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hq2
            rw [Real.rpow_two] at h'
            linarith
        have hlt : 0 ≤ lam * τ := mul_nonneg hlam.le hτ
        have h2 : τ ^ 2 ≤ 2 / lam ^ 2 * Real.exp (lam * τ) := by
          have hq := Real.quadratic_le_exp_of_nonneg hlt
          have e : (lam * τ) ^ 2 = τ ^ 2 * lam ^ 2 := by ring
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          nlinarith
        have h3 : 1 ≤ Real.exp (lam * τ) := Real.one_le_exp hlt
        nlinarith
    _ = ENNReal.ofReal (1 + 2 / lam ^ 2) * ∫⁻ b,
        ContinuousPath.exponentialStoppingWeight lam (ContinuousPath.exitTime D) b
          ∂planarBrownianMotion x :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_right (hbound x) _

/-- Above a positive smoothing cutoff, the stopped half-disc moment is bounded by
the cutoff factor times the moment of the exit time. -/
theorem stoppedHalfDiscMoment_le_of_scale_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε) (hε2 : ε ≤ 1 / 2) (γ : ℝ) {q : ℝ} (hq : 1 ≤ q)
    (x : ℂ) :
    stoppedHalfDiscMoment P hcirc γ ε q x ≤
      ENNReal.ofReal (η ^ (-(γ ^ 2 * q * (q - 1) / 2))) *
        ∫⁻ b, (ENNReal.ofReal (ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) b).toReal) ^ q
          ∂planarBrownianMotion x := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hε : 0 < ε := hη.trans_le hηε
  have hq0 : 0 < q := by linarith
  set D : Set ℂ := Metric.ball (0 : ℂ) 1 with hDdef
  set Td : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} with hTd
  have hTdm : MeasurableSet Td := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  set K := ENNReal.ofReal (η ^ (-(γ ^ 2 * q * (q - 1) / 2))) with hK
  let f : Ω → ℂ → ℝ≥0∞ := fun ω => Td.indicator (normalizedCircleDensity H γ ε ω)
  have hf : Measurable (Function.uncurry f) :=
    measurable_uncurry_indicator (measurable_normalizedCircleDensity (hHm ε hε) γ) hTdm
  -- one-point moments
  have hpt (w : ℂ) : (∫⁻ ω, f ω w ^ q ∂P) ≤ K := by
    by_cases hw : w ∈ Td
    · have hw1 : ‖w‖ + ε ≤ 1 := by have := hw.2; linarith
      have heq : (∫⁻ ω, f ω w ^ q ∂P) = ∫⁻ ω,
          (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε w))) ^ q ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hHae] with ω hω
        simp only [f, Set.indicator_of_mem hw, normalizedCircleDensity, hω]
        rw [← gmcDensity_eq_exp_normalized hcirc hε]
        rfl
      rw [heq, hh.lintegral_rpow_mul_exp_circle hε hw1 (γ ^ 2 / 2) γ hq0.le, hK]
      apply ENNReal.ofReal_le_ofReal
      have he : q * (γ ^ 2 / 2) - q ^ 2 * γ ^ 2 / 2 = -(γ ^ 2 * q * (q - 1) / 2) := by ring
      rw [he]
      apply Real.rpow_le_rpow_of_nonpos hη hηε
      have : 0 ≤ γ ^ 2 * q * (q - 1) := by
        have := sq_nonneg γ
        have : 0 ≤ q - 1 := by linarith
        positivity
      linarith
    · simp only [f, Set.indicator_of_notMem hw, ENNReal.zero_rpow_of_pos hq0, lintegral_zero]
      exact zero_le
  have hocc : Measurable (fun p : Ω × ContinuousPath ℂ =>
      pathOccupationBefore (f p.1) (ContinuousPath.exitTime D p.2) p.2 ^ q) :=
    (measurable_pathOccupationBefore (fun p : Ω × ContinuousPath ℂ => f p.1)
      (hf.comp (measurable_fst.fst.prodMk measurable_snd))
      (fun p => ContinuousPath.exitTime D p.2)
      ((ContinuousPath.measurable_exitTime D Metric.isOpen_ball).comp measurable_snd)
      (fun p => p.2) measurable_snd).pow_const q
  rw [stoppedHalfDiscMoment_congr (hHae.mono fun ω hω ε z => (hω ε z).symm)]
  unfold stoppedHalfDiscMoment
  change (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω) (ContinuousPath.exitTime D b) b ^ q
    ∂planarBrownianMotion x ∂P) ≤ _
  rw [lintegral_lintegral_swap hocc.aemeasurable]
  calc
    _ ≤ ∫⁻ b, K * (ENNReal.ofReal (ContinuousPath.exitTime D b).toReal) ^ q
        ∂planarBrownianMotion x := by
      apply lintegral_mono_ae
      filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x
        (Metric.isBounded_ball : Bornology.IsBounded D)] with b hb
      set I := Ioc (0 : ℝ) (ContinuousPath.exitTime D b).toReal with hI
      have hbm : Measurable (fun t : ℝ => b t.toNNReal) := by fun_prop
      have hvol : (volume.restrict I) univ = ENNReal.ofReal (ContinuousPath.exitTime D b).toReal := by
        rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
      have hjoint : Measurable (fun p : Ω × ℝ => f p.1 (b p.2.toNNReal) ^ q) :=
        (hf.comp (measurable_fst.prodMk (hbm.comp measurable_snd))).pow_const q
      calc
        (∫⁻ ω, pathOccupationBefore (f ω) (ContinuousPath.exitTime D b) b ^ q ∂P) =
            ∫⁻ ω, (∫⁻ t in I, f ω (b t.toNNReal)) ^ q ∂P := by
          apply lintegral_congr
          intro ω
          unfold pathOccupationBefore
          rw [lintegral_stopped_indicator_eq b _ hb.ne]
        _ ≤ ∫⁻ ω, (volume.restrict I) univ ^ (q - 1) *
            (∫⁻ t in I, f ω (b t.toNNReal) ^ q) ∂P := by
          apply lintegral_mono
          intro ω
          exact LatticeProb.lintegral_rpow_le_measure_univ_mul _ hq
            ((hf.comp (measurable_const.prodMk hbm)).aemeasurable)
        _ = (volume.restrict I) univ ^ (q - 1) *
            ∫⁻ t in I, (∫⁻ ω, f ω (b t.toNNReal) ^ q ∂P) := by
          rw [lintegral_const_mul _ (hjoint.lintegral_prod_right'), lintegral_lintegral_swap
            hjoint.aemeasurable]
        _ ≤ (volume.restrict I) univ ^ (q - 1) * ∫⁻ _ in I, K := by
          gcongr with t
          exact hpt _
        _ = K * (ENNReal.ofReal (ContinuousPath.exitTime D b).toReal) ^ q := by
          rw [lintegral_const, hvol]
          set u := ENNReal.ofReal (ContinuousPath.exitTime D b).toReal
          calc
            _ = K * (u ^ (q - 1) * u) := by ring
            _ = K * u ^ ((q - 1) + 1) := by
              rw [ENNReal.rpow_add_of_nonneg (q - 1) 1 (by linarith) (by norm_num),
                ENNReal.rpow_one]
            _ = K * u ^ q := by congr 2; ring
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Scale recursion.** The stopped half-disc moment at smoothing `4 r δ` is at most
the square coefficient, including the logarithmic return factor, times the largest
stopped half-disc moment at smoothing `δ`, plus a separated-pair term controlled by
the moment of the exit time. -/
theorem stoppedHalfDiscMoment_le_square_return_add
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (γ : ℝ) {q : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (x : ℂ) :
    stoppedHalfDiscMoment P hcirc γ (4 * r * δ) q x ≤
      18 * ((LatticeProb.squareIndex r).card : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
          ENNReal.ofReal ((4 * r) ^ 2) ^ q *
          ENNReal.ofReal ((q * (Real.log 2 - Real.log r) /
            (Real.log (3 * r / 2) - Real.log r)) ^ q)) *
        (⨆ y, stoppedHalfDiscMoment P hcirc γ δ q y) +
      ((LatticeProb.squareIndex r).card : ℝ≥0∞) * ((LatticeProb.squareIndex r).card : ℝ≥0∞) *
        ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) ^ (q / 2) *
        ∫⁻ b, (ENNReal.ofReal (ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) b).toReal) ^ q
          ∂planarBrownianMotion x := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hq0 : 0 < q := by linarith
  have hε : 0 < 4 * r * δ := by positivity
  have hε2 : 4 * r * δ ≤ 1 / 2 := by nlinarith
  set S := LatticeProb.squareIndex r with hS
  set D : Set ℂ := Metric.ball (0 : ℂ) 1 with hDdef
  set Td : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} with hTd
  set C := ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) with hCdef
  set F := ENNReal.ofReal ((q * (Real.log 2 - Real.log r) /
    (Real.log (3 * r / 2) - Real.log r)) ^ q) with hFdef
  set Φ := ⨆ y, stoppedHalfDiscMoment P hcirc γ δ q y with hΦ
  have hDo : IsOpen D := Metric.isOpen_ball
  have hTdm : MeasurableSet Td := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hsqm (i : ℤ × ℤ) : MeasurableSet (LatticeProb.dyadicSquare r i ∩ Td) :=
    (LatticeProb.measurableSet_dyadicSquare r i).inter hTdm
  let fA : Set ℂ → Ω → ℂ → ℝ≥0∞ := fun A ω =>
    A.indicator (normalizedCircleDensity H γ (4 * r * δ) ω)
  have hfA (A : Set ℂ) (hA : MeasurableSet A) : Measurable (Function.uncurry (fA A)) :=
    measurable_uncurry_indicator (measurable_normalizedCircleDensity (hHm _ hε) γ) hA
  have hocc (A : Set ℂ) (hA : MeasurableSet A) : Measurable (fun p : Ω × ContinuousPath ℂ =>
      pathOccupationBefore (fA A p.1) (ContinuousPath.exitTime D p.2) p.2 ^ q) :=
    (measurable_pathOccupationBefore (fun p : Ω × ContinuousPath ℂ => fA A p.1)
      ((hfA A hA).comp (measurable_fst.fst.prodMk measurable_snd))
      (fun p => ContinuousPath.exitTime D p.2)
      ((ContinuousPath.measurable_exitTime D hDo).comp measurable_snd)
      (fun p => p.2) measurable_snd).pow_const q
  let G : ℤ × ℤ → ContinuousPath ℂ → ℝ≥0∞ := fun i b => ∫⁻ ω,
    pathOccupationBefore (fA (LatticeProb.dyadicSquare r i ∩ Td) ω)
      (ContinuousPath.exitTime D b) b ^ q ∂P
  have hG (i : ℤ × ℤ) : Measurable (G i) := (hocc _ (hsqm i)).lintegral_prod_left'
  let X : ContinuousPath ℂ → ℝ≥0∞ := fun b =>
    ((LatticeProb.squareIndex r).card : ℝ≥0∞) * (((LatticeProb.squareIndex r).card : ℝ≥0∞) *
      (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) *
        (ENNReal.ofReal ((ContinuousPath.exitTime D b).toReal - 0) *
          ENNReal.ofReal ((ContinuousPath.exitTime D b).toReal - 0))) ^ (q / 2))
  -- pathwise square decomposition
  have hpath : ∀ᵐ b ∂planarBrownianMotion x, (∫⁻ ω, pathOccupationBefore (fA Td ω)
      (ContinuousPath.exitTime D b) b ^ q ∂P) ≤ 18 * ∑ i ∈ S, G i b + X b := by
    filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x
      (Metric.isBounded_ball : Bornology.IsBounded D)] with b hb
    have hdec := lintegral_annular_mass_rpow_le_square_moments_add_cell hh b 0
      (ContinuousPath.exitTime D b).toReal 0 hε hε2 hr γ hq0 hq2
    dsimp only at hdec
    have hconv (A : Set ℂ) (hA : MeasurableSet A) : (∫⁻ ω, pathOccupationBefore (fA A ω)
        (ContinuousPath.exitTime D b) b ^ q ∂P) = ∫⁻ ω, (∫⁻ t in {t | b t.toNNReal ∈ A} ∩
          Ioc 0 (ContinuousPath.exitTime D b).toReal, ENNReal.ofReal
            (LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω)) ^ q ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hHae] with ω hω
      rw [pathOccupationBefore_indicator_normalizedCircleDensity_eq hω hε γ A hA b hb.ne]
    rw [hconv Td hTdm]
    refine hdec.trans (le_of_eq ?_)
    congr 1
    all_goals first
      | rfl
      | (congr 1
         apply Finset.sum_congr rfl
         intro i _
         exact (hconv _ (hsqm i)).symm)
  -- one visit and the disc return iteration for each square
  have hsquare (i : ℤ × ℤ) (hi : i ∈ S) : (∫⁻ b, G i b ∂planarBrownianMotion x) ≤
      C * ENNReal.ofReal ((4 * r) ^ 2) ^ q * Φ * F := by
    set z := LatticeProb.dyadicSquareCentre r i with hz
    have hz1 : ‖z‖ < 1 / 2 + r := LatticeProb.norm_dyadicSquareCentre_lt hr hi
    have hDR : D ⊆ Metric.ball z 2 := by
      intro w hw
      rw [Metric.mem_ball, dist_zero_right] at hw
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le _ _
        _ < 2 := by linarith
    have hfQ : ∀ ω w, w ∉ Metric.closedBall z r →
        fA (LatticeProb.dyadicSquare r i ∩ Td) ω w = 0 := by
      intro ω w hw
      apply Set.indicator_of_notMem
      intro hw'
      apply hw
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact (LatticeProb.norm_sub_centre_lt hr hw'.1).le
    have hM : ∀ y ∈ Metric.closedBall z r, (∫⁻ ω, ∫⁻ b, pathOccupationBefore
        (fA (LatticeProb.dyadicSquare r i ∩ Td) ω)
        (min (ContinuousPath.exitTime (Metric.ball z (3 * r / 2)) b)
          (ContinuousPath.exitTime D b)) b ^ q ∂planarBrownianMotion y ∂P) ≤
        C * ENNReal.ofReal ((4 * r) ^ 2) ^ q * Φ := by
      intro y _
      have hvisit := lintegral_square_visit_rpow_le_reference hh hHm hHae hr hr10 hδ hδ2 hi γ hq y
      calc
        _ ≤ ∫⁻ ω, ∫⁻ b, pathOccupationBefore ((LatticeProb.dyadicSquare r i).indicator
            (normalizedCircleDensity H γ (4 * r * δ) ω))
            (ContinuousPath.exitTime (Metric.ball z (3 * r / 2)) b) b ^ q
              ∂planarBrownianMotion y ∂P := by
          refine lintegral_mono fun ω => lintegral_mono fun b => ?_
          exact ENNReal.rpow_le_rpow (pathOccupationBefore_mono
            (fun w => Set.indicator_le_indicator_of_subset inter_subset_left (fun _ => zero_le) w)
            (min_le_left _ _) b) hq0.le
        _ ≤ _ := hvisit
        _ ≤ C * ENNReal.ofReal ((4 * r) ^ 2) ^ q * stoppedHalfDiscMoment P H γ δ q
            ((4 * r)⁻¹ • (y - z)) := by
          refine mul_le_mul_right ?_ _
          refine lintegral_mono fun ω => lintegral_mono fun b => ?_
          refine ENNReal.rpow_le_rpow (pathOccupationBefore_mono
            (fun w => Set.indicator_le_indicator_of_subset lqgSquare_subset_halfDisc
              (fun _ => zero_le) w) ?_ b) hq0.le
          apply ContinuousPath.exitTime_mono
          exact Metric.ball_subset_ball (by norm_num)
        _ ≤ _ := by
          rw [stoppedHalfDiscMoment_congr hHae]
          exact mul_le_mul_right (le_iSup (fun y => stoppedHalfDiscMoment P hcirc γ δ q y) _) _
    have hret := lintegral_pathOccupationBefore_rpow_le_of_disc_return
      (fA (LatticeProb.dyadicSquare r i ∩ Td)) (hfA _ (hsqm i)) (c := z) hr
      (by linarith : r < 3 * r / 2) (by linarith : 3 * r / 2 < 2) hDo hDR hfQ hq hM x
    calc
      (∫⁻ b, G i b ∂planarBrownianMotion x) = ∫⁻ ω, ∫⁻ b, pathOccupationBefore
          (fA (LatticeProb.dyadicSquare r i ∩ Td) ω) (ContinuousPath.exitTime D b) b ^ q
            ∂planarBrownianMotion x ∂P :=
        (lintegral_lintegral_swap (hocc _ (hsqm i)).aemeasurable).symm
      _ ≤ _ := hret
  -- cross term
  have hX (b : ContinuousPath ℂ) : X b = ((LatticeProb.squareIndex r).card : ℝ≥0∞) *
      ((LatticeProb.squareIndex r).card : ℝ≥0∞) * ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) ^ (q / 2) *
      (ENNReal.ofReal (ContinuousPath.exitTime D b).toReal) ^ q := by
    simp only [X, sub_zero]
    set u := ENNReal.ofReal (ContinuousPath.exitTime D b).toReal
    have hq2' : 0 ≤ q / 2 := by positivity
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq2']
    have hu : (u * u) ^ (q / 2) = u ^ q := by
      rw [← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      congr 1
      push_cast
      ring
    rw [hu]
    ring
  -- assembly
  have hsum : Measurable (fun b => ∑ i ∈ S, G i b) := Finset.measurable_sum S (fun i _ => hG i)
  rw [stoppedHalfDiscMoment_congr (hHae.mono fun ω hω ε z => (hω ε z).symm)]
  unfold stoppedHalfDiscMoment
  change (∫⁻ ω, ∫⁻ b, pathOccupationBefore (fA Td ω) (ContinuousPath.exitTime D b) b ^ q
    ∂planarBrownianMotion x ∂P) ≤ _
  rw [lintegral_lintegral_swap (hocc Td hTdm).aemeasurable]
  calc
    _ ≤ ∫⁻ b, 18 * ∑ i ∈ S, G i b + X b ∂planarBrownianMotion x := lintegral_mono_ae hpath
    _ = 18 * ∑ i ∈ S, ∫⁻ b, G i b ∂planarBrownianMotion x +
        ∫⁻ b, X b ∂planarBrownianMotion x := by
      rw [lintegral_add_left' (hsum.const_mul 18).aemeasurable, lintegral_const_mul _ hsum,
        lintegral_finsetSum S (fun i _ => hG i)]
    _ ≤ 18 * ∑ _i ∈ S, C * ENNReal.ofReal ((4 * r) ^ 2) ^ q * Φ * F +
        ∫⁻ b, X b ∂planarBrownianMotion x := by
      gcongr with i hi
      exact hsquare i hi
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      · ring
      · simp only [hX]
        rw [lintegral_const_mul' _ _ ?_]
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          (ENNReal.natCast_ne_top _))
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)

/-- **Smoothing-uniform stopped half-disc moment.** For `γ² < 4` there is an order
`q ∈ (1, 2]` with `q γ² < 4` such that the stopped half-disc moments are bounded
uniformly over all smoothing radii in `(0, 1/2]` and all Brownian starts. -/
theorem exists_uniform_stoppedHalfDiscMoment_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ2 : γ ^ 2 < 4) :
    ∃ q : ℝ, 1 < q ∧ q ≤ 2 ∧ q * γ ^ 2 < 4 ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ε, 0 < ε → ε ≤ 1 / 2 → ∀ x : ℂ, stoppedHalfDiscMoment P hcirc γ ε q x ≤ C := by
  set q : ℝ := 1 + (4 - γ ^ 2) / (8 + γ ^ 2) with hqdef
  have hγ0 : 0 ≤ γ ^ 2 := sq_nonneg γ
  have hd : 0 < 8 + γ ^ 2 := by positivity
  have hfrac : 0 < (4 - γ ^ 2) / (8 + γ ^ 2) := div_pos (by linarith) hd
  have hfrac1 : (4 - γ ^ 2) / (8 + γ ^ 2) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hq1 : 1 < q := by rw [hqdef]; linarith
  have hq2 : q ≤ 2 := by rw [hqdef]; linarith
  have hq0 : 0 < q := by linarith
  have hqγ : q * γ ^ 2 < 4 := by
    have heq : q * γ ^ 2 = 12 * γ ^ 2 / (8 + γ ^ 2) := by
      rw [hqdef]
      field_simp
      ring
    rw [heq, div_lt_iff₀ hd]
    nlinarith
  refine ⟨q, hq1, hq2, hqγ, ?_⟩
  obtain ⟨r, hr, hr10, hcoef⟩ := exists_annular_square_return_coefficient_lt_half hq1 hqγ
  obtain ⟨Cτ, hCτ, hτ⟩ := exists_uniform_lintegral_exitTime_rpow_le Metric.isOpen_ball
    (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball (0 : ℂ) 1)) hq0.le hq2
  set N : ℝ≥0∞ := ((LatticeProb.squareIndex r).card : ℝ≥0∞) with hN
  set f : ℝ := q * (Real.log 2 - Real.log r) / (Real.log (3 * r / 2) - Real.log r) with hf
  set θ : ℝ≥0∞ := 18 * N *
    (ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
      ENNReal.ofReal ((4 * r) ^ 2) ^ q * ENNReal.ofReal (f ^ q)) with hθdef
  set A : ℝ≥0∞ := N * N * ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) ^ (q / 2) * Cτ with hA
  set B : ℝ≥0∞ := ENNReal.ofReal ((2 * r) ^ (-(γ ^ 2 * q * (q - 1) / 2))) * Cτ with hB
  have hθeq : θ = ENNReal.ofReal (18 * ((LatticeProb.squareIndex r).card : ℝ) *
      ((4 * r) ^ 2) ^ q * Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) * f ^ q) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_natCast, ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le, hθdef, hN]
    norm_num
    ring
  have hθ : θ < 1 := by
    rw [hθeq]
    exact ENNReal.ofReal_lt_one.mpr (by linarith [hcoef])
  let M : ℝ → ℝ≥0∞ := fun ε => ⨆ x, stoppedHalfDiscMoment P hcirc γ ε q x
  have hrec : ∀ ε, 0 < ε → ε < 2 * r → M ε ≤ A + θ * M (ε / (4 * r)) := by
    intro ε hε hεη
    apply iSup_le
    intro x
    have h4r : 0 < 4 * r := by positivity
    have hδ : 0 < ε / (4 * r) := by positivity
    have hδ2 : ε / (4 * r) ≤ 1 / 2 := by
      rw [div_le_iff₀ h4r]
      linarith
    have heq : 4 * r * (ε / (4 * r)) = ε := by field_simp
    have h := stoppedHalfDiscMoment_le_square_return_add hh hr hr10 hδ hδ2 γ hq1.le hq2 x
    rw [heq] at h
    calc
      _ ≤ _ := h
      _ ≤ θ * M (ε / (4 * r)) + A := add_le_add le_rfl (mul_le_mul_right (hτ x) _)
      _ = A + θ * M (ε / (4 * r)) := add_comm _ _
  have hhalf : 2 * r / (4 * r) = 1 / 2 := by field_simp; ring
  have hbase' : ∀ ε, 2 * r ≤ ε → ε ≤ 1 / 2 → M ε ≤ B := by
    intro ε h1 h2
    apply iSup_le
    intro x
    exact (stoppedHalfDiscMoment_le_of_scale_lower_bound hh (by positivity) h1 h2 γ hq1.le x).trans
      (mul_le_mul_right (hτ x) _)
  have hmain := le_of_scale_recursion (M := M) (by positivity : 0 < 4 * r)
    (by linarith : 4 * r < 1) (by positivity : 0 < 2 * r) hθ hrec
    (fun ε h1 h2 => hbase' ε h1 (by rw [hhalf] at h2; exact h2.le))
  refine ⟨A * (1 - θ)⁻¹ + B, ?_, ?_⟩
  · have hAt : A < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.natCast_lt_top _) (ENNReal.natCast_lt_top _))
      (ENNReal.rpow_lt_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)) hCτ
    have hBt : B < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCτ
    have hinv : (1 - θ)⁻¹ < ⊤ := ENNReal.inv_lt_top.mpr (tsub_pos_of_lt hθ)
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hAt hinv, hBt⟩
  · intro ε hε hε2 x
    have hx : stoppedHalfDiscMoment P hcirc γ ε q x ≤ M ε :=
      le_iSup (fun x => stoppedHalfDiscMoment P hcirc γ ε q x) x
    rcases lt_or_eq_of_le hε2 with hlt | heq
    · exact hx.trans (hmain ε hε (by rw [hhalf]; exact hlt))
    · refine hx.trans ((hbase' ε ?_ hε2).trans le_add_self)
      rw [heq]
      linarith

/-- **Stopped grid-square moments.** For a grid square of side `r` meeting the half
disc and a smoothing radius `4 r δ` with `δ ≤ 1/2`, the field-Brownian moment of the
occupation of the square before the exit from any open set inside a disc of radius `R`
about its centre is bounded by the Gaussian and time scale factors, the logarithmic
return factor and the largest stopped half-disc moment at smoothing `δ`. -/
theorem lintegral_square_occupation_rpow_le_stoppedHalfDiscMoment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) (γ : ℝ) {q : ℝ} (hq : 1 ≤ q)
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ} (hR : 3 * r / 2 < R)
    (hDR : D ⊆ Metric.ball (LatticeProb.dyadicSquareCentre r i) R) (x : ℂ) :
    (∫⁻ ω, ∫⁻ b, pathOccupationBefore ((LatticeProb.dyadicSquare r i).indicator
      (normalizedCircleDensity hcirc γ (4 * r * δ) ω)) (ContinuousPath.exitTime D b) b ^ q
        ∂planarBrownianMotion x ∂P) ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
        ENNReal.ofReal ((4 * r) ^ 2) ^ q * (⨆ y, stoppedHalfDiscMoment P hcirc γ δ q y) *
        ENNReal.ofReal ((q * (Real.log R - Real.log r) /
          (Real.log (3 * r / 2) - Real.log r)) ^ q) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hq0 : 0 < q := by linarith
  have hε : 0 < 4 * r * δ := by positivity
  set z := LatticeProb.dyadicSquareCentre r i with hz
  set Φ := ⨆ y, stoppedHalfDiscMoment P hcirc γ δ q y with hΦ
  set C := ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) with hCdef
  let f : Ω → ℂ → ℝ≥0∞ := fun ω =>
    (LatticeProb.dyadicSquare r i).indicator (normalizedCircleDensity H γ (4 * r * δ) ω)
  have hf : Measurable (Function.uncurry f) :=
    measurable_uncurry_indicator (measurable_normalizedCircleDensity (hHm _ hε) γ)
      (LatticeProb.measurableSet_dyadicSquare r i)
  have hfQ : ∀ ω w, w ∉ Metric.closedBall z r → f ω w = 0 := by
    intro ω w hw
    apply Set.indicator_of_notMem
    intro hw'
    apply hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (LatticeProb.norm_sub_centre_lt hr hw').le
  have hM : ∀ y ∈ Metric.closedBall z r, (∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω)
      (min (ContinuousPath.exitTime (Metric.ball z (3 * r / 2)) b)
        (ContinuousPath.exitTime D b)) b ^ q ∂planarBrownianMotion y ∂P) ≤
      C * ENNReal.ofReal ((4 * r) ^ 2) ^ q * Φ := by
    intro y _
    have hvisit := lintegral_square_visit_rpow_le_reference hh hHm hHae hr hr10 hδ hδ2 hi γ hq y
    calc
      _ ≤ ∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω)
          (ContinuousPath.exitTime (Metric.ball z (3 * r / 2)) b) b ^ q
            ∂planarBrownianMotion y ∂P := by
        refine lintegral_mono fun ω => lintegral_mono fun b => ?_
        exact ENNReal.rpow_le_rpow (pathOccupationBefore_mono (fun w => le_rfl)
          (min_le_left _ _) b) hq0.le
      _ ≤ _ := hvisit
      _ ≤ C * ENNReal.ofReal ((4 * r) ^ 2) ^ q * stoppedHalfDiscMoment P H γ δ q
          ((4 * r)⁻¹ • (y - z)) := by
        refine mul_le_mul_right ?_ _
        refine lintegral_mono fun ω => lintegral_mono fun b => ?_
        refine ENNReal.rpow_le_rpow (pathOccupationBefore_mono
          (fun w => Set.indicator_le_indicator_of_subset lqgSquare_subset_halfDisc
            (fun _ => zero_le) w) ?_ b) hq0.le
        apply ContinuousPath.exitTime_mono
        exact Metric.ball_subset_ball (by norm_num)
      _ ≤ _ := by
        rw [stoppedHalfDiscMoment_congr hHae]
        exact mul_le_mul_right (le_iSup (fun y => stoppedHalfDiscMoment P hcirc γ δ q y) _) _
  have hret := lintegral_pathOccupationBefore_rpow_le_of_disc_return f hf (c := z) hr
    (by linarith : r < 3 * r / 2) hR hD hDR hfQ hq hM x
  calc
    _ = ∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω) (ContinuousPath.exitTime D b) b ^ q
        ∂planarBrownianMotion x ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hHae] with ω hω
      have h : normalizedCircleDensity hcirc γ (4 * r * δ) ω =
          normalizedCircleDensity H γ (4 * r * δ) ω := by
        funext w
        simp only [normalizedCircleDensity, hω]
      simp only [f, h]
    _ ≤ _ := hret

/-- The displacement of planar Brownian motion at a positive time has the law of the
time-one position from zero, scaled by the square root of the time. -/
theorem planarBrownianMotion_le_norm_sub_eq (w : ℂ) {s : ℝ≥0} (hs : s ≠ 0) (a : ℝ) :
    planarBrownianMotion w {b | a ≤ ‖b s - w‖} =
      planarBrownianMotion 0 {b | a / Real.sqrt s ≤ ‖b 1‖} := by
  have hmap := planarBrownianMotion_map_scaledCenteredPlanarPath w hs
  have hm : MeasurableSet {b : ContinuousPath ℂ | a / Real.sqrt s ≤ ‖b 1‖} :=
    measurableSet_le measurable_const (continuous_eval_const 1).norm.measurable
  rw [← hmap, Measure.map_apply (continuous_scaledCenteredPlanarPath w s).measurable hm]
  have hs' : 0 < Real.sqrt s := Real.sqrt_pos.mpr (lt_of_le_of_ne s.coe_nonneg
    (by exact_mod_cast hs.symm))
  congr 1
  ext b
  simp only [mem_preimage, mem_ofPred_eq]
  change a ≤ ‖b s - w‖ ↔ a / Real.sqrt s ≤ ‖(Real.sqrt s)⁻¹ • (b (s * 1) - w)‖
  rw [mul_one, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs', div_le_iff₀ hs',
    inv_mul_eq_div, div_mul_cancel₀ _ hs'.ne']

/-- The probability that planar Brownian motion from zero is far at time one tends
to zero as the distance tends to infinity. -/
theorem tendsto_planarBrownianMotion_le_norm_one :
    Tendsto (fun u : ℝ => planarBrownianMotion 0 {b | u ≤ ‖b 1‖}) atTop (𝓝 0) := by
  have h := tendsto_measure_iInter_atTop (μ := planarBrownianMotion (0 : ℂ))
    (s := fun u : ℝ => {b : ContinuousPath ℂ | u ≤ ‖b 1‖})
    (fun u => (measurableSet_le measurable_const
      (continuous_eval_const 1).norm.measurable).nullMeasurableSet)
    (fun u v huv b hb => le_trans huv hb) ⟨0, measure_ne_top _ _⟩
  have he : (⋂ u : ℝ, {b : ContinuousPath ℂ | u ≤ ‖b 1‖}) = ∅ := by
    ext b
    simp only [mem_iInter, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall, not_le]
    exact ⟨‖b 1‖ + 1, by linarith⟩
  rw [he, measure_empty] at h
  exact h

/-- **Short-time exit from a ball.** If, at times up to `h`, Brownian motion stays
within `ρ / 2` of its start with probability at least one half, then the probability
of leaving the ball of radius `ρ` by time `h` is at most four times the probability of
a displacement `ρ / 2` at time `2 h`. -/
theorem planarBrownianMotion_exitTime_ball_le_le (y : ℂ) {ρ h : ℝ} (hρ : 0 < ρ) (hh : 0 < h)
    (hG : planarBrownianMotion 0 {b | ρ / 2 / Real.sqrt h ≤ ‖b 1‖} ≤ 2⁻¹) :
    planarBrownianMotion y
        {b | ContinuousPath.exitTime (Metric.ball y ρ) b ≤ ENNReal.ofReal h} ≤
      4 * planarBrownianMotion 0 {b | ρ / 2 / Real.sqrt (2 * h) ≤ ‖b 1‖} := by
  set τ := ContinuousPath.exitTime (Metric.ball y ρ) with hτdef
  have hτ : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := ℂ)) τ :=
    ContinuousPath.isStoppingTime_exitTime _ Metric.isOpen_ball
  set A : Set (ContinuousPath ℂ) := {b | τ b ≤ ENNReal.ofReal h} with hAdef
  have hA : MeasurableSet[hτ.measurableSpace] A := hτ.measurableSet_le' h.toNNReal
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  set G' := planarBrownianMotion 0 {b | ρ / 2 / Real.sqrt (2 * h) ≤ ‖b 1‖} with hG'
  have hev : Measurable (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hev0 : Measurable (fun p : ContinuousPath ℂ × ℝ => p.1 0) :=
    (continuous_eval_const (0 : ℝ≥0)).measurable.comp measurable_fst
  set S : Set (ContinuousPath ℂ × ℝ) := {p | ‖p.1 p.2.toNNReal - p.1 0‖ < ρ / 2} with hSdef
  have hS : MeasurableSet S := measurableSet_lt (hev.sub hev0).norm measurable_const
  set Su : Set (ContinuousPath ℂ × ℝ) := {p | ρ / 2 ≤ ‖p.1 p.2.toNNReal - y‖} with hSudef
  have hSu : MeasurableSet Su := measurableSet_le measurable_const (hev.sub measurable_const).norm
  let F : ContinuousPath ℂ → ℝ≥0∞ := fun b' =>
    ∫⁻ s, S.indicator 1 (b', s) ∂(volume.restrict (Ioc 0 h))
  have hFm : Measurable F := (measurable_one.indicator hS).lintegral_prod_right'
  -- the probability of a displacement at a positive time
  have hdisp (w : ℂ) {s : ℝ} (hs : 0 < s) : planarBrownianMotion w {b | ρ / 2 ≤ ‖b s.toNNReal - w‖} =
      planarBrownianMotion 0 {b | ρ / 2 / Real.sqrt s ≤ ‖b 1‖} := by
    rw [planarBrownianMotion_le_norm_sub_eq w (Real.toNNReal_pos.mpr hs).ne',
      Real.coe_toNNReal _ hs.le]
  have hanti {u v : ℝ} (huv : u ≤ v) : planarBrownianMotion 0 {b | v ≤ ‖b 1‖} ≤
      planarBrownianMotion 0 {b | u ≤ ‖b 1‖} :=
    measure_mono (fun b hb => le_trans huv hb)
  -- lower bound for the restarted functional
  have hlow (w : ℂ) : 2⁻¹ * ENNReal.ofReal h ≤ ∫⁻ b', F b' ∂planarBrownianMotion w := by
    have hswap : (∫⁻ b', F b' ∂planarBrownianMotion w) =
        ∫⁻ s, planarBrownianMotion w {b' | (b', s) ∈ S} ∂(volume.restrict (Ioc 0 h)) := by
      rw [lintegral_lintegral_swap (f := fun b' s => S.indicator (1 : ContinuousPath ℂ × ℝ → ℝ≥0∞)
        (b', s)) (measurable_one.indicator hS).aemeasurable]
      apply lintegral_congr
      intro s
      exact lintegral_indicator_one (measurable_prodMk_right hS)
    rw [hswap]
    calc
      2⁻¹ * ENNReal.ofReal h = ∫⁻ _s, (2⁻¹ : ℝ≥0∞) ∂(volume.restrict (Ioc 0 h)) := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hset : {b' : ContinuousPath ℂ | (b', s) ∈ S} =ᵐ[planarBrownianMotion w]
            {b | ρ / 2 ≤ ‖b s.toNNReal - w‖}ᶜ := by
          filter_upwards [ae_planarBrownianMotion_eval_zero w] with b hb
          apply propext
          simp only [hSdef, mem_ofPred_eq, mem_compl_iff, not_le, hb]
        have hmeas : MeasurableSet {b : ContinuousPath ℂ | ρ / 2 ≤ ‖b s.toNNReal - w‖} :=
          measurableSet_le measurable_const
            (((continuous_eval_const s.toNNReal).sub continuous_const).norm.measurable)
        rw [measure_congr hset, prob_compl_eq_one_sub hmeas, hdisp w hs.1]
        have hle : planarBrownianMotion 0 {b | ρ / 2 / Real.sqrt s ≤ ‖b 1‖} ≤ 2⁻¹ := by
          refine (hanti ?_).trans hG
          apply div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hs.1)
          exact Real.sqrt_le_sqrt hs.2
        calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := by rw [ENNReal.one_sub_inv_two]
          _ ≤ _ := tsub_le_tsub_left hle 1
  -- pathwise upper bound after the exit
  let Gup : ContinuousPath ℂ → ℝ≥0∞ := fun b =>
    ∫⁻ u, Su.indicator 1 (b, u) ∂(volume.restrict (Ioc 0 (2 * h)))
  have hGupm : Measurable Gup := (measurable_one.indicator hSu).lintegral_prod_right'
  have hpath (b : ContinuousPath ℂ) (hb : b ∈ A) :
      F (ContinuousPath.shift (τ b).toNNReal b) ≤ Gup b := by
    have hfin : τ b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
    set T := (τ b).toNNReal with hT
    have hTh : (T : ℝ) ≤ h := ENNReal.toReal_le_of_le_ofReal hh.le hb
    have hnot : b T ∉ Metric.ball y ρ := coordinate_exitTime_notMem Metric.isOpen_ball b hfin
    have hρT : ρ ≤ ‖b T - y‖ := by
      rw [Metric.mem_ball, dist_eq_norm, not_lt] at hnot
      exact hnot
    let φ : ℝ → ℝ≥0∞ := fun u => (Ioc 0 (2 * h)).indicator (fun u => Su.indicator 1 (b, u)) u
    have hpt (s : ℝ) : (Ioc 0 h).indicator (fun s => S.indicator 1
        (ContinuousPath.shift T b, s)) s ≤ φ ((T : ℝ) + s) := by
      by_cases hs : s ∈ Ioc 0 h
      · rw [Set.indicator_of_mem hs]
        by_cases hS' : (ContinuousPath.shift T b, s) ∈ S
        · have hu : (T : ℝ) + s ∈ Ioc 0 (2 * h) :=
            ⟨by linarith [hs.1, T.coe_nonneg], by linarith [hs.2]⟩
          have htn : ((T : ℝ) + s).toNNReal = T + s.toNNReal := by
            rw [Real.toNNReal_add T.coe_nonneg hs.1.le, Real.toNNReal_coe]
          have hmem : (b, (T : ℝ) + s) ∈ Su := by
            change ρ / 2 ≤ ‖b ((T : ℝ) + s).toNNReal - y‖
            have h1 : ‖b (T + s.toNNReal) - b (T + 0)‖ < ρ / 2 := hS'
            rw [add_zero] at h1
            rw [htn]
            have h2 := norm_sub_le_norm_sub_add_norm_sub (b T) (b (T + s.toNNReal)) y
            have h3 : ‖b T - b (T + s.toNNReal)‖ < ρ / 2 := by rwa [norm_sub_rev]
            linarith
          rw [Set.indicator_of_mem hS', show φ ((T : ℝ) + s) = Su.indicator 1 (b, (T : ℝ) + s)
            from Set.indicator_of_mem hu _, Set.indicator_of_mem hmem]
          exact le_rfl
        · rw [Set.indicator_of_notMem hS']
          exact zero_le
      · rw [Set.indicator_of_notMem hs]
        exact zero_le
    calc
      F (ContinuousPath.shift T b) = ∫⁻ s, (Ioc 0 h).indicator (fun s => S.indicator 1
          (ContinuousPath.shift T b, s)) s := by
        rw [lintegral_indicator measurableSet_Ioc]
      _ ≤ ∫⁻ s, φ ((T : ℝ) + s) := lintegral_mono hpt
      _ = ∫⁻ u, φ u := lintegral_add_left_eq_self φ (T : ℝ)
      _ = Gup b := by rw [lintegral_indicator measurableSet_Ioc]
  -- the strong Markov property at the exit time
  have hmarkov := lintegral_lintegral_indicator_shift_stoppingTime (P := Measure.dirac ())
    (fun (_ : Unit) b => F b) (hFm.comp measurable_snd) y τ hτ A hA
  simp only [lintegral_dirac] at hmarkov
  have hAtop : A ∩ {b | τ b < ⊤} = A := by
    ext b
    simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
    intro hb
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  rw [hAtop] at hmarkov
  have hkey : 2⁻¹ * ENNReal.ofReal h * planarBrownianMotion y A ≤
      ENNReal.ofReal (2 * h) * G' := by
    calc
      2⁻¹ * ENNReal.ofReal h * planarBrownianMotion y A =
          ∫⁻ b, A.indicator (fun _ => 2⁻¹ * ENNReal.ofReal h) b ∂planarBrownianMotion y := by
        rw [lintegral_indicator_const hAm]
      _ ≤ ∫⁻ b, A.indicator (fun b => ∫⁻ b', F b'
          ∂planarBrownianMotion (b (τ b).toNNReal)) b ∂planarBrownianMotion y := by
        apply lintegral_mono
        intro b
        apply Set.indicator_le_indicator
        exact hlow _
      _ = ∫⁻ b, A.indicator (fun b => F (ContinuousPath.shift (τ b).toNNReal b)) b
          ∂planarBrownianMotion y := hmarkov.symm
      _ ≤ ∫⁻ b, Gup b ∂planarBrownianMotion y := by
        apply lintegral_mono
        intro b
        by_cases hb : b ∈ A
        · rw [Set.indicator_of_mem hb]
          exact hpath b hb
        · rw [Set.indicator_of_notMem hb]
          exact zero_le
      _ = ∫⁻ u, planarBrownianMotion y {b | (b, u) ∈ Su} ∂(volume.restrict (Ioc 0 (2 * h))) := by
        rw [lintegral_lintegral_swap (f := fun b u => Su.indicator (1 : ContinuousPath ℂ × ℝ → ℝ≥0∞)
          (b, u)) (measurable_one.indicator hSu).aemeasurable]
        apply lintegral_congr
        intro u
        exact lintegral_indicator_one (measurable_prodMk_right hSu)
      _ ≤ ∫⁻ _u, G' ∂(volume.restrict (Ioc 0 (2 * h))) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        change planarBrownianMotion y {b | ρ / 2 ≤ ‖b u.toNNReal - y‖} ≤ G'
        rw [hdisp y hu.1]
        apply hanti
        apply div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hu.1)
        exact Real.sqrt_le_sqrt hu.2
      _ = ENNReal.ofReal (2 * h) * G' := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, mul_comm]
  have ha0 : ENNReal.ofReal h ≠ 0 := (ENNReal.ofReal_pos.mpr hh).ne'
  have hatop : ENNReal.ofReal h ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2h : ENNReal.ofReal (2 * h) = 2 * ENNReal.ofReal h := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [h2h] at hkey
  have hkey' : ENNReal.ofReal h * (2⁻¹ * planarBrownianMotion y A) ≤
      ENNReal.ofReal h * (2 * G') := by
    calc ENNReal.ofReal h * (2⁻¹ * planarBrownianMotion y A) =
        2⁻¹ * ENNReal.ofReal h * planarBrownianMotion y A := by ring
      _ ≤ 2 * ENNReal.ofReal h * G' := hkey
      _ = ENNReal.ofReal h * (2 * G') := by ring
  have h3 := (ENNReal.mul_le_mul_iff_right ha0 hatop).mp hkey'
  calc planarBrownianMotion y A = 2 * (2⁻¹ * planarBrownianMotion y A) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * (2 * G') := by gcongr
    _ = 4 * G' := by ring

/-- Above a positive smoothing cutoff, the half-disc occupation moment over a
deterministic time interval of length `h` is bounded by the cutoff factor times
`h ^ q`. -/
theorem lintegral_halfDisc_occupation_rpow_le_of_scale_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε) (hε2 : ε ≤ 1 / 2) (γ : ℝ) {q : ℝ} (hq : 1 ≤ q)
    {h : ℝ} (hh0 : 0 ≤ h) (x : ℂ) :
    (∫⁻ ω, ∫⁻ b, pathOccupationBefore ({z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator
      (normalizedCircleDensity hcirc γ ε ω)) (ENNReal.ofReal h) b ^ q
        ∂planarBrownianMotion x ∂P) ≤
      ENNReal.ofReal (η ^ (-(γ ^ 2 * q * (q - 1) / 2))) * (ENNReal.ofReal h) ^ q := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hε : 0 < ε := hη.trans_le hηε
  have hq0 : 0 < q := by linarith
  set Td : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} with hTd
  have hTdm : MeasurableSet Td := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  set K := ENNReal.ofReal (η ^ (-(γ ^ 2 * q * (q - 1) / 2))) with hK
  let f : Ω → ℂ → ℝ≥0∞ := fun ω => Td.indicator (normalizedCircleDensity H γ ε ω)
  have hf : Measurable (Function.uncurry f) :=
    measurable_uncurry_indicator (measurable_normalizedCircleDensity (hHm ε hε) γ) hTdm
  have hpt (w : ℂ) : (∫⁻ ω, f ω w ^ q ∂P) ≤ K := by
    by_cases hw : w ∈ Td
    · have hw1 : ‖w‖ + ε ≤ 1 := by have := hw.2; linarith
      have heq : (∫⁻ ω, f ω w ^ q ∂P) = ∫⁻ ω,
          (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε w))) ^ q ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hHae] with ω hω
        simp only [f, Set.indicator_of_mem hw, normalizedCircleDensity, hω]
        rw [← gmcDensity_eq_exp_normalized hcirc hε]
        rfl
      rw [heq, hh.lintegral_rpow_mul_exp_circle hε hw1 (γ ^ 2 / 2) γ hq0.le, hK]
      apply ENNReal.ofReal_le_ofReal
      have he : q * (γ ^ 2 / 2) - q ^ 2 * γ ^ 2 / 2 = -(γ ^ 2 * q * (q - 1) / 2) := by ring
      rw [he]
      apply Real.rpow_le_rpow_of_nonpos hη hηε
      have : 0 ≤ γ ^ 2 * q * (q - 1) := by
        have := sq_nonneg γ
        have : 0 ≤ q - 1 := by linarith
        positivity
      linarith
    · simp only [f, Set.indicator_of_notMem hw, ENNReal.zero_rpow_of_pos hq0, lintegral_zero]
      exact zero_le
  have hocc : Measurable (fun p : Ω × ContinuousPath ℂ =>
      pathOccupationBefore (f p.1) (ENNReal.ofReal h) p.2 ^ q) :=
    (measurable_pathOccupationBefore (fun p : Ω × ContinuousPath ℂ => f p.1)
      (hf.comp (measurable_fst.fst.prodMk measurable_snd))
      (fun _ => ENNReal.ofReal h) measurable_const (fun p => p.2) measurable_snd).pow_const q
  calc
    _ = ∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω) (ENNReal.ofReal h) b ^ q
        ∂planarBrownianMotion x ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hHae] with ω hω
      have h' : normalizedCircleDensity hcirc γ ε ω = normalizedCircleDensity H γ ε ω := by
        funext w
        simp only [normalizedCircleDensity, hω]
      simp only [f, h']
    _ = ∫⁻ b, ∫⁻ ω, pathOccupationBefore (f ω) (ENNReal.ofReal h) b ^ q
        ∂P ∂planarBrownianMotion x := lintegral_lintegral_swap hocc.aemeasurable
    _ ≤ ∫⁻ _b, K * (ENNReal.ofReal h) ^ q ∂planarBrownianMotion x := by
      apply lintegral_mono
      intro b
      set I := Ioc (0 : ℝ) h with hI
      have hbm : Measurable (fun t : ℝ => b t.toNNReal) := by fun_prop
      have hvol : (volume.restrict I) univ = ENNReal.ofReal h := by
        rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
      have hjoint : Measurable (fun p : Ω × ℝ => f p.1 (b p.2.toNNReal) ^ q) :=
        (hf.comp (measurable_fst.prodMk (hbm.comp measurable_snd))).pow_const q
      calc
        (∫⁻ ω, pathOccupationBefore (f ω) (ENNReal.ofReal h) b ^ q ∂P) =
            ∫⁻ ω, (∫⁻ t in I, f ω (b t.toNNReal)) ^ q ∂P := by
          apply lintegral_congr
          intro ω
          unfold pathOccupationBefore
          rw [lintegral_stopped_indicator_eq b _ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hh0]
        _ ≤ ∫⁻ ω, (volume.restrict I) univ ^ (q - 1) *
            (∫⁻ t in I, f ω (b t.toNNReal) ^ q) ∂P := by
          apply lintegral_mono
          intro ω
          exact LatticeProb.lintegral_rpow_le_measure_univ_mul _ hq
            ((hf.comp (measurable_const.prodMk hbm)).aemeasurable)
        _ = (volume.restrict I) univ ^ (q - 1) *
            ∫⁻ t in I, (∫⁻ ω, f ω (b t.toNNReal) ^ q ∂P) := by
          rw [lintegral_const_mul _ (hjoint.lintegral_prod_right'), lintegral_lintegral_swap
            hjoint.aemeasurable]
        _ ≤ (volume.restrict I) univ ^ (q - 1) * ∫⁻ _ in I, K := by
          gcongr with t
          exact hpt _
        _ = K * (ENNReal.ofReal h) ^ q := by
          rw [lintegral_const, hvol]
          set u := ENNReal.ofReal h
          calc
            _ = K * (u ^ (q - 1) * u) := by ring
            _ = K * u ^ ((q - 1) + 1) := by
              rw [ENNReal.rpow_add_of_nonneg (q - 1) 1 (by linarith) (by norm_num),
                ENNReal.rpow_one]
            _ = K * u ^ q := by congr 2; ring
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- The occupation before a deterministic time splits at a random time into the
part before it and the occupation of the path restarted at that time. -/
theorem pathOccupationBefore_le_add_shift_of_le (g : ℂ → ℝ≥0∞) (hg : Measurable g)
    (T σ : ℝ≥0∞) (b : ContinuousPath ℂ) :
    pathOccupationBefore g T b ≤ pathOccupationBefore g (min σ T) b +
      (if σ ≤ T then pathOccupationBefore g T (ContinuousPath.shift σ.toNNReal b) else 0) := by
  have huniv (b' : ContinuousPath ℂ) : ContinuousPath.exitTime (univ : Set ℂ) b' = ⊤ := by
    rw [exitTime_eq_iInf]
    simp
  by_cases hσT : σ ≤ T
  · simp only [hσT, ↓reduceIte]
    by_cases hσ : σ = ⊤
    · rw [min_eq_right (hσ ▸ le_top : T ≤ σ)]
      exact le_self_add
    · have h := pathOccupationBefore_le_add_shift hg univ T σ.toNNReal b
      rw [huniv, huniv, min_eq_right le_top, ENNReal.coe_toNNReal hσ] at h
      exact h
  · simp only [hσT, ↓reduceIte]
    rw [add_zero,
      min_eq_right (le_of_lt (not_le.mp hσT))]

/-- A ball of radius `r / 2` meets the half disc inside at most `36` grid squares of
side `r`, each of whose centres is within `2 r` of the centre of the ball. -/
theorem exists_square_cover_halfDisc_ball (y : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ J : Finset (ℤ × ℤ), J.card ≤ 36 ∧ J ⊆ LatticeProb.squareIndex r ∧
      (∀ i ∈ J, ‖y - LatticeProb.dyadicSquareCentre r i‖ < 2 * r) ∧
      ∀ z : ℂ, ‖z - y‖ < r / 2 → ‖z‖ ≤ 1 / 2 → ∃ i ∈ J, z ∈ LatticeProb.dyadicSquare r i := by
  classical
  set k : ℤ := ⌊y.re / r⌋ with hk
  set l : ℤ := ⌊y.im / r⌋ with hl
  let J : Finset (ℤ × ℤ) := ((Finset.Icc (k - 3) (k + 2)) ×ˢ (Finset.Icc (l - 3) (l + 2))).filter
    (fun i => i ∈ LatticeProb.squareIndex r ∧ ‖y - LatticeProb.dyadicSquareCentre r i‖ < 2 * r)
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
    have h1 : (k + 2 + 1 - (k - 3)).toNat = 6 := by omega
    have h2 : (l + 2 + 1 - (l - 3)).toNat = 6 := by omega
    rw [h1, h2]
  · intro i hi
    exact (Finset.mem_filter.mp hi).2.1
  · intro i hi
    exact (Finset.mem_filter.mp hi).2.2
  · intro z hz hz2
    have hball : z ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
      rwa [Metric.mem_closedBall, dist_zero_right]
    have hcover := LatticeProb.closedBall_subset_iUnion_dyadicSquare hr hball
    simp only [Set.mem_iUnion] at hcover
    obtain ⟨i, hi, hzi⟩ := hcover
    have hzc := LatticeProb.norm_sub_centre_lt hr hzi
    have hyc : ‖y - LatticeProb.dyadicSquareCentre r i‖ < 2 * r := by
      calc ‖y - LatticeProb.dyadicSquareCentre r i‖ ≤
          ‖y - z‖ + ‖z - LatticeProb.dyadicSquareCentre r i‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < r / 2 + r := by rw [norm_sub_rev]; exact add_lt_add hz hzc
        _ ≤ 2 * r := by linarith
    refine ⟨i, ?_, hzi⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hi, hyc⟩
    · have hre : |(y - LatticeProb.dyadicSquareCentre r i).re| < 2 * r :=
        (Complex.abs_re_le_norm _).trans_lt hyc
      have hre' : |y.re - ((i.1 : ℝ) + 1 / 2) * r| < 2 * r := by
        simpa [LatticeProb.dyadicSquareCentre] using hre
      rw [abs_lt] at hre'
      have hk1 : (k : ℝ) ≤ y.re / r := Int.floor_le _
      have hk2 : y.re / r < (k : ℝ) + 1 := Int.lt_floor_add_one _
      rw [le_div_iff₀ hr] at hk1
      rw [div_lt_iff₀ hr] at hk2
      have hlo : ((k - 3 : ℤ) : ℝ) < (i.1 : ℝ) := by
        push_cast
        nlinarith
      have hhi : (i.1 : ℝ) < ((k + 3 : ℤ) : ℝ) := by
        push_cast
        nlinarith
      have := Int.cast_lt.mp hlo
      have := Int.cast_lt.mp hhi
      constructor <;> omega
    · have him : |(y - LatticeProb.dyadicSquareCentre r i).im| < 2 * r :=
        (Complex.abs_im_le_norm _).trans_lt hyc
      have him' : |y.im - ((i.2 : ℝ) + 1 / 2) * r| < 2 * r := by
        simpa [LatticeProb.dyadicSquareCentre] using him
      rw [abs_lt] at him'
      have hl1 : (l : ℝ) ≤ y.im / r := Int.floor_le _
      have hl2 : y.im / r < (l : ℝ) + 1 := Int.lt_floor_add_one _
      rw [le_div_iff₀ hr] at hl1
      rw [div_lt_iff₀ hr] at hl2
      have hlo : ((l - 3 : ℤ) : ℝ) < (i.2 : ℝ) := by
        push_cast
        nlinarith
      have hhi : (i.2 : ℝ) < ((l + 3 : ℤ) : ℝ) := by
        push_cast
        nlinarith
      have := Int.cast_lt.mp hlo
      have := Int.cast_lt.mp hhi
      constructor <;> omega

/-- **Occupation of a small ball.** For a smoothing radius `4 r δ` with `δ ≤ 1/2`, the
field-Brownian moment of the half-disc occupation before the exit from a ball of radius
`r / 2` is at most `2592` times the stopped grid-square bound. -/
theorem lintegral_halfDisc_occupation_ball_exit_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (γ : ℝ) {q : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2) (y x : ℂ) :
    (∫⁻ ω, ∫⁻ b, pathOccupationBefore ({z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator
      (normalizedCircleDensity hcirc γ (4 * r * δ) ω))
        (ContinuousPath.exitTime (Metric.ball y (r / 2)) b) b ^ q ∂planarBrownianMotion x ∂P) ≤
      2592 * (ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
        ENNReal.ofReal ((4 * r) ^ 2) ^ q * (⨆ w, stoppedHalfDiscMoment P hcirc γ δ q w) *
        ENNReal.ofReal ((q * (Real.log (5 * r / 2) - Real.log r) /
          (Real.log (3 * r / 2) - Real.log r)) ^ q)) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hq0 : 0 < q := by linarith
  have hε : 0 < 4 * r * δ := by positivity
  obtain ⟨J, hJcard, hJsub, hJnear, hJcover⟩ := exists_square_cover_halfDisc_ball y hr
  set U : Set ℂ := Metric.ball y (r / 2) with hU
  set Td : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} with hTd
  set B := ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
    ENNReal.ofReal ((4 * r) ^ 2) ^ q * (⨆ w, stoppedHalfDiscMoment P hcirc γ δ q w) *
    ENNReal.ofReal ((q * (Real.log (5 * r / 2) - Real.log r) /
      (Real.log (3 * r / 2) - Real.log r)) ^ q) with hB
  have hnd : Measurable (Function.uncurry fun ω w => normalizedCircleDensity H γ (4 * r * δ) ω w) :=
    measurable_normalizedCircleDensity (hHm _ hε) γ
  let fi : ℤ × ℤ → Ω → ℂ → ℝ≥0∞ := fun i ω =>
    (LatticeProb.dyadicSquare r i).indicator (normalizedCircleDensity H γ (4 * r * δ) ω)
  have hfi (i : ℤ × ℤ) : Measurable (Function.uncurry (fi i)) :=
    measurable_uncurry_indicator hnd (LatticeProb.measurableSet_dyadicSquare r i)
  -- pathwise cover of the density inside the ball
  have hcov (ω : Ω) (b : ContinuousPath ℂ) :
      pathOccupationBefore (Td.indicator (normalizedCircleDensity H γ (4 * r * δ) ω))
        (ContinuousPath.exitTime U b) b ≤
      ∑ i ∈ J, pathOccupationBefore (fi i ω) (ContinuousPath.exitTime U b) b := by
    unfold pathOccupationBefore
    rw [← lintegral_finsetSum' J (fun i _ => ?_)]
    · apply lintegral_mono
      intro s
      by_cases hs : s ∈ {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < ContinuousPath.exitTime U b}
      · rw [Set.indicator_of_mem hs]
        simp only [Set.indicator_of_mem hs]
        by_cases hz : b s.toNNReal ∈ Td
        · rw [Set.indicator_of_mem hz]
          have hin : b s.toNNReal ∈ U :=
            ContinuousPath.mem_of_lt_exitTime U b s.toNNReal hs.2
          have hin' : ‖b s.toNNReal - y‖ < r / 2 := by
            rwa [hU, Metric.mem_ball, dist_eq_norm] at hin
          obtain ⟨i, hiJ, hzi⟩ := hJcover _ hin' hz.2
          calc normalizedCircleDensity H γ (4 * r * δ) ω (b s.toNNReal) =
              fi i ω (b s.toNNReal) := by simp only [fi, Set.indicator_of_mem hzi]
            _ ≤ _ := Finset.single_le_sum (f := fun i => fi i ω (b s.toNNReal))
              (fun _ _ => zero_le) hiJ
        · rw [Set.indicator_of_notMem hz]
          exact zero_le
      · rw [Set.indicator_of_notMem hs]
        exact zero_le
    · exact ((((hfi i).comp (measurable_const.prodMk
        (b.continuous.measurable.comp measurable_real_toNNReal))).indicator
        ((measurableSet_le measurable_const measurable_id).inter
          (measurableSet_lt ENNReal.measurable_ofReal measurable_const)))).aemeasurable
  -- each square
  have hsq (i : ℤ × ℤ) (hi : i ∈ J) : (∫⁻ ω, ∫⁻ b, pathOccupationBefore (fi i ω)
      (ContinuousPath.exitTime U b) b ^ q ∂planarBrownianMotion x ∂P) ≤ B := by
    have hDR : U ⊆ Metric.ball (LatticeProb.dyadicSquareCentre r i) (5 * r / 2) := by
      intro w hw
      rw [hU, Metric.mem_ball, dist_eq_norm] at hw
      rw [Metric.mem_ball, dist_eq_norm]
      have := hJnear i hi
      calc ‖w - LatticeProb.dyadicSquareCentre r i‖ ≤
          ‖w - y‖ + ‖y - LatticeProb.dyadicSquareCentre r i‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < r / 2 + 2 * r := add_lt_add hw this
        _ = 5 * r / 2 := by ring
    have h := lintegral_square_occupation_rpow_le_stoppedHalfDiscMoment hh hr hr10 hδ hδ2
      (hJsub hi) γ hq Metric.isOpen_ball (by linarith : 3 * r / 2 < 5 * r / 2) hDR x
    refine le_trans (le_of_eq ?_) h
    apply lintegral_congr_ae
    filter_upwards [hHae] with ω hω
    have h' : normalizedCircleDensity hcirc γ (4 * r * δ) ω =
        normalizedCircleDensity H γ (4 * r * δ) ω := by
      funext w
      simp only [normalizedCircleDensity, hω]
    simp only [fi, h']
    rfl
  have hoccm (i : ℤ × ℤ) : Measurable (fun p : Ω × ContinuousPath ℂ =>
      pathOccupationBefore (fi i p.1) (ContinuousPath.exitTime U p.2) p.2 ^ q) :=
    (measurable_pathOccupationBefore (fun p : Ω × ContinuousPath ℂ => fi i p.1)
      ((hfi i).comp (measurable_fst.fst.prodMk measurable_snd))
      (fun p => ContinuousPath.exitTime U p.2)
      ((ContinuousPath.measurable_exitTime U Metric.isOpen_ball).comp measurable_snd)
      (fun p => p.2) measurable_snd).pow_const q
  calc
    _ = ∫⁻ ω, ∫⁻ b, pathOccupationBefore (Td.indicator (normalizedCircleDensity H γ (4 * r * δ) ω))
        (ContinuousPath.exitTime U b) b ^ q ∂planarBrownianMotion x ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hHae] with ω hω
      have h' : normalizedCircleDensity hcirc γ (4 * r * δ) ω =
          normalizedCircleDensity H γ (4 * r * δ) ω := by
        funext w
        simp only [normalizedCircleDensity, hω]
      rw [h']
    _ ≤ ∫⁻ ω, ∫⁻ b, 2 * (36 : ℝ≥0∞) * ∑ i ∈ J, pathOccupationBefore (fi i ω)
        (ContinuousPath.exitTime U b) b ^ q ∂planarBrownianMotion x ∂P := by
      refine lintegral_mono fun ω => lintegral_mono fun b => ?_
      calc _ ≤ (∑ i ∈ J, pathOccupationBefore (fi i ω) (ContinuousPath.exitTime U b) b) ^ q :=
            ENNReal.rpow_le_rpow (hcov ω b) hq0.le
        _ ≤ ∑ i ∈ J, ∑ j ∈ J, (pathOccupationBefore (fi i ω) (ContinuousPath.exitTime U b) b *
            pathOccupationBefore (fi j ω) (ContinuousPath.exitTime U b) b) ^ (q / 2) :=
          rpow_sum_le_sum_cross J _ hq0 hq2
        _ = ∑ i ∈ J, ∑ j ∈ J.filter (fun _ => True),
            (pathOccupationBefore (fi i ω) (ContinuousPath.exitTime U b) b *
            pathOccupationBefore (fi j ω) (ContinuousPath.exitTime U b) b) ^ (q / 2) := by
          rw [Finset.filter_true_of_mem (fun _ _ => trivial)]
        _ ≤ _ := sum_rpow_mul_le_degree_mul_sum_rpow J _ (fun _ _ => True)
            (fun _ _ _ => trivial) 36 (fun i _ => by simpa using hJcard) hq0.le
    _ = 2 * 36 * ∑ i ∈ J, ∫⁻ ω, ∫⁻ b, pathOccupationBefore (fi i ω)
        (ContinuousPath.exitTime U b) b ^ q ∂planarBrownianMotion x ∂P := by
      have hinner (ω : Ω) : (∫⁻ b, 2 * (36 : ℝ≥0∞) * ∑ i ∈ J, pathOccupationBefore (fi i ω)
          (ContinuousPath.exitTime U b) b ^ q ∂planarBrownianMotion x) =
          2 * 36 * ∑ i ∈ J, ∫⁻ b, pathOccupationBefore (fi i ω)
          (ContinuousPath.exitTime U b) b ^ q ∂planarBrownianMotion x := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_finsetSum' J
          (f := fun i b => pathOccupationBefore (fi i ω) (ContinuousPath.exitTime U b) b ^ q)
          (fun i _ => ((hoccm i).comp (measurable_const.prodMk measurable_id)).aemeasurable)]
      simp only [hinner]
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_finsetSum' J
        (f := fun i ω => ∫⁻ b, pathOccupationBefore (fi i ω) (ContinuousPath.exitTime U b) b ^ q
          ∂planarBrownianMotion x)
        (fun i _ => ((hoccm i).lintegral_prod_right').aemeasurable)]
    _ ≤ 2 * 36 * ∑ _i ∈ J, B := by
      gcongr with i hi
      exact hsq i hi
    _ ≤ 2592 * B := by
      rw [Finset.sum_const, nsmul_eq_mul]
      calc 2 * 36 * ((J.card : ℝ≥0∞) * B) ≤ 2 * 36 * (36 * B) := by
            gcongr
            exact_mod_cast hJcard
        _ = 2592 * B := by ring

/-- **Restart at a ball exit.** The half-disc occupation moment over a time
interval of length `h` is at most `2 ^ (q - 1)` times the moment before the exit from
a ball about the start plus the exit probability by time `h` times the largest moment
over all starts. -/
theorem lintegral_halfDisc_occupation_rpow_le_ball_exit_add
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {ε : ℝ} (hε : 0 < ε) (γ : ℝ) {q : ℝ} (hq : 1 ≤ q) (h ρ : ℝ) (y : ℂ) :
    (∫⁻ ω, ∫⁻ b, pathOccupationBefore ({z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator
      (normalizedCircleDensity hcirc γ ε ω)) (ENNReal.ofReal h) b ^ q
        ∂planarBrownianMotion y ∂P) ≤
      2 ^ (q - 1) * ((∫⁻ ω, ∫⁻ b, pathOccupationBefore
        ({z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (normalizedCircleDensity hcirc γ ε ω))
          (ContinuousPath.exitTime (Metric.ball y ρ) b) b ^ q ∂planarBrownianMotion y ∂P) +
        planarBrownianMotion y
          {b | ContinuousPath.exitTime (Metric.ball y ρ) b ≤ ENNReal.ofReal h} *
        ⨆ w, ∫⁻ ω, ∫⁻ b, pathOccupationBefore
          ({z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (normalizedCircleDensity hcirc γ ε ω))
            (ENNReal.ofReal h) b ^ q ∂planarBrownianMotion w ∂P) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hq0 : 0 < q := by linarith
  set Td : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} with hTd
  have hTdm : MeasurableSet Td := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  set U : Set ℂ := Metric.ball y ρ with hU
  set τ := ContinuousPath.exitTime U with hτdef
  have hτ : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := ℂ)) τ :=
    ContinuousPath.isStoppingTime_exitTime _ Metric.isOpen_ball
  set A : Set (ContinuousPath ℂ) := {b | τ b ≤ ENNReal.ofReal h} with hAdef
  have hA : MeasurableSet[hτ.measurableSpace] A := hτ.measurableSet_le' h.toNNReal
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  let f : Ω → ℂ → ℝ≥0∞ := fun ω => Td.indicator (normalizedCircleDensity H γ ε ω)
  have hf : Measurable (Function.uncurry f) :=
    measurable_uncurry_indicator (measurable_normalizedCircleDensity (hHm ε hε) γ) hTdm
  have hfω (ω : Ω) : Measurable (f ω) := hf.comp (measurable_const.prodMk measurable_id)
  have hconv (ω : Ω) (hω : ∀ r z, H ω r z = hcirc ω r z) :
      Td.indicator (normalizedCircleDensity hcirc γ ε ω) = f ω := by
    have h' : normalizedCircleDensity hcirc γ ε ω = normalizedCircleDensity H γ ε ω := by
      funext w
      simp only [normalizedCircleDensity, hω]
    simp only [f, h']
  let F : Ω → ContinuousPath ℂ → ℝ≥0∞ := fun ω b =>
    pathOccupationBefore (f ω) (ENNReal.ofReal h) b ^ q
  have hF : Measurable (Function.uncurry F) :=
    (measurable_pathOccupationBefore (fun p : Ω × ContinuousPath ℂ => f p.1)
      (hf.comp (measurable_fst.fst.prodMk measurable_snd))
      (fun _ => ENNReal.ofReal h) measurable_const (fun p => p.2) measurable_snd).pow_const q
  have hN : Measurable (fun p : Ω × ContinuousPath ℂ =>
      pathOccupationBefore (f p.1) (τ p.2) p.2 ^ q) :=
    (measurable_pathOccupationBefore (fun p : Ω × ContinuousPath ℂ => f p.1)
      (hf.comp (measurable_fst.fst.prodMk measurable_snd))
      (fun p => τ p.2) ((ContinuousPath.measurable_exitTime U Metric.isOpen_ball).comp
        measurable_snd) (fun p => p.2) measurable_snd).pow_const q
  set W := ⨆ w, ∫⁻ ω, ∫⁻ b, pathOccupationBefore (Td.indicator (normalizedCircleDensity hcirc γ ε ω))
    (ENNReal.ofReal h) b ^ q ∂planarBrownianMotion w ∂P with hW
  have hWF (w : ℂ) : (∫⁻ ω, ∫⁻ b, F ω b ∂planarBrownianMotion w ∂P) ≤ W := by
    refine le_trans (le_of_eq ?_) (le_iSup (fun w => ∫⁻ ω, ∫⁻ b, pathOccupationBefore
      (Td.indicator (normalizedCircleDensity hcirc γ ε ω)) (ENNReal.ofReal h) b ^ q
        ∂planarBrownianMotion w ∂P) w)
    apply lintegral_congr_ae
    filter_upwards [hHae] with ω hω
    rw [hconv ω hω]
  -- pathwise restart
  have hpath (ω : Ω) (b : ContinuousPath ℂ) : F ω b ≤ 2 ^ (q - 1) *
      (pathOccupationBefore (f ω) (τ b) b ^ q +
        A.indicator (fun b => F ω (ContinuousPath.shift (τ b).toNNReal b)) b) := by
    have hsplit := pathOccupationBefore_le_add_shift_of_le (f ω) (hfω ω) (ENNReal.ofReal h) (τ b) b
    have hfirst : pathOccupationBefore (f ω) (min (τ b) (ENNReal.ofReal h)) b ≤
        pathOccupationBefore (f ω) (τ b) b :=
      pathOccupationBefore_mono (fun _ => le_rfl) (min_le_left _ _) b
    calc F ω b ≤ (pathOccupationBefore (f ω) (τ b) b +
          (if τ b ≤ ENNReal.ofReal h then pathOccupationBefore (f ω) (ENNReal.ofReal h)
            (ContinuousPath.shift (τ b).toNNReal b) else 0)) ^ q :=
          ENNReal.rpow_le_rpow (hsplit.trans (add_le_add hfirst le_rfl)) hq0.le
      _ ≤ 2 ^ (q - 1) * (pathOccupationBefore (f ω) (τ b) b ^ q +
          (if τ b ≤ ENNReal.ofReal h then pathOccupationBefore (f ω) (ENNReal.ofReal h)
            (ContinuousPath.shift (τ b).toNNReal b) else 0) ^ q) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hq
      _ = _ := by
        have hind : (if τ b ≤ ENNReal.ofReal h then pathOccupationBefore (f ω) (ENNReal.ofReal h)
            (ContinuousPath.shift (τ b).toNNReal b) else 0) ^ q =
            A.indicator (fun b => F ω (ContinuousPath.shift (τ b).toNNReal b)) b := by
          by_cases hb : τ b ≤ ENNReal.ofReal h
          · simp only [hb, ↓reduceIte, Set.indicator_of_mem (show b ∈ A from hb), F]
          · simp only [hb, ↓reduceIte, Set.indicator_of_notMem (show b ∉ A from hb),
              ENNReal.zero_rpow_of_pos hq0]
        rw [hind]
  -- the strong Markov property at the exit time
  have hmarkov := lintegral_lintegral_indicator_shift_stoppingTime (P := P) F hF y τ hτ A hA
  have hAtop : A ∩ {b | τ b < ⊤} = A := by
    ext b
    simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
    intro hb
    exact lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  rw [hAtop] at hmarkov
  have hsecond : (∫⁻ ω, ∫⁻ b, A.indicator (fun b => F ω (ContinuousPath.shift (τ b).toNNReal b)) b
      ∂planarBrownianMotion y ∂P) ≤ planarBrownianMotion y A * W := by
    rw [hmarkov]
    calc
      _ ≤ ∫⁻ b, A.indicator (fun _ => W) b ∂planarBrownianMotion y := by
        apply lintegral_mono
        intro b
        apply Set.indicator_le_indicator
        exact hWF _
      _ = _ := by rw [lintegral_indicator_const hAm, mul_comm]
  have hfirstm (ω : Ω) : Measurable (fun b => pathOccupationBefore (f ω) (τ b) b ^ q) :=
    (measurable_pathOccupationBefore (fun _ : ContinuousPath ℂ => f ω)
      ((hfω ω).comp measurable_snd) τ (ContinuousPath.measurable_exitTime U Metric.isOpen_ball)
      id measurable_id).pow_const q
  calc
    _ = ∫⁻ ω, ∫⁻ b, F ω b ∂planarBrownianMotion y ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hHae] with ω hω
      rw [hconv ω hω]
    _ ≤ ∫⁻ ω, ∫⁻ b, 2 ^ (q - 1) * (pathOccupationBefore (f ω) (τ b) b ^ q +
        A.indicator (fun b => F ω (ContinuousPath.shift (τ b).toNNReal b)) b)
          ∂planarBrownianMotion y ∂P :=
      lintegral_mono fun ω => lintegral_mono fun b => hpath ω b
    _ = 2 ^ (q - 1) * ((∫⁻ ω, ∫⁻ b, pathOccupationBefore (f ω) (τ b) b ^ q
          ∂planarBrownianMotion y ∂P) +
        ∫⁻ ω, ∫⁻ b, A.indicator (fun b => F ω (ContinuousPath.shift (τ b).toNNReal b)) b
          ∂planarBrownianMotion y ∂P) := by
      have hin (ω : Ω) : (∫⁻ b, 2 ^ (q - 1) * (pathOccupationBefore (f ω) (τ b) b ^ q +
          A.indicator (fun b => F ω (ContinuousPath.shift (τ b).toNNReal b)) b)
            ∂planarBrownianMotion y) = 2 ^ (q - 1) *
          ((∫⁻ b, pathOccupationBefore (f ω) (τ b) b ^ q ∂planarBrownianMotion y) +
            ∫⁻ b, A.indicator (fun b => F ω (ContinuousPath.shift (τ b).toNNReal b)) b
              ∂planarBrownianMotion y) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
          (by norm_num)), lintegral_add_left (hfirstm ω)]
      simp only [hin]
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)),
        lintegral_add_left (hN.lintegral_prod_right')]
    _ ≤ _ := by
      refine mul_le_mul_right (add_le_add (le_of_eq ?_) hsecond) _
      apply lintegral_congr_ae
      filter_upwards [hHae] with ω hω
      rw [hconv ω hω]

/-- The Gaussian and time scale factors of a grid square combine into a single power. -/
theorem exp_mul_sq_rpow_eq_rpow {γ q R : ℝ} (hR : 0 < R) :
    (R ^ 2) ^ q * Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log R) / 2) =
      R ^ (2 * q - γ ^ 2 * q * (q - 1) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
  rw [Real.rpow_def_of_pos hR, Real.rpow_def_of_pos hR, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Powers of a multiple of the square root of `h`. -/
theorem mul_sqrt_rpow_eq {s h x : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h) :
    (s * Real.sqrt h) ^ x = s ^ x * h ^ (x / 2) := by
  rw [Real.mul_rpow hs (Real.sqrt_nonneg h), Real.sqrt_eq_rpow, ← Real.rpow_mul hh]
  congr 2
  ring

/-- **Smoothing-uniform half-disc time moments.** For `γ² < 4` there are an order
`q ∈ (1, 2]` with `q γ² < 4`, a time scale `h₀ > 0` and a finite constant such that,
for all times `h ≤ h₀`, all smoothing radii in `(0, 1/2]` and all Brownian starts, the
field-Brownian `q`-th moment of the half-disc occupation up to time `h` is at most the
constant times `h ^ (q - γ² q (q - 1) / 4)`. -/
theorem exists_halfDisc_occupation_rpow_le_time
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ2 : γ ^ 2 < 4) :
    ∃ q : ℝ, 1 < q ∧ q ≤ 2 ∧ q * γ ^ 2 < 4 ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ h, 0 < h → h ≤ h₀ → ∀ ε, 0 < ε → ε ≤ 1 / 2 → ∀ y : ℂ,
        (∫⁻ ω, ∫⁻ b, pathOccupationBefore ({z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator
          (normalizedCircleDensity hcirc γ ε ω)) (ENNReal.ofReal h) b ^ q
            ∂planarBrownianMotion y ∂P) ≤
          C * ENNReal.ofReal (h ^ (q - γ ^ 2 * q * (q - 1) / 4)) := by
  obtain ⟨q, hq1, hq2, hqγ, CΦ, hCΦ, hΦ⟩ := exists_uniform_stoppedHalfDiscMoment_le hh hγ2
  have hq0 : 0 < q := by linarith
  refine ⟨q, hq1, hq2, hqγ, ?_⟩
  set e : ℝ := γ ^ 2 * q * (q - 1) / 2 with he
  set ζ : ℝ := 2 * q - γ ^ 2 * q * (q - 1) / 2 with hζ
  set a : ℝ := q - γ ^ 2 * q * (q - 1) / 4 with ha
  have hζa : ζ / 2 = a := by rw [hζ, ha]; ring
  have hea : q + -e / 2 = a := by rw [he, ha]; ring
  -- a far displacement threshold
  set ε₁ : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-q) / 4) with hε₁
  have hε₁pos : 0 < ε₁ := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp
    ((tendsto_planarBrownianMotion_le_norm_one.eventually (gt_mem_nhds hε₁pos)))
  set s₀ : ℝ := max (4 * Real.sqrt 2 * U₀) 1 with hs₀
  have hs₀pos : 0 < s₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set h₀ : ℝ := (1 / (10 * s₀)) ^ 2 with hh₀
  have hh₀pos : 0 < h₀ := by positivity
  set F : ℝ≥0∞ := ENNReal.ofReal ((q * Real.log (5 / 2) / Real.log (3 / 2)) ^ q) with hF
  set CA : ℝ≥0∞ := ENNReal.ofReal ((2 * s₀) ^ (-e)) with hCA
  set CB : ℝ≥0∞ := 2 ^ q * 2592 * (ENNReal.ofReal ((4 * s₀) ^ ζ) * CΦ * F) with hCB
  refine ⟨h₀, hh₀pos, CA + CB, ?_, ?_⟩
  · refine ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ?_⟩
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0.le
      (by norm_num)) (by norm_num)) (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        hCΦ) ENNReal.ofReal_lt_top)
  intro h hh0 hhh₀ ε hε hε2 y
  set r : ℝ := s₀ * Real.sqrt h with hrdef
  have hsq : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  have hr : 0 < r := mul_pos hs₀pos hsq
  have hr10 : r ≤ 1 / 10 := by
    have h1 : Real.sqrt h ≤ 1 / (10 * s₀) := by
      rw [show 1 / (10 * s₀) = Real.sqrt ((1 / (10 * s₀)) ^ 2) from
        (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt hhh₀
    calc r = s₀ * Real.sqrt h := rfl
      _ ≤ s₀ * (1 / (10 * s₀)) := mul_le_mul_of_nonneg_left h1 hs₀pos.le
      _ = 1 / 10 := by field_simp
  set Cell : ℂ → ℝ≥0∞ := fun w => ∫⁻ ω, ∫⁻ b, pathOccupationBefore
    ({z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (normalizedCircleDensity hcirc γ ε ω))
      (ENNReal.ofReal h) b ^ q ∂planarBrownianMotion w ∂P with hCell
  change Cell y ≤ _
  by_cases hεr : 2 * r ≤ ε
  · -- coarse smoothing
    have hJ := lintegral_halfDisc_occupation_rpow_le_of_scale_lower_bound hh (by positivity) hεr hε2
      γ hq1.le hh0.le y
    have key : (2 * r) ^ (-(γ ^ 2 * q * (q - 1) / 2)) * h ^ q = (2 * s₀) ^ (-e) * h ^ a := by
      rw [show 2 * r = (2 * s₀) * Real.sqrt h by rw [hrdef]; ring,
        mul_sqrt_rpow_eq (by positivity) hh0.le, mul_assoc, ← Real.rpow_add hh0, he, ha]
      congr 2
      ring
    refine hJ.trans (le_trans (le_of_eq ?_) (mul_le_mul' le_self_add le_rfl))
    rw [ENNReal.ofReal_rpow_of_nonneg hh0.le hq0.le, ← ENNReal.ofReal_mul (by positivity), hCA,
      ← ENNReal.ofReal_mul (by positivity), key]
  · -- fine smoothing: restart at the exit from a ball of radius r / 2
    replace hεr : ε < 2 * r := not_le.mp hεr
    set δ : ℝ := ε / (4 * r) with hδdef
    have hδ : 0 < δ := by positivity
    have hδ2 : δ ≤ 1 / 2 := by
      rw [hδdef, div_le_iff₀ (by positivity)]
      linarith
    have hεδ : 4 * r * δ = ε := by rw [hδdef]; field_simp
    set W := ⨆ w, Cell w with hW
    have hWfin : W < ⊤ := by
      refine lt_of_le_of_lt (iSup_le fun w =>
        lintegral_halfDisc_occupation_rpow_le_of_scale_lower_bound hh hε le_rfl hε2 γ hq1.le
          hh0.le w) ?_
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.rpow_lt_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)
    set Bsq := ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
      ENNReal.ofReal ((4 * r) ^ 2) ^ q * (⨆ w, stoppedHalfDiscMoment P hcirc γ δ q w) *
      ENNReal.ofReal ((q * (Real.log (5 * r / 2) - Real.log r) /
        (Real.log (3 * r / 2) - Real.log r)) ^ q) with hBsq
    -- the exit probability is small
    have hexit (w : ℂ) : planarBrownianMotion w
        {b | ContinuousPath.exitTime (Metric.ball w (r / 2)) b ≤ ENNReal.ofReal h} ≤
        (2 : ℝ≥0∞) ^ (-q) := by
      have hu : U₀ ≤ r / 2 / 2 / Real.sqrt (2 * h) := by
        have h2 : Real.sqrt (2 * h) = Real.sqrt 2 * Real.sqrt h := by
          rw [Real.sqrt_mul (by norm_num)]
        rw [h2, hrdef]
        have hs2 : 0 < Real.sqrt 2 := by positivity
        rw [show s₀ * Real.sqrt h / 2 / 2 / (Real.sqrt 2 * Real.sqrt h) = s₀ / (4 * Real.sqrt 2) by
          field_simp; ring]
        rw [le_div_iff₀ (by positivity)]
        have := le_max_left (4 * Real.sqrt 2 * U₀) 1
        linarith
      have hu' : r / 2 / 2 / Real.sqrt (2 * h) ≤ r / 2 / 2 / Real.sqrt h := by
        apply div_le_div_of_nonneg_left (by positivity) hsq
        exact Real.sqrt_le_sqrt (by linarith)
      have hG1 := (hU₀ _ hu).le
      have hG2 : planarBrownianMotion 0 {b | r / 2 / 2 / Real.sqrt h ≤ ‖b 1‖} ≤ 2⁻¹ := by
        refine (measure_mono (fun b hb => le_trans hu' hb)).trans (hG1.trans ?_)
        rw [hε₁]
        have : (2 : ℝ) ^ (-q) / 4 ≤ 1 / 2 := by
          have : (2 : ℝ) ^ (-q) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
          linarith
        calc ENNReal.ofReal ((2 : ℝ) ^ (-q) / 4) ≤ ENNReal.ofReal (1 / 2) :=
              ENNReal.ofReal_le_ofReal this
          _ = 2⁻¹ := by rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
      calc _ ≤ 4 * planarBrownianMotion 0 {b | r / 2 / 2 / Real.sqrt (2 * h) ≤ ‖b 1‖} :=
            planarBrownianMotion_exitTime_ball_le_le w (by positivity) hh0 hG2
        _ ≤ 4 * ε₁ := mul_le_mul' le_rfl hG1
        _ = (2 : ℝ≥0∞) ^ (-q) := by
          rw [hε₁, ENNReal.ofReal_div_of_pos (by norm_num), ← ENNReal.ofReal_rpow_of_pos
            (by norm_num)]
          norm_num
          rw [ENNReal.mul_div_cancel (by norm_num) (by norm_num)]
    have hcell (w : ℂ) : Cell w ≤ 2 ^ (q - 1) * (2592 * Bsq) + 2⁻¹ * W := by
      have hrest := lintegral_halfDisc_occupation_rpow_le_ball_exit_add hh hε γ hq1.le h (r / 2) w
      have hnear := lintegral_halfDisc_occupation_ball_exit_rpow_le hh hr hr10 hδ hδ2 γ hq1.le
        hq2 w w
      rw [hεδ] at hnear
      calc Cell w ≤ _ := hrest
        _ ≤ 2 ^ (q - 1) * (2592 * Bsq + (2 : ℝ≥0∞) ^ (-q) * W) :=
          mul_le_mul' le_rfl (add_le_add hnear (mul_le_mul' (hexit w) le_rfl))
        _ = 2 ^ (q - 1) * (2592 * Bsq) + 2 ^ (q - 1) * (2 : ℝ≥0∞) ^ (-q) * W := by ring
        _ = 2 ^ (q - 1) * (2592 * Bsq) + 2⁻¹ * W := by
          rw [← ENNReal.rpow_add _ _ (by norm_num) (by norm_num)]
          congr 2
          rw [show q - 1 + -q = (-1 : ℝ) by ring, ENNReal.rpow_neg_one]
    have hWle : W ≤ 2 * (2 ^ (q - 1) * (2592 * Bsq)) := by
      have h1 : W ≤ 2 ^ (q - 1) * (2592 * Bsq) + 2⁻¹ * W := iSup_le hcell
      have hhalf : W = 2⁻¹ * W + 2⁻¹ * W := by
        rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      have h2 : 2⁻¹ * W + 2⁻¹ * W ≤ 2 ^ (q - 1) * (2592 * Bsq) + 2⁻¹ * W := by
        rw [← hhalf]
        exact h1
      have h3 : 2⁻¹ * W ≤ 2 ^ (q - 1) * (2592 * Bsq) :=
        (ENNReal.add_le_add_iff_right (ENNReal.mul_ne_top (by norm_num) hWfin.ne)).mp h2
      calc W = 2 * (2⁻¹ * W) := by
            rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ 2 * (2 ^ (q - 1) * (2592 * Bsq)) := mul_le_mul' le_rfl h3
    have hlog5 : Real.log (5 * r / 2) - Real.log r = Real.log (5 / 2) := by
      rw [show 5 * r / 2 = (5 / 2) * r by ring, Real.log_mul (by norm_num) hr.ne']
      ring
    have hlog3 : Real.log (3 * r / 2) - Real.log r = Real.log (3 / 2) := by
      rw [show 3 * r / 2 = (3 / 2) * r by ring, Real.log_mul (by norm_num) hr.ne']
      ring
    have hreal : Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) * ((4 * r) ^ 2) ^ q =
        (4 * s₀) ^ ζ * h ^ a := by
      rw [mul_comm, exp_mul_sq_rpow_eq_rpow (by positivity : (0 : ℝ) < 4 * r),
        show 4 * r = (4 * s₀) * Real.sqrt h by rw [hrdef]; ring,
        mul_sqrt_rpow_eq (by positivity) hh0.le, hζ, ha]
      congr 2
    have hfac : ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
        ENNReal.ofReal ((4 * r) ^ 2) ^ q =
        ENNReal.ofReal ((4 * s₀) ^ ζ) * ENNReal.ofReal (h ^ a) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le, ← ENNReal.ofReal_mul (by positivity),
        hreal, ENNReal.ofReal_mul (by positivity)]
    have hFeq : ENNReal.ofReal ((q * (Real.log (5 * r / 2) - Real.log r) /
        (Real.log (3 * r / 2) - Real.log r)) ^ q) = F := by
      rw [hlog5, hlog3]
    have h2q : (2 : ℝ≥0∞) ^ q = 2 * 2 ^ (q - 1) := by
      conv_lhs => rw [show q = 1 + (q - 1) by ring]
      rw [ENNReal.rpow_add _ _ (by norm_num) (by norm_num), ENNReal.rpow_one]
    calc Cell y ≤ W := le_iSup (fun w => Cell w) y
      _ ≤ 2 * (2 ^ (q - 1) * (2592 * Bsq)) := hWle
      _ = 2 ^ q * 2592 * (ENNReal.ofReal ((4 * s₀) ^ ζ) *
          (⨆ w, stoppedHalfDiscMoment P hcirc γ δ q w) * F) * ENNReal.ofReal (h ^ a) := by
        rw [hBsq, hfac, hFeq, h2q]
        ring
      _ ≤ CB * ENNReal.ofReal (h ^ a) := by
        rw [hCB]
        gcongr
        exact iSup_le (fun w => hΦ δ hδ hδ2 w)
      _ ≤ (CA + CB) * ENNReal.ofReal (h ^ a) := mul_le_mul' le_add_self le_rfl

/-- **Time cells.** A bound on the half-disc occupation moments up to time `h` that is
uniform in the start bounds the moments over every time cell `(t, t + h]`. -/
theorem lintegral_halfDisc_occupation_cell_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {ε : ℝ} (hε : 0 < ε) (γ : ℝ) (q : ℝ) {h : ℝ} (hh0 : 0 ≤ h) (B : ℝ≥0∞)
    (hB : ∀ y : ℂ, (∫⁻ ω, ∫⁻ b, pathOccupationBefore
      ({z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (normalizedCircleDensity hcirc γ ε ω))
        (ENNReal.ofReal h) b ^ q ∂planarBrownianMotion y ∂P) ≤ B) (x : ℂ) (t : ℝ≥0) :
    (∫⁻ ω, ∫⁻ b, (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h),
      {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (normalizedCircleDensity hcirc γ ε ω)
        (b s.toNNReal)) ^ q ∂planarBrownianMotion x ∂P) ≤ B := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  set Td : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} with hTd
  have hTdm : MeasurableSet Td := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let f : Ω → ℂ → ℝ≥0∞ := fun ω => Td.indicator (normalizedCircleDensity H γ ε ω)
  have hf : Measurable (Function.uncurry f) :=
    measurable_uncurry_indicator (measurable_normalizedCircleDensity (hHm ε hε) γ) hTdm
  have hconv (ω : Ω) (hω : ∀ r z, H ω r z = hcirc ω r z) :
      Td.indicator (normalizedCircleDensity hcirc γ ε ω) = f ω := by
    have h' : normalizedCircleDensity hcirc γ ε ω = normalizedCircleDensity H γ ε ω := by
      funext w
      simp only [normalizedCircleDensity, hω]
    simp only [f, h']
  let G : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun p =>
    pathOccupationBefore (f p.1) (ENNReal.ofReal h) p.2 ^ q
  have hG : Measurable G :=
    (measurable_pathOccupationBefore (fun p : Ω × ContinuousPath ℂ => f p.1)
      (hf.comp (measurable_fst.fst.prodMk measurable_snd))
      (fun _ => ENNReal.ofReal h) measurable_const (fun p => p.2) measurable_snd).pow_const q
  have hshift : Measurable (ContinuousPath.shift (alpha := ℂ) t) :=
    (ContinuousPath.continuous_shift_fixed t).measurable
  have hGs : Measurable (fun p : Ω × ContinuousPath ℂ => G (p.1, ContinuousPath.shift t p.2)) :=
    hG.comp (measurable_fst.prodMk (hshift.comp measurable_snd))
  have hcell (ω : Ω) (b : ContinuousPath ℂ) : (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h),
      f ω (b s.toNNReal)) = pathOccupationBefore (f ω) (ENNReal.ofReal h)
        (ContinuousPath.shift t b) := by
    unfold pathOccupationBefore
    rw [lintegral_stopped_indicator_eq _ _ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hh0,
      lintegral_shift_path_occupation]
  calc
    _ = ∫⁻ ω, ∫⁻ b, G (ω, ContinuousPath.shift t b) ∂planarBrownianMotion x ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hHae] with ω hω
      apply lintegral_congr
      intro b
      rw [hconv ω hω, hcell ω b]
    _ = ∫⁻ b, ∫⁻ ω, G (ω, ContinuousPath.shift t b) ∂P ∂planarBrownianMotion x :=
      lintegral_lintegral_swap hGs.aemeasurable
    _ ≤ B := by
      apply lintegral_planarBrownianMotion_shift_le_uniform x t (fun b' => ∫⁻ ω, G (ω, b') ∂P)
        hG.lintegral_prod_left' B
      intro y
      calc (∫⁻ b', ∫⁻ ω, G (ω, b') ∂P ∂planarBrownianMotion y) =
          ∫⁻ ω, ∫⁻ b', G (ω, b') ∂planarBrownianMotion y ∂P :=
            (lintegral_lintegral_swap (hG.comp measurable_swap).aemeasurable)
        _ = _ := by
          apply lintegral_congr_ae
          filter_upwards [hHae] with ω hω
          rw [hconv ω hω]
        _ ≤ B := hB y

/-- A time interval split into `N` consecutive pieces of equal length. -/
theorem lintegral_Ioc_eq_sum_Ioc (f : ℝ → ℝ≥0∞) (t d : ℝ) (hd : 0 ≤ d) (N : ℕ) :
    (∫⁻ s in Ioc t (t + N * d), f s) =
      ∑ k ∈ Finset.range N, ∫⁻ s in Ioc (t + k * d) (t + k * d + d), f s := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h1 : t ≤ t + N * d := by have : 0 ≤ (N : ℝ) * d := by positivity
                                  linarith
    have h2 : t + N * d ≤ t + N * d + d := by linarith
    rw [show t + ((N + 1 : ℕ) : ℝ) * d = t + N * d + d by push_cast; ring,
      ← Ioc_union_Ioc_eq_Ioc h1 h2, lintegral_union measurableSet_Ioc
        (Ioc_disjoint_Ioc_of_le le_rfl)]

/-- **Smoothing-uniform half-disc cell moments.** For `γ² < 4` there are an order
`p ∈ (1, 2]` with `p γ² < 4`, the exponent `a = p - γ² p (p - 1) / 4 > 1` and a finite
constant such that, for every smoothing radius in `(0, 1/2]`, every Brownian start, every
time `t ≥ 0` and every `h ∈ (0, 1]`, the field-Brownian `p`-th moment of the half-disc
occupation of the normalized density over `(t, t + h]` is at most the constant times
`h ^ a`. -/
theorem exists_halfDisc_cell_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ2 : γ ^ 2 < 4) :
    ∃ p a : ℝ, 1 < p ∧ p ≤ 2 ∧ p * γ ^ 2 < 4 ∧ a = p - γ ^ 2 * p * (p - 1) / 4 ∧ 1 < a ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ε, 0 < ε → ε ≤ 1 / 2 → ∀ (x : ℂ) (t : ℝ≥0) (h : ℝ), 0 < h → h ≤ 1 →
        (∫⁻ ω, ∫⁻ b, (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h),
          {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (normalizedCircleDensity hcirc γ ε ω)
            (b s.toNNReal)) ^ p ∂planarBrownianMotion x ∂P) ≤ C * ENNReal.ofReal (h ^ a) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  obtain ⟨q, hq1, hq2, hqγ, h₀, hh₀, C, hC, hcell⟩ := exists_halfDisc_occupation_rpow_le_time hh hγ2
  have hq0 : 0 < q := by linarith
  set a : ℝ := q - γ ^ 2 * q * (q - 1) / 4 with ha
  have ha1 : 1 < a := by
    have : a - 1 = (q - 1) * (4 - q * γ ^ 2) / 4 := by rw [ha]; ring
    have : 0 < (q - 1) * (4 - q * γ ^ 2) / 4 := by
      apply div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)
    linarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈1 / h₀⌉₊ + 1 := ⟨_, rfl⟩
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; positivity
  have hNh₀ : 1 / (N : ℝ) ≤ h₀ := by
    have h1 : 1 / h₀ ≤ (N : ℝ) := by
      have := Nat.le_ceil (1 / h₀)
      rw [hNdef]
      push_cast
      linarith
    rw [div_le_iff₀ hNpos]
    rw [div_le_iff₀ hh₀] at h1
    linarith
  refine ⟨q, a, hq1, hq2, hqγ, ha, ha1, 2 * N * (N * C),
    ENNReal.mul_lt_top (by finiteness) (ENNReal.mul_lt_top (by finiteness) hC), ?_⟩
  intro ε hε hε2 x t h hh0 hh1
  set Td : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} with hTd
  have hTdm : MeasurableSet Td := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let f : Ω → ℂ → ℝ≥0∞ := fun ω => Td.indicator (normalizedCircleDensity H γ ε ω)
  have hf : Measurable (Function.uncurry f) :=
    measurable_uncurry_indicator (measurable_normalizedCircleDensity (hHm ε hε) γ) hTdm
  have hev : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ => p.1.2 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  have hYm (u v : ℝ) : Measurable (fun pr : Ω × ContinuousPath ℂ =>
      (∫⁻ s in Ioc u v, f pr.1 (pr.2 s.toNNReal)) ^ q) := by
    apply Measurable.pow_const
    exact (hf.comp (measurable_fst.fst.prodMk hev)).lintegral_prod_right'
  have hevb : Measurable (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hYω (ω : Ω) (u v : ℝ) : Measurable (fun b : ContinuousPath ℂ =>
      (∫⁻ s in Ioc u v, f ω (b s.toNNReal)) ^ q) :=
    ((hf.comp ((measurable_const (a := ω)).prodMk hevb)).lintegral_prod_right'
      (ν := volume.restrict (Ioc u v))).pow_const q
  have hconv (ω : Ω) (hω : ∀ r z, H ω r z = hcirc ω r z) :
      Td.indicator (normalizedCircleDensity hcirc γ ε ω) = f ω := by
    have h' : normalizedCircleDensity hcirc γ ε ω = normalizedCircleDensity H γ ε ω := by
      funext w
      simp only [normalizedCircleDensity, hω]
    simp only [f, h']
  -- subcells of length h / N
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = h / N := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; positivity
  have hdh₀ : d ≤ h₀ := by
    calc d = h * (1 / N) := by rw [hd]; ring
      _ ≤ 1 * (1 / N) := by gcongr
      _ ≤ h₀ := by linarith
  have hdh : d ≤ h := by
    rw [hd, div_le_iff₀ hNpos]
    have : (1 : ℝ) ≤ N := by
      rw [hNdef]
      push_cast
      have := Nat.cast_nonneg (α := ℝ) ⌈1 / h₀⌉₊
      linarith
    nlinarith
  obtain ⟨tk, htk⟩ : ∃ tk : ℕ → ℝ≥0, ∀ k, (tk k : ℝ) = (t : ℝ) + k * d :=
    ⟨fun k => ⟨(t : ℝ) + k * d, by positivity⟩, fun _ => rfl⟩
  have hsub (k : ℕ) : (∫⁻ ω, ∫⁻ b, (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d),
      f ω (b s.toNNReal)) ^ q ∂planarBrownianMotion x ∂P) ≤ C * ENNReal.ofReal (d ^ a) := by
    have hB : ∀ y : ℂ, (∫⁻ ω, ∫⁻ b, pathOccupationBefore
        (Td.indicator (normalizedCircleDensity hcirc γ ε ω)) (ENNReal.ofReal d) b ^ q
          ∂planarBrownianMotion y ∂P) ≤ C * ENNReal.ofReal (d ^ a) :=
      fun y => hcell d hd0 hdh₀ ε hε hε2 y
    have h := lintegral_halfDisc_occupation_cell_rpow_le hh hε γ q hd0.le _ hB x (tk k)
    refine le_trans (le_of_eq ?_) h
    apply lintegral_congr_ae
    filter_upwards [hHae] with ω hω
    rw [hconv ω hω]
  have hsplit (ω : Ω) (b : ContinuousPath ℂ) : (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h),
      f ω (b s.toNNReal)) = ∑ k ∈ Finset.range N,
        ∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal) := by
    have hNd : (t : ℝ) + h = (t : ℝ) + N * d := by
      rw [hd]
      field_simp
    rw [hNd, lintegral_Ioc_eq_sum_Ioc _ _ _ hd0.le]
    simp only [htk]
  have hpow (ω : Ω) (b : ContinuousPath ℂ) : (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h),
      f ω (b s.toNNReal)) ^ q ≤ 2 * N * ∑ k ∈ Finset.range N,
        (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q := by
    rw [hsplit ω b]
    set X : ℕ → ℝ≥0∞ := fun k => ∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)
    calc (∑ k ∈ Finset.range N, X k) ^ q ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (X i * X j) ^ (q / 2) := rpow_sum_le_sum_cross _ X hq0 hq2
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ (Finset.range N).filter (fun _ => True),
          (X i * X j) ^ (q / 2) := by
        rw [Finset.filter_true_of_mem (fun _ _ => trivial)]
      _ ≤ _ := sum_rpow_mul_le_degree_mul_sum_rpow _ X (fun _ _ => True)
          (fun _ _ _ => trivial) N (fun i _ => by simp) hq0.le
  calc
    _ = ∫⁻ ω, ∫⁻ b, (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h), f ω (b s.toNNReal)) ^ q
        ∂planarBrownianMotion x ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hHae] with ω hω
      rw [hconv ω hω]
    _ ≤ ∫⁻ ω, ∫⁻ b, 2 * N * ∑ k ∈ Finset.range N,
        (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q
          ∂planarBrownianMotion x ∂P :=
      lintegral_mono fun ω => lintegral_mono fun b => hpow ω b
    _ = (2 * N * ∑ k ∈ Finset.range N, ∫⁻ ω, ∫⁻ b,
        (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q
          ∂planarBrownianMotion x ∂P) := by
      have hne : 2 * (N : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top N)
      calc (∫⁻ ω, ∫⁻ b, 2 * (N : ℝ≥0∞) * ∑ k ∈ Finset.range N,
            (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q
              ∂planarBrownianMotion x ∂P) =
          ∫⁻ ω, 2 * (N : ℝ≥0∞) * ∑ k ∈ Finset.range N, ∫⁻ b,
            (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q
              ∂planarBrownianMotion x ∂P := by
            apply lintegral_congr
            intro ω
            rw [lintegral_const_mul' (2 * (N : ℝ≥0∞)) _ hne]
            congr 1
            exact lintegral_finsetSum' _ (fun k _ => (hYω ω _ _).aemeasurable)
        _ = 2 * N * ∑ k ∈ Finset.range N, ∫⁻ ω, ∫⁻ b,
            (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q
              ∂planarBrownianMotion x ∂P := by
            rw [lintegral_const_mul' (2 * (N : ℝ≥0∞)) _ hne]
            congr 1
            exact lintegral_finsetSum' _ (fun k _ => ((hYm _ _).lintegral_prod_right').aemeasurable)
    _ ≤ (2 * N * ∑ _k ∈ Finset.range N, C * ENNReal.ofReal (d ^ a)) := by
      gcongr with k hk
      exact hsub k
    _ ≤ (2 * N * (N * C)) * ENNReal.ofReal (h ^ a) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hda : ENNReal.ofReal (d ^ a) ≤ ENNReal.ofReal (h ^ a) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hd0.le hdh (by linarith))
      calc (2 * N * (N * (C * ENNReal.ofReal (d ^ a)))) ≤
          (2 * N * (N * (C * ENNReal.ofReal (h ^ a)))) := by gcongr
        _ = _ := by ring


/-- **Smoothing-uniform moments of inserted annular clock cells.** For `γ² < 4`, any
insertion `α` and any inner radius `δ ∈ (0, 1/2]`, there are `p ∈ (1, 2]`, `a > 1` and
a finite constant such that, for every smoothing radius `ε ∈ (0, δ]`, every Brownian
start, every time `t ≥ 0` and every `h ∈ (0, 1]`, the product-law `p`-th moment of the
inserted annular clock increment over `(t, t + h]` is at most the constant times
`h ^ a`. -/
theorem exists_inserted_annular_cell_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ2 : γ ^ 2 < 4) (α : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∃ p a : ℝ, 1 < p ∧ p ≤ 2 ∧ 1 < a ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ε, 0 < ε → ε ≤ δ → ∀ (x : ℂ) (t : ℝ≥0) (h : ℝ), 0 < h → h ≤ 1 →
        (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h), ENNReal.ofReal
          ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal))) ^ p
          ∂(P.prod (planarBrownianMotion x))) ≤ C * ENNReal.ofReal (h ^ a) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  obtain ⟨q, hq1, hq2, hqγ, h₀, hh₀, C, hC, hcell⟩ := exists_halfDisc_occupation_rpow_le_time hh hγ2
  have hq0 : 0 < q := by linarith
  set a : ℝ := q - γ ^ 2 * q * (q - 1) / 4 with ha
  have ha1 : 1 < a := by
    have : a - 1 = (q - 1) * (4 - q * γ ^ 2) / 4 := by rw [ha]; ring
    have : 0 < (q - 1) * (4 - q * γ ^ 2) / 4 := by
      apply div_pos (mul_pos (by linarith) (by linarith)) (by norm_num)
    linarith
  set K := ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|)) with hK
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈1 / h₀⌉₊ + 1 := ⟨_, rfl⟩
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; positivity
  have hNh₀ : 1 / (N : ℝ) ≤ h₀ := by
    have h1 : 1 / h₀ ≤ (N : ℝ) := by
      have := Nat.le_ceil (1 / h₀)
      rw [hNdef]
      push_cast
      linarith
    rw [div_le_iff₀ hNpos]
    rw [div_le_iff₀ hh₀] at h1
    linarith
  refine ⟨q, a, hq1, hq2, ha1, K ^ q * (2 * N * (N * C)),
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)
      (ENNReal.mul_lt_top (by finiteness) (ENNReal.mul_lt_top (by finiteness) hC)), ?_⟩
  intro ε hε hεδ x t h hh0 hh1
  have hε2 : ε ≤ 1 / 2 := hεδ.trans hδ2
  set Td : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} with hTd
  have hTdm : MeasurableSet Td := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hdens : ∀ᵐ ω ∂P, ∀ w : ℂ, ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator
      (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) w) ≤
      K * Td.indicator (normalizedCircleDensity H γ ε ω) w := by
    filter_upwards [ae_annular_inserted_clock_density_le_uninserted hh hε hεδ γ α,
      ae_recentered_inserted_circle_average hh 0, hh.ae_circleAverage_one_zero, hHae]
      with ω hins h0 hone hω w
    refine (hins w).trans (mul_le_mul' le_rfl ?_)
    by_cases hw : δ ≤ ‖w‖ ∧ ‖w‖ ≤ 1 / 2
    · rw [Set.indicator_of_mem (show w ∈ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} from hw),
        Set.indicator_of_mem (show w ∈ Td from ⟨norm_nonneg _, hw.2⟩)]
      apply le_of_eq
      rw [← h0 ε w hε, hone]
      simp only [zero_mul, sub_zero, normalizedCircleDensity, hω]
      rw [← gmcDensity_eq_exp_normalized hcirc hε]
      rfl
    · rw [Set.indicator_of_notMem (show w ∉ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} from hw),
        ENNReal.ofReal_zero]
      exact zero_le
  let f : Ω → ℂ → ℝ≥0∞ := fun ω => Td.indicator (normalizedCircleDensity H γ ε ω)
  have hf : Measurable (Function.uncurry f) :=
    measurable_uncurry_indicator (measurable_normalizedCircleDensity (hHm ε hε) γ) hTdm
  have hev : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ => p.1.2 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  have hYm (u v : ℝ) : Measurable (fun pr : Ω × ContinuousPath ℂ =>
      (∫⁻ s in Ioc u v, f pr.1 (pr.2 s.toNNReal)) ^ q) := by
    apply Measurable.pow_const
    exact (hf.comp (measurable_fst.fst.prodMk hev)).lintegral_prod_right'
  have hevb : Measurable (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hYω (ω : Ω) (u v : ℝ) : Measurable (fun b : ContinuousPath ℂ =>
      (∫⁻ s in Ioc u v, f ω (b s.toNNReal)) ^ q) :=
    ((hf.comp ((measurable_const (a := ω)).prodMk hevb)).lintegral_prod_right'
      (ν := volume.restrict (Ioc u v))).pow_const q
  have hconv (ω : Ω) (hω : ∀ r z, H ω r z = hcirc ω r z) :
      Td.indicator (normalizedCircleDensity hcirc γ ε ω) = f ω := by
    have h' : normalizedCircleDensity hcirc γ ε ω = normalizedCircleDensity H γ ε ω := by
      funext w
      simp only [normalizedCircleDensity, hω]
    simp only [f, h']
  -- subcells of length h / N
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = h / N := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; positivity
  have hdh₀ : d ≤ h₀ := by
    calc d = h * (1 / N) := by rw [hd]; ring
      _ ≤ 1 * (1 / N) := by gcongr
      _ ≤ h₀ := by linarith
  have hdh : d ≤ h := by
    rw [hd, div_le_iff₀ hNpos]
    have : (1 : ℝ) ≤ N := by
      rw [hNdef]
      push_cast
      have := Nat.cast_nonneg (α := ℝ) ⌈1 / h₀⌉₊
      linarith
    nlinarith
  obtain ⟨tk, htk⟩ : ∃ tk : ℕ → ℝ≥0, ∀ k, (tk k : ℝ) = (t : ℝ) + k * d :=
    ⟨fun k => ⟨(t : ℝ) + k * d, by positivity⟩, fun _ => rfl⟩
  have hsub (k : ℕ) : (∫⁻ ω, ∫⁻ b, (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d),
      f ω (b s.toNNReal)) ^ q ∂planarBrownianMotion x ∂P) ≤ C * ENNReal.ofReal (d ^ a) := by
    have hB : ∀ y : ℂ, (∫⁻ ω, ∫⁻ b, pathOccupationBefore
        (Td.indicator (normalizedCircleDensity hcirc γ ε ω)) (ENNReal.ofReal d) b ^ q
          ∂planarBrownianMotion y ∂P) ≤ C * ENNReal.ofReal (d ^ a) :=
      fun y => hcell d hd0 hdh₀ ε hε hε2 y
    have h := lintegral_halfDisc_occupation_cell_rpow_le hh hε γ q hd0.le _ hB x (tk k)
    refine le_trans (le_of_eq ?_) h
    apply lintegral_congr_ae
    filter_upwards [hHae] with ω hω
    rw [hconv ω hω]
  have hsplit (ω : Ω) (b : ContinuousPath ℂ) : (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h),
      f ω (b s.toNNReal)) = ∑ k ∈ Finset.range N,
        ∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal) := by
    have hNd : (t : ℝ) + h = (t : ℝ) + N * d := by
      rw [hd]
      field_simp
    rw [hNd, lintegral_Ioc_eq_sum_Ioc _ _ _ hd0.le]
    simp only [htk]
  have hpow (ω : Ω) (b : ContinuousPath ℂ) : (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h),
      f ω (b s.toNNReal)) ^ q ≤ 2 * N * ∑ k ∈ Finset.range N,
        (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q := by
    rw [hsplit ω b]
    set X : ℕ → ℝ≥0∞ := fun k => ∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)
    calc (∑ k ∈ Finset.range N, X k) ^ q ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (X i * X j) ^ (q / 2) := rpow_sum_le_sum_cross _ X hq0 hq2
      _ = ∑ i ∈ Finset.range N, ∑ j ∈ (Finset.range N).filter (fun _ => True),
          (X i * X j) ^ (q / 2) := by
        rw [Finset.filter_true_of_mem (fun _ _ => trivial)]
      _ ≤ _ := sum_rpow_mul_le_degree_mul_sum_rpow _ X (fun _ _ => True)
          (fun _ _ _ => trivial) N (fun i _ => by simp) hq0.le
  calc
    _ ≤ ∫⁻ pr : Ω × ContinuousPath ℂ, K ^ q * (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h),
        f pr.1 (pr.2 s.toNNReal)) ^ q ∂(P.prod (planarBrownianMotion x)) := by
      apply lintegral_mono_ae
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
        (ν := planarBrownianMotion x)).ae hdens] with p hp
      rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.rpow_le_rpow (lintegral_mono fun s => hp _) hq0.le
    _ = K ^ q * ∫⁻ ω, ∫⁻ b, (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h), f ω (b s.toNNReal)) ^ q
        ∂planarBrownianMotion x ∂P := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top),
        lintegral_prod _ (hYm _ _).aemeasurable]
    _ ≤ K ^ q * ∫⁻ ω, ∫⁻ b, 2 * N * ∑ k ∈ Finset.range N,
        (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q
          ∂planarBrownianMotion x ∂P :=
      mul_le_mul' le_rfl (lintegral_mono fun ω => lintegral_mono fun b => hpow ω b)
    _ = K ^ q * (2 * N * ∑ k ∈ Finset.range N, ∫⁻ ω, ∫⁻ b,
        (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q
          ∂planarBrownianMotion x ∂P) := by
      congr 1
      have hne : 2 * (N : ℝ≥0∞) ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top N)
      calc (∫⁻ ω, ∫⁻ b, 2 * (N : ℝ≥0∞) * ∑ k ∈ Finset.range N,
            (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q
              ∂planarBrownianMotion x ∂P) =
          ∫⁻ ω, 2 * (N : ℝ≥0∞) * ∑ k ∈ Finset.range N, ∫⁻ b,
            (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q
              ∂planarBrownianMotion x ∂P := by
            apply lintegral_congr
            intro ω
            rw [lintegral_const_mul' (2 * (N : ℝ≥0∞)) _ hne]
            congr 1
            exact lintegral_finsetSum' _ (fun k _ => (hYω ω _ _).aemeasurable)
        _ = 2 * N * ∑ k ∈ Finset.range N, ∫⁻ ω, ∫⁻ b,
            (∫⁻ s in Ioc ((tk k : ℝ)) ((tk k : ℝ) + d), f ω (b s.toNNReal)) ^ q
              ∂planarBrownianMotion x ∂P := by
            rw [lintegral_const_mul' (2 * (N : ℝ≥0∞)) _ hne]
            congr 1
            exact lintegral_finsetSum' _ (fun k _ => ((hYm _ _).lintegral_prod_right').aemeasurable)
    _ ≤ K ^ q * (2 * N * ∑ _k ∈ Finset.range N, C * ENNReal.ofReal (d ^ a)) := by
      gcongr with k hk
      exact hsub k
    _ ≤ K ^ q * (2 * N * (N * C)) * ENNReal.ofReal (h ^ a) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hda : ENNReal.ofReal (d ^ a) ≤ ENNReal.ofReal (h ^ a) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hd0.le hdh (by linarith))
      calc K ^ q * (2 * N * (N * (C * ENNReal.ofReal (d ^ a)))) ≤
          K ^ q * (2 * N * (N * (C * ENNReal.ofReal (h ^ a)))) := by gcongr
        _ = _ := by ring

/-- Exponential moments of a circle average are finite. -/
theorem lintegral_exp_mul_circle_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ) (l : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (l * hcirc ω r z)) ∂P) < ⊤ := by
  have hX := hh.hasLaw_circle hr z
  have hm : Measurable (fun ω => hcirc ω r z) := hh.measurable_circle r z hr
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (l * x))) := by fun_prop
  rw [← lintegral_map hf hm, hX.map_eq, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_mul_gaussianReal l) (ae_of_all _ fun x => (Real.exp_pos _).le)]
  exact ENNReal.ofReal_lt_top

/-- Outside the closed disc of radius `1/2` and inside the disc of radius `R`, the
inserted density is bounded by a constant, the exponential of the circle average at
radius `κ = 2 R`, and the normalized density of the field rescaled by `κ` at the
rescaled point. -/
theorem exterior_inserted_density_le {Ω : Type*} (hcirc H' : Ω → ℝ → ℂ → ℝ) (ω : Ω)
    {γ α R ε : ℝ} (hR : 0 < R)
    (hH' : ∀ r z, H' ω r z = hcirc ω (2 * R * r) (((2 * R : ℝ) : ℂ) * z) - hcirc ω (2 * R) 0)
    (hone : hcirc ω 1 0 = 0)
    (hrec : ∀ r z, 0 < r → hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) =
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (z : ℂ) :
    ENNReal.ofReal ({w : ℂ | 1 / 2 < ‖w‖ ∧ ‖w‖ ≤ R}.indicator (fun w => ε ^ (γ ^ 2 / 2) *
      Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w)) z) ≤
      ENNReal.ofReal (Real.exp (|γ * α| * (Real.log 2 + |Real.log R|)) * (2 * R) ^ (γ ^ 2 / 2) *
        Real.exp (γ * hcirc ω (2 * R) 0)) *
      {u : ℂ | (0 : ℝ) ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2}.indicator
        (normalizedCircleDensity H' γ (ε / (2 * R)) ω)
        (affineScaling (show (0 : ℝ) < 2 * R by positivity) 0 z) := by
  have hκ : (0 : ℝ) < 2 * R := by positivity
  by_cases hz : 1 / 2 < ‖z‖ ∧ ‖z‖ ≤ R
  · rw [Set.indicator_of_mem (show z ∈ {w : ℂ | 1 / 2 < ‖w‖ ∧ ‖w‖ ≤ R} from hz)]
    set u := affineScaling hκ 0 z with hu
    have hu' : u = ((2 * R)⁻¹ : ℝ) • z := by rw [hu, affineScaling_apply, sub_zero]
    have hun : ‖u‖ = ‖z‖ / (2 * R) := by
      rw [hu', norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hκ, inv_mul_eq_div]
    have huT : u ∈ {u : ℂ | (0 : ℝ) ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2} := by
      refine ⟨norm_nonneg _, ?_⟩
      rw [hun, div_le_iff₀ hκ]
      linarith [hz.2]
    rw [Set.indicator_of_mem huT, normalizedCircleDensity]
    have hκu : ((2 * R : ℝ) : ℂ) * u = z := by
      rw [hu', Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
        mul_inv_cancel₀ hκ.ne', Complex.ofReal_one, one_mul]
    have hrad : 2 * R * (ε / (2 * R)) = ε := by field_simp
    rw [hH', hrad, hκu, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hz0 : 0 < ‖z‖ := by linarith [hz.1]
    have hmax : max ε ‖z‖ = ‖z‖ := max_eq_right (by linarith [hz.1])
    rw [← hrec ε z hε, hone, hmax]
    have hlog : -(γ * α) * Real.log ‖z‖ ≤ |γ * α| * (Real.log 2 + |Real.log R|) := by
      have h1 : |Real.log ‖z‖| ≤ Real.log 2 + |Real.log R| := by
        rw [abs_le]
        constructor
        · have : Real.log (1 / 2) ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) hz.1.le
          rw [one_div, Real.log_inv] at this
          linarith [abs_nonneg (Real.log R)]
        · have : Real.log ‖z‖ ≤ Real.log R := Real.log_le_log hz0 hz.2
          have := le_abs_self (Real.log R)
          have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
          linarith
      calc -(γ * α) * Real.log ‖z‖ ≤ |-(γ * α) * Real.log ‖z‖| := le_abs_self _
        _ = |γ * α| * |Real.log ‖z‖| := by rw [abs_mul, abs_neg]
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have hεκ : 0 < ε / (2 * R) := by positivity
    rw [Real.rpow_def_of_pos hε, Real.rpow_def_of_pos hκ, Real.log_div hε.ne' hκ.ne']
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hlog]
  · rw [Set.indicator_of_notMem (show z ∉ {w : ℂ | 1 / 2 < ‖w‖ ∧ ‖w‖ ≤ R} from hz),
      ENNReal.ofReal_zero]
    exact zero_le

/-- A time integral of a density at the rescaled path position, under the affine
space-time scaling by `κ` about the origin. -/
theorem lintegral_Ioc_affineScaling_rescale (b : ContinuousPath ℂ) {κ : ℝ} (hκ : 0 < κ)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (t h : ℝ) :
    (∫⁻ s in Ioc t (t + h), g (affineScaling hκ 0 (b s.toNNReal))) =
      ENNReal.ofReal (κ ^ 2) * ∫⁻ σ in Ioc (t / κ ^ 2) (t / κ ^ 2 + h / κ ^ 2),
        g (ContinuousPath.rescale (affineScaling hκ 0) (κ ^ 2).toNNReal b σ.toNNReal) := by
  have hc : (0 : ℝ) < κ ^ 2 := by positivity
  have hf : Measurable (fun s : ℝ => g (affineScaling hκ 0 (b s.toNNReal))) :=
    hg.comp ((affineScaling hκ 0).continuous.measurable.comp
      (b.continuous.measurable.comp measurable_real_toNNReal))
  rw [lintegral_time_dilation hc _ measurableSet_Ioc _ hf]
  congr 1
  have hpre : (fun s : ℝ => κ ^ 2 * s) ⁻¹' Ioc t (t + h) =
      Ioc (t / κ ^ 2) (t / κ ^ 2 + h / κ ^ 2) := by
    ext s
    simp only [mem_preimage, mem_Ioc]
    rw [div_lt_iff₀ hc, ← add_div, le_div_iff₀ hc, mul_comm s]
  rw [hpre]
  apply lintegral_congr
  intro s
  rw [ContinuousPath.rescale_apply, Real.toNNReal_mul hc.le]

/-- **Smoothing-uniform moments of exterior inserted clock cells.** For `γ² < 4`, any
insertion `α` and any radius `R ≥ 1/2`, there are `p > 1`, `a > 1` and a finite
constant such that, for every smoothing radius `ε ∈ (0, 1/2]`, every Brownian start,
every time `t ≥ 0` and every `h ∈ (0, 1]`, the product-law `p`-th moment of the inserted
clock increment of the region `1/2 < ‖z‖ ≤ R` over `(t, t + h]` is at most the constant
times `h ^ a`. -/
theorem exists_exterior_inserted_cell_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ2 : γ ^ 2 < 4) (α : ℝ)
    {R : ℝ} (hR : 1 / 2 ≤ R) :
    ∃ p a : ℝ, 1 < p ∧ 1 < a ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ ε, 0 < ε → ε ≤ 1 / 2 → ∀ (x : ℂ) (t : ℝ≥0) (h : ℝ), 0 < h → h ≤ 1 →
        (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h), ENNReal.ofReal
          ({z : ℂ | 1 / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal))) ^ p
          ∂(P.prod (planarBrownianMotion x))) ≤ C * ENNReal.ofReal (h ^ a) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hR0 : 0 < R := by linarith
  set κ : ℝ := 2 * R with hκdef
  have hκ : 0 < κ := by positivity
  have hκ1 : 1 ≤ κ := by rw [hκdef]; linarith
  have hac : ((κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hnorm : ‖((κ : ℝ) : ℂ)‖ = κ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  -- the rescaled field is a whole-plane GFF
  have hh' := LatticeProb.LQG.AffineDerived.wholePlaneGFFAffineInvariance_lp P hC hcirc hh ((κ : ℝ) : ℂ) hac 0
  set hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (‖((κ : ℝ) : ℂ)‖ * r) (((κ : ℝ) : ℂ) * z + 0) - hcirc ω ‖((κ : ℝ) : ℂ)‖ 0 with hc'
  obtain ⟨q₀, a₀, hq₀1, hq₀2, hq₀γ, ha₀def, ha₀1, C₀, hC₀, hcell₀⟩ :=
    exists_halfDisc_cell_rpow_le hh' hγ2
  obtain ⟨H', _, hH'm, hH'ae⟩ := hh'.exists_jointlyMeasurable_circleAverage
  -- exponents
  set s' : ℝ := (1 + min q₀ a₀) / 2 with hs'
  have hs'1 : 1 < s' := by
    have := lt_min hq₀1 ha₀1
    rw [hs']
    linarith
  have hs'q : s' < q₀ := by
    have := min_le_left q₀ a₀
    have := lt_min hq₀1 ha₀1
    rw [hs']
    linarith
  have hs'a : s' < a₀ := by
    have := min_le_right q₀ a₀
    have := lt_min hq₀1 ha₀1
    rw [hs']
    linarith
  have hs'0 : 0 < s' := by linarith
  set p : ℝ := q₀ / s' with hp
  set a : ℝ := a₀ / s' with ha
  have hp1 : 1 < p := by rw [hp, one_lt_div hs'0]; exact hs'q
  have ha1 : 1 < a := by rw [ha, one_lt_div hs'0]; exact hs'a
  have hp0 : 0 < p := by linarith
  have hconj : (Real.conjExponent s').HolderConjugate s' :=
    (Real.HolderConjugate.conjExponent hs'1).symm
  set c : ℝ := Real.conjExponent s' with hc
  have hc0 : 0 < c := by
    rw [hc, Real.conjExponent]
    exact div_pos hs'0 (by linarith)
  -- constants
  set K₁ : ℝ := Real.exp (|γ * α| * (Real.log 2 + |Real.log R|)) * (2 * R) ^ (γ ^ 2 / 2) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  set M : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (Real.exp ((γ * p * c) * hcirc ω (2 * R) 0)) ∂P with hM
  have hMt : M < ⊤ := lintegral_exp_mul_circle_lt_top hh (by positivity) 0 _
  refine ⟨p, a, hp1, ha1, (ENNReal.ofReal K₁ * ENNReal.ofReal (κ ^ 2)) ^ p * M ^ (1 / c) *
    C₀ ^ (1 / s'), ?_, ?_⟩
  · refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ ?_) ?_
    · exact ENNReal.rpow_lt_top_of_nonneg hp0.le (by finiteness)
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hMt.ne
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hC₀.ne
  intro ε hε hε2 x t h hh0 hh1
  have hκ2 : (0 : ℝ) < κ ^ 2 := by positivity
  have hκ21 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ1
  set ε' : ℝ := ε / κ with hε'
  have hε'0 : 0 < ε' := by positivity
  have hε'2 : ε' ≤ 1 / 2 := by
    rw [hε', div_le_iff₀ hκ]
    nlinarith
  obtain ⟨t', ht'⟩ : ∃ t' : ℝ≥0, (t' : ℝ) = (t : ℝ) / κ ^ 2 := ⟨⟨_, by positivity⟩, rfl⟩
  set h' : ℝ := h / κ ^ 2 with hh'def
  have hh'0 : 0 < h' := by positivity
  have hh'h : h' ≤ h := by rw [hh'def, div_le_iff₀ hκ2]; nlinarith
  have hh'1 : h' ≤ 1 := hh'h.trans hh1
  set e := affineScaling hκ 0 with he
  set Bmap := ContinuousPath.rescale e (κ ^ 2).toNNReal with hBmap
  have hcpos : 0 < (κ ^ 2).toNNReal := Real.toNNReal_pos.mpr hκ2
  have hBm : Measurable Bmap :=
    (continuousPathRescaleHomeomorph e _ hcpos).continuous.measurable
  set x' : ℂ := κ⁻¹ • (x - 0) with hx'
  have hlaw : (planarBrownianMotion x).map Bmap = planarBrownianMotion x' :=
    planarBrownianMotion_map_rescale_affineScaling hκ 0 x
  set Td : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} with hTd
  have hTdm : MeasurableSet Td := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let f' : Ω → ℂ → ℝ≥0∞ := fun ω => Td.indicator (normalizedCircleDensity H' γ ε' ω)
  have hf' : Measurable (Function.uncurry f') :=
    measurable_uncurry_indicator (measurable_normalizedCircleDensity (hH'm ε' hε'0) γ) hTdm
  have hXm : Measurable (fun ω => hcirc ω (2 * R) 0) := hh.measurable_circle _ 0 (by positivity)
  have hev : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ => p.1.2 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  let Y0 : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun pr =>
    ∫⁻ σ in Ioc (t' : ℝ) ((t' : ℝ) + h'), f' pr.1 (pr.2 σ.toNNReal)
  have hY0 : Measurable Y0 := (hf'.comp (measurable_fst.fst.prodMk hev)).lintegral_prod_right'
  set Kc : ℝ≥0∞ := ENNReal.ofReal K₁ * ENNReal.ofReal (κ ^ 2) with hKc
  -- the good field event
  have hgood : ∀ᵐ ω ∂P, (∀ r z, H' ω r z =
      hcirc ω (2 * R * r) (((2 * R : ℝ) : ℂ) * z) - hcirc ω (2 * R) 0) ∧ hcirc ω 1 0 = 0 ∧
      (∀ r z, 0 < r → hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) =
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
    filter_upwards [hH'ae, hh.ae_circleAverage_one_zero,
      ae_recentered_inserted_circle_average hh α] with ω hω hone hrec
    refine ⟨fun r z => ?_, hone, hrec⟩
    rw [hω r z]
    simp only [hc', hnorm, add_zero]
    rfl
  -- pointwise bound on the product space
  have hpt : ∀ᵐ pr ∂(P.prod (planarBrownianMotion x)),
      (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h), ENNReal.ofReal
        ({z : ℂ | 1 / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc pr.1) ε z)) (pr.2 s.toNNReal))) ^ p ≤
      Kc ^ p * (ENNReal.ofReal (Real.exp (γ * hcirc pr.1 (2 * R) 0)) ^ p *
        Y0 (pr.1, Bmap pr.2) ^ p) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae hgood] with pr hpr
    obtain ⟨hH'pr, hone, hrec⟩ := hpr
    have hfm : Measurable (f' pr.1) := hf'.comp (measurable_const.prodMk measurable_id)
    have hin : (∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h), ENNReal.ofReal
        ({z : ℂ | 1 / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc pr.1) ε z)) (pr.2 s.toNNReal))) ≤
        ENNReal.ofReal (K₁ * Real.exp (γ * hcirc pr.1 (2 * R) 0)) *
          (ENNReal.ofReal (κ ^ 2) * Y0 (pr.1, Bmap pr.2)) := by
      calc _ ≤ ∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h),
            ENNReal.ofReal (K₁ * Real.exp (γ * hcirc pr.1 (2 * R) 0)) *
              f' pr.1 (e (pr.2 s.toNNReal)) := by
            apply lintegral_mono
            intro s
            exact exterior_inserted_density_le hcirc H' pr.1 hR0 hH'pr hone hrec hε hε2 _
        _ = ENNReal.ofReal (K₁ * Real.exp (γ * hcirc pr.1 (2 * R) 0)) *
            ∫⁻ s in Ioc (t : ℝ) ((t : ℝ) + h), f' pr.1 (e (pr.2 s.toNNReal)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = _ := by
          rw [lintegral_Ioc_affineScaling_rescale pr.2 hκ (f' pr.1) hfm]
          congr 2
          show _ = ∫⁻ σ in Ioc (t' : ℝ) ((t' : ℝ) + h'), f' pr.1 (Bmap pr.2 σ.toNNReal)
          rw [ht']
    calc _ ≤ (ENNReal.ofReal (K₁ * Real.exp (γ * hcirc pr.1 (2 * R) 0)) *
          (ENNReal.ofReal (κ ^ 2) * Y0 (pr.1, Bmap pr.2))) ^ p :=
          ENNReal.rpow_le_rpow hin hp0.le
      _ = _ := by
        rw [ENNReal.ofReal_mul hK₁0, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
          ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hKc,
          ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        ring
  -- integration, Hölder in the field and Jensen in the path
  let A : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (γ * hcirc ω (2 * R) 0)) ^ p
  have hAm : Measurable A :=
    (ENNReal.measurable_ofReal.comp (hXm.const_mul γ).exp).pow_const p
  let Z : Ω → ℝ≥0∞ := fun ω => ∫⁻ b', Y0 (ω, b') ^ p ∂planarBrownianMotion x'
  have hZm : Measurable Z := (hY0.pow_const p).lintegral_prod_right'
  have hprodm : Measurable (fun pr : Ω × ContinuousPath ℂ => A pr.1 * Y0 (pr.1, Bmap pr.2) ^ p) :=
    (hAm.comp measurable_fst).mul
      ((hY0.comp (measurable_fst.prodMk (hBm.comp measurable_snd))).pow_const p)
  have hKct : Kc ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le (by finiteness)
  have hAc (ω : Ω) : A ω ^ c = ENNReal.ofReal (Real.exp ((γ * p * c) * hcirc ω (2 * R) 0)) := by
    simp only [A]
    rw [← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity),
      ← Real.exp_mul]
    congr 2
    ring
  have hZs (ω : Ω) : Z ω ^ s' ≤ ∫⁻ b', Y0 (ω, b') ^ q₀ ∂planarBrownianMotion x' := by
    have hJ := LatticeProb.lintegral_rpow_le_measure_univ_mul (planarBrownianMotion x') hs'1.le
      (g := fun b' => Y0 (ω, b') ^ p)
      (((hY0.pow_const p).comp (measurable_const.prodMk measurable_id)).aemeasurable)
    rw [measure_univ, ENNReal.one_rpow, one_mul] at hJ
    refine hJ.trans (le_of_eq ?_)
    apply lintegral_congr
    intro b'
    rw [← ENNReal.rpow_mul]
    congr 1
    rw [hp]
    field_simp
  have hZint : (∫⁻ ω, ∫⁻ b', Y0 (ω, b') ^ q₀ ∂planarBrownianMotion x' ∂P) ≤
      C₀ * ENNReal.ofReal (h' ^ a₀) := by
    refine le_trans (le_of_eq ?_) (hcell₀ ε' hε'0 hε'2 x' t' h' hh'0 hh'1)
    apply lintegral_congr_ae
    filter_upwards [hH'ae] with ω hω
    have hcv : normalizedCircleDensity H' γ ε' ω = normalizedCircleDensity hcirc' γ ε' ω := by
      funext w
      simp only [normalizedCircleDensity, hω]
    simp only [Y0, f', hcv]
  calc
    _ ≤ ∫⁻ pr : Ω × ContinuousPath ℂ, Kc ^ p * (A pr.1 * Y0 (pr.1, Bmap pr.2) ^ p)
        ∂(P.prod (planarBrownianMotion x)) := lintegral_mono_ae hpt
    _ = Kc ^ p * ∫⁻ ω, ∫⁻ b, A ω * Y0 (ω, Bmap b) ^ p ∂planarBrownianMotion x ∂P := by
      rw [lintegral_const_mul' _ _ hKct, lintegral_prod _ hprodm.aemeasurable]
    _ = Kc ^ p * ∫⁻ ω, A ω * Z ω ∂P := by
      congr 1
      apply lintegral_congr
      intro ω
      have hAt : A ω ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
      rw [lintegral_const_mul' _ _ hAt]
      congr 1
      simp only [Z]
      rw [← hlaw]
      exact (lintegral_map (f := fun b' => Y0 (ω, b') ^ p)
        ((hY0.pow_const p).comp measurable_prodMk_left) hBm).symm
    _ ≤ Kc ^ p * ((∫⁻ ω, A ω ^ c ∂P) ^ (1 / c) * (∫⁻ ω, Z ω ^ s' ∂P) ^ (1 / s')) :=
      mul_le_mul' le_rfl (ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj hAm.aemeasurable
        hZm.aemeasurable)
    _ ≤ Kc ^ p * (M ^ (1 / c) * (C₀ * ENNReal.ofReal (h' ^ a₀)) ^ (1 / s')) := by
      refine mul_le_mul' le_rfl (mul_le_mul' (le_of_eq ?_) ?_)
      · congr 1
        rw [hM]
        exact lintegral_congr hAc
      · exact ENNReal.rpow_le_rpow ((lintegral_mono hZs).trans hZint) (by positivity)
    _ ≤ _ := by
      rw [ENNReal.mul_rpow_of_nonneg C₀ (ENNReal.ofReal (h' ^ a₀)) (by positivity : (0 : ℝ) ≤ 1 / s'),
        ENNReal.ofReal_rpow_of_nonneg (x := h' ^ a₀) (by positivity) (by positivity),
        ← Real.rpow_mul hh'0.le]
      have hpow : h' ^ (a₀ * (1 / s')) ≤ h ^ a := by
        rw [show a₀ * (1 / s') = a by rw [ha]; ring]
        exact Real.rpow_le_rpow hh'0.le hh'h (by linarith)
      calc Kc ^ p * (M ^ (1 / c) * (C₀ ^ (1 / s') * ENNReal.ofReal (h' ^ (a₀ * (1 / s'))))) ≤
          Kc ^ p * (M ^ (1 / c) * (C₀ ^ (1 / s') * ENNReal.ofReal (h ^ a))) := by
            gcongr
        _ = _ := by rw [hKc]; ring

end HarmonicBalls
