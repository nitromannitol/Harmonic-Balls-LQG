import HarmonicBalls.Proofs.Potential.LQGClockSquareVisitComparison
import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability

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
      {b : ContinuousPath ℂ | σ ≤ T}.indicator
        (fun b => pathOccupationBefore g T (ContinuousPath.shift σ.toNNReal b)) b := by
  have huniv (b' : ContinuousPath ℂ) : ContinuousPath.exitTime (univ : Set ℂ) b' = ⊤ := by
    rw [exitTime_eq_iInf]
    simp
  by_cases hσT : σ ≤ T
  · rw [Set.indicator_of_mem (show b ∈ {b : ContinuousPath ℂ | σ ≤ T} from hσT)]
    by_cases hσ : σ = ⊤
    · rw [min_eq_right (hσ ▸ le_top : T ≤ σ)]
      exact le_self_add
    · have h := pathOccupationBefore_le_add_shift hg univ T σ.toNNReal b
      rw [huniv, huniv, min_eq_right le_top, ENNReal.coe_toNNReal hσ] at h
      exact h
  · rw [Set.indicator_of_notMem (show b ∉ {b : ContinuousPath ℂ | σ ≤ T} from hσT), add_zero,
      min_eq_right (le_of_lt (not_le.mp hσT))]

end HarmonicBalls
