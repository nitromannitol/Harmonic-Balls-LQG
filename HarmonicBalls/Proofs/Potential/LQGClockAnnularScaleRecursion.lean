import HarmonicBalls.Proofs.Potential.LQGClockAnnularFineFractionalMoment
import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability
import HarmonicBalls.Proofs.Sec8.ExitTimeScaling

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
        ((1 - ((Real.log 2 - Real.log (3 * r / 2)) /
          (Real.log 2 - Real.log r)) ^ (1 / q))⁻¹) ^ q < 1 / 2 := by
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
  set t : ℝ := (Real.log 2 - Real.log (3 * r / 2)) / (Real.log 2 - Real.log r) with htdef
  have hden : 0 < Real.log 2 - Real.log r := by rw [hlogr]; linarith
  have hlog32 : Real.log (3 * r / 2) = Real.log (3 / 2) + Real.log r := by
    rw [show 3 * r / 2 = (3 / 2) * r by ring, Real.log_mul (by norm_num) hr.ne']
  have h1t : 1 - t = Real.log (3 / 2) / (Real.log 2 - Real.log r) := by
    rw [htdef]
    field_simp
    rw [hlog32]
    ring
  have ht0 : 0 ≤ t := by
    rw [htdef]
    apply div_nonneg _ hden.le
    rw [hlog32, hlogr]
    have h3 : Real.log (3 / 2) ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)
    linarith
  have ht1 : 0 < 1 - t := by rw [h1t]; positivity
  have hbern : t ^ (1 / q) ≤ 1 + 1 / q * (t - 1) := by
    have h := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith)
      (p := 1 / q) (by positivity) (by rw [div_le_one hq0]; linarith)
    simpa using h
  have hgap : (1 - t) / q ≤ 1 - t ^ (1 / q) := by
    have : 1 / q * (t - 1) = -((1 - t) / q) := by ring
    linarith
  have hgap0 : 0 < (1 - t) / q := by positivity
  have hinv : (1 - t ^ (1 / q))⁻¹ ≤ 2 * q / Real.log (3 / 2) * L := by
    calc
      (1 - t ^ (1 / q))⁻¹ ≤ ((1 - t) / q)⁻¹ := by
        gcongr
      _ = q * (Real.log 2 - Real.log r) / Real.log (3 / 2) := by
        rw [h1t]
        field_simp
      _ ≤ q * (2 * L) / Real.log (3 / 2) := by
        gcongr
        rw [hlogr]
        linarith
      _ = 2 * q / Real.log (3 / 2) * L := by ring
  have hinv0 : 0 ≤ (1 - t ^ (1 / q))⁻¹ := (inv_pos.mpr (lt_of_lt_of_le hgap0 hgap)).le
  have hret : ((1 - t ^ (1 / q))⁻¹) ^ q ≤ (2 * q / Real.log (3 / 2)) ^ q * L ^ q := by
    rw [← Real.mul_rpow (by positivity) hL.le]
    exact Real.rpow_le_rpow hinv0 hinv hq0.le
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

/-- The field moment of a restricted circle-average occupation over a
path-dependent horizon has a jointly measurable version off one field-null set. -/
theorem exists_measurable_field_path_occupation_rpow
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε) (γ : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) (κ : ContinuousPath ℂ → ℝ → ℂ)
    (hκ : Measurable (Function.uncurry κ)) (T : ContinuousPath ℂ → ℝ) (hT : Measurable T)
    (q : ℝ) :
    ∃ F : Ω × ContinuousPath ℂ → ℝ≥0∞, Measurable F ∧ ∀ᵐ ω ∂P, ∀ b, F (ω, b) =
      (∫⁻ t in Ioc 0 (T b), A.indicator (fun z =>
        ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε z ω)) (κ b t)) ^ q := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let g : (Ω × ContinuousPath ℂ) × ℝ → ℝ≥0∞ := fun p =>
    {p : (Ω × ContinuousPath ℂ) × ℝ | 0 < p.2 ∧ p.2 ≤ T p.1.2}.indicator (fun p =>
      A.indicator (fun z => ENNReal.ofReal (LatticeProb.Gauss.gmcDensity H γ ε z p.1.1))
        (κ p.1.2 p.2)) p
  have hκ' : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ => κ p.1.2 p.2) :=
    hκ.comp (measurable_fst.snd.prodMk measurable_snd)
  have hg : Measurable g := by
    apply Measurable.indicator _ ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hT.comp measurable_fst.snd)))
    apply Measurable.indicator _ (hA.preimage hκ')
    dsimp only [LatticeProb.Gauss.gmcDensity]
    exact (measurable_const.mul (measurable_const.mul
      ((hHm ε hε).comp (hκ'.prodMk measurable_fst.fst))).exp).ennreal_ofReal
  refine ⟨fun p => (∫⁻ t, g (p, t)) ^ q, hg.lintegral_prod_right'.pow_const q, ?_⟩
  filter_upwards [hHae] with ω hω b
  congr 1
  rw [← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro t
  simp only [g, Set.indicator_apply, mem_ofPred_eq, mem_Ioc, LatticeProb.Gauss.gmcDensity, hω]

/-- A field-path moment that agrees with a jointly measurable function off one
field-null set may be integrated in either order. -/
theorem lintegral_lintegral_swap_of_ae_eq {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} {μ : Measure X} [SFinite P] [SFinite μ] (G : Ω → X → ℝ≥0∞)
    (F : Ω × X → ℝ≥0∞) (hF : Measurable F) (hFG : ∀ᵐ ω ∂P, ∀ x, F (ω, x) = G ω x) :
    (∫⁻ x, ∫⁻ ω, G ω x ∂P ∂μ) = ∫⁻ ω, ∫⁻ x, G ω x ∂μ ∂P := by
  calc
    (∫⁻ x, ∫⁻ ω, G ω x ∂P ∂μ) = ∫⁻ x, ∫⁻ ω, F (ω, x) ∂P ∂μ := by
      apply lintegral_congr
      intro x
      apply lintegral_congr_ae
      filter_upwards [hFG] with ω hω
      exact (hω x).symm
    _ = ∫⁻ ω, ∫⁻ x, F (ω, x) ∂μ ∂P :=
      lintegral_lintegral_swap (f := fun x ω => F (ω, x)) (hF.comp measurable_swap).aemeasurable
    _ = ∫⁻ ω, ∫⁻ x, G ω x ∂μ ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hFG] with ω hω
      exact lintegral_congr hω

/-- A field average that agrees with a jointly measurable function off one
field-null set is measurable in the path. -/
theorem measurable_lintegral_of_ae_eq {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} [SFinite P] (G : Ω → X → ℝ≥0∞)
    (F : Ω × X → ℝ≥0∞) (hF : Measurable F) (hFG : ∀ᵐ ω ∂P, ∀ x, F (ω, x) = G ω x) :
    Measurable (fun x => ∫⁻ ω, G ω x ∂P) := by
  have h : (fun x => ∫⁻ ω, G ω x ∂P) = fun x => ∫⁻ ω, F (ω, x) ∂P := by
    funext x
    apply lintegral_congr_ae
    filter_upwards [hFG] with ω hω
    exact (hω x).symm
  rw [h]
  exact hF.lintegral_prod_left'

/-- The affine homeomorphism `w ↦ (w - z) / R` of the plane, for a nonzero real `R`. -/
noncomputable def affineRescaleHomeomorph (z : ℂ) {R : ℝ} (hR : R ≠ 0) : ℂ ≃ₜ ℂ where
  toFun w := (w - z) / (R : ℂ)
  invFun w := (R : ℂ) * w + z
  left_inv w := by
    have h : (R : ℂ) ≠ 0 := by exact_mod_cast hR
    change (R : ℂ) * ((w - z) / (R : ℂ)) + z = w
    rw [mul_div_cancel₀ _ h, sub_add_cancel]
  right_inv w := by
    have h : (R : ℂ) ≠ 0 := by exact_mod_cast hR
    change ((R : ℂ) * w + z - z) / (R : ℂ) = w
    rw [add_sub_cancel_right, mul_div_cancel_left₀ _ h]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem affineRescaleHomeomorph_apply (z : ℂ) {R : ℝ} (hR : R ≠ 0) (w : ℂ) :
    affineRescaleHomeomorph z hR w = (w - z) / (R : ℂ) := rfl

/-- Space-time rescaling about a point carries planar Brownian motion to planar
Brownian motion started at the rescaled point. -/
theorem planarBrownianMotion_map_rescale_affine (x z : ℂ) {R : ℝ} (hR : 0 < R) :
    (planarBrownianMotion x).map
        (ContinuousPath.rescale (affineRescaleHomeomorph z hR.ne') ⟨R ^ 2, by positivity⟩) =
      planarBrownianMotion ((x - z) / (R : ℂ)) := by
  let c : ℝ≥0 := ⟨R ^ 2, by positivity⟩
  have hc0 : c ≠ 0 := by
    intro h
    have h' : R ^ 2 = 0 := congrArg (fun u : ℝ≥0 => (u : ℝ)) h
    have : 0 < R ^ 2 := by positivity
    linarith
  have hsq : Real.sqrt (c : ℝ) = R := Real.sqrt_sq hR.le
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  let Tv := (Homeomorph.refl NNReal).arrowCongr (Homeomorph.addRight ((x - z) / (R : ℂ)))
  have hcomp : ContinuousPath.rescale (affineRescaleHomeomorph z hR.ne') c =
      Tv ∘ scaledCenteredPlanarPath x c := by
    funext b
    ext t
    change (b (c * t) - z) / (R : ℂ) =
      (Real.sqrt (c : ℝ))⁻¹ • (b (c * t) - x) + (x - z) / (R : ℂ)
    rw [hsq, Complex.real_smul, Complex.ofReal_inv]
    field_simp
    ring
  rw [hcomp, ← Measure.map_map Tv.measurable (continuous_scaledCenteredPlanarPath x c).measurable,
    planarBrownianMotion_map_scaledCenteredPlanarPath x hc0, planarBrownianMotion_map_add]

/-- An occupation integral up to a measurable path-dependent horizon is measurable
in the path. -/
theorem measurable_lintegral_Ioc_path (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ)
    (T : ContinuousPath ℂ → ℝ) (hT : Measurable T) :
    Measurable (fun b : ContinuousPath ℂ => ∫⁻ s in Ioc 0 (T b), φ (b s.toNNReal)) := by
  have hev : Measurable (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hg : Measurable (fun p : ContinuousPath ℂ × ℝ =>
      {p : ContinuousPath ℂ × ℝ | 0 < p.2 ∧ p.2 ≤ T p.1}.indicator (fun p => φ (p.1 p.2.toNNReal)) p) :=
    (hφ.comp hev).indicator ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hT.comp measurable_fst)))
  convert hg.lintegral_prod_right' (ν := (volume : Measure ℝ)) using 1
  funext b
  rw [← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro s
  simp only [Set.indicator_apply, mem_ofPred_eq, mem_Ioc]

/-- Rescaling space and time about a point carries the occupation up to an exit
time to the occupation of the rescaled path up to the exit from the image set. -/
theorem lintegral_exit_occupation_rescale (b : ContinuousPath ℂ) (z : ℂ) {R : ℝ} (hR : 0 < R)
    (U : Set ℂ) (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ) :
    let e := affineRescaleHomeomorph z hR.ne'
    let c : ℝ≥0 := ⟨R ^ 2, by positivity⟩
    (∫⁻ t in Ioc 0 (ContinuousPath.exitTime U b).toReal, φ ((b t.toNNReal - z) / (R : ℂ))) =
      ENNReal.ofReal (R ^ 2) * ∫⁻ s in Ioc 0 (ContinuousPath.exitTime (e '' U)
        (ContinuousPath.rescale e c b)).toReal, φ (ContinuousPath.rescale e c b s.toNNReal) := by
  intro e c
  have hc : (0 : ℝ) < R ^ 2 := by positivity
  have hcpos : 0 < c := by
    change (0 : ℝ) < R ^ 2
    exact hc
  have hf : Measurable (fun t : ℝ => φ ((b t.toNNReal - z) / (R : ℂ))) := by
    apply hφ.comp
    fun_prop
  have hexit : ContinuousPath.exitTime U b =
      (c : ℝ≥0∞) * ContinuousPath.exitTime (e '' U) (ContinuousPath.rescale e c b) := by
    rw [exitTime_rescale_mul e c hcpos (e '' U) b, e.injective.preimage_image]
  have hτ : (ContinuousPath.exitTime U b).toReal = R ^ 2 *
      (ContinuousPath.exitTime (e '' U) (ContinuousPath.rescale e c b)).toReal := by
    rw [hexit, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rfl
  rw [lintegral_time_dilation hc _ measurableSet_Ioc _ hf]
  congr 1
  have hpre : (fun s : ℝ => R ^ 2 * s) ⁻¹' Ioc 0 (ContinuousPath.exitTime U b).toReal =
      Ioc 0 (ContinuousPath.exitTime (e '' U) (ContinuousPath.rescale e c b)).toReal := by
    ext s
    simp only [mem_preimage, mem_Ioc, hτ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨pos_of_mul_pos_right h1 hc.le, le_of_mul_le_mul_left h2 hc⟩
    · rintro ⟨h1, h2⟩
      exact ⟨mul_pos hc h1, mul_le_mul_of_nonneg_left h2 hc.le⟩
  rw [hpre]
  apply lintegral_congr
  intro s
  congr 1
  have ht : Real.toNNReal (R ^ 2 * s) = c * Real.toNNReal s := by
    rw [Real.toNNReal_mul hc.le]
    congr 1
    exact Real.toNNReal_of_nonneg hc.le
  rw [ht]
  rfl

/-- Brownian scaling about a point transfers the moment of an occupation up to an
exit time to the rescaled start and the image set. -/
theorem lintegral_planarBrownianMotion_exit_occupation_rescale (x z : ℂ) {R : ℝ} (hR : 0 < R)
    (U : Set ℂ) (hU : IsOpen U) (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ) {q : ℝ} (hq : 0 ≤ q) :
    (∫⁻ b, (∫⁻ t in Ioc 0 (ContinuousPath.exitTime U b).toReal,
      φ ((b t.toNNReal - z) / (R : ℂ))) ^ q ∂planarBrownianMotion x) =
      (ENNReal.ofReal (R ^ 2)) ^ q * ∫⁻ b, (∫⁻ s in Ioc 0 (ContinuousPath.exitTime
        (affineRescaleHomeomorph z hR.ne' '' U) b).toReal, φ (b s.toNNReal)) ^ q
        ∂planarBrownianMotion ((x - z) / (R : ℂ)) := by
  let e := affineRescaleHomeomorph z hR.ne'
  let c : ℝ≥0 := ⟨R ^ 2, by positivity⟩
  have hV : IsOpen (e '' U) := e.isOpenMap U hU
  let G : ContinuousPath ℂ → ℝ≥0∞ := fun b =>
    (∫⁻ s in Ioc 0 (ContinuousPath.exitTime (e '' U) b).toReal, φ (b s.toNNReal)) ^ q
  have hG : Measurable G :=
    (measurable_lintegral_Ioc_path φ hφ _
      (ContinuousPath.measurable_exitTime (e '' U) hV).ennreal_toReal).pow_const q
  have hcpos : 0 < c := by
    change (0 : ℝ) < R ^ 2
    positivity
  have hresc : Measurable (ContinuousPath.rescale e c) :=
    (continuousPathRescaleHomeomorph e c hcpos).continuous.measurable
  calc
    _ = ∫⁻ b, (ENNReal.ofReal (R ^ 2)) ^ q * G (ContinuousPath.rescale e c b)
        ∂planarBrownianMotion x := by
      apply lintegral_congr
      intro b
      rw [lintegral_exit_occupation_rescale b z hR U φ hφ, ENNReal.mul_rpow_of_nonneg _ _ hq]
    _ = (ENNReal.ofReal (R ^ 2)) ^ q * ∫⁻ b, G (ContinuousPath.rescale e c b)
        ∂planarBrownianMotion x := lintegral_const_mul _ (hG.comp hresc)
    _ = _ := by
      rw [← lintegral_map hG hresc, planarBrownianMotion_map_rescale_affine x z hR]

/-- The field-Brownian moment of the half-disc occupation of the normalized
circle-average density before the exit from the unit disc. -/
noncomputable def stoppedHalfDiscMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ δ q : ℝ) (y : ℂ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ b, (∫⁻ t in Ioc 0 (ContinuousPath.exitTime (Metric.ball (0 : ℂ) 1) b).toReal,
    {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator
      (fun z => ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ δ z ω)) (b t.toNNReal)) ^ q
    ∂planarBrownianMotion y ∂P

/-- A triple grid square is bounded. -/
theorem tripleGridSquare_subset_ball (r : ℝ) (i : ℤ × ℤ) :
    tripleGridSquare r i ⊆ Metric.ball (LatticeProb.dyadicSquareCentre r i) (3 * r) := by
  intro w ⟨h1, h2⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have := Complex.norm_le_abs_re_add_abs_im (w - LatticeProb.dyadicSquareCentre r i)
  linarith

theorem isBounded_tripleGridSquare (r : ℝ) (i : ℤ × ℤ) :
    Bornology.IsBounded (tripleGridSquare r i) :=
  Metric.isBounded_ball.subset (tripleGridSquare_subset_ball r i)

/-- The triple grid square is carried into the unit disc by the rescaling of its
square onto the reference square. -/
theorem affineRescale_image_tripleGridSquare_subset_ball {r : ℝ} (hr : 0 < r) (i : ℤ × ℤ) :
    affineRescaleHomeomorph (LatticeProb.dyadicSquareCentre r i)
      (show (4 * r : ℝ) ≠ 0 by positivity) '' tripleGridSquare r i ⊆ Metric.ball (0 : ℂ) 1 := by
  rintro _ ⟨w, ⟨h1, h2⟩, rfl⟩
  rw [affineRescaleHomeomorph_apply, mem_ball_zero_iff]
  have h4 : (0 : ℝ) < 4 * r := by positivity
  have hre : |((w - LatticeProb.dyadicSquareCentre r i) / ((4 * r : ℝ) : ℂ)).re| < 3 / 8 := by
    rw [Complex.div_ofReal_re, abs_div, abs_of_pos h4, div_lt_iff₀ h4]
    linarith
  have him : |((w - LatticeProb.dyadicSquareCentre r i) / ((4 * r : ℝ) : ℂ)).im| < 3 / 8 := by
    rw [Complex.div_ofReal_im, abs_div, abs_of_pos h4, div_lt_iff₀ h4]
    linarith
  have := Complex.norm_le_abs_re_add_abs_im
    ((w - LatticeProb.dyadicSquareCentre r i) / ((4 * r : ℝ) : ℂ))
  linarith

/-- The reference square lies in the closed half disc. -/
theorem lqgSquare_subset_halfDisc :
    LatticeProb.LQG.lqgSquare ⊆ {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} := by
  intro w hw
  have h := LatticeProb.LQG.lqgSquare_subset_closedBall hw
  rw [mem_closedBall_zero_iff] at h
  exact ⟨norm_nonneg _, by linarith⟩

/-- One visit to a grid square, followed until the exit from its triple, has a
field-Brownian moment bounded by the scale factor times the stopped half-disc
moment at the reference smoothing radius and the rescaled start. -/
theorem lintegral_field_brownian_square_visit_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) (γ : ℝ) (y : ℂ) {q : ℝ} (hq : 1 ≤ q)
    (T : ContinuousPath ℂ → ℝ≥0∞)
    (hTU : ∀ b, T b ≤ ContinuousPath.exitTime (tripleGridSquare r i) b) :
    (∫⁻ ω, ∫⁻ b, (∫⁻ s, {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T b}.indicator (fun s =>
      (LatticeProb.dyadicSquare r i ∩ {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}).indicator
        (fun z => ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) z ω))
          (b s.toNNReal)) s) ^ q ∂planarBrownianMotion y ∂P) ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
        ((ENNReal.ofReal ((4 * r) ^ 2)) ^ q *
        stoppedHalfDiscMoment P hcirc γ δ q
          ((y - LatticeProb.dyadicSquareCentre r i) / ((4 * r : ℝ) : ℂ))) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hq0 : 0 ≤ q := by linarith
  have h4r : (0 : ℝ) < 4 * r := by positivity
  set z := LatticeProb.dyadicSquareCentre r i with hz
  set U := tripleGridSquare r i with hUdef
  set A := LatticeProb.dyadicSquare r i ∩ {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} with hAdef
  set D : Set ℂ := Metric.ball (0 : ℂ) 1 with hDdef
  set C := ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) with hCdef
  set e := affineRescaleHomeomorph z (show (4 * r : ℝ) ≠ 0 by positivity) with hedef
  have hUo : IsOpen U := isOpen_tripleGridSquare r i
  have hDo : IsOpen D := Metric.isOpen_ball
  have hA : MeasurableSet A := (LatticeProb.measurableSet_dyadicSquare r i).inter
    ((measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const))
  have hB : MeasurableSet {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hTm : Measurable (fun b : ContinuousPath ℂ => (ContinuousPath.exitTime U b).toReal) :=
    (ContinuousPath.measurable_exitTime U hUo).ennreal_toReal
  have hκ : Measurable (Function.uncurry (fun (b : ContinuousPath ℂ) (t : ℝ) => b t.toNNReal)) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hκ' : Measurable (Function.uncurry (fun (b : ContinuousPath ℂ) (t : ℝ) =>
      (b t.toNNReal - z) / ((4 * r : ℝ) : ℂ))) :=
    (hκ.sub measurable_const).div_const _
  let g : ℝ → Ω → ℂ → ℝ≥0∞ := fun ε ω w =>
    ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε w ω)
  -- first reduction: horizon to the triple exit and interval form
  have hstep1 : (∫⁻ ω, ∫⁻ b, (∫⁻ s, {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s < T b}.indicator
      (fun s => A.indicator (g (4 * r * δ) ω) (b s.toNNReal)) s) ^ q
        ∂planarBrownianMotion y ∂P) ≤
      ∫⁻ ω, ∫⁻ b, (∫⁻ t in Ioc 0 (ContinuousPath.exitTime U b).toReal,
        A.indicator (g (4 * r * δ) ω) (b t.toNNReal)) ^ q ∂planarBrownianMotion y ∂P := by
    apply lintegral_mono
    intro ω
    apply lintegral_mono_ae
    filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top y (isBounded_tripleGridSquare r i)]
      with b hb
    rw [← lintegral_stopped_indicator_eq b _ hb.ne]
    apply ENNReal.rpow_le_rpow _ hq0
    apply lintegral_mono
    intro s
    apply Set.indicator_le_indicator_of_subset _ (fun _ => zero_le)
    intro s ⟨h0, h1⟩
    exact ⟨h0, h1.trans_le (hTU b)⟩
  obtain ⟨F₁, hF₁, hF₁e⟩ := exists_measurable_field_path_occupation_rpow hh
    (show 0 < 4 * r * δ by positivity) γ A hA _ hκ _ hTm q
  obtain ⟨F₂, hF₂, hF₂e⟩ := exists_measurable_field_path_occupation_rpow hh hδ γ
    LatticeProb.LQG.lqgSquare LatticeProb.LQG.measurableSet_lqgSquare _ hκ' _ hTm q
  -- pathwise comparison with the reference smoothing radius
  have hpath (b : ContinuousPath ℂ) :
      (∫⁻ ω, (∫⁻ t in Ioc 0 (ContinuousPath.exitTime U b).toReal,
        A.indicator (g (4 * r * δ) ω) (b t.toNNReal)) ^ q ∂P) ≤
      C * ∫⁻ ω, (∫⁻ t in Ioc 0 (ContinuousPath.exitTime U b).toReal,
        LatticeProb.LQG.lqgSquare.indicator (g δ ω)
          ((b t.toNNReal - z) / ((4 * r : ℝ) : ℂ))) ^ q ∂P := by
    have hb : Measurable (fun t : ℝ => b t.toNNReal) := by fun_prop
    have hb' : Measurable (fun t : ℝ => (b t.toNNReal - z) / ((4 * r : ℝ) : ℂ)) := by fun_prop
    have hcomp := lintegral_rpow_annularSquare_gmcDensity_le_reference hh hr hr10 hδ hδ2 hi γ b
      0 (ContinuousPath.exitTime U b).toReal 0 hq
    simp only at hcomp
    calc
      _ = ∫⁻ ω, (∫⁻ t in annularSquareTimeSet b 0 r i ∩ Ioc 0
          (ContinuousPath.exitTime U b).toReal,
          ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω)) ^ q
            ∂P := by
        apply lintegral_congr
        intro ω
        rw [lintegral_Ioc_indicator_comp_eq _ hb A hA]
        rfl
      _ ≤ _ := hcomp
      _ ≤ _ := by
        refine mul_le_mul_right ?_ C
        apply lintegral_mono
        intro ω
        apply ENNReal.rpow_le_rpow _ hq0
        rw [lintegral_Ioc_indicator_comp_eq _ hb' _ LatticeProb.LQG.measurableSet_lqgSquare]
        calc
          _ ≤ ∫⁻ t in {t | (b t.toNNReal - z) / ((4 * r : ℝ) : ℂ) ∈ LatticeProb.LQG.lqgSquare} ∩
              Ioc 0 (ContinuousPath.exitTime U b).toReal,
              ENNReal.ofReal (Real.exp (γ * hcirc ω δ ((b t.toNNReal - z) / ((4 * r : ℝ) : ℂ)) -
                γ ^ 2 * (-Real.log δ) / 2)) := by
            apply lintegral_mono_set
            intro t ⟨ht, ht'⟩
            exact ⟨dyadicSquare_rescaled_mem_lqgSquare hr ht.1, ht'⟩
          _ = _ := by
            apply lintegral_congr
            intro t
            simp only [g]
            rw [gmcDensity_eq_exp_normalized hcirc hδ]
  have hsub : e '' U ⊆ D := affineRescale_image_tripleGridSquare_subset_ball hr i
  set y' := (y - z) / ((4 * r : ℝ) : ℂ) with hy'
  calc
    _ ≤ _ := hstep1
    _ = ∫⁻ b, ∫⁻ ω, (∫⁻ t in Ioc 0 (ContinuousPath.exitTime U b).toReal,
        A.indicator (g (4 * r * δ) ω) (b t.toNNReal)) ^ q ∂P ∂planarBrownianMotion y :=
      (lintegral_lintegral_swap_of_ae_eq (fun ω b => (∫⁻ t in Ioc 0
        (ContinuousPath.exitTime U b).toReal, A.indicator (g (4 * r * δ) ω) (b t.toNNReal)) ^ q)
        F₁ hF₁ hF₁e).symm
    _ ≤ ∫⁻ b, C * ∫⁻ ω, (∫⁻ t in Ioc 0 (ContinuousPath.exitTime U b).toReal,
        LatticeProb.LQG.lqgSquare.indicator (g δ ω)
          ((b t.toNNReal - z) / ((4 * r : ℝ) : ℂ))) ^ q ∂P ∂planarBrownianMotion y :=
      lintegral_mono hpath
    _ = C * ∫⁻ b, ∫⁻ ω, (∫⁻ t in Ioc 0 (ContinuousPath.exitTime U b).toReal,
        LatticeProb.LQG.lqgSquare.indicator (g δ ω)
          ((b t.toNNReal - z) / ((4 * r : ℝ) : ℂ))) ^ q ∂P ∂planarBrownianMotion y :=
      lintegral_const_mul' C _ ENNReal.ofReal_ne_top
    _ = C * ∫⁻ ω, ∫⁻ b, (∫⁻ t in Ioc 0 (ContinuousPath.exitTime U b).toReal,
        LatticeProb.LQG.lqgSquare.indicator (g δ ω)
          ((b t.toNNReal - z) / ((4 * r : ℝ) : ℂ))) ^ q ∂planarBrownianMotion y ∂P := by
      rw [lintegral_lintegral_swap_of_ae_eq (fun ω b => (∫⁻ t in Ioc 0
        (ContinuousPath.exitTime U b).toReal, LatticeProb.LQG.lqgSquare.indicator (g δ ω)
          ((b t.toNNReal - z) / ((4 * r : ℝ) : ℂ))) ^ q) F₂ hF₂ hF₂e]
    _ ≤ C * ∫⁻ ω, (ENNReal.ofReal ((4 * r) ^ 2)) ^ q * ∫⁻ b,
        (∫⁻ s in Ioc 0 (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (g δ ω) (b s.toNNReal)) ^ q
          ∂planarBrownianMotion y' ∂P := by
      refine mul_le_mul_right ?_ C
      apply lintegral_mono_ae
      filter_upwards [hh.ae_continuous_circle_fixed hδ] with ω hω
      have hgm : Measurable (LatticeProb.LQG.lqgSquare.indicator (g δ ω)) := by
        apply Measurable.indicator _ LatticeProb.LQG.measurableSet_lqgSquare
        show Measurable (fun w => ENNReal.ofReal (δ ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω δ w)))
        exact (continuous_const.mul (Real.continuous_exp.comp
          (continuous_const.mul hω))).measurable.ennreal_ofReal
      rw [lintegral_planarBrownianMotion_exit_occupation_rescale y z h4r U hUo _ hgm hq0]
      refine mul_le_mul_right ?_ _
      apply lintegral_mono_ae
      filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top y'
        (Metric.isBounded_ball : Bornology.IsBounded D)] with b hb
      apply ENNReal.rpow_le_rpow _ hq0
      calc
        _ ≤ ∫⁻ s in Ioc 0 (ContinuousPath.exitTime D b).toReal,
            LatticeProb.LQG.lqgSquare.indicator (g δ ω) (b s.toNNReal) :=
          lintegral_mono_set (Ioc_subset_Ioc le_rfl
            (ENNReal.toReal_mono hb.ne (ContinuousPath.exitTime_mono hsub b)))
        _ ≤ _ := lintegral_mono (fun s =>
          Set.indicator_le_indicator_of_subset lqgSquare_subset_halfDisc (fun _ => zero_le) _)
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0 ENNReal.ofReal_ne_top)]
      rfl

end HarmonicBalls
