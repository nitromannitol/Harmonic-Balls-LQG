import HarmonicBalls.FirstPass.Phase2.SquarePositiveHolds
import HarmonicBalls.Defs.LBM
import HarmonicBalls.FirstPass.Cited.Section2HeatKernel

/-!
# Volume bounds on clipped balls of a square, the input (13.1) of Kigami's Theorem 13.1

The proof of Proposition 2.6 (prop:lbm-continuity, corrected paper lines 563-567) applies
Kigami 2019, Theorem 13.1, "with input given by Lemma 2.4". The input is the two-sided bound (13.1)
`c₁ r^{α₁} ≤ ν(B(x, r) ∩ K) ≤ c₂ r^{α₂}` for every `x` in the square `K` and every scale `r` up
to the side length, with positive exponents `α₂ ≤ α₁`, for the LQG measure restricted to `K`.

`ae_forall_closedSquare_volume_bounds` proves it almost surely, simultaneously for every closed
square, for every `0 < γ < 2` and every insertion `α₀ < Q`, together with `0 < μ_h(K) < ∞`. The
argument is the one of the consultant note on target 12: for `x ∈ K` and `r ≤ L` the clipped ball
`B(x, r) ∩ K` contains a disk of radius `r/8` (`exists_ball_subset_ball_inter_closedSquare`),
which gives the lower bound from the almost sure all-scales bound
`r^{β⁻} ≤ μ_h(B_r(z)) ≤ r^{β⁺}` (`lqgVolumeGrowthAllScalesStmt_holds`); the upper bound is the
bound on `B(x, r)`; scales between the threshold of that bound and `L` are absorbed into the
constants. The exponents are positive also when the insertion lies in `K`, by the corrected
exponent ranges of Lemma 2.4 ([C1]).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set MarkovProcess

/-- In an interval of length `L ≥ ρ`, every point is within `ρ/4` of a point whose
`ρ/8`-neighbourhood lies in the interval. -/
theorem exists_near_Icc_of_le {c u L ρ : ℝ} (hu : u ∈ Icc c (c + L)) (hρ : 0 < ρ) (hρL : ρ ≤ L) :
    ∃ v : ℝ, |v - u| ≤ ρ / 4 ∧ ∀ w : ℝ, |w - v| < ρ / 8 → w ∈ Icc c (c + L) := by
  by_cases h : u ≤ c + L / 2
  · refine ⟨u + ρ / 4, by rw [add_sub_cancel_left, abs_of_pos (by positivity)], fun w hw => ?_⟩
    rw [abs_lt] at hw
    exact ⟨by linarith [hu.1], by linarith⟩
  · refine ⟨u - ρ / 4, by rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by positivity)],
      fun w hw => ?_⟩
    rw [abs_lt] at hw
    push Not at h
    exact ⟨by linarith, by linarith [hu.2]⟩

/-- **A clipped ball of a square contains a disk of comparable radius**: for `x` in the closed
square `K` of side `L` and `0 < ρ ≤ L`, some disk of radius `ρ/8` lies in `B(x, ρ) ∩ K`. -/
theorem exists_ball_subset_ball_inter_closedSquare {a x : ℂ} {L ρ : ℝ} (hx : x ∈ closedSquare a L)
    (hρ : 0 < ρ) (hρL : ρ ≤ L) : ∃ y : ℂ, ball y (ρ / 8) ⊆ ball x ρ ∩ closedSquare a L := by
  rw [closedSquare, Complex.mem_reProdIm] at hx
  obtain ⟨v₁, hv₁, h₁⟩ := exists_near_Icc_of_le hx.1 hρ hρL
  obtain ⟨v₂, hv₂, h₂⟩ := exists_near_Icc_of_le hx.2 hρ hρL
  refine ⟨⟨v₁, v₂⟩, fun w hw => ?_⟩
  rw [mem_ball, Complex.dist_eq] at hw
  have hre : |w.re - v₁| < ρ / 8 :=
    lt_of_le_of_lt (by simpa using Complex.abs_re_le_norm (w - ⟨v₁, v₂⟩)) hw
  have him : |w.im - v₂| < ρ / 8 :=
    lt_of_le_of_lt (by simpa using Complex.abs_im_le_norm (w - ⟨v₁, v₂⟩)) hw
  refine ⟨?_, ?_⟩
  · rw [mem_ball, Complex.dist_eq]
    have hyx : ‖(⟨v₁, v₂⟩ : ℂ) - x‖ ≤ ρ / 2 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.sub_re, Complex.sub_im]
      linarith
    calc ‖w - x‖ = ‖(w - ⟨v₁, v₂⟩) + ((⟨v₁, v₂⟩ : ℂ) - x)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖w - ⟨v₁, v₂⟩‖ + ‖(⟨v₁, v₂⟩ : ℂ) - x‖ := norm_add_le _ _
      _ < ρ := by linarith
  · rw [closedSquare, Complex.mem_reProdIm]
    exact ⟨h₁ _ hre, h₂ _ him⟩

/-- A closed square is compact. -/
theorem isCompact_closedSquare (a : ℂ) (L : ℝ) : IsCompact (closedSquare a L) :=
  isCompact_Icc.reProdIm isCompact_Icc

/-- A closed square of side `L` lies in the ball `B(0, ‖a‖ + 2L + 1)`. -/
theorem closedSquare_subset_ball (a : ℂ) (L : ℝ) :
    closedSquare a L ⊆ ball (0 : ℂ) (‖a‖ + 2 * L + 1) := by
  intro z hz
  rw [closedSquare, Complex.mem_reProdIm, mem_Icc, mem_Icc] at hz
  rw [mem_ball, dist_zero_right]
  have h1 : ‖z - a‖ ≤ 2 * L := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  calc ‖z‖ = ‖a + (z - a)‖ := by rw [add_sub_cancel]
    _ ≤ ‖a‖ + ‖z - a‖ := norm_add_le _ _
    _ < ‖a‖ + 2 * L + 1 := by linarith

/-- **The input (13.1) of Kigami's Theorem 13.1 for every square.** For `0 < γ < 2` and `α₀ < Q`,
almost surely, for every closed square `K` of side `L > 0`: `0 < μ_h(K) < ∞`, and there are
positive constants `c₁, c₂` and exponents `0 < α₂ ≤ α₁` with
`c₁ r^{α₁} ≤ μ_h(B(x, r) ∩ K) ≤ c₂ r^{α₂}` for all `x ∈ K` and `0 < r ≤ L`. -/
theorem ae_forall_closedSquare_volume_bounds {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) (hh : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (a : ℂ) (L : ℝ), 0 < L →
      0 < μ ω (closedSquare a L) ∧ μ ω (closedSquare a L) < ⊤ ∧
      ∃ c₁ c₂ α₁ α₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < α₁ ∧ 0 < α₂ ∧ α₂ ≤ α₁ ∧
        ∀ x ∈ closedSquare a L, ∀ r : ℝ, 0 < r → r ≤ L →
          ENNReal.ofReal (c₁ * r ^ α₁) ≤ μ ω (ball x r ∩ closedSquare a L) ∧
            μ ω (ball x r ∩ closedSquare a L) ≤ ENNReal.ofReal (c₂ * r ^ α₂) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  filter_upwards [lqgVolumeGrowthAllScalesStmt_holds γ α₀ hγ hγ2 hα _ P hC hcirc μ hh hμ, hμ']
    with ω hvol hlim
  have := hlim.isLocallyFiniteMeasure
  intro a L hL
  have hQ : 0 < γ * (lqgQ γ - α₀) := mul_pos hγ (by linarith)
  have hm : 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) :=
    lt_min (by have : 0 < 2 - γ := by linarith
               positivity) hQ
  set βp := min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) / 2 with hβp
  set βm := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1 with hβm
  have hβp0 : 0 < βp := by positivity
  have hβpm : βp < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := by linarith
  have hβmM : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βm := by linarith
  have hβle : βp ≤ βm := by
    have h1 := min_le_right ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
    have h2 := le_max_right ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
    linarith
  have hβm0 : 0 < βm := hβp0.trans_le hβle
  obtain ⟨r₀, hr₀, hb⟩ := hvol (‖a‖ + 2 * L + 1) (by positivity) βp βm hβp0 hβpm hβmM
  set K := closedSquare a L with hK
  have hKR := closedSquare_subset_ball a L
  have hlow : ∀ x ∈ K, ∀ ρ : ℝ, 0 < ρ → ρ ≤ L → ρ < r₀ →
      ENNReal.ofReal ((ρ / 8) ^ βm) ≤ μ ω (ball x ρ ∩ K) := by
    intro x hx ρ hρ hρL hρr₀
    obtain ⟨y, hy⟩ := exists_ball_subset_ball_inter_closedSquare hx hρ hρL
    have hyK : y ∈ K := (hy (mem_ball_self (by positivity))).2
    exact (hb (ρ / 8) (by positivity) (by linarith) y (hKR hyK)).1.trans (measure_mono hy)
  have haK : a ∈ K := by
    rw [hK, closedSquare, Complex.mem_reProdIm]
    exact ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, by linarith⟩⟩
  set r₁ := min r₀ L with hr₁
  have hr₁0 : 0 < r₁ := lt_min hr₀ hL
  have hr₁L : r₁ ≤ L := min_le_right _ _
  have hr₁r₀ : r₁ ≤ r₀ := min_le_left _ _
  have hKfin : μ ω K < ⊤ := (isCompact_closedSquare a L).measure_lt_top
  have hKpos : 0 < μ ω K := by
    have h := hlow a haK (r₁ / 2) (by positivity) (by linarith) (by linarith)
    refine lt_of_lt_of_le ?_ (h.trans (measure_mono inter_subset_right))
    exact ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨hKpos, hKfin, (r₁ / (16 * L)) ^ βm, max 1 ((μ ω K).toReal / r₁ ^ βp), βm, βp,
    Real.rpow_pos_of_pos (by positivity) _, lt_of_lt_of_le one_pos (le_max_left _ _), hβm0, hβp0,
    hβle, fun x hx r hr hrL => ⟨?_, ?_⟩⟩
  · set ρ := min r (r₁ / 2) with hρ
    have hρ0 : 0 < ρ := lt_min hr (by positivity)
    have hρr : ρ ≤ r := min_le_left _ _
    have hρL : ρ ≤ L := hρr.trans hrL
    have hρr₀ : ρ < r₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hge : r₁ * r / (16 * L) ≤ ρ / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      rcases min_choice r (r₁ / 2) with h | h
      · rw [hρ, h]
        nlinarith
      · rw [hρ, h]
        nlinarith
    calc ENNReal.ofReal ((r₁ / (16 * L)) ^ βm * r ^ βm)
        = ENNReal.ofReal ((r₁ * r / (16 * L)) ^ βm) := by
          rw [← Real.mul_rpow (by positivity) hr.le]
          congr 2
          ring
      _ ≤ ENNReal.ofReal ((ρ / 8) ^ βm) :=
          ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by positivity) hge hβm0.le)
      _ ≤ μ ω (ball x ρ ∩ K) := hlow x hx ρ hρ0 hρL hρr₀
      _ ≤ μ ω (ball x r ∩ K) := measure_mono (inter_subset_inter_left _ (ball_subset_ball hρr))
  · rcases lt_or_ge r r₁ with hrr | hrr
    · calc μ ω (ball x r ∩ K) ≤ μ ω (ball x r) := measure_mono inter_subset_left
        _ ≤ ENNReal.ofReal (r ^ βp) := (hb r hr (by linarith) x (hKR hx)).2
        _ ≤ ENNReal.ofReal (max 1 ((μ ω K).toReal / r₁ ^ βp) * r ^ βp) :=
          ENNReal.ofReal_le_ofReal
            (le_mul_of_one_le_left (Real.rpow_nonneg hr.le _) (le_max_left _ _))
    · have hr₁β : 0 < r₁ ^ βp := Real.rpow_pos_of_pos hr₁0 _
      have hratio : 1 ≤ r ^ βp / r₁ ^ βp := by
        rw [one_le_div hr₁β]
        exact Real.rpow_le_rpow hr₁0.le hrr hβp0.le
      calc μ ω (ball x r ∩ K) ≤ μ ω K := measure_mono inter_subset_right
        _ = ENNReal.ofReal (μ ω K).toReal := (ENNReal.ofReal_toReal hKfin.ne).symm
        _ ≤ ENNReal.ofReal ((μ ω K).toReal / r₁ ^ βp * r ^ βp) := by
          refine ENNReal.ofReal_le_ofReal ?_
          calc (μ ω K).toReal = (μ ω K).toReal * 1 := (mul_one _).symm
            _ ≤ (μ ω K).toReal * (r ^ βp / r₁ ^ βp) :=
              mul_le_mul_of_nonneg_left hratio ENNReal.toReal_nonneg
            _ = (μ ω K).toReal / r₁ ^ βp * r ^ βp := by ring
        _ ≤ ENNReal.ofReal (max 1 ((μ ω K).toReal / r₁ ^ βp) * r ^ βp) :=
          ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _))

/-- The LQG measure `m` of the square `closedSquare a L`, carried to the unit square by
`z ↦ (z - a)/L` and normalized by its total mass: the measure to which Kigami's Theorem 13.1 is
applied in the proof of Proposition 2.6 (`kigamiHeatKernelContinuityCited`). -/
noncomputable def unitSquareNormalizedMeasure (m : Measure ℂ) (a : ℂ) (L : ℝ) : Measure ℂ :=
  (m (closedSquare a L))⁻¹ • (m.restrict (closedSquare a L)).map (fun z : ℂ => (z - a) / (L : ℂ))

theorem measurable_unitSquareChart (a : ℂ) (L : ℝ) : Measurable (fun z : ℂ => (z - a) / (L : ℂ)) :=
  ((continuous_id.sub continuous_const).div_const _).measurable

theorem unitSquareChart_preimage_ball {a x : ℂ} {L r : ℝ} (hL : 0 < L) :
    (fun z : ℂ => (z - a) / (L : ℂ)) ⁻¹' ball x r = ball (a + (L : ℂ) * x) (L * r) := by
  ext z
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  have heq : (z - a) / (L : ℂ) - x = (z - (a + (L : ℂ) * x)) / (L : ℂ) := by
    field_simp
    ring
  simp only [mem_preimage, mem_ball, Complex.dist_eq]
  rw [heq, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL, div_lt_iff₀ hL, mul_comm r L]

theorem unitSquareChart_preimage_closedSquare {a : ℂ} {L : ℝ} (hL : 0 < L) :
    (fun z : ℂ => (z - a) / (L : ℂ)) ⁻¹' closedSquare 0 1 = closedSquare a L := by
  ext z
  simp only [mem_preimage, closedSquare, Complex.mem_reProdIm, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im,
    zero_add, mem_Icc, le_div_iff₀ hL, div_le_iff₀ hL, zero_mul, one_mul]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3, h4⟩ <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem unitSquareNormalizedMeasure_apply {m : Measure ℂ} {a : ℂ} {L : ℝ} {S : Set ℂ}
    (hS : MeasurableSet S) :
    unitSquareNormalizedMeasure m a L S =
      (m (closedSquare a L))⁻¹ * m ((fun z : ℂ => (z - a) / (L : ℂ)) ⁻¹' S ∩ closedSquare a L) := by
  rw [unitSquareNormalizedMeasure, Measure.smul_apply, Measure.map_apply
    (measurable_unitSquareChart a L) hS, Measure.restrict_apply
    (measurable_unitSquareChart a L hS), smul_eq_mul]

/-- **The hypotheses of Kigami's Theorem 13.1 for the LQG measure of every square**
(`kigamiHeatKernelContinuityCited`): for `0 < γ < 2` and `α₀ < Q`, almost surely, for every
closed square of side `L > 0`, the normalized LQG measure carried to the unit square is a
probability measure carried by the unit square with
`c₁ r^{α₁} ≤ ν(B(x, r)) ≤ c₂ r^{α₂}` for all `x` in the unit square and `0 < r ≤ 1`, with positive
constants and `0 < α₂ ≤ α₁`. -/
theorem ae_forall_closedSquare_kigamiVolumeBounds {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) (hh : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (a : ℂ) (L : ℝ), 0 < L →
      IsProbabilityMeasure (unitSquareNormalizedMeasure (μ ω) a L) ∧
      unitSquareNormalizedMeasure (μ ω) a L (closedSquare 0 1)ᶜ = 0 ∧
      ∃ c₁ c₂ α₁ α₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < α₁ ∧ 0 < α₂ ∧ α₂ ≤ α₁ ∧
        ∀ x ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → r ≤ 1 →
          ENNReal.ofReal (c₁ * r ^ α₁) ≤ unitSquareNormalizedMeasure (μ ω) a L (ball x r) ∧
            unitSquareNormalizedMeasure (μ ω) a L (ball x r) ≤ ENNReal.ofReal (c₂ * r ^ α₂) := by
  filter_upwards [ae_forall_closedSquare_volume_bounds hγ hγ2 hα hh hμ] with ω hω
  intro a L hL
  obtain ⟨hpos, hfin, c₁, c₂, α₁, α₂, hc₁, hc₂, hα₁, hα₂, hα₂₁, hb⟩ := hω a L hL
  set K := closedSquare a L with hK
  set M := (μ ω K).toReal with hM
  have hM0 : 0 < M := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hMK : μ ω K = ENNReal.ofReal M := (ENNReal.ofReal_toReal hfin.ne).symm
  have hinv : (μ ω K)⁻¹ = ENNReal.ofReal M⁻¹ := by
    rw [hMK, ENNReal.ofReal_inv_of_pos hM0]
  refine ⟨⟨?_⟩, ?_, c₁ * L ^ α₁ / M, c₂ * L ^ α₂ / M, α₁, α₂, by positivity, by positivity, hα₁,
    hα₂, hα₂₁, fun x hx r hr hr1 => ?_⟩
  · rw [unitSquareNormalizedMeasure_apply MeasurableSet.univ, preimage_univ, univ_inter,
      ENNReal.inv_mul_cancel hpos.ne' hfin.ne]
  · rw [unitSquareNormalizedMeasure_apply (isCompact_closedSquare 0 1).isClosed.measurableSet.compl,
      preimage_compl, unitSquareChart_preimage_closedSquare hL, compl_inter_self, measure_empty,
      mul_zero]
  · have hxK : a + (L : ℂ) * x ∈ K := by
      rw [closedSquare, Complex.mem_reProdIm] at hx
      rw [hK, closedSquare, Complex.mem_reProdIm]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im, zero_add, zero_mul,
        sub_zero, add_zero, mem_Icc] at hx ⊢
      have e1 : 0 ≤ L * x.re := mul_nonneg hL.le hx.1.1
      have e2 : L * x.re ≤ L := mul_le_of_le_one_right hL.le hx.1.2
      have e3 : 0 ≤ L * x.im := mul_nonneg hL.le hx.2.1
      have e4 : L * x.im ≤ L := mul_le_of_le_one_right hL.le hx.2.2
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
    have hLr : 0 < L * r := mul_pos hL hr
    obtain ⟨hlo, hup⟩ := hb _ hxK (L * r) hLr (by nlinarith)
    rw [unitSquareNormalizedMeasure_apply measurableSet_ball, unitSquareChart_preimage_ball hL, hinv]
    have hlo' : c₁ * (L * r) ^ α₁ = M * (c₁ * L ^ α₁ / M * r ^ α₁) := by
      rw [Real.mul_rpow hL.le hr.le]
      field_simp
    have hup' : c₂ * (L * r) ^ α₂ = M * (c₂ * L ^ α₂ / M * r ^ α₂) := by
      rw [Real.mul_rpow hL.le hr.le]
      field_simp
    have hMinv : ∀ y : ℝ, 0 ≤ y → ENNReal.ofReal M⁻¹ * ENNReal.ofReal (M * y) = ENNReal.ofReal y := by
      intro y hy
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hM0.le), ← mul_assoc, inv_mul_cancel₀ hM0.ne', one_mul]
    rw [hlo'] at hlo
    rw [hup'] at hup
    constructor
    · rw [← hMinv (c₁ * L ^ α₁ / M * r ^ α₁) (by positivity)]
      exact mul_le_mul_right hlo _
    · rw [← hMinv (c₂ * L ^ α₂ / M * r ^ α₂) (by positivity)]
      exact mul_le_mul_right hup _

/-- **Kigami's Theorem 13.1 applies to the LQG measure of every square**: from the cited
statement `kigamiHeatKernelContinuityCited`, almost surely, for every closed square of side
`L > 0`, every PCAF of reflected Brownian motion in the unit square whose Revuz measure is the
normalized LQG measure of the square carried to the unit square has a jointly continuous heat
kernel with respect to that measure. What Proposition 2.6 still needs beyond this: the
identification of the LQG clock of reflected Brownian motion with such a PCAF, the strict
positivity of the kernel, and the scaling from the unit square to the square. -/
theorem ae_forall_closedSquare_heatKernel_of_kigami (hKig : kigamiHeatKernelContinuityCited)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (a : ℂ) (L : ℝ), 0 < L →
      ∀ A : NNReal → ContinuousPath ℂ → NNReal, IsUnitSquarePCAF A →
        unitSquareRevuzMeasure A = unitSquareNormalizedMeasure (μ ω) a L →
        ∃ p : ℝ → ℂ → ℂ → ℝ,
          IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
            (closedSquare 0 1) (unitSquareNormalizedMeasure (μ ω) a L) p ∧
          ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
            (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1) := by
  filter_upwards [ae_forall_closedSquare_kigamiVolumeBounds hγ hγ2 hα hh hμ] with ω hω
  intro a L hL A hA hRevuz
  obtain ⟨hprob, hcarried, c₁, c₂, α₁, α₂, hc₁, hc₂, hα₁, hα₂, hα₂₁, hb⟩ := hω a L hL
  exact hKig _ hprob hcarried c₁ c₂ α₁ α₂ hc₁ hc₂ hα₁ hα₂ hα₂₁ hb A hA hRevuz

end HarmonicBalls

