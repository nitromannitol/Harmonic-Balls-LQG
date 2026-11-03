import HarmonicBalls.Draft.Section2
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# Lemma 2.4, I1 and I2: LQG mass of Euclidean balls

Phase B for Lemma 2.4 (`LiouvilleVolumeGrowthStmt`, lemma:volume-growth, line 497 of
paper/lqg_harmonic_ball-corrected.tex, with correction [C1]) and for the unnumbered consequences I2
(`LQGVolumeGrowthAllScalesStmt`, eq:volume-growth, line 3527) and I1 (`LQGMeasureFullSupportStmt`, lines 134-135),
all in HarmonicBalls/Draft/Section2.lean.

## Steps

* `LiouvilleBallMassBoundStep`: the ball clause eq:ball-volume of Lemma 2.4, with the exponent ranges of [C1], for
  centres in every ball `B_R(0)` (Lemma 2.4 prints `B_1`). With polynomially high probability as `ε → 0`,
  `ε^{β⁻} ≤ μ_h(B_ε(z)) ≤ ε^{β⁺}` for all `z ∈ B_R`.
* `liouvilleVolumeGrowthStmt_of_ballMass` (proved): Lemma 2.4. The ball clause is the step at `R = 1`. The annulus
  clause eq:ann-volume: `𝔸_{r₁ε,r₂ε}(z) ⊆ B_{r₂ε}(z)` gives the upper bound with `C₁ = r₂^{β⁺}`, and
  `𝔸_{r₁ε,r₂ε}(z) ⊇ B_{ρε}(w)` with `ρ = (r₂-r₁)/2` and `w = z + (r₁+r₂)ε/2 ∈ B_2` gives the lower bound with
  `C₂ = ρ^{β⁻}` (step at `R = 2`).
* `lqgVolumeGrowthAllScalesStmt_of_ballMass` (proved): I2. For rational exponents `a < β⁺'`, `b > β⁻'` the step
  at `(β⁺', β⁻')` gives, for small `ε`, the bounds with exponents `(a, b)` at every radius `s ∈ [ε/2, ε]`
  (monotonicity of `s ↦ μ_h(B_s(z))` and the slack). Borel-Cantelli along `ε = 2^{-k}`
  (`PolyHighProb.ae_eventually_dyadic`) gives a.s. all radii `s < 2^{-K}`. The index set `ℕ × ℚ × ℚ`
  (radius `R = n + 1` and rational exponents) is countable, which gives one event for all `R`, `β⁺`, `β⁻`.
* `lqgMeasureFullSupportStmt_of_volumeGrowth` (proved): I1 from the lower bound of I2. Every nonempty open `U`
  contains a ball `B_r(x)` with `r` small.

The step `LiouvilleBallMassBoundStep` is the content of Lemma 2.4 and is derived from Ding-Gwynne 2020, Lemma 3.8
(`WholePlaneLQGBallMassBounds`, HarmonicBalls/Proposed/LQG.lean) by the carving below.

## The field near the origin

`WholePlaneLQGBallMassBounds` is a bound uniform over `z` in the unit square for the field `h^ℂ` (`α₀ = 0`). It
yields exponents `(2∓γ)²/2`, the thickest and the thinnest points. Away from `0`, `μ_h = |x|^{-γα₀} μ_{h^ℂ}`
(Weyl scaling, `SingularWeightStep`). Near `0`, this comparison with the uniform bound alone gives, at `z = 0`,
the upper exponent `(2-γ)²/2 - γ max(α₀, 0)` and the lower exponent `(2+γ)²/2 + γ max(-α₀, 0)`. These match
[C1] for the upper bound when `α₀ ≤ 0` and for the lower bound when `α₀ ≥ 0`. In the two other cases [C1]
requires the exponent `γQ` of the typical point `0` of `h^ℂ` at every scale `2^{-k}`, i.e.
`μ_{h^ℂ}(B_{2^{-k}}(0)) = 2^{-kγQ} e^{γ h^ℂ_{2^{-k}}(0)} μ_{h^{(k)}}(B_1(0))` with
`h^{(k)} = h^ℂ(2^{-k} ·) - h^ℂ_{2^{-k}}(0)` (`WholePlaneGFFAffineInvariance`, `LQGMeasureCoordChange`). This needs
Lemma 3.8 for the rescaled fields `h^{(k)}`, `k ∈ ℕ`, with failure probabilities uniform in `k` up to a polynomial
factor. `WholePlaneLQGBallMassBounds` quantifies over fields and then over constants, so it does not give this
uniformity directly. It does give it through a mixture: the field `(k, ω) ↦ h^{(k)}(ω)` under
`∑ₖ wₖ δₖ ⊗ P`, with `wₖ ∝ (k+1)⁻²`, is again a whole-plane GFF, since every `h^{(k)}` has the law of `h^ℂ`.
This is `WholePlaneScaledBallMassStep` (BG20, Lemma A.1, scale invariance on the annuli around `0`). Besides the
inputs named in the task, the route uses `LQGMeasureExistence` at `α₀ = 0` (a measure `μ_{h^ℂ}` on the same
probability space) and `LQGMeasureNonatomic` (`μ_h({0}) = 0`; the comparison does not reach the point `0`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Set
open scoped ENNReal

universe u

/-- The event of eq:ball-volume (Lemma 2.4, line 501) on `B_R(0)` at scale `ε`:
`ε^{β⁻} ≤ μ(B_ε(z)) ≤ ε^{β⁺}` for every `z ∈ B_R(0)`. -/
def ballMassBoundEvent {Ω : Type*} (μ : Ω → Measure ℂ) (R βplus βminus ε : ℝ) : Set Ω :=
  {ω | ∀ z ∈ ball (0 : ℂ) R,
    ENNReal.ofReal (ε ^ βminus) ≤ μ ω (ball z ε) ∧ μ ω (ball z ε) ≤ ENNReal.ofReal (ε ^ βplus)}

/-- Step of Lemma 2.4, I1 and I2: eq:ball-volume (Lemma 2.4, line 501, with the exponent ranges of [C1]) for
centres in every ball `B_R(0)`. For each `R > 0`, `β⁺ ∈ (0, min {(2-γ)²/2, γ(Q-α₀)})` and
`β⁻ > max {(2+γ)²/2, γ(Q-α₀)}`, with polynomially high probability as `ε → 0`,
`ε^{β⁻} ≤ μ_h(B_ε(z)) ≤ ε^{β⁺}` for all `z ∈ B_R(0)`. The paper states `R = 1` and obtains other radii by
scaling (lines 3529-3530). -/
def LiouvilleBallMassBoundStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ R : ℝ, 0 < R → ∀ βplus βminus : ℝ, 0 < βplus → βplus < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) →
    max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus →
    PolyHighProb P (ballMassBoundEvent μ R βplus βminus)

/-! ### Lemma 2.4 from the step -/

/-- Lemma 2.4 (with [C1]) from `LiouvilleBallMassBoundStep`. -/
theorem liouvilleVolumeGrowthStmt_of_ballMass (h : LiouvilleBallMassBoundStep.{u}) :
    LiouvilleVolumeGrowthStmt.{u} := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hμ βplus βminus hβp hβpm hβmM
  have hstep := h γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ
  refine ⟨hstep 1 one_pos βplus βminus hβp hβpm hβmM, fun r₁ r₂ hr₁ hr₁₂ => ?_⟩
  have hr₂ : 0 < r₂ := hr₁.trans hr₁₂
  have hρ : 0 < (r₂ - r₁) / 2 := by linarith
  refine ⟨r₂ ^ βplus, ((r₂ - r₁) / 2) ^ βminus, Real.rpow_pos_of_pos hr₂ _,
    Real.rpow_pos_of_pos hρ _, ?_⟩
  have hU := (hstep 1 one_pos βplus βminus hβp hβpm hβmM).comp_mul hr₂
  have hL := (hstep 2 two_pos βplus βminus hβp hβpm hβmM).comp_mul hρ
  refine (hU.inter hL).mono_of_small (r₁ := 2 / (r₁ + r₂)) (by positivity) ?_
  rintro ε hε hεs ω ⟨hωU, hωL⟩ z hz
  refine ⟨?_, ?_⟩
  · -- lower bound: the annulus contains the ball `B_{ρε}(w)`, `w = z + (r₁+r₂)ε/2`
    have hc : 0 < (r₁ + r₂) / 2 * ε := by positivity
    have hc1 : (r₁ + r₂) / 2 * ε < 1 := by
      rw [lt_div_iff₀ (by positivity)] at hεs
      linarith
    set w : ℂ := z + (((r₁ + r₂) / 2 * ε : ℝ) : ℂ) with hw_def
    have hwz : dist w z = (r₁ + r₂) / 2 * ε := by
      rw [dist_eq_norm, show w - z = (((r₁ + r₂) / 2 * ε : ℝ) : ℂ) by simp [hw_def], Complex.norm_real,
        Real.norm_of_nonneg hc.le]
    have hw : w ∈ ball (0 : ℂ) 2 := by
      rw [mem_ball] at hz ⊢
      have := dist_triangle w z 0
      linarith
    have hsub : ball w ((r₂ - r₁) / 2 * ε) ⊆ annulus z (r₁ * ε) (r₂ * ε) := by
      intro x hx
      rw [mem_ball] at hx
      refine ⟨mem_ball.2 ?_, fun hx' => ?_⟩
      · have := dist_triangle x w z
        linarith
      · rw [mem_closedBall] at hx'
        have := dist_triangle w x z
        rw [dist_comm w x] at this
        linarith
    calc ENNReal.ofReal (((r₂ - r₁) / 2) ^ βminus * ε ^ βminus)
        = ENNReal.ofReal (((r₂ - r₁) / 2 * ε) ^ βminus) := by rw [Real.mul_rpow hρ.le hε.le]
      _ ≤ μ ω (ball w ((r₂ - r₁) / 2 * ε)) := (hωL w hw).1
      _ ≤ _ := measure_mono hsub
  · -- upper bound: the annulus is contained in `B_{r₂ε}(z)`
    calc μ ω (annulus z (r₁ * ε) (r₂ * ε)) ≤ μ ω (ball z (r₂ * ε)) := measure_mono sdiff_subset
      _ ≤ ENNReal.ofReal ((r₂ * ε) ^ βplus) := (hωU z hz).2
      _ = _ := by rw [Real.mul_rpow hr₂.le hε.le]

/-! ### I2 from the step -/

/-- With slack in the exponents (`a < β⁺`, `b > β⁻`), the ball bounds at the two scales `ε` and `ε/2` give the
bounds with exponents `(a, b)` at every radius `s ∈ [ε/2, ε]`, for small `ε`. -/
theorem ballMassBoundEvent_window {Ω : Type*} (μ : Ω → Measure ℂ) {R a b βplus βminus : ℝ}
    (ha : 0 < a) (hab : a < βplus) (hb : 0 < b) (hba : βminus < b) :
    ∃ r₁ > 0, ∀ ε : ℝ, 0 < ε → ε < r₁ →
      ballMassBoundEvent μ R βplus βminus ε ∩ ballMassBoundEvent μ R βplus βminus (2⁻¹ * ε) ⊆
        {ω | ∀ s : ℝ, 2⁻¹ * ε ≤ s → s ≤ ε → ∀ z ∈ ball (0 : ℂ) R,
          ENNReal.ofReal (s ^ b) ≤ μ ω (ball z s) ∧ μ ω (ball z s) ≤ ENNReal.ofReal (s ^ a)} := by
  obtain ⟨r₁, hr₁, h₁⟩ := exists_pos_forall_rpow_le (sub_pos.2 hab)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2⁻¹) a)
  obtain ⟨r₂, hr₂, h₂⟩ := exists_pos_forall_rpow_le (sub_pos.2 hba)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2⁻¹) βminus)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun ε hε hεr ω ⟨hω₁, hω₂⟩ s hs₁ hs₂ z hz => ?_⟩
  have hs : 0 < s := lt_of_lt_of_le (by positivity) hs₁
  have hε₁ := h₁ ε hε (hεr.trans_le (min_le_left _ _))
  have hε₂ := h₂ ε hε (hεr.trans_le (min_le_right _ _))
  refine ⟨?_, ?_⟩
  · have hle : s ^ b ≤ (2⁻¹ * ε) ^ βminus := by
      calc s ^ b ≤ ε ^ b := Real.rpow_le_rpow hs.le hs₂ hb.le
        _ = ε ^ (b - βminus) * ε ^ βminus := by rw [← Real.rpow_add hε, sub_add_cancel]
        _ ≤ 2⁻¹ ^ βminus * ε ^ βminus := by gcongr
        _ = (2⁻¹ * ε) ^ βminus := by rw [Real.mul_rpow (by norm_num) hε.le]
    calc ENNReal.ofReal (s ^ b) ≤ ENNReal.ofReal ((2⁻¹ * ε) ^ βminus) := ENNReal.ofReal_le_ofReal hle
      _ ≤ μ ω (ball z (2⁻¹ * ε)) := (hω₂ z hz).1
      _ ≤ μ ω (ball z s) := measure_mono (ball_subset_ball hs₁)
  · have hle : ε ^ βplus ≤ s ^ a := by
      calc ε ^ βplus = ε ^ (βplus - a) * ε ^ a := by rw [← Real.rpow_add hε, sub_add_cancel]
        _ ≤ 2⁻¹ ^ a * ε ^ a := by gcongr
        _ = (2⁻¹ * ε) ^ a := by rw [Real.mul_rpow (by norm_num) hε.le]
        _ ≤ s ^ a := Real.rpow_le_rpow (by positivity) hs₁ ha.le
    calc μ ω (ball z s) ≤ μ ω (ball z ε) := measure_mono (ball_subset_ball hs₂)
      _ ≤ ENNReal.ofReal (ε ^ βplus) := (hω₁ z hz).2
      _ ≤ ENNReal.ofReal (s ^ a) := ENNReal.ofReal_le_ofReal hle

/-- I2 (`LQGVolumeGrowthAllScalesStmt`) from `LiouvilleBallMassBoundStep`: Borel-Cantelli along the dyadic
scales, over the countable family of radii `R = n + 1` and rational exponents. -/
theorem lqgVolumeGrowthAllScalesStmt_of_ballMass (h : LiouvilleBallMassBoundStep.{u}) :
    LQGVolumeGrowthAllScalesStmt.{u} := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hμ
  have hM0 : 0 < max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) :=
    lt_max_of_lt_left (by have : 0 < 2 + γ := by linarith
                          positivity)
  have key : ∀ i : ℕ × ℚ × ℚ, ∀ᵐ ω ∂P, 0 < (i.2.1 : ℝ) →
      (i.2.1 : ℝ) < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) →
      max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < (i.2.2 : ℝ) →
      ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) (i.1 + 1),
        ENNReal.ofReal (r ^ (i.2.2 : ℝ)) ≤ μ ω (ball z r) ∧
          μ ω (ball z r) ≤ ENNReal.ofReal (r ^ (i.2.1 : ℝ)) := by
    rintro ⟨n, a, b⟩
    by_cases hcond : 0 < (a : ℝ) ∧ (a : ℝ) < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) ∧
        max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < (b : ℝ)
    swap
    · exact Eventually.of_forall fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hcond
    obtain ⟨ha, ham, hMb⟩ := hcond
    set m := min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
    set M := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
    have hstep := h γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ ((n : ℝ) + 1) (by positivity)
      ((a + m) / 2) ((b + M) / 2) (by linarith) (by linarith) (by linarith)
    obtain ⟨r₁, hr₁, hwin⟩ := ballMassBoundEvent_window μ (R := (n : ℝ) + 1) ha
      (by linarith : (a : ℝ) < (a + m) / 2) (by linarith : (0 : ℝ) < b)
      (by linarith : (b + M) / 2 < (b : ℝ))
    have hpoly := (hstep.inter (hstep.comp_mul (by norm_num : (0 : ℝ) < 2⁻¹))).mono_of_small hr₁ hwin
    filter_upwards [hpoly.ae_eventually_dyadic] with ω hω _ _ _
    obtain ⟨K, hK⟩ := eventually_atTop.1 hω
    refine ⟨(2 : ℝ)⁻¹ ^ K, by positivity, fun r hr hrK z hz => ?_⟩
    obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hr
      (hrK.le.trans (pow_le_one₀ (by norm_num) (by norm_num))) (by norm_num : (0 : ℝ) < 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hkK : K ≤ k := by
      by_contra hlt
      have h' : k + 1 ≤ K := by omega
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num) h'
      linarith
    refine hK k hkK r ?_ hk2 z hz
    rw [pow_succ] at hk1
    linarith
  filter_upwards [ae_all_iff.2 key] with ω hω R hR βplus βminus hβp hβpm hβmM
  obtain ⟨a, hβa, ham⟩ := exists_rat_btwn hβpm
  obtain ⟨b, hMb, hbβ⟩ := exists_rat_btwn hβmM
  obtain ⟨r₀, hr₀, hr⟩ := hω (⌈R⌉₊, a, b) (hβp.trans hβa) ham hMb
  refine ⟨min r₀ 1, lt_min hr₀ one_pos, fun r hr0 hrr z hz => ?_⟩
  have hz' : z ∈ ball (0 : ℂ) ((⌈R⌉₊ : ℝ) + 1) :=
    ball_subset_ball (by linarith [Nat.le_ceil R]) hz
  obtain ⟨h1, h2⟩ := hr r hr0 (hrr.trans_le (min_le_left _ _)) z hz'
  have hr1 : r < 1 := hrr.trans_le (min_le_right _ _)
  exact ⟨le_trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hbβ.le)) h1,
    h2.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hr0 hr1.le hβa.le))⟩

/-! ### I1 from I2 -/

/-- I1 (`LQGMeasureFullSupportStmt`) from I2: every nonempty open set contains a small ball, whose mass is at
least `r^{β⁻} > 0`. -/
theorem lqgMeasureFullSupportStmt_of_volumeGrowth (h : LQGVolumeGrowthAllScalesStmt.{u}) :
    LQGMeasureFullSupportStmt.{u} := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hμ
  have hm : 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := by
    have h1 : 0 < 2 - γ := by linarith
    have h2 : 0 < lqgQ γ - α₀ := by linarith
    exact lt_min (by positivity) (by positivity)
  filter_upwards [h γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hω U hU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨r₀, hr₀, hr⟩ := hω (‖x‖ + 1) (by positivity) _
    (max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1) (half_pos hm) (half_lt_self hm) (lt_add_one _)
  have hmin : 0 < min δ r₀ := lt_min hδ hr₀
  have hpos : 0 < min δ r₀ / 2 := half_pos hmin
  have hlt : min δ r₀ / 2 < min δ r₀ := half_lt_self hmin
  obtain ⟨h1, -⟩ := hr (min δ r₀ / 2) hpos (hlt.trans_le (min_le_right _ _)) x
    (by rw [mem_ball_zero_iff]; linarith)
  calc (0 : ℝ≥0∞) < ENNReal.ofReal ((min δ r₀ / 2) ^ (max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1)) :=
        ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpos _)
    _ ≤ μ ω (ball x (min δ r₀ / 2)) := h1
    _ ≤ μ ω U := measure_mono ((ball_subset_ball (hlt.le.trans (min_le_left _ _))).trans hδU)

end HarmonicBalls
