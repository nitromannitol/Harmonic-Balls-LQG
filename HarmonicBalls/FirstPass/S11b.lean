import HarmonicBalls.FirstPass.Frozen.S11b
import HarmonicBalls.FirstPass.S11b.Counting
import HarmonicBalls.Draft.Section11
import HarmonicBalls.Proposed.LQG

/-!
# Section 11, ergodic inputs

Each theorem `firstPass_11_<k>` concludes the Draft statement of a numbered result of Section 11
(`HarmonicBalls/Draft/Section11.lean`). Its hypotheses are only Draft statements of other numbered results,
EXTERNAL Props (FIRST-PASS FROZEN Props in `FirstPass/Frozen/S11b.lean`) and the staged `Proposed/` inputs.

Status:
* Lemma 11.7 (`ManyConeBadScalesStmt`): `firstPass_11_7`. Route: Lemma 11.8 at the origin gives a uniform positive
  probability `p` of the origin-rooted good event (the origin meets the separation hypothesis of Lemma 11.8,
  `dist({r < |w| < 6r}, {0}) = r > r/100`, and the rooted field has `α = γ`); the frozen dilation ergodicity turns
  it into a positive frequency `q ≥ p`; the window count helper gives `(q/2) N` good scales in `(N, 2N]`; the frozen
  rooted transfer moves the frequency statement to `μ_h`-a.e. `z`. The constant is `δ = p/2`, uniform in the space.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

open FirstPassS11 FirstPassS11b

/-- `γ < Q = 2/γ + γ/2` for `0 < γ < 2` (the rooted field with `α = γ` is admissible). -/
lemma lt_lqgQ_self {γ : ℝ} (h0 : 0 < γ) (h2 : γ < 2) : γ < lqgQ γ := by
  unfold lqgQ
  have h : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) h0]
    nlinarith
  linarith

/-- The annulus `𝔸_{r,6r}(0) = {r < |w| < 6r}` lies at distance at least `r` from `0`. -/
lemma le_infDist_origin_annulus {r : ℝ} (hr : 0 < r) :
    r ≤ Metric.infDist (0 : ℂ) (annulus 0 r (6 * r)) := by
  have hmem : ∀ y ∈ annulus 0 r (6 * r), r < ‖y‖ := by
    intro y hy
    have hy2 : y ∉ Metric.closedBall (0 : ℂ) r := by
      unfold annulus at hy
      exact hy.2
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy2
    exact hy2
  have hne : (annulus 0 r (6 * r)).Nonempty := by
    refine ⟨((3 * r : ℝ) : ℂ), ?_⟩
    unfold annulus
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith),
        not_le]
      linarith
  by_contra hcon
  obtain ⟨y, hy, hlt⟩ := (Metric.infDist_lt_iff hne).1 (not_le.1 hcon)
  have hyr := hmem y hy
  rw [dist_zero_left] at hlt
  linarith

/-- FIRST-PASS, Lemma 11.7 (lemma:mu_h-bad-and-harnack, corrected [C39]), for `ManyConeBadScalesStmt`
(`Draft/Section11.lean`). WITHDRAWN: it uses the two RETIRED Props
`OriginRootedConeFrequencyFrozen` and `RootedConeFrequencyTransferFrozen`; the redo is `firstPass_11_7` in
`FirstPass/S11c.lean`. The inputs of this withdrawn version are: the Draft Lemma 11.8 (`ConeBadEventProbabilityStmt`), applied with
`α₀ := γ` at the origin; the staged existence of the LQG measure `LQGMeasureExistence` (`Proposed/LQG.lean`, pending
operator source-check), used to produce the origin-rooted measure `μ0`; the frozen dilation ergodicity
`OriginRootedConeFrequencyFrozen` and the frozen rooted transfer `RootedConeFrequencyTransferFrozen`.
The printed origin bump argument (paper, the paragraph before the transfer) is not used: Lemma 11.8 already covers
`z = 0`, since its separation hypothesis holds there. -/
theorem firstPass_11_7.{u}
    (h8 : ConeBadEventProbabilityStmt.{u})
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hFreq : OriginRootedConeFrequencyFrozen.{u})
    (hTr : RootedConeFrequencyTransferFrozen.{u}) :
    ManyConeBadScalesStmt.{u} := by
  classical
  intro γ α₀ hγ0 hγ2 hα₀ Q hQ M hM
  have hγQ : γ < lqgQ γ := lt_lqgQ_self hγ0 hγ2
  obtain ⟨p, ⟨hp0, hp1⟩, hp⟩ := h8 γ γ hγ0 hγ2 hγQ Q hQ M hM
  refine ⟨p / 2, ⟨half_pos hp0, by linarith⟩, ?_⟩
  intro Ω _ P hC hcirc μ hWP hμ
  have : IsProbabilityMeasure P := hWP.isProbabilityMeasure
  obtain ⟨μ0, hμ0⟩ := hE Ω P γ γ hC hcirc hWP hγ0 hγ2 hγQ
  obtain ⟨N₀, hN₀⟩ := hp Ω P hC hcirc μ0 hWP hμ0 0
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ N₀ := by positivity
  have hcond : (2 : ℝ)⁻¹ ^ N₀ / 100 <
      infDist (0 : ℂ) (annulus 0 ((2 : ℝ)⁻¹ ^ N₀) (6 * (2 : ℝ)⁻¹ ^ N₀)) := by
    have h1 := le_infDist_origin_annulus hr
    linarith
  obtain ⟨A, hAsub, hAmeas, hAP⟩ := hN₀ N₀ le_rfl hcond
  -- the origin event at scale `N₀` and its (lower) expectation
  set E : Set Ω := {ω' : Ω | coneMassEvent (μ0 ω') Q M ((2 : ℝ)⁻¹ ^ N₀) 0} with hE_def
  set q : ℝ := (∫⁻ ω, Set.indicator E (fun _ => (1 : ℝ≥0∞)) ω ∂P).toReal with hq_def
  have hlint : ENNReal.ofReal p ≤ ∫⁻ ω, Set.indicator E (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
    calc ENNReal.ofReal p ≤ P A := hAP
      _ = ∫⁻ ω, Set.indicator A (fun _ => (1 : ℝ≥0∞)) ω ∂P := (lintegral_indicator_one hAmeas).symm
      _ ≤ ∫⁻ ω, Set.indicator E (fun _ => (1 : ℝ≥0∞)) ω ∂P :=
          lintegral_mono (fun ω => Set.indicator_le_indicator_of_subset hAsub (fun _ => zero_le) ω)
  have hle_one : ∫⁻ ω, Set.indicator E (fun _ => (1 : ℝ≥0∞)) ω ∂P ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ne_of_lt (ENNReal.one_lt_top))
    calc ∫⁻ ω, Set.indicator E (fun _ => (1 : ℝ≥0∞)) ω ∂P ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂P :=
          lintegral_mono (fun ω => by by_cases h : ω ∈ E <;> simp [Set.indicator, h])
      _ = 1 := by simp
  have hqp : p ≤ q := by
    have h1 := ENNReal.toReal_mono hle_one hlint
    rwa [ENNReal.toReal_ofReal hp0.le] at h1
  have hqpos : 0 < q := lt_of_lt_of_le hp0 hqp
  -- the origin frequency of good scales, almost surely, from the frozen ergodic input
  have hfreq := hFreq γ Q M hγ0 hγ2 hQ hM Ω P hC hcirc μ0 hWP hμ0 N₀
  have hgood0 : ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      p / 2 * (N : ℝ) ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ coneMassEvent (μ0 ω) Q M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ) := by
    filter_upwards [hfreq] with ω hω
    have hω' : Tendsto (fun N : ℕ => (occCount (fun n => coneMassEvent (μ0 ω) Q M ((2 : ℝ)⁻¹ ^ n) 0) N : ℝ)
        / (N : ℝ)) atTop (𝓝 q) := by
      refine Tendsto.congr (fun N => ?_) hω
      rw [ncard_occ_eq]
    filter_upwards [eventually_window_count_ge (fun n => coneMassEvent (μ0 ω) Q M ((2 : ℝ)⁻¹ ^ n) 0)
      hqpos hω'] with N hN
    rw [ncard_window_eq]
    have hpq : p / 2 * (N : ℝ) ≤ q / 2 * (N : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
      linarith
    linarith
  exact hTr γ α₀ Q M (p / 2) hγ0 hγ2 hα₀ hQ hM (half_pos hp0) Ω P hC hcirc μ0 μ hWP hμ0 hμ hgood0


end HarmonicBalls
