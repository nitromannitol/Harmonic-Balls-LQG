import HarmonicBalls.Proofs.Potential.LQGClockTimeChangeReduction

/-! # Strict increase of LQG clocks from a zero-one law and a positive mean

Garban, Rhodes and Vargas (*Liouville Brownian motion*, Ann. Probab. 44 (2016), arXiv:1301.2876),
proof of Theorem 2.7 (3) for a fixed start: for almost every Brownian path the event that the clock
increases over a fixed time interval has probability zero or one under the law of the field (the
event lies in the tail σ-algebra of the independent scales of the field, so Kolmogorov's zero-one
law applies), and the expected increase of the clock over the interval is positive (Lemma 2.8,
where it equals the length of the interval). Hence the clock increases over the interval for
almost every field, for almost every path. By Fubini's theorem the order of the two almost sure
quantifiers can be exchanged, and countably many intervals with rational endpoints give, for
almost every field, the strict increase between any two rational times for almost every path.

The zero-one law and the positive mean enter as hypotheses on one jointly measurable LQG clock;
since two LQG clocks from the same start agree almost surely, the conclusion holds for every LQG
clock from that start, and together with divergence it gives the time-change property.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- If, for almost every `b`, the event `{f ω b < g ω b}` has probability zero or one under `P`
and the mean of `(g ω b - f ω b)⁺` under `P` is positive, then `f ω b < g ω b` for almost every
`b`, for almost every `ω`. -/
theorem ae_ae_lt_of_zero_one_of_lintegral_pos {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure X} [SFinite μ]
    {f g : Ω → X → ℝ} (hf : Measurable fun p : Ω × X => f p.1 p.2)
    (hg : Measurable fun p : Ω × X => g p.1 p.2)
    (h01 : ∀ᵐ b ∂μ, P {ω | f ω b < g ω b} = 0 ∨ P {ω | f ω b < g ω b} = 1)
    (hmean : ∀ᵐ b ∂μ, 0 < ∫⁻ ω, ENNReal.ofReal (g ω b - f ω b) ∂P) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂μ, f ω b < g ω b := by
  have hS : MeasurableSet {p : Ω × X | f p.1 p.2 < g p.1 p.2} := measurableSet_lt hf hg
  have hb : ∀ᵐ b ∂μ, ∀ᵐ ω ∂P, f ω b < g ω b := by
    filter_upwards [h01, hmean] with b hb01 hbmean
    have hSb : MeasurableSet {ω | f ω b < g ω b} :=
      measurableSet_lt (hf.comp (measurable_id.prodMk measurable_const))
        (hg.comp (measurable_id.prodMk measurable_const))
    have hne : P {ω | f ω b < g ω b} ≠ 0 := by
      intro h0
      have hz : (fun ω => ENNReal.ofReal (g ω b - f ω b)) =ᵐ[P] 0 := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with ω hω
        have hω' : ¬ f ω b < g ω b := hω
        have hle : g ω b - f ω b ≤ 0 := by linarith [not_lt.mp hω']
        simp [ENNReal.ofReal_eq_zero.mpr hle]
      rw [lintegral_congr_ae hz] at hbmean
      simp at hbmean
    have h1 : P {ω | f ω b < g ω b} = 1 := hb01.resolve_left hne
    rw [ae_iff]
    have hc : {ω | ¬ f ω b < g ω b} = {ω | f ω b < g ω b}ᶜ := rfl
    rw [hc, prob_compl_eq_zero_iff hSb]
    exact h1
  exact (Measure.ae_ae_comm (μ := P) (ν := μ) (p := fun ω b => f ω b < g ω b) hS).mpr hb

/-- Garban-Rhodes-Vargas 2016, Theorem 2.7 (3), for a fixed start: if, for almost every path, the
increase of a jointly measurable clock between two rational times is positive with probability
zero or one under the field law and has positive mean, then for almost every field the clock
increases strictly between any two rational times for almost every path. -/
theorem ae_forall_rat_lt_of_zero_one_of_lintegral_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {x : ℂ}
    (G : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hG : ∀ t : ℝ≥0, Measurable fun p : Ω × ContinuousPath ℂ => G p.1 p.2 t)
    (h01 : ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ b ∂(planarBrownianMotion x),
      P {ω | G ω b (s : ℝ).toNNReal < G ω b (t : ℝ).toNNReal} = 0 ∨
        P {ω | G ω b (s : ℝ).toNNReal < G ω b (t : ℝ).toNNReal} = 1)
    (hmean : ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ b ∂(planarBrownianMotion x),
      0 < ∫⁻ ω, ENNReal.ofReal (G ω b (t : ℝ).toNNReal - G ω b (s : ℝ).toNNReal) ∂P) :
    ∀ᵐ ω ∂P, ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ b ∂(planarBrownianMotion x),
      G ω b (s : ℝ).toNNReal < G ω b (t : ℝ).toNNReal := by
  have hst : ∀ s t : ℚ, ∀ᵐ ω ∂P, 0 ≤ s → s < t → ∀ᵐ b ∂(planarBrownianMotion x),
      G ω b (s : ℝ).toNNReal < G ω b (t : ℝ).toNNReal := by
    intro s t
    by_cases hs : 0 ≤ s
    · by_cases hlt : s < t
      · filter_upwards [ae_ae_lt_of_zero_one_of_lintegral_pos (hG _) (hG _) (h01 s t hs hlt)
          (hmean s t hs hlt)] with ω hω _ _
        exact hω
      · exact Filter.Eventually.of_forall fun ω _ h => absurd h hlt
    · exact Filter.Eventually.of_forall fun ω h => absurd h hs
  rw [ae_all_iff]
  intro s
  rw [ae_all_iff]
  exact hst s

/-- Strict increase between rational times passes from one LQG clock to every LQG clock from the
same start. -/
theorem ae_forall_rat_lt_of_isLQGClock_of_ae {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock planarBrownianMotion γ hε x F)
    (hG : IsLQGClock planarBrownianMotion γ hε x G)
    (hpos : ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ b ∂(planarBrownianMotion x),
      G b (s : ℝ).toNNReal < G b (t : ℝ).toNNReal) :
    ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ b ∂(planarBrownianMotion x),
      F b (s : ℝ).toNNReal < F b (t : ℝ).toNNReal := by
  intro s t hs hlt
  filter_upwards [ae_eq_of_isLQGClock hG hF, hpos s t hs hlt] with b hb hbp
  rw [← hb]
  exact hbp

/-- Garban-Rhodes-Vargas 2016, Theorem 2.7 (3) with (4), for a fixed start: if a jointly
measurable LQG clock satisfies the zero-one law and has positive mean increments between rational
times, then for almost every field every LQG clock from that start that tends to infinity almost
surely is almost surely a time-change clock. -/
theorem ae_isTimeChangeClock_of_zero_one_of_lintegral_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {x : ℂ} {γ : ℝ}
    {hε : Ω → ℝ → ℂ → ℝ} (hcont : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (hε ω (dyadicScale k)))
    (F G : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hε ω) x (F ω))
    (hG : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hε ω) x (G ω))
    (hGm : ∀ t : ℝ≥0, Measurable fun p : Ω × ContinuousPath ℂ => G p.1 p.2 t)
    (h01 : ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ b ∂(planarBrownianMotion x),
      P {ω | G ω b (s : ℝ).toNNReal < G ω b (t : ℝ).toNNReal} = 0 ∨
        P {ω | G ω b (s : ℝ).toNNReal < G ω b (t : ℝ).toNNReal} = 1)
    (hmean : ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ b ∂(planarBrownianMotion x),
      0 < ∫⁻ ω, ENNReal.ofReal (G ω b (t : ℝ).toNNReal - G ω b (s : ℝ).toNNReal) ∂P)
    (hdiv : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion x), Tendsto (F ω b) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω b) := by
  filter_upwards [hcont, hF, hG, ae_forall_rat_lt_of_zero_one_of_lintegral_pos G hGm h01 hmean,
    hdiv] with ω hcω hFω hGω hposω hdω
  exact ae_isTimeChangeClock_of_isLQGClock hcω hFω
    (ae_forall_rat_lt_of_isLQGClock_of_ae hFω hGω hposω) hdω

end HarmonicBalls
