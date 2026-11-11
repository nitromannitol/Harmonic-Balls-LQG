import HarmonicBalls.FirstPass.S11c.ScaleEvent
import HarmonicBalls.FirstPass.S11c.OriginFrequency
import HarmonicBalls.FirstPass.S11c.ProfileBridge
import HarmonicBalls.FirstPass.S11c.Stationary
import HarmonicBalls.Proofs.GFF.ContinuousCircleDilationMixing
import HarmonicBalls.Proofs.Sec8.CircleLogPotential
import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion
import HarmonicBalls.Steps.Sec11.PinchNormalizedMeasure

/-!
# Lemma 11.7: the origin-level window frequency

Steps S1-S4 of the written proof (paper `lemma:mu_h-bad-and-harnack`, line 2896).
For the `γ`-rooted LQG measure `μ` of a whole-plane GFF, the cone event at the origin occurs at a positive proportion of
the scales of every window `[N+1, 2N]`, almost surely. Ingredients: the ergodicity of the profile dilation
(`IsWholePlaneGFF.ergodic_continuousCircleDilation`), Birkhoff's theorem (`ae_window_visits_of_map`), the stationarity of
the cone event under the dilation (`coneMassEvent_iterate_dilate`), and a measurable version of the profile event.
The probability bound at the origin is taken as the hypothesis `P A ≥ p` of a measurable event `A` contained in the cone
event (Draft Lemma 11.8 at `z = 0`, `ConeBadEventProbabilityStmt`).

The `α`-shift `fieldCircleAverage α` of the profile is handled by the scaling identity of the circle averages of
`log ‖·‖`, `L(e, z) = log max(e, ‖z‖)` (`HarmonicBalls.circleAverage_log_norm_sub_eq_log_max`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls

namespace HarmonicBalls.S11c

noncomputable section

/-! ## 1. Circle averages of `log ‖·‖` and the α-shifted profile -/

lemma circleAvgLog_eq (r : ℝ) (c : ℂ) (hr : 0 < r) :
    Real.circleAverage (fun x => Real.log ‖x‖) c r = Real.log (max r ‖c‖) := by
  have h := HarmonicBalls.circleAverage_log_norm_sub_eq_log_max hr c 0
  simpa only [sub_zero] using h

/-- The circle averages of `log ‖·‖` satisfy `L(e/2, z/2) - L(1/2, 0) = L(e, z)` (scaling by `2`). -/
lemma circleAvgLog_scale (e : ℝ) (he : 0 < e) (z : ℂ) :
    Real.circleAverage (fun x => Real.log ‖x‖) (z / 2) (e / 2) -
        Real.circleAverage (fun x => Real.log ‖x‖) 0 (1 / 2) =
      Real.circleAverage (fun x => Real.log ‖x‖) z e := by
  have hpos : 0 < max e ‖z‖ := lt_max_of_lt_left he
  have hn : ‖z / 2‖ = ‖z‖ / 2 := by rw [norm_div]; norm_num
  have hmax : max (e / 2) (‖z‖ / 2) = max e ‖z‖ / 2 := by
    rcases le_total e ‖z‖ with h | h
    · rw [max_eq_right h, max_eq_right (show e / 2 ≤ ‖z‖ / 2 by linarith)]
    · rw [max_eq_left h, max_eq_left (show ‖z‖ / 2 ≤ e / 2 by linarith)]
  have hA : Real.log (max (e / 2) ‖z / 2‖) = Real.log (max e ‖z‖) - Real.log 2 := by
    rw [hn, hmax, Real.log_div hpos.ne' (by norm_num)]
  have hB : Real.log (max (1 / 2) ‖(0 : ℂ)‖) = -Real.log 2 := by
    rw [norm_zero, max_eq_left (by norm_num), one_div, Real.log_inv]
  rw [circleAvgLog_eq _ _ (by positivity), circleAvgLog_eq _ _ (by norm_num),
    circleAvgLog_eq _ _ he, hA, hB]
  ring

/-- The α-shifted profile `(e, z) ↦ fieldCircleAverage α (circleProfile y) e z` on positive scales, and `0` otherwise.
It is measurable in `z` for every `e` (the value at `e ≤ 0` is irrelevant: the LQG limit only reads positive scales). -/
def originProfile (α : ℝ) (y : C(CircleParameter, ℝ)) : ℝ → ℂ → ℝ :=
  fun e z => if 0 < e then fieldCircleAverage α (circleProfile y) e z else 0

lemma originProfile_of_pos (α : ℝ) (y : C(CircleParameter, ℝ)) {e : ℝ} (he : 0 < e) (z : ℂ) :
    originProfile α y e z = fieldCircleAverage α (circleProfile y) e z := by
  simp [originProfile, he]

lemma originProfile_pos_eq (α : ℝ) (y : C(CircleParameter, ℝ)) {e : ℝ} (he : 0 < e) (z : ℂ) :
    originProfile α y e z = circleProfile y e z - α * Real.circleAverage (fun x => Real.log ‖x‖) z e := by
  rw [originProfile_of_pos α y he z]
  unfold fieldCircleAverage
  rfl

lemma measurable_originProfile (α : ℝ) (y : C(CircleParameter, ℝ)) (e : ℝ) :
    Measurable (originProfile α y e) := by
  by_cases he : 0 < e
  · have hcp : Measurable (fun z : ℂ => circleProfile y e z) := by
      have hfun : (fun z : ℂ => circleProfile y e z) = fun z => y (⟨e, he⟩, z) := by
        funext z
        simp only [circleProfile, he, ↓reduceDIte]
      rw [hfun]
      exact (y.continuous.comp (continuous_const.prodMk continuous_id)).measurable
    have hlog : Measurable (fun z : ℂ => Real.log (max e ‖z‖)) :=
      ((continuous_const.max continuous_norm).log fun z => (lt_max_of_lt_left he).ne').measurable
    have hfun : originProfile α y e = fun z => circleProfile y e z - α * Real.log (max e ‖z‖) := by
      funext z
      rw [originProfile_pos_eq α y he z, circleAvgLog_eq e z he]
    rw [hfun]
    exact hcp.sub (measurable_const.mul hlog)
  · have hfun : originProfile α y e = fun _ => 0 := by
      funext z
      simp [originProfile, he]
    rw [hfun]
    exact measurable_const

/-! ## 2. The normalized dilation of the α-shifted profile -/

/-- The normalized dilation of the α-shifted profile is the α-shifted profile of the dilated profile, on positive scales. -/
lemma normalizedDilation_originProfile (α : ℝ) (y : C(CircleParameter, ℝ)) {e : ℝ} (he : 0 < e) (z : ℂ) :
    normalizedDilation (originProfile α y) e z = originProfile α (continuousCircleDilation y) e z := by
  have hT : circleProfile (continuousCircleDilation y) e z =
      circleProfile y (e / 2) (z / 2) - circleProfile y (1 / 2) 0 := by
    unfold circleProfile
    simp only [he, ↓reduceDIte]
    exact continuousCircleDilation_eq_normalizedDilation y _
  have hL := circleAvgLog_scale e he z
  show originProfile α y (e / 2) (z / 2) - originProfile α y (1 / 2) 0 = _
  rw [originProfile_pos_eq α y (by positivity : (0 : ℝ) < e / 2),
    originProfile_pos_eq α y (by norm_num : (0 : ℝ) < 1 / 2),
    originProfile_pos_eq α (continuousCircleDilation y) he, hT]
  linear_combination (-α) * hL

/-- Iterated normalized dilation of the α-shifted profile, on positive scales. -/
lemma iterate_normalizedDilation_originProfile (α : ℝ) (y : C(CircleParameter, ℝ)) (n : ℕ) :
    ∀ {e : ℝ}, 0 < e → ∀ z : ℂ,
      (normalizedDilation)^[n] (originProfile α y) e z = originProfile α (continuousCircleDilation^[n] y) e z := by
  induction n with
  | zero =>
    intro e he z
    simp only [Function.iterate_zero, id]
  | succ n ih =>
    intro e he z
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    show (normalizedDilation)^[n] (originProfile α y) (e / 2) (z / 2) -
        (normalizedDilation)^[n] (originProfile α y) (1 / 2) 0 = _
    rw [ih (by positivity : (0 : ℝ) < e / 2), ih (by norm_num : (0 : ℝ) < 1 / 2)]
    exact normalizedDilation_originProfile α (continuousCircleDilation^[n] y) he z

/-! ## 3. Transport of LQG limits along positive scales -/

/-- The LQG limit depends only on the values of the circle average at positive scales. -/
lemma isLQGLimit_of_congr_pos {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (h : ∀ e, 0 < e → ∀ z, hε e z = hε' e z) (hm : IsLQGLimit γ hε m) : IsLQGLimit γ hε' m := by
  refine ⟨hm.isLocallyFiniteMeasure, fun f hf hc => ?_⟩
  have key : ∀ k : ℕ, lqgApprox γ hε' (dyadicScale k) = lqgApprox γ hε (dyadicScale k) := by
    intro k
    have hpos : 0 < dyadicScale k := by unfold dyadicScale; positivity
    unfold lqgApprox
    congr 1
    funext z
    rw [h _ hpos z]
  simp only [key]
  exact hm.tendsto_integral f hf hc

/-- The cone mass event at the origin, read on the dilated profile: the stationarity of Lemma 11.7 in the form used below. -/
lemma coneMassEvent_originProfile_iterate {γ : ℝ} {Q : Set ℂ} (hQ : IsCone Q) (M : ℝ) (α : ℝ)
    (y : C(CircleParameter, ℝ)) {m mk : Measure ℂ} (n N0 : ℕ)
    (hm : IsLQGLimit γ (fieldCircleAverage α (circleProfile y)) m)
    (hmk : IsLQGLimit γ (fieldCircleAverage α (circleProfile (continuousCircleDilation^[n] y))) mk) :
    coneMassEvent mk Q M (dyadicScale N0) 0 ↔ coneMassEvent m Q M (dyadicScale (N0 + n)) 0 := by
  have hm' : IsLQGLimit γ (originProfile α y) m :=
    isLQGLimit_of_congr_pos (fun e he z => (originProfile_of_pos α y he z).symm) hm
  have hmk' : IsLQGLimit γ (normalizedDilation^[n] (originProfile α y)) mk :=
    isLQGLimit_of_congr_pos (fun e he z => (iterate_normalizedDilation_originProfile α y n he z).symm ▸
      (originProfile_of_pos α (continuousCircleDilation^[n] y) he z).symm) hmk
  exact HarmonicBalls.coneMassEvent_iterate_dilate hQ M n (originProfile α y)
    (measurable_originProfile α y) hm' hmk' N0

/-! ## 4. A measurable version of the profile event (step S1) -/

/-- The cone mass event at the origin, as a function of the decoded measure, agrees `ν`-a.e. with a measurable subset
of the profile space (the potential `annulusGreenPotentialSup` is a.e. a Borel function of the measure). -/
lemma exists_measurable_coneMassEvent {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {Dec : X → Measure ℂ} (hDec : Measurable Dec) {Q : Set ℂ} (hQ : IsCone Q) (M r : ℝ) :
    ∃ E : Set X, MeasurableSet E ∧ ∀ᵐ y ∂ν, (coneMassEvent (Dec y) Q M r 0 ↔ y ∈ E) := by
  have hmass : ∀ B : Set ℂ, MeasurableSet B → B ⊆ ball (0 : ℂ) (6 * r) →
      ∃ Y : X → ℝ≥0∞, Measurable Y ∧ ∀ᵐ y ∂ν, Dec y B = Y y := fun B hB _ =>
    ⟨fun y => Dec y B, (Measure.measurable_coe hB).comp hDec, ae_of_all _ fun _ => rfl⟩
  obtain ⟨Y1, hY1m, hY1⟩ :=
    exists_local_annulusGreenPotentialSup_of_borel_mass ν inferInstance Dec 0 (3 * r) (6 * r) hmass
  have hB : MeasurableSet (annulus 0 r (2 * r) ∩ coneAt Q 0) :=
    (measurableSet_annulus_scale 0 r (2 * r)).inter (measurableSet_coneAt hQ 0)
  have hY2 : Measurable fun y => Dec y (annulus 0 r (2 * r) ∩ coneAt Q 0) :=
    (Measure.measurable_coe hB).comp hDec
  refine ⟨{y | ENNReal.ofReal M * Y1 y ≤ Dec y (annulus 0 r (2 * r) ∩ coneAt Q 0)},
    measurableSet_le (measurable_const.mul hY1m) hY2, ?_⟩
  filter_upwards [hY1] with y hy
  show coneMassEvent (Dec y) Q M r 0 ↔ _
  unfold coneMassEvent
  rw [hy]

end

/-! ## 5. The origin-level window frequency (steps S1-S4) -/

open Classical in
/-- Steps S1-S4 of Lemma 11.7 at the origin. Let `μ` be the `γ`-rooted LQG measure of the whole-plane GFF, written as
`μ = Dec ∘ F` through its continuous circle profile `F` (`LQGMeasureOfProfileMeasurableFrozen`, `hDec`, `hμD`), and let
`A` be a measurable event of probability at least `p` on which the cone event at scale `2^{-N₀}` holds (Draft Lemma 11.8
at `z = 0`). Then almost surely, for all large `N`, the cone event holds at the scales `2^{-(N₀+n)}`, `n ∈ [N+1, 2N]`, for at
least `p N / 4` of the indices. -/
theorem origin_window_visits {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} {Q : Set ℂ} (hQ : IsCone Q) {M : ℝ} {μ : Ω → Measure ℂ}
    {F : Ω → C(CircleParameter, ℝ)} (hF : Measurable F)
    (hversion : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2)
    {Dec : C(CircleParameter, ℝ) → Measure ℂ} (hDec : Measurable Dec)
    (hμD : ∀ᵐ ω ∂P, μ ω = Dec (F ω))
    (hlim : ∀ᵐ y ∂(P.map F), IsLQGLimit γ (fieldCircleAverage γ (circleProfile y)) (Dec y))
    (N0 : ℕ) {p : ℝ} (hp : 0 < p) {A : Set Ω}
    (hAev : A ⊆ {ω | coneMassEvent (μ ω) Q M (dyadicScale N0) 0})
    (hPA : ENNReal.ofReal p ≤ P A) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      p / 4 * (N : ℝ) ≤ (((Finset.Icc (N + 1) (2 * N)).filter
        (fun n : ℕ => coneMassEvent (μ ω) Q M (dyadicScale (N0 + n)) 0)).card : ℝ) := by
  set ν := P.map F with hν_def
  have hν : IsProbabilityMeasure ν := by
    rw [hν_def]
    infer_instance
  have herg : Ergodic continuousCircleDilation ν := hh.ergodic_continuousCircleDilation hF hversion
  have hmp : MeasurePreserving continuousCircleDilation ν ν := herg.toMeasurePreserving
  -- S1: a measurable version of the profile event at scale 2^{-N₀}
  obtain ⟨E, hE, hEae⟩ := exists_measurable_coneMassEvent ν hDec hQ M (dyadicScale N0)
  -- S2: the profile event has ν-measure at least p
  have hAE : ∀ᵐ ω ∂P, ω ∈ A → F ω ∈ E := by
    filter_upwards [ae_of_ae_map hF.aemeasurable hEae, hμD] with ω hω hμ hωA
    have h1 : coneMassEvent (μ ω) Q M (dyadicScale N0) 0 := hAev hωA
    rw [hμ] at h1
    exact hω.mp h1
  have hPE : ENNReal.ofReal p ≤ ν E := by
    rw [hν_def, Measure.map_apply hF hE]
    exact le_trans hPA (measure_mono_ae hAE)
  have hpE : p ≤ (ν E).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top ν E)).mp hPE
  -- S4: Birkhoff for the ergodic profile dilation
  have hwin := ae_window_visits_of_map P hF rfl herg hE hp hpE
  -- S3: stationarity of the cone event along the orbit, a.s.
  have hcov : ∀ n : ℕ, ∀ᵐ y ∂ν, (coneMassEvent (Dec (continuousCircleDilation^[n] y)) Q M (dyadicScale N0) 0 ↔
      coneMassEvent (Dec y) Q M (dyadicScale (N0 + n)) 0) := by
    intro n
    filter_upwards [hlim, (hmp.iterate n).quasiMeasurePreserving.ae hlim] with y h1 h2
    exact coneMassEvent_originProfile_iterate hQ M γ y n N0 h1 h2
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      (coneMassEvent (Dec (continuousCircleDilation^[n] (F ω))) Q M (dyadicScale N0) 0 ↔
        continuousCircleDilation^[n] (F ω) ∈ E) ∧
      (coneMassEvent (Dec (continuousCircleDilation^[n] (F ω))) Q M (dyadicScale N0) 0 ↔
        coneMassEvent (Dec (F ω)) Q M (dyadicScale (N0 + n)) 0) := by
    rw [ae_all_iff]
    intro n
    have h1 := ae_of_ae_map hF.aemeasurable ((hmp.iterate n).quasiMeasurePreserving.ae hEae)
    have h2 := ae_of_ae_map hF.aemeasurable (hcov n)
    filter_upwards [h1, h2] with ω h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [hwin, hall, hμD] with ω hwω hallω hμω
  have hfilt : ∀ N : ℕ, ((Finset.Icc (N + 1) (2 * N)).filter
      (fun n : ℕ => continuousCircleDilation^[n] (F ω) ∈ E)) =
      ((Finset.Icc (N + 1) (2 * N)).filter
        (fun n : ℕ => coneMassEvent (μ ω) Q M (dyadicScale (N0 + n)) 0)) := by
    intro N
    apply Finset.filter_congr
    intro n _
    rw [← (hallω n).1, (hallω n).2, hμω]
  filter_upwards [hwω] with N hN
  rw [hfilt N] at hN
  exact hN


end HarmonicBalls.S11c
