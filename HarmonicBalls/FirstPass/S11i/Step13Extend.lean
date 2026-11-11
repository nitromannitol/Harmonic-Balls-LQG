import HarmonicBalls.FirstPass.S11i.DilatePinch

/-!
# Step 13 of the proof of Lemma 11.13: from the B_1 window limit to the whole plane

Source: Step 13 of the written proof. For `R = 2^k` the rescaled field
`h^(R)(w) = h(R w) - h_R(0)` has LQG pair `(c • mu.map (· / R), b * D(R ·, R ·))` with random `c, b > 0`
 (Proposed inputs LQGMeasureCoordChange and LQGMetricFieldAxioms IV). Its window
count at `w` is the window count of `(mu, D)` at `R w` with the scale index shifted by `k`
(`pinchWindowCount_rescale`, from `pinchPointEvent_dilate_iff`). The windows `[N+1, 2N]` and `[N+1-k, 2N-k]`
differ by at most `k` indices (`ncard_window_shift_sub_le`), so the limit transfers (`tendsto_div_of_abs_sub_le`).
Step 12 (the B_1 window limit for the rescaled pair) is the NAMED HYPOTHESIS `hstep12` of `step13_extend`.
Nothing here is frozen; the Step 12 proof is pending.
-/

namespace HarmonicBalls.Step13

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- The window count `B_N(mu, D; z)`: the number of `n ∈ [N+1, 2N]` with the pinch event at scale `2^{-n}`
about `z` (write-up Step 13; the `Set.ncard` count of Lemma 11.13). -/
noncomputable def pinchWindowCount (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M : ℝ) (N : ℕ)
    (z : ℂ) : ℕ :=
  {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ pinchPointEvent μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard

section Counting

theorem card_filter_le_add_of_sdiff_card_le (Q : ℕ → Prop) [DecidablePred Q] (I J : Finset ℕ) (k : ℕ)
    (h : (I \ J).card ≤ k) : (I.filter Q).card ≤ (J.filter Q).card + k := by
  have h1 := Finset.card_le_card_sdiff_add_card (s := I.filter Q) (t := J.filter Q)
  have h2 : I.filter Q \ J.filter Q ⊆ I \ J := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_filter] at hx ⊢
    exact ⟨hx.1.1, fun hJ => hx.2 ⟨hJ, hx.1.2⟩⟩
  have h3 := Finset.card_le_card h2
  omega

theorem card_Icc_sdiff_upper_le (N k : ℕ) (hk : k ≤ N) :
    (Finset.Icc (N + 1) (2 * N) \ Finset.Icc (N + 1 - k) (2 * N - k)).card ≤ k := by
  have hsub : Finset.Icc (N + 1) (2 * N) \ Finset.Icc (N + 1 - k) (2 * N - k) ⊆
      Finset.Icc (2 * N - k + 1) (2 * N) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hx ⊢
    omega
  have h := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at h
  omega

theorem card_Icc_sdiff_lower_le (N k : ℕ) (hk : k ≤ N) :
    (Finset.Icc (N + 1 - k) (2 * N - k) \ Finset.Icc (N + 1) (2 * N)).card ≤ k := by
  have hsub : Finset.Icc (N + 1 - k) (2 * N - k) \ Finset.Icc (N + 1) (2 * N) ⊆
      Finset.Icc (N + 1 - k) N := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hx ⊢
    omega
  have h := Finset.card_le_card hsub
  simp only [Nat.card_Icc] at h
  omega

theorem card_filter_shift_sub (Q : ℕ → Prop) [DecidablePred Q] (N k : ℕ) (hk : k ≤ N) :
    ((Finset.Icc (N + 1) (2 * N)).filter (fun n => Q (n - k))).card =
      ((Finset.Icc (N + 1 - k) (2 * N - k)).filter Q).card := by
  refine Finset.card_nbij' (fun n => n - k) (fun m => m + k) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨h1, h2⟩, hq⟩ := hn
    exact ⟨⟨by omega, by omega⟩, hq⟩
  · intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Nat.add_sub_cancel] at hm ⊢
    obtain ⟨⟨h1, h2⟩, hq⟩ := hm
    exact ⟨⟨by omega, by omega⟩, hq⟩
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, _⟩, _⟩ := hn
    show n - k + k = n
    omega
  · intro m _
    show m + k - k = m
    omega

theorem ncard_window_eq_card (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard = ((Finset.Icc (N + 1) (2 * N)).filter P).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- Window shift: for `k ≤ N`, the window count of `n ↦ Q (n - k)` over `[N+1, 2N]` (that is, of `Q` over
`[N+1-k, 2N-k]`) and the window count of `Q` over `[N+1, 2N]` differ by at most `k` in each direction. -/
theorem ncard_window_shift_sub_le (Q : ℕ → Prop) (N k : ℕ) (hk : k ≤ N) :
    {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q (n - k)}.ncard ≤ {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard + k ∧
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard ≤ {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q (n - k)}.ncard + k := by
  classical
  have e1 : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q (n - k)}.ncard =
      ((Finset.Icc (N + 1) (2 * N)).filter (fun n => Q (n - k))).card :=
    ncard_window_eq_card (fun n => Q (n - k)) N
  have e2 : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard = ((Finset.Icc (N + 1) (2 * N)).filter Q).card :=
    ncard_window_eq_card Q N
  rw [e1, e2, card_filter_shift_sub Q N k hk]
  have c1 := card_filter_le_add_of_sdiff_card_le Q (Finset.Icc (N + 1 - k) (2 * N - k))
    (Finset.Icc (N + 1) (2 * N)) k (card_Icc_sdiff_lower_le N k hk)
  have c2 := card_filter_le_add_of_sdiff_card_le Q (Finset.Icc (N + 1) (2 * N))
    (Finset.Icc (N + 1 - k) (2 * N - k)) k (card_Icc_sdiff_upper_le N k hk)
  exact ⟨c1, c2⟩

end Counting

section Rescale

theorem real_two_pow_mul_inv_pow {k n : ℕ} (hkn : k ≤ n) :
    (2 : ℝ) ^ k * ((2 : ℝ)⁻¹) ^ n = ((2 : ℝ)⁻¹) ^ (n - k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  have h2 : (2 : ℝ) ^ k * ((2 : ℝ)⁻¹) ^ k = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
  rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, h2, one_mul]

/-- Window count of the rescaled pair at `w` equals the count of `(mu, D)` at `R w` with scale index `n - k`
(write-up Step 13: `E^{h^(R)}_{2^{-n}}(w) <-> E^h_{2^{-(n-k)}}(R w)`), for `R = 2^k` and `k ≤ N`. -/
theorem pinchWindowCount_rescale (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M : ℝ)
    {a b R : ℝ} (ha : 0 < a) (hb : 0 < b) (hR0 : 0 < R) (k N : ℕ) (hR : R = (2 : ℝ) ^ k) (hk : k ≤ N)
    (w : ℂ) :
    pinchWindowCount (ENNReal.ofReal a • μ.map (fun x : ℂ => x / (R : ℂ)))
        (fun u v => b * D ((R : ℂ) * u) ((R : ℂ) * v)) U T Q' Q M N w =
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ (n - k)) ((R : ℂ) * w)}.ncard := by
  unfold pinchWindowCount
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq]
  have hpos : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := fun n => pow_pos (by norm_num) n
  have e : ∀ n : ℕ, k ≤ n → R * ((2 : ℝ)⁻¹ ^ n) = (2 : ℝ)⁻¹ ^ (n - k) := by
    intro n hkn
    rw [hR]
    exact real_two_pow_mul_inv_pow hkn
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have h4 := (pinchPointEvent_dilate_iff μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) w hR0 ha hb (hpos n)).1 h3
    rw [e n (by omega)] at h4
    exact h4
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [← e n (by omega)] at h3
    exact (pinchPointEvent_dilate_iff μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) w hR0 ha hb (hpos n)).2 h3

end Rescale

section Limits

/-- Transfer of a window limit across window counts differing by at most `k` (for large `N`). -/
theorem tendsto_div_of_abs_sub_le {c d : ℕ → ℕ} {p : ℝ} {k : ℕ}
    (hc : Tendsto (fun N : ℕ => (c N : ℝ) / N) atTop (𝓝 p))
    (hcd : ∀ᶠ N : ℕ in atTop, (c N : ℝ) ≤ d N + k ∧ (d N : ℝ) ≤ c N + k) :
    Tendsto (fun N : ℕ => (d N : ℝ) / N) atTop (𝓝 p) := by
  have hdiff : Tendsto (fun N : ℕ => (d N : ℝ) / N - (c N : ℝ) / N) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ))
    filter_upwards [hcd] with N hN
    have habs : |(d N : ℝ) - c N| ≤ k :=
      abs_le.2 ⟨by linarith [hN.1, hN.2], by linarith [hN.1, hN.2]⟩
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
    exact div_le_div_of_nonneg_right habs (Nat.cast_nonneg N)
  have h3 := hc.add hdiff
  rw [add_zero] at h3
  exact Tendsto.congr (fun N => by ring) h3

end Limits

/-- Removing a nonzero constant scalar from an almost-everywhere statement (`ENNReal` is not a domain, so
`Measure.ae_smul_measure_iff` does not apply to the scalar `ENNReal.ofReal a`). -/
theorem ae_of_ae_smul_const {α : Type*} [MeasurableSpace α] (μ : Measure α) {c : ℝ≥0∞} (hc0 : c ≠ 0)
    {p : α → Prop} (h : ∀ᵐ x ∂(c • μ), p x) : ∀ᵐ x ∂μ, p x := by
  rw [ae_iff] at h ⊢
  rw [Measure.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left hc0

/-- **Step 13 (extension to the plane), conditional form.** `μk k` and `Dk k` are the LQG pair of the rescaled
field `h^(2^k)`: almost surely `μk k = c • mu.map (· / 2^k)` and `Dk k = b * D(2^k ·, 2^k ·)` for random
`c, b > 0`. Hypothesis `hstep12` is Step 12 for these pairs: almost surely, for `μk k`-a.e. `w ∈ B_1`, the window
count has limit `p`. Conclusion: almost surely, for `mu`-a.e. `z ∈ ℂ`, the window count of `(mu, D)` at `z` has
limit `p`. Uses the cover `ℂ = ⋃_k B_{2^k}`, countable intersections over `k`, and `ae_of_ae_map` (no
measurability of the windows is needed). -/
theorem step13_extend {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M p : ℝ)
    (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ)
    (hscale : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      μk k ω = ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) ∧
      ∀ u v : ℂ, Dk k ω u v = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v))
    (hstep12 : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), w ∈ ball (0 : ℂ) 1 →
      Tendsto (fun N : ℕ => (pinchWindowCount (μk k ω) (Dk k ω) U T Q' Q M N w : ℝ) / N) atTop (𝓝 p)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω),
      Tendsto (fun N : ℕ => (pinchWindowCount (μ ω) (D ω) U T Q' Q M N z : ℝ) / N) atTop (𝓝 p) := by
  classical
  have key : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
      Tendsto (fun N : ℕ => (pinchWindowCount (μ ω) (D ω) U T Q' Q M N z : ℝ) / N) atTop (𝓝 p) := by
    intro k
    filter_upwards [hscale k, hstep12 k] with ω hsc hst
    obtain ⟨a, b, ha, hb, hμ, hD⟩ := hsc
    have hR0 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hRc : ((((2 : ℝ) ^ k : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
    have hRz : ∀ z : ℂ, ((((2 : ℝ) ^ k : ℝ)) : ℂ) * (z / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) = z :=
      fun z => by field_simp
    have hDfun : Dk k ω = fun u v => b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v) :=
      funext fun u => funext fun v => hD u v
    rw [hμ, hDfun] at hst
    have hst' := ae_of_ae_smul_const _ (ENNReal.ofReal_pos.2 ha).ne' hst
    have hf : AEMeasurable (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) (μ ω) :=
      (continuous_id.div_const _).measurable.aemeasurable
    have h2 := ae_of_ae_map hf hst'
    filter_upwards [h2] with z hz
    intro hzball
    have hzb : z / ((((2 : ℝ) ^ k : ℝ)) : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hR0.le, div_lt_one hR0]
      exact mem_ball_zero_iff.1 hzball
    have hz' := hz hzb
    have hcount : ∀ N : ℕ, k ≤ N →
        pinchWindowCount (ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)))
          (fun u v => b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v))
          U T Q' Q M N (z / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) =
        {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ (n - k)) z}.ncard := by
      intro N hN
      rw [pinchWindowCount_rescale (μ ω) (D ω) U T Q' Q M ha hb hR0 k N rfl hN, hRz z]
    have hc : Tendsto (fun N : ℕ =>
        ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ (n - k)) z}.ncard : ℝ) / N)
        atTop (𝓝 p) :=
      Tendsto.congr' (eventually_atTop.2 ⟨k, fun N hN => by simp only [hcount N hN]⟩) hz'
    have hs : ∀ N : ℕ, k ≤ N →
        {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ (n - k)) z}.ncard ≤
            pinchWindowCount (μ ω) (D ω) U T Q' Q M N z + k ∧
        pinchWindowCount (μ ω) (D ω) U T Q' Q M N z ≤
          {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
            pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ (n - k)) z}.ncard + k :=
      fun N hN => ncard_window_shift_sub_le
        (fun m => pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ m) z) N k hN
    have hcd : ∀ᶠ N : ℕ in atTop,
        ((({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ (n - k)) z}.ncard : ℕ)) : ℝ) ≤
          ((pinchWindowCount (μ ω) (D ω) U T Q' Q M N z : ℕ) : ℝ) + (k : ℝ) ∧
        ((pinchWindowCount (μ ω) (D ω) U T Q' Q M N z : ℕ) : ℝ) ≤
          ((({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ (n - k)) z}.ncard : ℕ)) : ℝ) + (k : ℝ) := by
      refine eventually_atTop.2 ⟨k, fun N hN => ?_⟩
      obtain ⟨s1, s2⟩ := hs N hN
      exact ⟨by exact_mod_cast s1, by exact_mod_cast s2⟩
    exact tendsto_div_of_abs_sub_le hc hcd
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
      Tendsto (fun N : ℕ => (pinchWindowCount (μ ω) (D ω) U T Q' Q M N z : ℝ) / N) atTop (𝓝 p) :=
    ae_all_iff.2 key
  filter_upwards [hall] with ω hω
  have hall2 : ∀ᵐ z ∂(μ ω), ∀ k : ℕ, z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
      Tendsto (fun N : ℕ => (pinchWindowCount (μ ω) (D ω) U T Q' Q M N z : ℝ) / N) atTop (𝓝 p) :=
    ae_all_iff.2 hω
  filter_upwards [hall2] with z hz
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖z‖ (by norm_num : (1 : ℝ) < 2)
  exact hz k (mem_ball_zero_iff.2 hk)

end HarmonicBalls.Step13
