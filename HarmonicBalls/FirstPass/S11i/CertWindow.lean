import HarmonicBalls.FirstPass.S11i.DilatePinch
import HarmonicBalls.FirstPass.S11i.WindowShift
import HarmonicBalls.FirstPass.S11i.Step13Extend

/-!
# Lemma 11.13, Steps 13-14: from certificate window frequencies to pinch window counts

Write-up `notes/fp-gaps/CHATGPT-n3-step12-gaps.md` section 8, equations (40)-(44), and the corrected proof of
`lemma:mu_h-pinch-bad` (corrected paper lines 3900-3910, the dilation step). Step 12 conclusion (10) is taken as an
explicit hypothesis `hstep12`, stated for a certificate predicate `Cert` (the event `E^{f}_{2^{-n}}(w; M)` of Lemma 11.12
for the rescaled model); the implication `hcert` states that a certificate index forces the actual pinch event.
NEW, deterministic: no LQG input. The rescaling hypotheses `hscale` are those of `HarmonicBalls.Step13.step13_extend`.
-/

namespace HarmonicBalls.CertWindow

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Window lower bound from a certificate frequency (write-up (41)-(43)). If the window frequency of `cert` on `(N, 2N]`
tends to `q > 0`, and every shifted certificate index `n + k` forces the predicate `Pn n`, then eventually
`q N / 4 <= #{n in (N, 2N] : Pn n}`. -/
theorem eventually_window_of_cert_freq (Pn cert : ℕ → Prop) (k : ℕ) (himp : ∀ n, cert (n + k) → Pn n) {q : ℝ}
    (hq : 0 < q)
    (hfreq : Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ cert n}.ncard : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    ∀ᶠ N : ℕ in atTop, q / 4 * (N : ℝ) ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Pn n}.ncard : ℝ) := by
  have hlow : ∀ᶠ N : ℕ in atTop,
      q / 2 * (N : ℝ) ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ cert n}.ncard : ℝ) := by
    filter_upwards [hfreq.eventually (lt_mem_nhds (by linarith : q / 2 < q))] with N hN
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp only [Nat.cast_zero, div_zero] at hN
      linarith
    · have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
      rw [lt_div_iff₀ hNr] at hN
      linarith
  have hgrow : ∀ᶠ N : ℕ in atTop, 4 * (k : ℝ) / q ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hlow, hgrow] with N hN hN'
  have h4 : 4 * (k : ℝ) ≤ q * N := by
    have := (div_le_iff₀ hq).1 hN'
    linarith [mul_comm (N : ℝ) q]
  have hsh := FirstPassS11i.ncard_window_shift_le cert k N
  have hfinP : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Pn n}.Finite :=
    (Set.finite_Icc (N + 1) (2 * N)).subset fun n hn => ⟨hn.1, hn.2.1⟩
  have hsub : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ cert (n + k)} ⊆ {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Pn n} :=
    fun n hn => ⟨hn.1, hn.2.1, himp n hn.2.2⟩
  have hcard : (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ cert (n + k)}.ncard : ℕ) : ℝ) ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Pn n}.ncard : ℝ) :=
    Nat.cast_le.mpr (Set.ncard_le_ncard hsub hfinP)
  linarith

/-- **Steps 13-14 (conditional form, write-up section 8).** `μk k` and `Dk k` are the LQG pair of the rescaled model at
scale `2^k`: almost surely `μk k = c • μ.map (· / 2^k)` and `Dk k = b * D(2^k ·, 2^k ·)` (the shape of
`step13_extend`). `hcert`: a certificate index of the rescaled model forces the actual pinch event at the rescaled
point. `hstep12`: the certificate window frequency tends to `q` for `μk`-almost every `w` in the unit ball (Step 12,
conclusion (10)). Conclusion: almost surely, for `μ`-almost every `z`, eventually `q N / 4` is at most the number of
pinch-window indices at `z`. -/
theorem pinch_window_ae_of_cert {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M q : ℝ) (hq : 0 < q)
    (Cert : ℕ → Ω → ℕ → ℂ → Prop)
    (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ)
    (hscale : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      μk k ω = ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) ∧
      ∀ u v : ℂ, Dk k ω u v = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v))
    (hcert : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ w : ℂ, Cert k ω n w →
      pinchPointEvent (μk k ω) (Dk k ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) w)
    (hstep12 : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), w ∈ ball (0 : ℂ) 1 →
      Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Cert k ω n w}.ncard : ℝ) / (N : ℝ))
        atTop (𝓝 q)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N : ℕ in atTop,
      q / 4 * (N : ℝ) ≤
        ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  have key : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
      ∀ᶠ N : ℕ in atTop, q / 4 * (N : ℝ) ≤
        ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
    intro k
    filter_upwards [hscale k, hcert k, hstep12 k] with ω hsc hcc hst
    obtain ⟨a, b, ha, hb, hμ, hD⟩ := hsc
    set R : ℝ := (2 : ℝ) ^ k with hRdef
    have hR0 : (0 : ℝ) < R := by positivity
    have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
    have hDfun : Dk k ω = fun u v => b * D ω ((R : ℂ) * u) ((R : ℂ) * v) :=
      funext fun u => funext fun v => hD u v
    rw [hμ, hDfun] at hcc
    rw [hμ] at hst
    -- transport the certificate frequency from `μk`-a.e. `w` in the unit ball to `μ`-a.e. `z`
    have hae : ∀ᵐ z ∂(μ ω), z / (R : ℂ) ∈ ball (0 : ℂ) 1 →
        Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Cert k ω n (z / (R : ℂ))}.ncard : ℝ) / (N : ℝ))
          atTop (𝓝 q) := by
      have h1 := HarmonicBalls.Step13.ae_of_ae_smul_const _ (ENNReal.ofReal_pos.2 ha).ne' hst
      exact ae_of_ae_map (by fun_prop : Continuous fun x : ℂ => x / (R : ℂ)).aemeasurable h1
    filter_upwards [hae] with z hz hzR
    have hw : z / (R : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff] at hzR ⊢
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR0.le, div_lt_one hR0]
      exact hzR
    refine eventually_window_of_cert_freq
      (fun n => pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z)
      (fun n => Cert k ω n (z / (R : ℂ))) k ?_ hq (hz hw)
    intro n hn
    -- write-up (40): dilation identity for the pinch event, with `R * 2^{-(n+k)} = 2^{-n}` and `R * (z / R) = z`
    have hdil := HarmonicBalls.pinchPointEvent_dilate_iff (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ (n + k))
      (z / (R : ℂ)) hR0 ha hb (by positivity)
    have e1 : R * ((2 : ℝ)⁻¹ ^ (n + k)) = (2 : ℝ)⁻¹ ^ n := by
      have hk1 : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
      rw [hRdef, pow_add]
      linear_combination ((2 : ℝ)⁻¹ ^ n) * hk1
    have e2 : (R : ℂ) * (z / (R : ℂ)) = z := by
      field_simp
    rw [e1, e2] at hdil
    exact hdil.1 (hcc (n + k) (z / (R : ℂ)) hn)
  filter_upwards [ae_all_iff.2 key] with ω hω
  filter_upwards [ae_all_iff.2 hω] with z hz
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖z‖ (by norm_num : (1 : ℝ) < 2)
  exact hz k (mem_ball_zero_iff.2 hk)

end HarmonicBalls.CertWindow
