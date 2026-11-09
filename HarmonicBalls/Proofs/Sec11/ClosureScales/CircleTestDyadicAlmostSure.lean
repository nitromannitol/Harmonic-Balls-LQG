import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Notation
import HarmonicBalls.Proofs.Sec2.PolyHighProb
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestIntegralL2Limit
import HarmonicBalls.Proofs.Sec11.ClosureScales.SmoothCircleAverageRate

/-!
# Almost-sure convergence of the dyadic circle-test integrals

Source. `notes/sec11-proof/sec11-proof-r10.tex`, lines 1046-1061 (audited CORRECT): for a test function `φ` the limit
`lim_{n→∞} ∫ c(2^{-n}, z) φ(z) d²z` is read off the field, and "this identity follows first in `L²` from the joint Gaussian
covariance formula and then almost surely for our countable family of tests and radii".

Main results. `Ω : Type u` is arbitrary and `P` is any measure with `IsWholePlaneGFF P hC hcirc`; no canonical sample
space and no samplewise linearity of `hC` are assumed.
* `ae_tendsto_circleTestIntegral_dyadicScale`: for each `φ` with `IsTestFunction Set.univ φ`, almost surely
  `∫ w, hcirc ω (dyadicScale n) w * φ w → hC ω φ` as `n → ∞`.
* `ae_tendsto_circleTestIntegral_two_zpow`: the same statement with the radius written as `(2 : ℝ) ^ (-(n : ℤ))`.
* `exists_measurable_conull_tendsto_circleTestIntegral_two_zpow`: for a countable family `φ i` of test functions (the
  family is fixed first, the event second, all indices third), a measurable event of full measure on which the
  convergence holds for every `i`.

Route. The mean-square rate `E[(∫ hcirc_r φ - hC φ)²] ≤ C r²` for `0 < r ≤ 1`
(`SmoothCircleAverageRate.exists_second_moment_circleTestIntegral_le`, with `C` depending only on `φ`) and Chebyshev's
inequality for the square give `P{|X_r| ≥ ε} ≤ C r² / ε²`. So the events `{|X_r| < ε}` occur with polynomially high
probability as `r → 0` (`PolyHighProb`, `Defs/Notation.lean`, exponent `p = 2`). The Borel-Cantelli statement along the
dyadic scales, `PolyHighProb.ae_eventually_dyadic` (`Proofs/Sec2/PolyHighProb.lean`), gives `|X_{2^{-n}}| < ε` for all
large `n`, almost surely, for each `ε > 0`. Countably many `ε = 1/(k+1)` give `X_{2^{-n}} → 0` almost surely. For a
countable family, `ae_all_iff` and a measurable conull superset of the exceptional set
(`exists_measurable_superset_of_null`) give the measurable event.

Dyadic index. `dyadicScale k = (2⁻¹)^k = 2^{-k}` (`Defs/LQG.lean`) has no index offset; `dyadicScale_eq_zpow` identifies
it with the literal `2^{-n}`. Only the radii `r < 1` enter the Borel-Cantelli step, which does not affect the limit.
-/

universe u

namespace HarmonicBalls

namespace CircleTestDyadicAlmostSure

open MeasureTheory Filter Topology Set
open scoped ENNReal

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The project's dyadic radius `dyadicScale n = (2⁻¹)^n` is the integer power `2^{-n}` (no index offset). -/
lemma dyadicScale_eq_zpow (n : ℕ) : dyadicScale n = (2 : ℝ) ^ (-(n : ℤ)) := by
  simp [dyadicScale, zpow_neg, inv_pow]

/-- **Chebyshev's inequality for the square.** For a probability measure `P` and `g` with integrable square,
`P {ε ≤ |g|} ≤ K / ε²` whenever `E[g²] ≤ K` and `ε > 0`. The set need not be measurable (outer measure). -/
lemma measure_abs_ge_le_div_sq {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → ℝ}
    (hg : Integrable (fun ω => g ω ^ 2) P) {ε K : ℝ} (hε : 0 < ε) (hK : ∫ ω, g ω ^ 2 ∂P ≤ K) :
    P {ω | ε ≤ |g ω|} ≤ ENNReal.ofReal (K / ε ^ 2) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := fun ω => g ω ^ 2)
    (Filter.Eventually.of_forall fun ω => sq_nonneg (g ω)) hg (ε ^ 2)
  have hsub : {ω | ε ≤ |g ω|} ⊆ {ω | ε ^ 2 ≤ g ω ^ 2} := by
    intro ω hω
    have h1 : ε ^ 2 ≤ |g ω| ^ 2 := pow_le_pow_left₀ hε.le hω 2
    rwa [sq_abs] at h1
  have hsq : ε ^ 2 * P.real {ω | ε ^ 2 ≤ g ω ^ 2} ≤ K := hmarkov.trans hK
  have hmono : P.real {ω | ε ≤ |g ω|} ≤ P.real {ω | ε ^ 2 ≤ g ω ^ 2} := measureReal_mono hsub
  have hreal : P.real {ω | ε ≤ |g ω|} ≤ K / ε ^ 2 := by
    rw [le_div_iff₀ (pow_pos hε 2)]
    have h2 := mul_le_mul_of_nonneg_left hmono (pow_pos hε 2).le
    linarith
  calc P {ω | ε ≤ |g ω|}
      = ENNReal.ofReal (P.real {ω | ε ≤ |g ω|}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
    _ ≤ ENNReal.ofReal (K / ε ^ 2) := ENNReal.ofReal_le_ofReal hreal

/-- **Polynomially high probability of the radial errors.** Let `G r ω` be the error `∫ hcirc_r φ - hC φ` at radius `r`.
If `E[G r ²] ≤ C r²` for `0 < r < 1`, then for each `ε > 0` the events `{|G r| < ε}` occur with polynomially high
probability as `r → 0`, with exponent `p = 2` and constant `C / ε²` (`PolyHighProb`). -/
lemma polyHighProb_abs_lt_of_sq_integral_le {P : Measure Ω} [IsProbabilityMeasure P] {G : ℝ → Ω → ℝ} {C : ℝ}
    (hint : ∀ r : ℝ, 0 < r → r < 1 → Integrable (fun ω => G r ω ^ 2) P)
    (hbd : ∀ r : ℝ, 0 < r → r < 1 → ∫ ω, G r ω ^ 2 ∂P ≤ C * r ^ 2) {ε : ℝ} (hε : 0 < ε) :
    PolyHighProb P (fun r => {ω | |G r ω| < ε}) := by
  unfold PolyHighProb
  refine ⟨2, two_pos, C / ε ^ 2, 1, one_pos, fun r hr hr1 => ?_⟩
  have hset : {ω | |G r ω| < ε}ᶜ = {ω | ε ≤ |G r ω|} := by
    ext ω
    show ¬ (|G r ω| < ε) ↔ ε ≤ |G r ω|
    exact not_lt
  have hbound := measure_abs_ge_le_div_sq (hint r hr hr1) hε (hbd r hr hr1)
  have hr2 : C / ε ^ 2 * r ^ (2 : ℝ) = C * r ^ 2 / ε ^ 2 := by
    rw [Real.rpow_two]
    ring
  show P {ω | |G r ω| < ε}ᶜ ≤ ENNReal.ofReal (C / ε ^ 2 * r ^ (2 : ℝ))
  rw [hset, hr2]
  exact hbound

/-- **Almost-sure convergence along the dyadic scales.** Under the hypotheses of
`polyHighProb_abs_lt_of_sq_integral_le`, almost surely `G (2^{-n}) ω → 0` as `n → ∞`. -/
lemma ae_tendsto_zero_dyadic_of_sq_integral_le {P : Measure Ω} [IsProbabilityMeasure P] {G : ℝ → Ω → ℝ} {C : ℝ}
    (hint : ∀ r : ℝ, 0 < r → r < 1 → Integrable (fun ω => G r ω ^ 2) P)
    (hbd : ∀ r : ℝ, 0 < r → r < 1 → ∫ ω, G r ω ^ 2 ∂P ≤ C * r ^ 2) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => G (dyadicScale n) ω) atTop (𝓝 0) := by
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, |G (dyadicScale n) ω| < 1 / ((k : ℝ) + 1) := by
    refine ae_all_iff.2 fun k => ?_
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    filter_upwards [(polyHighProb_abs_lt_of_sq_integral_le hint hbd hε).ae_eventually_dyadic] with ω hω
    exact hω
  filter_upwards [hall] with ω hω
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω k] with n hn
  rw [Real.dist_eq, sub_zero]
  exact lt_trans hn hk

/-- **Almost-sure convergence of the dyadic circle-test integrals.** For every whole-plane Gaussian free field
`IsWholePlaneGFF P hC hcirc` on an arbitrary `Ω : Type u` and every test function `φ` on `ℂ`, almost surely
`∫ w, hcirc ω (dyadicScale n) w * φ w → hC ω φ` as `n → ∞` (paper, sec11-proof-r10.tex lines 1046-1061). -/
theorem ae_tendsto_circleTestIntegral_dyadicScale {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ w, hcirc ω (dyadicScale n) w * φ w) atTop (𝓝 (hC ω φ)) := by
  have : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨C, -, hsec⟩ := SmoothCircleAverageRate.exists_second_moment_circleTestIntegral_le.{u} hφ
  have hint : ∀ r : ℝ, 0 < r → r < 1 →
      Integrable (fun ω => ((∫ w, hcirc ω r w * φ w) - hC ω φ) ^ 2) P := fun r hr hr1 =>
    (hgff.memLp_circleTestIntegral_sub hφ hr hr1.le).integrable_sq
  have hbd : ∀ r : ℝ, 0 < r → r < 1 →
      ∫ ω, ((∫ w, hcirc ω r w * φ w) - hC ω φ) ^ 2 ∂P ≤ C * r ^ 2 := fun r hr hr1 =>
    hsec Ω P hC hcirc hgff r hr hr1.le
  filter_upwards [ae_tendsto_zero_dyadic_of_sq_integral_le
    (G := fun r ω => (∫ w, hcirc ω r w * φ w) - hC ω φ) hint hbd] with ω hω
  have h2 : Tendsto (fun n : ℕ => (∫ w, hcirc ω (dyadicScale n) w * φ w) - hC ω φ) atTop (𝓝 0) := hω
  exact tendsto_sub_nhds_zero_iff.1 h2

/-- **The same almost-sure limit with the literal radii `2^{-n}`** (`(2 : ℝ) ^ (-(n : ℤ))`). -/
theorem ae_tendsto_circleTestIntegral_two_zpow {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction Set.univ φ) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ w, hcirc ω ((2 : ℝ) ^ (-(n : ℤ))) w * φ w) atTop (𝓝 (hC ω φ)) := by
  filter_upwards [ae_tendsto_circleTestIntegral_dyadicScale hgff hφ] with ω hω
  simp only [dyadicScale_eq_zpow] at hω
  exact hω

/-- **Countable family, one measurable conull event.** For a countable family `φ i` of test functions on `ℂ` (fixed
first), there is a measurable event `E` of full measure (second) on which, for every index `i` (third), the literal
integrals `∫ w, hcirc ω (2^{-n}) w * φ i w` converge to `hC ω (φ i)` as `n → ∞`. -/
theorem exists_measurable_conull_tendsto_circleTestIntegral_two_zpow {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {ι : Type*} [Countable ι] (φ : ι → ℂ → ℝ) (hφ : ∀ i, IsTestFunction Set.univ (φ i)) :
    ∃ E : Set Ω, MeasurableSet E ∧ P Eᶜ = 0 ∧
      ∀ ω ∈ E, ∀ i : ι,
        Tendsto (fun n : ℕ => ∫ w, hcirc ω ((2 : ℝ) ^ (-(n : ℤ))) w * φ i w) atTop (𝓝 (hC ω (φ i))) := by
  have h : ∀ᵐ ω ∂P, ∀ i : ι,
      Tendsto (fun n : ℕ => ∫ w, hcirc ω ((2 : ℝ) ^ (-(n : ℤ))) w * φ i w) atTop (𝓝 (hC ω (φ i))) :=
    ae_all_iff.2 fun i => ae_tendsto_circleTestIntegral_two_zpow hgff (hφ i)
  obtain ⟨t, hsub, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  refine ⟨tᶜ, htm.compl, by rw [compl_compl]; exact ht0, fun ω hω i => ?_⟩
  by_contra hn
  exact hω (hsub fun hall => hn (hall i))

end CircleTestDyadicAlmostSure

end HarmonicBalls
