import HarmonicBalls.FirstPass.S11c.Assembly11_7
import HarmonicBalls.FirstPass.S11c.FixedRoot11_7
import HarmonicBalls.FirstPass.S11c.ShiftCM11_7
import HarmonicBalls.FirstPass.S11c.ShiftObs11_7
import HarmonicBalls.FirstPass.S11c.TranslateField11_7
import HarmonicBalls.FirstPass.S11c.CoordRooted11_7
import HarmonicBalls.FirstPass.Frozen.S8d
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# The fixed-root input `hRef` of Lemma 11.7

For each rational disc `k` (centre `c_k`, radii `s_k < t_k`, `U_k = B(c_k, s_k)`, `D_k = B(c_k, t_k)`) this file builds the
kernel `K` and the integer `nD` of `hRef` (Assembly11_7.lean) from the frozen common decoder `LocalLQGDecoderCommonFrozen`
(one kernel for all insertions `α₀ < Q(γ)` and `α₀ = 0`), and proves the fixed-root null section for every `z ∈ U_k`:
the translated field `h(· + z) - h_1(z)` (`isWholePlaneGFF_translate`) has an LQG measure at the origin
(`ae_isLQGLimit_rooted_translate` and the coordinate change), `fixedRoot_null_of_origin` gives the origin window, and the
Cameron-Martin transfer (`campbellRef_absCont_of_CM`) moves it to the Campbell-reference observation.

Frozen inputs: `LocalLQGDecoderCommonFrozen`, `LQGMeasureOfProfileMeasurableFrozen`, `CameronMartinLocallyLipschitzShiftAbsCont`.
Proposed inputs (universal over the probability space): `LQGMeasureCoordChange`, `LQGMeasureExistence`.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

universe u

namespace HarmonicBalls.S11c

/-- The `nD` of a rational disc: for `z` in the inner disc `U_k` and `n ≥ nD`, the closed ball of radius
`6 · 2^{-n}` about `z` lies in the outer disc `D_k` (because `t_k - s_k > 0`). -/
lemma exists_nD_ratDisc (k : RatDiscIdx) :
    ∃ nD : ℕ, ∀ z ∈ ratDiscBall k, ∀ n : ℕ, nD ≤ n → closedBall z (6 * (2 : ℝ)⁻¹ ^ n) ⊆ ratDiscOuter k := by
  have hgap : 0 < (k.1.2.2.2 : ℝ) - (k.1.2.2.1 : ℝ) := sub_pos.mpr (ratDisc_lt k)
  obtain ⟨nD, hnD⟩ := exists_pow_lt_of_lt_one (show 0 < ((k.1.2.2.2 : ℝ) - (k.1.2.2.1 : ℝ)) / 6 by positivity)
    (show (2 : ℝ)⁻¹ < 1 by norm_num)
  refine ⟨nD, fun z hz n hn w hw => ?_⟩
  rw [mem_closedBall] at hw
  unfold ratDiscBall at hz
  rw [mem_ball] at hz
  show w ∈ ball (ratDiscCentre k) (k.1.2.2.2 : ℝ)
  rw [mem_ball]
  have hpow : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ nD := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have h6 : 6 * (2 : ℝ)⁻¹ ^ nD < (k.1.2.2.2 : ℝ) - (k.1.2.2.1 : ℝ) := by
    have := hnD
    linarith
  have htri := dist_triangle w z (ratDiscCentre k)
  linarith

/-- The fixed-root input `hRef` of Lemma 11.7 for all rational discs, from the frozen common decoder, the universal
coordinate-change and existence inputs, and the cone-probability input `hPp` at `(γ, γ, p)`. The threshold of the bad
set is `a = p / 8` (Lemma 11.8 with `p`). -/
theorem hRef_of_decoder {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hDec : LocalLQGDecoderCommonFrozen.{u}) (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hCC : ∀ (γ α₀ : ℝ) (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω')
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ), LQGMeasureCoordChange P' γ α₀ hC' hcirc')
    (hE : ∀ (γ α₀ : ℝ) (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω')
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ), LQGMeasureExistence P' γ α₀ hC' hcirc')
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Q : Set ℂ} (hQ : IsCone Q) {M p : ℝ} (hp : 0 < p) (hPp : ConeBadEventAt.{u} γ γ p Q M)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ k : RatDiscIdx, ∃ K : Kernel ({φ : ℂ → ℝ // IsTestFunction (ratDiscOuter k) φ ∧ ∫ x, φ x = 0} → ℝ) ℂ,
      IsSFiniteKernel K ∧ ∃ nD : ℕ,
        (∀ z ∈ ratDiscBall k, ∀ n : ℕ, nD ≤ n → closedBall z (6 * (2 : ℝ)⁻¹ ^ n) ⊆ ratDiscOuter k) ∧
        (∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
          K (localMeanZeroObs α₀ (ratDiscOuter k) (hC ω)) = c • (μ ω).restrict (ratDiscOuter k)) ∧
        ∀ z ∈ ratDiscBall k, ∫⁻ ω, (localBadSet K Q M (p / 8) (ratDiscBall k) nD).indicator
          (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ (ratDiscOuter k) (hC ω) z) ∂P = 0 := by
  intro k
  have hr : (0 : ℝ) < (k.1.2.2.2 : ℝ) := lt_trans (ratDisc_pos k) (ratDisc_lt k)
  have hlt : (0 : ℝ) < lqgQ γ := lt_trans hγ0 (gamma_lt_lqgQ hγ0 hγ2)
  obtain ⟨K, hK, c1, c2⟩ := hDec γ hγ0 hγ2 (ratDiscCentre k) (k.1.2.2.2 : ℝ) hr
    (zero_not_mem_closedBall_ratDiscOuter k)
  obtain ⟨nD, hnD⟩ := exists_nD_ratDisc k
  refine ⟨K, hK, nD, fun z hz n hn => hnD z hz n hn, c1 α₀ hα Ω P hC hcirc μ hh hμ, fun z hz => ?_⟩
  -- the translated field at `z`, its origin LQG measure, and the rooted measure `μ_z`
  have hW' := isWholePlaneGFF_translate hh z
  obtain ⟨ν, hν⟩ := hE γ γ Ω P (translatedPairing hC hcirc z) (translatedCircle hcirc z) hW' hγ0 hγ2
    (gamma_lt_lqgQ hγ0 hγ2)
  have hCC' := hCC γ γ Ω P (translatedPairing hC hcirc z) (translatedCircle hcirc z)
  have hμz : IsLQGMeasure P γ (fun ω => rootedCircleAverage 0 γ z (hcirc ω))
      (fun ω => ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) • (ν ω).map (fun x => x + z)) :=
    ae_isLQGLimit_rooted_translate hγ0 hγ2 z (fun _ _ _ => rfl) hW' hCC' hν
  have hdec0 := c2 0 hlt z Ω P hC hcirc _ hh hμz
  have h0 := fixedRoot_null_of_origin hDecFrozen hγ0 hγ2 hQ hp hPp z (fun _ _ _ => rfl) hW' hCC' hν hμz
    (D := ratDiscOuter k) (U := ratDiscBall k) measurableSet_ball (hnD z hz) hz hdec0
  obtain ⟨χ, hχ, hcs, hLL⟩ := exists_campbellShift_cut γ α₀ hr (zero_not_mem_closedBall_ratDiscOuter k)
  have := hK
  exact lintegral_localBadSet_campbellRef_eq_zero (measurableSet_of_isCone hQ) measurableSet_ball h0
    (fun S hS h => campbellRef_absCont_of_CM hCM hh χ hχ hLL hcs S hS h)

end HarmonicBalls.S11c
