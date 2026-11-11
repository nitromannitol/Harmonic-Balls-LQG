import HarmonicBalls.FirstPass.S11c.FixedRootNull11_7
import HarmonicBalls.FirstPass.S11c.CoordRooted11_7
import HarmonicBalls.FirstPass.S11c.Origin11_7
import HarmonicBalls.FirstPass.S8d.ProfileVersion
import HarmonicBalls.FirstPass.Frozen.S8d
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.Draft.Section11

/-!
# Lemma 11.7, the fixed-root null section on the origin route (assembled)

Inputs (all explicit):
* `LQGMeasureOfProfileMeasurableFrozen`;
* `ConeBadEventAt γ γ p Q M`: the body of Draft Lemma 11.8 (`ConeBadEventProbabilityStmt`, Draft/Section11.lean:186,
  `lemma:positive-probability`, corrected paper lines 2903-2908) at one fixed constant `p`, insertion `α₀ = γ`. It is used at
  `z = 0` only, and its proof (paper lines 2903-2934) does not cite Lemma 11.7 (`lemma:mu_h-bad-and-harnack`, line 2896), so
  it is admissible as a hypothesis. The constant `p` is passed in, so that one `p` serves all discs and
  all `Ω` (the Draft requires `δ` fixed before `Ω`);
* the whole-plane GFF `hW'` of the translated field (`WholePlaneGFFAffineInvariance`, Proposed; pending approval);
* the coordinate change `LQGMeasureCoordChange` (Proposed, approved as hypothesis);
* the decoder identity `hdec0` for the rooted observation at insertion `0` (the decoder kernel `K` is supplied by the caller, the decision on its α₀-dependence, is not made here).
-/

universe u

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- The body of Draft Lemma 11.8 (`ConeBadEventProbabilityStmt`, Draft/Section11.lean:186) at a fixed constant `p`, insertion
`α₀` and cone `Q`, mass `M`: for every `z` there is `N` such that for `n ≥ N` with `2^{-n}/100 < dist(𝔸_{2^{-n},6·2^{-n}}(z), 0)`
the event `G̃_n(z; M, Q)` (coneMassEvent) contains a measurable event of probability at least `p`. -/
def ConeBadEventAt (γ α₀ p : ℝ) (Q : Set ℂ) (M : ℝ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ z : ℂ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (2 : ℝ)⁻¹ ^ n / 100 < infDist (0 : ℂ) (annulus z ((2 : ℝ)⁻¹ ^ n) (6 * (2 : ℝ)⁻¹ ^ n)) →
    ∃ A ⊆ {ω | coneMassEvent (μ ω) Q M ((2 : ℝ)⁻¹ ^ n) z}, MeasurableSet A ∧ ENNReal.ofReal p ≤ P A

/-- The annulus `annulus 0 r (6r)` lies outside `closedBall 0 r`, so `infDist 0 _ ≥ r > r/100` (Metric.le_infDist). This is
the distance condition of Lemma 11.8 at `z = 0`. -/
lemma infDist_zero_annulus_gt {r : ℝ} (hr : 0 < r) :
    r / 100 < infDist (0 : ℂ) (annulus 0 r (6 * r)) := by
  have h2 : ‖((2 * r : ℝ) : ℂ)‖ = 2 * r := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hne : (annulus 0 r (6 * r)).Nonempty := by
    refine ⟨((2 * r : ℝ) : ℂ), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, h2]
      linarith
    · rw [Metric.mem_closedBall, dist_zero_right, h2, not_le]
      linarith
  have hle : r ≤ infDist (0 : ℂ) (annulus 0 r (6 * r)) := by
    refine (Metric.le_infDist hne).mpr fun y hy => ?_
    have hy2 := hy.2
    rw [Metric.mem_closedBall, not_le] at hy2
    rw [dist_comm]
    exact hy2.le
  linarith

open Classical in
/-- **Origin window for the translated field (Lemma 11.7 origin statement, Origin11_7.lean:192, with the profile
framework).** For the γ-LQG measure `ν` of the translated whole-plane GFF `hcirc'` at insertion `γ`, almost surely, for all
large `N`, the cone event holds at the shifted scales `2^{-(N₀+n)}`, `n ∈ [N+1, 2N]`, for at least `p N / 4` indices. The
constant `p > 0` and the Lemma 11.8 body `hPp` are the same for every `Ω`, disc and root. -/
theorem origin_window_of_translate {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    {γ : ℝ} {Q : Set ℂ} (hQ : IsCone Q) {M : ℝ}
    {p : ℝ} (hp : 0 < p) (hPp : ConeBadEventAt.{u} γ γ p Q M)
    {hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc' : Ω → ℝ → ℂ → ℝ} (hW' : IsWholePlaneGFF P hC' hcirc')
    {ν : Ω → Measure ℂ} (hν : IsLQGMeasureOfField P γ γ hcirc' ν) :
    ∃ N0 : ℕ, ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      p / 4 * (N : ℝ) ≤ (((Finset.Icc (N + 1) (2 * N)).filter
        (fun n : ℕ => coneMassEvent (ν ω) Q M (dyadicScale (N0 + n)) 0)).card : ℝ) := by
  obtain ⟨N0, hN0⟩ := hPp Ω P hC' hcirc' ν hW' hν 0
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ N0 := pow_pos (by norm_num) N0
  obtain ⟨A, hAsub, -, hPA⟩ := hN0 N0 le_rfl (infDist_zero_annulus_gt hr)
  obtain ⟨F, hFm, -, hversion⟩ := hW'.exists_measurable_continuous_circle_version_univ
  obtain ⟨Dec, hDecM, hμD, hlim⟩ := hDecFrozen Ω P γ γ hC' hcirc' ν F hW' hν hFm hversion
  exact ⟨N0, origin_window_visits hW' hQ hFm hversion hDecM hμD hlim N0 hp hAsub hPA⟩

/-- **Fixed-root null section on the origin route.** Assume the translated field `hcirc'` is a whole-plane GFF with
the coordinate change, `ν` is its γ-LQG measure, `μz` is the γ-LQG measure of the rooted profile at `z` (insertion `0`), and
the decoder identity holds for the rooted observation. Then, for the constant `p` of Lemma 11.8 and `δ = p/8`, the rooted
observation at `z` is almost surely outside the local bad set `localBadSet K Q M (p/8) U nD` (BadSetMeasurable11_7.lean:43). -/
theorem fixedRoot_null_of_origin {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Q : Set ℂ} (hQ : IsCone Q) {M : ℝ}
    {p : ℝ} (hp : 0 < p) (hPp : ConeBadEventAt.{u} γ γ p Q M)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ} (z : ℂ)
    (hcirc'_eq : ∀ ω r x, hcirc' ω r x = hcirc ω r (x + z) - hcirc ω 1 z)
    {hC' : Ω → (ℂ → ℝ) → ℝ} (hW' : IsWholePlaneGFF P hC' hcirc')
    (hCC : LQGMeasureCoordChange P γ γ hC' hcirc')
    {ν : Ω → Measure ℂ} (hν : IsLQGMeasureOfField P γ γ hcirc' ν)
    {μz : Ω → Measure ℂ} (hμz : IsLQGMeasure P γ (fun ω => rootedCircleAverage 0 γ z (hcirc ω)) μz)
    {D U : Set ℂ} (hDm : MeasurableSet D) {nD : ℕ}
    (hD : ∀ n : ℕ, nD ≤ n → Metric.closedBall z (6 * (2 : ℝ)⁻¹ ^ n) ⊆ D) (hzU : z ∈ U)
    {K : ProbabilityTheory.Kernel ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ) ℂ}
    (hdec0 : ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
      K (rootedMeanZeroObs 0 γ D z (hC ω)) = c • (μz ω).restrict D) :
    ∀ᵐ ω ∂P, (z, rootedMeanZeroObs 0 γ D z (hC ω)) ∉ localBadSet K Q M (p / 8) U nD := by
  obtain ⟨N0, hOrig⟩ := origin_window_of_translate hDecFrozen hQ hp hPp hW' hν
  have hμ := ae_rootedMeasure_eq_translate hγ0 hγ2 z hcirc'_eq hW' hCC hν hμz
  have hc' : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) ≠ 0 ∧
      ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) ≠ ⊤ :=
    ae_of_all _ fun ω => ⟨(ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne', ENNReal.ofReal_ne_top⟩
  exact ae_not_mem_localBadSet_of_origin hp.le hDm hD hzU hdec0 hμ hc' N0 hOrig

end HarmonicBalls.S11c
