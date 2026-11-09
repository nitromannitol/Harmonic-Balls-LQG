import HarmonicBalls.FirstPass.S11c.FixedRootNull11_7
import HarmonicBalls.FirstPass.S11c.CoordRooted11_7
import HarmonicBalls.FirstPass.S11c.Origin11_7
import HarmonicBalls.FirstPass.S8d.ProfileVersion
import HarmonicBalls.FirstPass.Frozen.S8d
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.Draft.Section11

/-!
# Lemma 11.7, the fixed-root null section on the origin route (B2 (5.1), assembled)

Inputs (all explicit):
* `LQGMeasureOfProfileMeasurableFrozen` (FirstPass/Frozen/S8d.lean:28, approved for this task, decision 2026-11-09 20:14);
* `ConeBadEventProbabilityStmt` (Draft Lemma 11.8, `lemma:positive-probability`, corrected paper lines 2903-2908), used at
  `z = 0` only. Its proof (paper lines 2903-2934) does not cite Lemma 11.7 (`lemma:mu_h-bad-and-harnack`, line 2896), so it is
  admissible as a hypothesis (operator decision 4);
* the whole-plane GFF `hW'` of the translated field (`WholePlaneGFFAffineInvariance`, Proposed; pending operator approval);
* the coordinate change `LQGMeasureCoordChange` (Proposed; approved as hypothesis, decision N3);
* the decoder identity `hdec0` for the rooted observation at insertion `0` (the decoder kernel `K` is supplied by the caller;
  the decision on its α₀-dependence, G1 of notes/n1.md, is not made here).
-/

universe u

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- The annulus `annulus 0 r (6r)` lies outside `closedBall 0 r`, so `infDist 0 _ ≥ r > r/100` (Metric.le_infDist). This is
the distance condition of Draft Lemma 11.8 at `z = 0` (`ConeBadEventProbabilityStmt`, Draft/Section11.lean). -/
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
framework).** For the γ-LQG measure `ν` of the translated whole-plane GFF `hcirc'` at insertion `γ`, there is a constant
`p > 0` (that of Draft Lemma 11.8 at `(γ, γ, Q, M)`) and an index `N₀` such that almost surely, for all large `N`, the cone
event holds at the shifted scales `2^{-(N₀+n)}`, `n ∈ [N+1, 2N]`, for at least `p N / 4` indices. -/
theorem origin_window_of_translate {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hP : ConeBadEventProbabilityStmt.{u})
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Q : Set ℂ} (hQ : IsCone Q) {M : ℝ} (hM : 0 < M)
    {hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc' : Ω → ℝ → ℂ → ℝ} (hW' : IsWholePlaneGFF P hC' hcirc')
    {ν : Ω → Measure ℂ} (hν : IsLQGMeasureOfField P γ γ hcirc' ν) :
    ∃ N0 : ℕ, ∃ p : ℝ, 0 < p ∧ ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      p / 4 * (N : ℝ) ≤ (((Finset.Icc (N + 1) (2 * N)).filter
        (fun n : ℕ => coneMassEvent (ν ω) Q M (dyadicScale (N0 + n)) 0)).card : ℝ) := by
  obtain ⟨p, hpI, hPall⟩ := hP γ γ hγ0 hγ2 (gamma_lt_lqgQ hγ0 hγ2) Q hQ M hM
  obtain ⟨N0, hN0⟩ := hPall Ω P hC' hcirc' ν hW' hν 0
  have hr : (0 : ℝ) < (2 : ℝ)⁻¹ ^ N0 := pow_pos (by norm_num) N0
  obtain ⟨A, hAsub, -, hPA⟩ := hN0 N0 le_rfl (infDist_zero_annulus_gt hr)
  obtain ⟨F, hFm, -, hversion⟩ := hW'.exists_measurable_continuous_circle_version_univ
  obtain ⟨Dec, hDecM, hμD, hlim⟩ := hDecFrozen Ω P γ γ hC' hcirc' ν F hW' hν hFm hversion
  exact ⟨N0, p, hpI.1, origin_window_visits hW' hQ hFm hversion hDecM hμD hlim N0 hpI.1 hAsub hPA⟩

/-- **Fixed-root null section on the origin route (B2 (5.1)).** Assume the translated field `hcirc'` is a whole-plane GFF with
the coordinate change, `ν` is its γ-LQG measure, `μz` is the γ-LQG measure of the rooted profile at `z` (insertion `0`), and
the decoder identity holds for the rooted observation. Then there is `δ = p/8 > 0` with `(z, rooted observation)` almost
surely outside the local bad set `localBadSet K Q M δ U nD` (BadSetMeasurable11_7.lean:43). -/
theorem fixedRoot_null_of_origin {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hP : ConeBadEventProbabilityStmt.{u})
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Q : Set ℂ} (hQ : IsCone Q) {M : ℝ} (hM : 0 < M)
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
    ∃ p : ℝ, 0 < p ∧ ∀ᵐ ω ∂P,
      (z, rootedMeanZeroObs 0 γ D z (hC ω)) ∉ localBadSet K Q M (p / 8) U nD := by
  obtain ⟨N0, p, hp, hOrig⟩ := origin_window_of_translate hDecFrozen hP hγ0 hγ2 hQ hM hW' hν
  have hμ := ae_rootedMeasure_eq_translate hγ0 hγ2 z hcirc'_eq hW' hCC hν hμz
  have hc' : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) ≠ 0 ∧
      ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) ≠ ⊤ :=
    ae_of_all _ fun ω => ⟨(ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne', ENNReal.ofReal_ne_top⟩
  exact ⟨p, hp, ae_not_mem_localBadSet_of_origin hp.le hDm hD hzU hdec0 hμ hc' N0 hOrig⟩

end HarmonicBalls.S11c
