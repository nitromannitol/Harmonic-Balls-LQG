import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# The minimum principle on discs and the Poisson integral of a disc

Generic potential theory in the plane used by Appendix A (sec:obstacle-appendix) of the corrected draft of
Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), in the proof of
Lemma A.1 (lemma:appendix-basic-properties, line 3589). Classical references: Armitage and Gardiner, *Classical
potential theory* (AG01), Chapters 1 and 3.

Superharmonicity is expressed here through explicit predicates (lower semicontinuity and the super-mean-value
inequality on circles), so that this file depends on Mathlib only.

## Main results

* `nonneg_of_lowerSemicontinuousOn_of_superMean`: the **minimum principle** on a disc `B_R(c)` for a lower
  semicontinuous function with the local super-mean-value property whose lower limits at `∂B_R(c)` are `≥ 0`
  (AG01 Thm 3.2.2 / Cor 3.2.3 for discs).
-/

namespace HarmonicBalls

open Complex Metric Real Filter Topology Set MeasureTheory InnerProductSpace

/-! ## The minimum principle on discs -/

/-- The circle average of `y ↦ ‖y - c‖²` over `∂B_r(x)` is `‖x - c‖² + r²`. -/
theorem circleAverage_norm_sub_sq (c x : ℂ) (r : ℝ) :
    Real.circleAverage (fun y => ‖y - c‖ ^ 2) x r = ‖x - c‖ ^ 2 + r ^ 2 := by
  set a : ℂ := x - c
  have hh : HarmonicOnNhd (fun y : ℂ => (starRingEnd ℂ a * (y - x)).re) (closedBall x |r|) := fun y _ =>
    AnalyticAt.harmonicAt_re (by fun_prop)
  have hmean := InnerProductSpace.HarmonicOnNhd.circleAverage_eq hh
  simp only [sub_self, mul_zero, zero_re] at hmean
  have hcont : Continuous fun y : ℂ => (starRingEnd ℂ a * (y - x)).re := by fun_prop
  have hci : CircleIntegrable (fun y : ℂ => (starRingEnd ℂ a * (y - x)).re) x r :=
    hcont.continuousOn.circleIntegrable'
  have hci' : CircleIntegrable (fun _ : ℂ => ‖a‖ ^ 2 + r ^ 2) x r :=
    continuousOn_const.circleIntegrable'
  have heq : EqOn (fun y => ‖y - c‖ ^ 2)
      (fun y => (‖a‖ ^ 2 + r ^ 2) + (2 : ℝ) • (starRingEnd ℂ a * (y - x)).re) (sphere x |r|) := by
    intro y hy
    have hyr : ‖y - x‖ = |r| := by simpa [dist_eq_norm] using hy
    have hsplit : y - c = (y - x) + a := by simp [a]
    simp only [smul_eq_mul]
    rw [hsplit, ← Complex.normSq_eq_norm_sq, Complex.normSq_add, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hyr, sq_abs]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [circleAverage_congr_sphere heq, circleAverage_fun_add hci'
    ((by fun_prop : Continuous fun y : ℂ => (2 : ℝ) • (starRingEnd ℂ a * (y - x)).re).continuousOn.circleIntegrable'),
    circleAverage_const, circleAverage_fun_smul, hmean]
  simp [a]

/-- **Minimum principle on a disc** (AG01 Thm 3.2.2 and Cor 3.2.3, for the disc `B_R(c)`). Let `v` be lower
semicontinuous on `B_R(c)`, with the local super-mean-value property (`M(v; x, r) ≤ v(x)` for all small `r`), and
with `liminf_{y → ξ, y ∈ B_R(c)} v(y) ≥ 0` at every `ξ ∈ ∂B_R(c)`. Then `v ≥ 0` on `B_R(c)`.
Proof: perturb by the strictly subharmonic function `η ‖y - c‖²`; a minimizer `y*` of the lower semicontinuous
extension of `v - η ‖· - c‖²` (by `0 - η ‖· - c‖²` on the circle) to `closedBall c R` lies in `B_R(c)`, and the
super-mean-value inequality at `y*` contradicts `M(‖· - c‖²; y*, r) = ‖y* - c‖² + r²`. -/
theorem nonneg_of_lowerSemicontinuousOn_of_superMean {v : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hlsc : LowerSemicontinuousOn v (ball c R))
    (hmean : ∀ x ∈ ball c R, ∃ ρ > 0, ∀ r ∈ Ioo 0 ρ,
      CircleIntegrable v x r ∧ Real.circleAverage v x r ≤ v x)
    (hbdry : ∀ ξ ∈ sphere c R, ∀ ε > 0, ∀ᶠ y in 𝓝[ball c R] ξ, -ε < v y) :
    ∀ x ∈ ball c R, 0 ≤ v x := by
  intro x₁ hx₁
  by_contra hneg
  push Not at hneg
  have hR : 0 < R := pos_of_mem_ball hx₁
  set K := closedBall c R
  have hBK : ball c R ⊆ K := ball_subset_closedBall
  set w : ℂ → ℝ := (ball c R).indicator v with hw
  set η : ℝ := -v x₁ / (2 * (R ^ 2 + 1))
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  have hηR : η * R ^ 2 < -v x₁ := by
    have : η * (R ^ 2 + 1) = -v x₁ / 2 := by
      simp only [η]; field_simp
    nlinarith
  set W : ℂ → ℝ := fun y => w y - η * ‖y - c‖ ^ 2
  -- `w` is lower semicontinuous on the closed disc
  have hwlsc : LowerSemicontinuousOn w K := by
    intro y hy a ha
    by_cases hyB : y ∈ ball c R
    · have hwy : w y = v y := Set.indicator_of_mem hyB v
      rw [hwy] at ha
      have h1 : ∀ᶠ y' in 𝓝 y, a < v y' := by
        have := hlsc y hyB a ha
        rwa [isOpen_ball.nhdsWithin_eq hyB] at this
      have h2 : ∀ᶠ y' in 𝓝 y, y' ∈ ball c R := isOpen_ball.mem_nhds hyB
      refine nhdsWithin_le_nhds ?_
      filter_upwards [h1, h2] with y' h1' h2'
      rw [hw, Set.indicator_of_mem h2' v]
      exact h1'
    · have hwy : w y = 0 := Set.indicator_of_notMem hyB v
      rw [hwy] at ha
      have hyS : y ∈ sphere c R := by
        rw [← closedBall_sdiff_ball]; exact ⟨hy, hyB⟩
      have h1 := hbdry y hyS (-a) (by linarith)
      rw [eventually_nhdsWithin_iff] at h1
      refine nhdsWithin_le_nhds ?_
      filter_upwards [h1] with y' h1'
      by_cases hy' : y' ∈ ball c R
      · rw [hw, Set.indicator_of_mem hy' v]
        have := h1' hy'
        linarith
      · rw [hw, Set.indicator_of_notMem hy' v]
        exact ha
  have hWlsc : LowerSemicontinuousOn W K := by
    have hc : ContinuousOn (fun y : ℂ => -(η * ‖y - c‖ ^ 2)) K := by fun_prop
    have := hwlsc.add hc.lowerSemicontinuousOn
    simpa [W, sub_eq_add_neg] using this
  obtain ⟨y, hyK, hymin⟩ := hWlsc.exists_isMinOn ⟨c, mem_closedBall_self hR.le⟩ (isCompact_closedBall c R)
  have hWx₁ : W x₁ ≤ v x₁ := by
    have : w x₁ = v x₁ := Set.indicator_of_mem hx₁ v
    simp only [W, this]
    nlinarith [sq_nonneg ‖x₁ - c‖]
  have hyB : y ∈ ball c R := by
    by_contra hyB
    have hwy : w y = 0 := Set.indicator_of_notMem hyB v
    have hyle : ‖y - c‖ ≤ R := by simpa [dist_eq_norm] using hyK
    have h1 : W y ≤ W x₁ := hymin (hBK hx₁)
    have h2 : -(η * R ^ 2) ≤ W y := by
      simp only [W, hwy, zero_sub, neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hyle 2) hη.le
    linarith
  obtain ⟨ρ, hρ, hρmean⟩ := hmean y hyB
  have hdist : dist y c < R := hyB
  set r : ℝ := min (ρ / 2) ((R - dist y c) / 2)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hrρ : r ∈ Ioo 0 ρ := ⟨hr, lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩
  have hsphB : sphere y r ⊆ ball c R := by
    intro y' hy'
    rw [mem_sphere] at hy'
    rw [mem_ball]
    calc dist y' c ≤ dist y' y + dist y c := dist_triangle _ _ _
      _ = r + dist y c := by rw [hy']
      _ < R := by have := min_le_right (ρ / 2) ((R - dist y c) / 2); linarith
  obtain ⟨hci, hle⟩ := hρmean r hrρ
  have hwyv : w y = v y := Set.indicator_of_mem hyB v
  -- pointwise lower bound on the circle
  have hpt : ∀ y' ∈ sphere y |r|, v y + η * (‖y' - c‖ ^ 2 - ‖y - c‖ ^ 2) ≤ v y' := by
    intro y' hy'
    rw [abs_of_pos hr] at hy'
    have hy'B := hsphB hy'
    have h1 : W y ≤ W y' := hymin (hBK hy'B)
    have hwy' : w y' = v y' := Set.indicator_of_mem hy'B v
    simp only [W, hwyv, hwy'] at h1
    nlinarith
  have hcq : CircleIntegrable (fun y' : ℂ => v y + η * (‖y' - c‖ ^ 2 - ‖y - c‖ ^ 2)) y r :=
    (by fun_prop : Continuous fun y' : ℂ => v y + η * (‖y' - c‖ ^ 2 - ‖y - c‖ ^ 2)).continuousOn.circleIntegrable'
  have hmono := circleAverage_mono hcq hci hpt
  have havg : Real.circleAverage (fun y' : ℂ => v y + η * (‖y' - c‖ ^ 2 - ‖y - c‖ ^ 2)) y r =
      v y + η * r ^ 2 := by
    have hci2 : CircleIntegrable (fun y' : ℂ => ‖y' - c‖ ^ 2) y r :=
      (by fun_prop : Continuous fun y' : ℂ => ‖y' - c‖ ^ 2).continuousOn.circleIntegrable'
    have e1 : (fun y' : ℂ => v y + η * (‖y' - c‖ ^ 2 - ‖y - c‖ ^ 2)) =
        fun y' => (v y - η * ‖y - c‖ ^ 2) + η • ‖y' - c‖ ^ 2 := by
      ext y'; simp only [smul_eq_mul]; ring
    rw [e1, circleAverage_fun_add continuousOn_const.circleIntegrable'
      ((by fun_prop : Continuous fun y' : ℂ => η • ‖y' - c‖ ^ 2).continuousOn.circleIntegrable'),
      circleAverage_const, circleAverage_fun_smul, circleAverage_norm_sub_sq, smul_eq_mul]
    ring
  rw [havg] at hmono
  have : 0 < η * r ^ 2 := by positivity
  linarith

/-! ## Circle averages: measurability, domination, limits -/

/-- A closed disc inside an open set is inside a slightly larger closed disc inside the open set. -/
theorem exists_closedBall_add_subset {U : Set ℂ} (hU : IsOpen U) {x : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : closedBall x r ⊆ U) : ∃ δ > 0, closedBall x (r + δ) ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall x r).exists_cthickening_subset_open hU h
  refine ⟨δ, hδ, ?_⟩
  rwa [cthickening_closedBall hδ.le hr, add_comm] at hsub

/-- The composite of a function lower semicontinuous on `U` with the parametrization of a circle inside `U` is
measurable. -/
theorem LowerSemicontinuousOn.measurable_comp_circleMap {g : ℂ → ℝ} {U : Set ℂ}
    (hg : LowerSemicontinuousOn g U) {x : ℂ} {r : ℝ} (hsph : sphere x |r| ⊆ U) :
    Measurable fun θ => g (circleMap x r θ) := by
  refine LowerSemicontinuous.measurable fun θ a ha => ?_
  have hU : circleMap x r θ ∈ U := hsph (circleMap_mem_sphere' x r θ)
  have h1 := hg _ hU a ha
  have h2 : Tendsto (circleMap x r) (𝓝 θ) (𝓝[U] circleMap x r θ) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_circleMap x r).tendsto θ,
      Eventually.of_forall fun θ' => hsph (circleMap_mem_sphere' x r θ')⟩
  exact h2.eventually h1

/-- A function lower semicontinuous on `U`, bounded below on a circle inside `U` and bounded above there by a circle
integrable function, is circle integrable. -/
theorem LowerSemicontinuousOn.circleIntegrable_of_le {g G : ℂ → ℝ} {U : Set ℂ}
    (hg : LowerSemicontinuousOn g U) {x : ℂ} {r m : ℝ} (hsph : sphere x |r| ⊆ U)
    (hlo : ∀ y ∈ sphere x |r|, m ≤ g y) (hup : ∀ y ∈ sphere x |r|, g y ≤ G y)
    (hG : CircleIntegrable G x r) : CircleIntegrable g x r := by
  have hGm : CircleIntegrable (fun y => |G y| + |m|) x r :=
    hG.abs.add continuousOn_const.circleIntegrable'
  refine IntervalIntegrable.mono_fun' hGm (LowerSemicontinuousOn.measurable_comp_circleMap hg hsph).aestronglyMeasurable ?_
  refine Eventually.of_forall fun θ => ?_
  have hy := circleMap_mem_sphere' x r θ
  have h1 := hlo _ hy
  have h2 := hup _ hy
  simp only [Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> cases abs_cases (G (circleMap x r θ)) <;> cases abs_cases m <;> linarith

/-- **Dominated convergence for circle averages.** -/
theorem tendsto_circleAverage_of_dominated {F : ℕ → ℂ → ℝ} {f G : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hF : ∀ n, CircleIntegrable (F n) c r) (hG : CircleIntegrable G c r)
    (hbound : ∀ n, ∀ y ∈ sphere c |r|, |F n y| ≤ G y)
    (hlim : ∀ y ∈ sphere c |r|, Tendsto (fun n => F n y) atTop (𝓝 (f y))) :
    Tendsto (fun n => Real.circleAverage (F n) c r) atTop (𝓝 (Real.circleAverage f c r)) := by
  simp only [Real.circleAverage_def]
  refine Tendsto.const_smul ?_ _
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun θ => G (circleMap c r θ)) ?_ ?_ hG ?_
  · exact Eventually.of_forall fun n => (hF n).def'.aestronglyMeasurable
  · exact Eventually.of_forall fun n => Eventually.of_forall fun θ _ =>
      hbound n _ (circleMap_mem_sphere' c r θ)
  · exact Eventually.of_forall fun θ _ => hlim _ (circleMap_mem_sphere' c r θ)

end HarmonicBalls
