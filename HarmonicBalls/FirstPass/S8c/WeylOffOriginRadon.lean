import Mathlib
import HarmonicBalls.FirstPass.S8d.RadonUnique

/-!
# Weyl change off the origin: Radon identification (Steps 5-6)

Derivation: Steps 5-6. This is the
deterministic part of the off-origin Weyl identity behind `LocalLQGInsertionWeylOffOrigin`
(FirstPass/Frozen/S8c.lean:73). No new mathematics and no new input.

Route. Let `V = {0}ᶜ` and `ν = μ.withDensity (ofReal ∘ w)`.
* Cut-offs `offOriginCutoff k z = max 0 (min 1 (k‖z‖ - 1))` are continuous, vanish on `‖z‖ < 1/(k+1)`, are
  nondecreasing in `k`, and tend to `1_V` pointwise.
* Test functions vanishing near `0` satisfy `∫⁻ ofReal f ∂m = ∫⁻ ofReal f ∂ν` (`lintegral_ofReal_eq_of_vanishing`).
* Monotone convergence along the cut-offs gives the same identity on `V` for every nonnegative continuous compactly
  supported `g` (`lintegral_ofReal_restrict_compl_zero_eq`).
* `ν|V` is locally finite at `0` too: the bump `offOriginBump R` gives `ν(closedBall 0 R) ≤ m(closedBall 0 (R+1))`.
* `HarmonicBalls.radonIntegralUnique_proved` (Riesz-Markov uniqueness, FirstPass/S8d/RadonUnique.lean:17) gives
  `m|V = ν|V`; for measurable `s` with `0 ∉ s` this is the conclusion.
-/

open MeasureTheory Set Filter Topology

namespace HarmonicBalls.FirstPassS8cWeyl

/-- The measure `μ` weighted by the (possibly non-measurable at `0`) density `ofReal ∘ w`. -/
noncomputable def withDensityOffOrigin (μ : Measure ℂ) (w : ℂ → ℝ) : Measure ℂ :=
  μ.withDensity fun z => ENNReal.ofReal (w z)

/-- Continuous cut-off `k ↦ max 0 (min 1 (k‖z‖ - 1))`: zero for `‖z‖ < 1/(k+1)`, equal to `1` once `k‖z‖ ≥ 2`,
and nondecreasing in `k`. -/
noncomputable def offOriginCutoff (k : ℕ) (z : ℂ) : ℝ :=
  max 0 (min 1 ((k : ℝ) * ‖z‖ - 1))

lemma offOriginCutoff_continuous (k : ℕ) : Continuous (offOriginCutoff k) := by
  unfold offOriginCutoff
  fun_prop

lemma offOriginCutoff_nonneg (k : ℕ) (z : ℂ) : 0 ≤ offOriginCutoff k z :=
  le_max_left _ _

lemma offOriginCutoff_le_one (k : ℕ) (z : ℂ) : offOriginCutoff k z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma offOriginCutoff_monotone (z : ℂ) : Monotone fun k : ℕ => offOriginCutoff k z := by
  intro k k' hkk'
  have hk : (k : ℝ) * ‖z‖ ≤ (k' : ℝ) * ‖z‖ :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hkk') (norm_nonneg z)
  show offOriginCutoff k z ≤ offOriginCutoff k' z
  unfold offOriginCutoff
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

lemma offOriginCutoff_eq_zero {k : ℕ} {z : ℂ} (hz : ‖z‖ < 1 / ((k : ℝ) + 1)) :
    offOriginCutoff k z = 0 := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : ‖z‖ * ((k : ℝ) + 1) < 1 := (lt_div_iff₀ hpos).1 hz
  have h2 : (k : ℝ) * ‖z‖ - 1 ≤ 0 := by nlinarith [norm_nonneg z]
  unfold offOriginCutoff
  rw [min_eq_right (show (k : ℝ) * ‖z‖ - 1 ≤ 1 by linarith [norm_nonneg z]), max_eq_left h2]

lemma offOriginCutoff_zero_point (k : ℕ) : offOriginCutoff k 0 = 0 := by
  apply offOriginCutoff_eq_zero
  rw [norm_zero]
  positivity

lemma offOriginCutoff_eq_one {z : ℂ} (hz : z ≠ 0) : ∃ k : ℕ, offOriginCutoff k z = 1 := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ‖z‖)
  refine ⟨k, ?_⟩
  have hnz : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2 : 2 < (k : ℝ) * ‖z‖ := (div_lt_iff₀ hnz).1 hk
  unfold offOriginCutoff
  rw [min_eq_left (show (1 : ℝ) ≤ (k : ℝ) * ‖z‖ - 1 by linarith),
    max_eq_right (show (0 : ℝ) ≤ 1 by norm_num)]

/-- Continuous bump `max 0 (min 1 (R + 1 - ‖z‖))`: one on `‖z‖ ≤ R`, zero on `‖z‖ > R + 1`. -/
noncomputable def offOriginBump (R : ℝ) (z : ℂ) : ℝ :=
  max 0 (min 1 (R + 1 - ‖z‖))

lemma offOriginBump_continuous (R : ℝ) : Continuous (offOriginBump R) := by
  unfold offOriginBump
  fun_prop

lemma offOriginBump_nonneg (R : ℝ) (z : ℂ) : 0 ≤ offOriginBump R z :=
  le_max_left _ _

lemma offOriginBump_le_one (R : ℝ) (z : ℂ) : offOriginBump R z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma offOriginBump_eq_one {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) : offOriginBump R z = 1 := by
  unfold offOriginBump
  rw [min_eq_left (show (1 : ℝ) ≤ R + 1 - ‖z‖ by linarith), max_eq_right zero_le_one]

lemma offOriginBump_eq_zero {R : ℝ} {z : ℂ} (hz : R + 1 < ‖z‖) : offOriginBump R z = 0 := by
  unfold offOriginBump
  rw [min_eq_right (show R + 1 - ‖z‖ ≤ 1 by linarith), max_eq_left (show R + 1 - ‖z‖ ≤ 0 by linarith)]

lemma offOriginBump_hasCompactSupport (R : ℝ) : HasCompactSupport (offOriginBump R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (R + 1)) (fun z hz => ?_)
  have hz' : R + 1 < ‖z‖ := by
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    exact hz
  exact offOriginBump_eq_zero hz'

/-- A continuous function on `ℂ` minus the origin, extended to `ℂ`, is measurable. -/
lemma measurable_of_continuousOn_compl_singleton {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) :
    Measurable w := by
  classical
  have hV : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton (0 : ℂ)).compl
  have h := ContinuousOn.measurable_piecewise (f := w) (g := fun _ => w 0) (s := ({0}ᶜ : Set ℂ)) hw
    continuousOn_const hV
  convert h using 1
  funext z
  by_cases hz : z = 0
  · subst hz
    simp [Set.piecewise]
  · simp [Set.piecewise, hz]

/-- Test functions vanishing near `0`: the Bochner identity `∫ f dm = ∫ f w dμ`, rewritten for lower integrals
against `ν = μ.withDensity (ofReal ∘ w)`. -/
lemma lintegral_ofReal_eq_of_vanishing {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ)
    (f : ℂ → ℝ) (hf : Continuous f) (hcf : HasCompactSupport f) (hf0 : ∀ z, 0 ≤ f z)
    (δ : ℝ) (hδ : 0 < δ) (hfδ : ∀ z : ℂ, ‖z‖ < δ → f z = 0) :
    ∫⁻ z, ENNReal.ofReal (f z) ∂m = ∫⁻ z, ENNReal.ofReal (f z) ∂(withDensityOffOrigin μ w) := by
  -- the product `f * w` vanishes on the ball of radius `δ`, hence is continuous on `ℂ`
  have hFc : Continuous fun z => f z * w z := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z = 0
    · subst hz
      have hev : (fun z => f z * w z) =ᶠ[𝓝 (0 : ℂ)] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with z hz'
        have hz'' : ‖z‖ < δ := by simpa using hz'
        simp [hfδ z hz'']
      exact continuousAt_const.congr hev.symm
    · have hV : ({0}ᶜ : Set ℂ) ∈ 𝓝 z := isOpen_compl_singleton.mem_nhds hz
      exact hf.continuousAt.mul (hw.continuousAt hV)
  have hFsupp : HasCompactSupport fun z => f z * w z :=
    (show HasCompactSupport (f * w) from hcf.mul_right)
  have hFint : Integrable (fun z => f z * w z) μ := hFc.integrable_of_hasCompactSupport hFsupp
  have hfint : Integrable f m := hf.integrable_of_hasCompactSupport hcf
  have hA : ∫ z, f z ∂m = (∫⁻ z, ENNReal.ofReal (f z) ∂m).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf0) hf.aestronglyMeasurable
  have hB : ∫ z, f z * w z ∂μ = (∫⁻ z, ENNReal.ofReal (f z * w z) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => mul_nonneg (hf0 z) (hw0 z)) hFc.aestronglyMeasurable
  have hAfin : ∫⁻ z, ENNReal.ofReal (f z) ∂m ≠ ⊤ := hfint.lintegral_lt_top.ne
  have hBfin : ∫⁻ z, ENNReal.ofReal (f z * w z) ∂μ ≠ ⊤ := hFint.lintegral_lt_top.ne
  have hAB : ∫⁻ z, ENNReal.ofReal (f z) ∂m = ∫⁻ z, ENNReal.ofReal (f z * w z) ∂μ :=
    (ENNReal.toReal_eq_toReal_iff' hAfin hBfin).1 (by
      rw [← hA, ← hB]
      exact h f hf hcf ⟨δ, hδ, hfδ⟩)
  have hmeas : Measurable fun z => ENNReal.ofReal (w z) :=
    ENNReal.measurable_ofReal.comp (measurable_of_continuousOn_compl_singleton hw)
  have hfmeas : Measurable fun z => ENNReal.ofReal (f z) :=
    ENNReal.measurable_ofReal.comp hf.measurable
  unfold withDensityOffOrigin
  rw [lintegral_withDensity_eq_lintegral_mul μ hmeas hfmeas, hAB]
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul (hf0 z), mul_comm]

/-- Monotone convergence along the cut-offs: the identity of `lintegral_ofReal_eq_of_vanishing` holds on `{0}ᶜ`
for every nonnegative continuous compactly supported `g`. -/
lemma lintegral_ofReal_restrict_compl_zero_eq {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ)
    (g : ℂ → ℝ) (hg : Continuous g) (hcg : HasCompactSupport g) (hg0 : ∀ z, 0 ≤ g z) :
    ∫⁻ z, ENNReal.ofReal (g z) ∂(m.restrict ({0}ᶜ : Set ℂ)) =
      ∫⁻ z, ENNReal.ofReal (g z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := by
  have hV : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton (0 : ℂ)).compl
  have hF : ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (g z * offOriginCutoff k z) ∂m =
      ∫⁻ z, ENNReal.ofReal (g z * offOriginCutoff k z) ∂(withDensityOffOrigin μ w) := by
    intro k
    refine lintegral_ofReal_eq_of_vanishing hw hw0 h _ (hg.mul (offOriginCutoff_continuous k))
      (show HasCompactSupport (g * offOriginCutoff k) from hcg.mul_right)
      (fun z => mul_nonneg (hg0 z) (offOriginCutoff_nonneg k z))
      (1 / ((k : ℝ) + 1)) (by positivity) (fun z hz => ?_)
    simp only [offOriginCutoff_eq_zero hz, mul_zero]
  have hsup : ∀ z : ℂ, (⨆ k : ℕ, ENNReal.ofReal (g z * offOriginCutoff k z)) =
      ({0}ᶜ : Set ℂ).indicator (fun z => ENNReal.ofReal (g z)) z := by
    intro z
    by_cases hz : z = 0
    · subst hz
      simp only [offOriginCutoff_zero_point, mul_zero, ENNReal.ofReal_zero, iSup_const]
      rw [Set.indicator_of_notMem (show (0 : ℂ) ∉ ({0}ᶜ : Set ℂ) by simp)]
    · rw [Set.indicator_of_mem (show z ∈ ({0}ᶜ : Set ℂ) from hz)]
      obtain ⟨k0, hk0⟩ := offOriginCutoff_eq_one hz
      refine le_antisymm (iSup_le fun k => ?_) (le_iSup_of_le k0 (le_of_eq ?_))
      · exact ENNReal.ofReal_le_ofReal
          (mul_le_of_le_one_right (hg0 z) (offOriginCutoff_le_one k z))
      · rw [hk0, mul_one]
  have hmeasF : ∀ k : ℕ, Measurable fun z => ENNReal.ofReal (g z * offOriginCutoff k z) := fun k =>
    ENNReal.measurable_ofReal.comp (hg.mul (offOriginCutoff_continuous k)).measurable
  have hmonoF : Monotone fun (k : ℕ) (z : ℂ) => ENNReal.ofReal (g z * offOriginCutoff k z) := by
    intro k k' hkk' z
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (offOriginCutoff_monotone z hkk') (hg0 z))
  calc ∫⁻ z, ENNReal.ofReal (g z) ∂(m.restrict ({0}ᶜ : Set ℂ))
      = ∫⁻ z, ({0}ᶜ : Set ℂ).indicator (fun z => ENNReal.ofReal (g z)) z ∂m :=
        (lintegral_indicator hV _).symm
    _ = ∫⁻ z, ⨆ k : ℕ, ENNReal.ofReal (g z * offOriginCutoff k z) ∂m :=
        lintegral_congr fun z => (hsup z).symm
    _ = ⨆ k : ℕ, ∫⁻ z, ENNReal.ofReal (g z * offOriginCutoff k z) ∂m :=
        lintegral_iSup hmeasF hmonoF
    _ = ⨆ k : ℕ, ∫⁻ z, ENNReal.ofReal (g z * offOriginCutoff k z) ∂(withDensityOffOrigin μ w) :=
        iSup_congr fun k => hF k
    _ = ∫⁻ z, ⨆ k : ℕ, ENNReal.ofReal (g z * offOriginCutoff k z) ∂(withDensityOffOrigin μ w) :=
        (lintegral_iSup hmeasF hmonoF).symm
    _ = ∫⁻ z, ({0}ᶜ : Set ℂ).indicator (fun z => ENNReal.ofReal (g z)) z ∂(withDensityOffOrigin μ w) :=
        lintegral_congr fun z => hsup z
    _ = ∫⁻ z, ENNReal.ofReal (g z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) :=
        lintegral_indicator hV _

/-- Local finiteness of `ν|V` on balls about `0`: `ν(closedBall 0 R) ≤ m(closedBall 0 (R+1))`, via the bump. -/
lemma withDensityOffOrigin_restrict_closedBall_lt_top {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ)
    (R : ℝ) :
    ((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) (Metric.closedBall 0 R) < ⊤ := by
  have hbound : ((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) (Metric.closedBall 0 R) ≤
      ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := by
    refine (lintegral_indicator_one measurableSet_closedBall).symm.trans_le (lintegral_mono fun z => ?_)
    by_cases hz : ‖z‖ ≤ R
    · have hmem : z ∈ Metric.closedBall (0 : ℂ) R := mem_closedBall_zero_iff.2 hz
      rw [Set.indicator_of_mem hmem, offOriginBump_eq_one hz, Pi.one_apply]
      simp
    · have hmem : z ∉ Metric.closedBall (0 : ℂ) R := fun h' => hz (mem_closedBall_zero_iff.1 h')
      rw [Set.indicator_of_notMem hmem]
      exact zero_le
  have hlw := lintegral_ofReal_restrict_compl_zero_eq hw hw0 h (offOriginBump R)
    (offOriginBump_continuous R) (offOriginBump_hasCompactSupport R) (offOriginBump_nonneg R)
  have hpt : ∀ z : ℂ, ENNReal.ofReal (offOriginBump R z) ≤
      (Metric.closedBall (0 : ℂ) (R + 1)).indicator 1 z := by
    intro z
    by_cases hz : ‖z‖ ≤ R + 1
    · have hmem : z ∈ Metric.closedBall (0 : ℂ) (R + 1) := mem_closedBall_zero_iff.2 hz
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (offOriginBump_le_one R z)
    · have hmem : z ∉ Metric.closedBall (0 : ℂ) (R + 1) := fun h' => hz (mem_closedBall_zero_iff.1 h')
      rw [Set.indicator_of_notMem hmem, offOriginBump_eq_zero (not_le.1 hz), ENNReal.ofReal_zero]
  have hm_le : ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂(m.restrict ({0}ᶜ : Set ℂ)) ≤
      m (Metric.closedBall 0 (R + 1)) := by
    calc ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂(m.restrict ({0}ᶜ : Set ℂ))
        ≤ ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂m := lintegral_mono' Measure.restrict_le_self le_rfl
      _ ≤ ∫⁻ z, (Metric.closedBall (0 : ℂ) (R + 1)).indicator 1 z ∂m := lintegral_mono hpt
      _ = m (Metric.closedBall 0 (R + 1)) := lintegral_indicator_one measurableSet_closedBall
  calc ((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) (Metric.closedBall 0 R)
      ≤ ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := hbound
    _ = ∫⁻ z, ENNReal.ofReal (offOriginBump R z) ∂(m.restrict ({0}ᶜ : Set ℂ)) := hlw.symm
    _ ≤ m (Metric.closedBall 0 (R + 1)) := hm_le
    _ < ⊤ := measure_closedBall_lt_top

/-- `ν|V` is locally finite. -/
lemma isLocallyFiniteMeasure_withDensityOffOrigin_restrict {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ) :
    IsLocallyFiniteMeasure ((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := by
  refine ⟨fun x => ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x one_pos, ?_⟩⟩
  refine lt_of_le_of_lt (measure_mono ?_)
    (withDensityOffOrigin_restrict_closedBall_lt_top hw hw0 h (‖x‖ + 1))
  intro z hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  rw [mem_closedBall_zero_iff]
  linarith [norm_sub_norm_le z x]

/-- Lower integrals of `ofReal g` (any continuous compactly supported real `g`) agree on `{0}ᶜ`. -/
lemma lintegral_ofReal_restrict_compl_zero_eq' {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ)
    (g : ℂ → ℝ) (hg : Continuous g) (hcg : HasCompactSupport g) :
    ∫⁻ z, ENNReal.ofReal (g z) ∂(m.restrict ({0}ᶜ : Set ℂ)) =
      ∫⁻ z, ENNReal.ofReal (g z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := by
  have e : ∀ x : ℝ, ENNReal.ofReal x = ENNReal.ofReal (max x 0) := fun x => by
    rcases le_total x 0 with hx | hx
    · rw [ENNReal.ofReal_of_nonpos hx, max_eq_right hx, ENNReal.ofReal_zero]
    · rw [max_eq_left hx]
  have hcg' : HasCompactSupport fun z => max (g z) 0 :=
    HasCompactSupport.comp_left (g := fun x : ℝ => max x 0) hcg (by simp)
  calc ∫⁻ z, ENNReal.ofReal (g z) ∂(m.restrict ({0}ᶜ : Set ℂ))
      = ∫⁻ z, ENNReal.ofReal (max (g z) 0) ∂(m.restrict ({0}ᶜ : Set ℂ)) :=
        lintegral_congr fun z => e (g z)
    _ = ∫⁻ z, ENNReal.ofReal (max (g z) 0) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) :=
        lintegral_ofReal_restrict_compl_zero_eq hw hw0 h _ (hg.max continuous_const) hcg'
          (fun z => le_max_right _ _)
    _ = ∫⁻ z, ENNReal.ofReal (g z) ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) :=
        (lintegral_congr fun z => e (g z)).symm

/-- Integrals of continuous compactly supported real `f` agree on `{0}ᶜ`. -/
lemma integral_restrict_compl_zero_eq {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ)
    (f : ℂ → ℝ) (hf : Continuous f) (hcf : HasCompactSupport f) :
    ∫ z, f z ∂(m.restrict ({0}ᶜ : Set ℂ)) =
      ∫ z, f z ∂((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) := by
  have := isLocallyFiniteMeasure_withDensityOffOrigin_restrict hw hw0 h
  have hi1 : Integrable f (m.restrict ({0}ᶜ : Set ℂ)) := hf.integrable_of_hasCompactSupport hcf
  have hi2 : Integrable f ((withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ)) :=
    hf.integrable_of_hasCompactSupport hcf
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi2,
    lintegral_ofReal_restrict_compl_zero_eq' hw hw0 h f hf hcf,
    lintegral_ofReal_restrict_compl_zero_eq' hw hw0 h (fun z => -f z) hf.neg hcf.neg]

/-- Riesz-Markov uniqueness on the open set `{0}ᶜ`: `m|V = ν|V`. -/
lemma restrict_compl_zero_eq {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ] {w : ℂ → ℝ} (hw : ContinuousOn w ({0}ᶜ : Set ℂ)) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ) :
    m.restrict ({0}ᶜ : Set ℂ) = (withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ) :=
  HarmonicBalls.radonIntegralUnique_proved _ _ inferInstance
    (isLocallyFiniteMeasure_withDensityOffOrigin_restrict hw hw0 h)
    (fun f hf hcf => integral_restrict_compl_zero_eq hw hw0 h f hf hcf)

/-- **Step 5-6.** Let `m, μ` be locally finite measures on `ℂ` and `w : ℂ → ℝ` nonnegative,
continuous off the origin. If `∫ f dm = ∫ f · w dμ` for every continuous compactly supported real `f` vanishing near
`0`, then `m s = ∫⁻_s ofReal (w z) dμ` for every measurable `s` avoiding `0`.
(Weyl off-origin identity; for `m = λ_ω`, `μ = μ_ω`, `w z = ‖z‖^(γα₀)`, as in the write-up.) -/
theorem eq_withDensity_offOrigin_of_integral_eq {m μ : Measure ℂ} [IsLocallyFiniteMeasure m]
    [IsLocallyFiniteMeasure μ]
    {w : ℂ → ℝ} (hw : ContinuousOn w {0}ᶜ) (hw0 : ∀ z, 0 ≤ w z)
    (h : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂m = ∫ z, f z * w z ∂μ) :
    ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s → m s = ∫⁻ z in s, ENNReal.ofReal (w z) ∂μ := by
  intro s hs h0
  have hsV : s ⊆ ({0}ᶜ : Set ℂ) := by
    intro z hz
    rw [Set.mem_compl_singleton_iff]
    intro hz0
    exact h0 (hz0 ▸ hz)
  calc m s = m.restrict ({0}ᶜ : Set ℂ) s := by
        rw [Measure.restrict_apply hs, Set.inter_eq_left.2 hsV]
    _ = (withDensityOffOrigin μ w).restrict ({0}ᶜ : Set ℂ) s := by
        rw [restrict_compl_zero_eq hw hw0 h]
    _ = withDensityOffOrigin μ w s := by
        rw [Measure.restrict_apply hs, Set.inter_eq_left.2 hsV]
    _ = ∫⁻ z in s, ENNReal.ofReal (w z) ∂μ := by
        unfold withDensityOffOrigin
        exact withDensity_apply _ hs

end HarmonicBalls.FirstPassS8cWeyl
