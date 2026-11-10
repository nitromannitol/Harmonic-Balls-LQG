import HarmonicBalls.FirstPass.S11i.Step8PhysReduction
import HarmonicBalls.FirstPass.S11r.LogSingularCutoff
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived
import HarmonicBalls.FirstPass.S11asWeyl
import HarmonicBalls.FirstPass.S11r.RootedLocality
import HarmonicBalls.FirstPass.S11i.Step8Exhaustion
import HarmonicBalls.FirstPass.S11i.Step8Fitting
import HarmonicBalls.FirstPass.S11i.Step8LengthMetric
import HarmonicBalls.FirstPass.S11ap
import HarmonicBalls.FirstPass.S11af
import HarmonicBalls.FirstPass.Frozen.S11aj
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.S11r.LocalMetricReplacement
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.S11h.Faithful

/-!
# Insertion transfer: all-model zero-insertion physical frequency implies the insertion-`α` one
(fp-S11i-insertion-transfer, owner n4)

Source: `notes/fp-gaps/CODEX-hPhys-sol-20261110.md`, section "For insertion transfer" and VERDICT step 3.

`PhysicalAt` and `AllModelsAt` are the proposed interfaces of that note, written with the same bodies as the existing
binder `Step8PhysStmt` (`S11i/Step8PhysReduction.lean:84`). `Step8PhysExists.lean` is not in the repository yet, so the
two definitions are declared here locally (the bodies are unchanged).

Ingredients of the transfer, in the order of the note:
* a finite cover of `B_{2^k} \ {0}` by root balls whose decoder discs avoid `0` (dilates of the valid balls);
* on each decoder disc, a smooth compactly supported shift equal to `-α log|·|` (Cameron–Martin reweighting,
  frozen `CameronMartinGFFReweighting`, `S11aj.lean`);
* the zero-insertion statement applied under the changed law, and transfer of its conull event back;
* the eventual certificate fitting (`ae_fitting_eventually_of_decoders`, `S11i/Step8Fitting.lean:114`), which makes
  the window counts agree for all large `N`.

This file so far contains the definitions and the window-count lemma `tendsto_window_iff_of_eventually_iff`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iInsertionTransfer

open HarmonicBalls FirstPassS11i

universe u

/-- **Physical window frequency of one insertion-`α` model on `B_{2^k}(0)`** (body of `Step8PhysStmt`,
`S11i/Step8PhysReduction.lean:84`). Almost surely, for almost every `z` in `B_{2^k}(0)`, the window count of the
certificate events at radii `2^k 2^{-n}`, `n ∈ [N+1, 2N]`, divided by `N`, tends to `q`. -/
def PhysicalAt {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (q : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) (k : ℕ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
    Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 q)

/-- **All-model physical frequency at insertion `α`.** For every whole-plane GFF `hC` on every probability space
`(Ω, P)` and every insertion-`α` LQG measure `μ` and metric `D` of the field, `PhysicalAt` holds at scale `2^k`.
The quantification over all `Ω : Type u` and all laws is what the Cameron–Martin change of law uses. -/
def AllModelsAt (γ ξ α q : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) (k : ℕ) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α hcirc μ →
    IsLQGMetricOfField P γ ξ α hC D →
      PhysicalAt P q U V W T Q' Q δ M k μ D

/-- **Eventually equal window counts have the same frequency limit.** If two predicates on the index `n` agree for all
large `n`, then for all large `N` the window sets `{n ∈ [N+1, 2N] | P n}` and `{n ∈ [N+1, 2N] | Q n}` coincide, so the
window frequencies `#{…}/N` are eventually equal functions of `N` and have the same limit. This is the step where
eventual certificate fitting (`ae_fitting_eventually_of_decoders`) is turned into equal frequency limits. -/
theorem tendsto_window_iff_of_eventually_iff {P Q : ℕ → Prop} (h : ∀ᶠ n in atTop, (P n ↔ Q n)) (q : ℝ) :
    Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q) ↔
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q) := by
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 h
  have hEq : (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n}.ncard : ℕ) : ℝ) / (N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n}.ncard : ℕ) : ℝ) / (N : ℝ)) := by
    filter_upwards [eventually_ge_atTop n0] with N hN
    have hs : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ P n} = {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ Q n} := by
      ext n
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, (hn0 n (by omega)).1 h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, (hn0 n (by omega)).2 h3⟩
    rw [hs]
  exact tendsto_congr' hEq

/-- **Smooth cut-off of `-β log‖·‖` away from the origin.** For a disc `ball c ρ` not containing `0`
(`ρ < ‖c‖`), there is a smooth compactly supported `f` equal to `-β log‖·‖` on `ball c ρ`. Its unit-circle average is zero
because `log 1 = 0` on the unit circle, so no normalisation constant is needed. This is the shift of
`CameronMartinGFFReweighting` (frozen, `FirstPass/Frozen/S11aj.lean:33`) in the zero-insertion coordinates. The proof
follows `exists_log_sing_cutoff` (`S11r/LogSingularCutoff.lean:35`) with the singularity at `0`. -/
theorem exists_log_cutoff_avoid_zero (β : ℝ) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρc : ρ < ‖c‖) :
    ∃ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ Real.circleAverage f 0 1 = 0 ∧
      ∀ x ∈ ball c ρ, f x = -β * Real.log ‖x‖ := by
  let B : ContDiffBump c :=
    { rIn := ρ, rOut := (ρ + ‖c‖) / 2, rIn_pos := hρ, rIn_lt_rOut := by linarith }
  have hBz : ∀ y : ℂ, (ρ + ‖c‖) / 2 ≤ dist y c → B y = 0 := fun y hy => B.zero_of_le_dist hy
  refine ⟨fun x => B x * (-β * Real.log ‖x‖), ?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · -- near the origin the bump vanishes
      have hx0 : dist x c = ‖c‖ := by rw [hx, dist_zero_left]
      have hd : 0 < dist x c - (ρ + ‖c‖) / 2 := by rw [hx0]; linarith
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds x hd] with y hy
      have hy' : dist y x < dist x c - (ρ + ‖c‖) / 2 := mem_ball.1 hy
      have hyc : (ρ + ‖c‖) / 2 ≤ dist y c := by
        have h3 := dist_triangle x y c
        have h4 := dist_comm x y
        linarith
      simp [hBz y hyc]
    · have hL : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ℂ => -β * Real.log ‖y‖) x :=
        contDiffAt_const.mul ((Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hx)).comp x (contDiffAt_norm ℝ hx))
      exact B.contDiff.contDiffAt.mul hL
  · exact B.hasCompactSupport.mul_right
  · apply circleAverage_unit_zero_of_vanish
    intro x hx
    simp [hx]
  · intro x hx
    have hB1 : B x = 1 := B.one_of_mem_closedBall (ball_subset_closedBall hx)
    simp [hB1]

/-- **Restriction off the origin.** If `μ0` and `μα` satisfy the Weyl relation `μ0 t = ∫⁻_t w dμα` on every
measurable `t` avoiding `0`, then `μ0` and `(μα).withDensity w` agree on restriction to any measurable `s ∌ 0`. -/
theorem restrict_eq_withDensity_of_off_zero {μ0 μα : Measure ℂ} {w : ℂ → ℝ≥0∞} {s : Set ℂ}
    (hs : MeasurableSet s) (h0 : (0 : ℂ) ∉ s)
    (hW : ∀ t : Set ℂ, MeasurableSet t → (0 : ℂ) ∉ t → μ0 t = ∫⁻ z in t, w z ∂μα) :
    μ0.restrict s = (μα.restrict s).withDensity w := by
  ext t ht
  rw [Measure.restrict_apply ht, withDensity_apply _ ht, Measure.restrict_restrict ht]
  exact hW (t ∩ s) (ht.inter hs) (fun h => h0 h.2)

/-- **Zero-insertion measure of a smooth shift equals the insertion-`α` measure on a disc.** Let `f` be smooth and
equal to `-α log‖·‖` on the disc `ball c ρ` avoiding `0`. The zero-insertion LQG measure `μ'` of the shifted field
`h + f` is the density `e^{γ f} μ0` of the zero-insertion measure `μ0` of `h` (`lqgMeasure_eq_withDensity_of_shift`),
and `μ0 = |·|^{γα} μα` off `0` (`localLQGInsertionWeylOffOrigin_derived`). On the disc the two factors cancel:
`e^{γ f} |·|^{γα} = 1`. Hence `μ' = μα` on every measurable subset of the disc, almost surely. -/
theorem zeroInsertion_shift_eq_insertion_on_disc
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μα μ0 μ' : Ω → Measure ℂ}
    {c : ℂ} {ρ : ℝ} {f : ℂ → ℝ} (hf : Continuous f) (hfα : ∀ x ∈ ball c ρ, f x = -α * Real.log ‖x‖)
    (hD0 : (0 : ℂ) ∉ ball c ρ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hμα : IsLQGMeasureOfField P γ α hcirc μα) (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0)
    (hμ' : IsLQGMeasureOfField P γ 0 (fun ω r z => hcirc ω r z + Real.circleAverage f z r) μ') :
    ∀ᵐ ω ∂P, ∀ s : Set ℂ, MeasurableSet s → s ⊆ ball c ρ → μ' ω s = μα ω s := by
  have hW := localLQGInsertionWeylOffOrigin_derived.{u} Ω P γ α hC hcirc μα μ0 hGFF hγ0 hγ2 hα hμα hμ0
  have hcont : ∀ᵐ ω ∂P, ∀ n : ℕ, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale n)) := by
    filter_upwards [hGFF.ae_continuousOn_circle] with ω hω n
    have hpos : (0 : ℝ) < dyadicScale n := by
      unfold dyadicScale
      positivity
    have hc : Continuous fun z : ℂ => hcirc ω (dyadicScale n) z :=
      hω.comp_continuous (continuous_const.prodMk continuous_id)
        (fun z => (⟨hpos, Set.mem_univ z⟩ : (dyadicScale n, z) ∈ Set.Ioi 0 ×ˢ Set.univ))
    have hfun : fieldCircleAverage 0 (hcirc ω) (dyadicScale n) = fun z => hcirc ω (dyadicScale n) z := by
      funext z
      simp [fieldCircleAverage]
    rw [hfun]
    exact hc
  have hS := FirstPassS11asWeyl.lqgMeasure_eq_withDensity_of_shift (hv := hf) (hshift := fun ω r x => rfl) hcont
    hμ0 hμ'
  filter_upwards [hW, hS] with ω hWω hSω
  intro s hs hsb
  have h0 : (0 : ℂ) ∉ s := fun h => hD0 (hsb h)
  have hw : Measurable fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (γ * α)) :=
    ((measurable_norm.pow_const _)).ennreal_ofReal
  have hg : Measurable fun z : ℂ => ENNReal.ofReal (Real.exp (γ * f z)) :=
    ((Real.continuous_exp.comp (continuous_const.mul hf)).measurable).ennreal_ofReal
  have hrestr : (μ0 ω).restrict s = ((μα ω).restrict s).withDensity fun z => ENNReal.ofReal (‖z‖ ^ (γ * α)) :=
    restrict_eq_withDensity_of_off_zero hs h0 (fun t ht ht0 => hWω t ht ht0)
  rw [hSω, withDensity_apply _ hs]
  show ∫⁻ x, _ ∂((μ0 ω).restrict s) = μα ω s
  rw [hrestr, lintegral_withDensity_eq_lintegral_mul _ hw hg]
  have hone : ∀ x ∈ s, (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (γ * α)) * ENNReal.ofReal (Real.exp (γ * f z))) x = 1 := by
    intro x hx
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 (fun h => h0 (h ▸ hx))
    have hfx := hfα x (hsb hx)
    simp only
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _), Real.rpow_def_of_pos hx0, hfx, ← Real.exp_add]
    have hz : Real.log ‖x‖ * (γ * α) + γ * (-α * Real.log ‖x‖) = 0 := by ring
    rw [hz, Real.exp_zero, ENNReal.ofReal_one]
  change ∫⁻ x in s, (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (γ * α)) * ENNReal.ofReal (Real.exp (γ * f z))) x ∂(μα ω)
    = μα ω s
  rw [setLIntegral_congr_fun hs hone, setLIntegral_const, one_mul]

/-- **Internal metric of the Weyl-scaled metric on a disc depends only on the scaling there.** For a Euclidean length
metric `d` and a compactly supported continuous `f` which equals `-α log‖·‖` on the disc `ball c ρ` (`0 < ρ`), the
internal metrics on `ball c ρ` of `weylScaling d ξ f` and of `weylScaling d ξ (-α log‖·‖)` coincide. This is the
no-shortcut step: the Weyl-scaled path infimum outside the disc does not enter the internal metric
(`RootedLocal.internalMetric_weylScaling_eq_of_eventuallyEq`, `S11r/RootedLocality.lean:230`). -/
theorem internalMetric_shift_eq_on_disc {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) {ξ α : ℝ}
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hfα : ∀ x ∈ ball c ρ, f x = -α * Real.log ‖x‖) {x y : ℂ} :
    internalMetric (fun a b => (weylScaling d ξ (fun z => -α * Real.log ‖z‖) a b).toReal) (ball c ρ) x y =
      internalMetric (fun a b => (weylScaling d ξ f a b).toReal) (ball c ρ) x y :=
  RootedLocal.internalMetric_weylScaling_eq_of_eventuallyEq (g := fun z => -α * Real.log ‖z‖) hd hf hfc isOpen_ball
    ((convex_ball c ρ).isConnected ⟨c, mem_ball_self hρ⟩)
    (fun _ hz => Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) fun w hw => hfα w hw) (x := x) (y := y)

/-- **Shifted pairing equals insertion pairing on a disc.** For a test function `φ` supported in `ball c ρ`, the
zero-insertion pairing of `h + f` equals the pairing of `h` at insertion `α`, when `f = -α log‖·‖` on `ball c ρ`. -/
theorem fieldPairing_shift_eq_on_disc {hC : (ℂ → ℝ) → ℝ} {f : ℂ → ℝ} {α : ℝ} {c : ℂ} {ρ : ℝ} (φ : ℂ → ℝ)
    (hφ : tsupport φ ⊆ ball c ρ) (hfα : ∀ x ∈ ball c ρ, f x = -α * Real.log ‖x‖) :
    fieldPairing 0 (addFunPairing hC f) φ = fieldPairing α hC φ := by
  have key : (fun x => f x * φ x) = fun x => -α * (φ x * Real.log ‖x‖) := by
    funext x
    by_cases hx : x ∈ ball c ρ
    · rw [hfα x hx]
      ring
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hφ h))
      simp [hφx]
  unfold fieldPairing addFunPairing
  rw [key, integral_const_mul]
  ring

/-! ### The `k = 0` transfer -/

/-- The decoder observation space on a disc `D` (the domain of `κ` and `m` in `LocalMeasureKernelStmt`,
`LocalMetricReplacementStmt`). -/
abbrev DecObs (D : Set ℂ) : Type := {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ

/-- The window-frequency limit `q` of the predicate sequence `E` along the windows `[N+1, 2N]`
(the limit statement inside `PhysicalAt`, `S11i/InsertionTransfer.lean` above). -/
abbrev WinLim (E : ℕ → Prop) (q : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q)

/-- A metric is nonnegative: `D z z = 0` and the triangle inequality with symmetry give `2 D z w ≥ 0`. -/
theorem nonneg_of_isEuclideanLengthMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z w : ℂ) :
    0 ≤ D z w := by
  have h1 := hD.triangle z w z
  have h2 := hD.symm z w
  have h3 := hD.self_eq_zero z
  linarith

/-- Adding the zero function to a pairing does nothing. -/
theorem addFunPairing_zero_fun (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
  funext φ
  simp [addFunPairing]

theorem lqgQ_pos_of_pos {γ : ℝ} (hγ0 : 0 < γ) : (0 : ℝ) < lqgQ γ := by
  unfold lqgQ
  positivity

/-- An insertion-`α₀` LQG measure for `P'` is one for `P` when `P ≪ P'`. -/
theorem isLQGMeasureOfField_of_ae_le {Ω : Type} [MeasurableSpace Ω] {P P' : Measure Ω} {γ α₀ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (h : P ≪ P') (hμ : IsLQGMeasureOfField P' γ α₀ hcirc μ) :
    IsLQGMeasureOfField P γ α₀ hcirc μ := by
  unfold IsLQGMeasureOfField IsLQGMeasure at *
  exact h.ae_le hμ

theorem validBall_closedBall_sub {p : ℚ × ℚ × ℚ} (hp : HarmonicBalls.FirstPassS11iStep8Exhaustion.ValidBall p) :
    closedBall (HarmonicBalls.FirstPassS11iStep8Exhaustion.ballCen p) (2 * HarmonicBalls.FirstPassS11iStep8Exhaustion.ballRad p) ⊆ ball (0 : ℂ) 1 := by
  intro z hz
  show dist z 0 < 1
  linarith [dist_triangle z (HarmonicBalls.FirstPassS11iStep8Exhaustion.ballCen p) 0, mem_closedBall.1 hz, dist_zero_right (HarmonicBalls.FirstPassS11iStep8Exhaustion.ballCen p), hp.2.2]

/-- Equal measures on every measurable subset of a set give equal restrictions to that set. -/
theorem restrict_eq_of_subset_eq {ν₁ ν₂ : Measure ℂ} {S : Set ℂ} (hS : MeasurableSet S)
    (h : ∀ s : Set ℂ, MeasurableSet s → s ⊆ S → ν₁ s = ν₂ s) : ν₁.restrict S = ν₂.restrict S := by
  ext t ht
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
  exact h _ (ht.inter hS) Set.inter_subset_right

/-- **Per-disc transfer at unit scale.** Fix a valid disc `ball c (2r)` (with `closedBall c (2r) ⊆ ball 0 1`
and `0 ∉ closedBall c (2r)`). Let `f` be the smooth cut-off of `-α log‖·‖` on that disc, `P'` the Cameron–Martin
law (`CameronMartinGFFReweighting`) under which `h + f` is a whole-plane GFF, `μ'` a zero-insertion measure of
`h + f` under `P'` (`LQGMeasureExistence`), and `𝔇` the metric of the insertion-`α` field. The unit-scale
zero-insertion statement `hzero` applies to `(P', μ', 𝔇(h + f))`. Its window-frequency limit transfers to the
insertion-`α` measure on `ball c r` through the decoders `κ`, `m` of the disc (`LocalMeasureKernelStmt`,
`LocalMetricReplacementStmt`), the eventual certificate fitting `ae_fitting_eventually_of_decoders`, and the
measure identity `zeroInsertion_shift_eq_insertion_on_disc`. -/
theorem disc_transfer_k0 {γ α q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hCC : CertificateContainments δ (pinchOmegaGeom W Q δ) V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (hCM : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{0})
    (hEx : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hLF : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hzero : AllModelsAt.{0} γ (lqgXi γ) 0 q U V W T Q' Q δ M 0)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hcr : 2 * r < ‖c‖) (hsub : closedBall c (2 * r) ⊆ ball (0 : ℂ) 1)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : IsLQGMetricOfField P γ (lqgXi γ) α hC D) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball c r →
      WinLim (fun n : ℕ => CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ)⁻¹ ^ n) z) q := by
  classical
  have hPprob : IsProbabilityMeasure P := isProbabilityMeasure_of_isWholePlaneGFF hGFF
  have hr2 : (0 : ℝ) < 2 * r := by linarith
  have hcl : closedBall c r ⊆ ball c (2 * r) := closedBall_subset_ball (by linarith)
  have hnot : (0 : ℂ) ∉ closedBall c (2 * r) := fun h => by
    have h' := mem_closedBall.1 h
    rw [dist_comm, dist_zero_right] at h'
    linarith
  have hnot0 : (0 : ℂ) ∉ ball c (2 * r) := fun h => hnot (ball_subset_closedBall h)
  -- smooth cut-off of `-α log‖·‖` on the decoder disc, and the Cameron–Martin change of law
  obtain ⟨f, hf, hfc, hf0, hfα⟩ := exists_log_cutoff_avoid_zero α hr2 hcr
  have hfcont : Continuous f := hf.continuous
  obtain ⟨P', hP'P, hPP', hGFF'⟩ := hCM Ω P hC hcirc hGFF f hf hfc hf0
  have hP'prob : IsProbabilityMeasure P' := isProbabilityMeasure_of_isWholePlaneGFF hGFF'
  have hQ : (0 : ℝ) < lqgQ γ := lqgQ_pos_of_pos hγ0
  -- zero-insertion measures of `h` (under `P`) and of `h + f` (under `P'`)
  obtain ⟨μ0, hμ0⟩ := hEx Ω P hC hcirc hGFF hγ0 hγ2 hQ
  obtain ⟨μ', hμ'⟩ := hEx Ω P' (fun ω => addFunPairing (hC ω) f)
    (fun ω r z => hcirc ω r z + Real.circleAverage f z r) hGFF' hγ0 hγ2 hQ
  have hμ'P : IsLQGMeasureOfField P γ 0 (fun ω r z => hcirc ω r z + Real.circleAverage f z r) μ' :=
    isLQGMeasureOfField_of_ae_le hPP' hμ'
  -- the two measures agree on the decoder disc
  have hmeas : ∀ᵐ ω ∂P, ∀ s : Set ℂ, MeasurableSet s → s ⊆ ball c (2 * r) → μ' ω s = μ ω s :=
    zeroInsertion_shift_eq_insertion_on_disc hfcont hfα hnot0 hGFF hγ0 hγ2 hα hμ hμ0 hμ'P
  -- the metric of `h + f`: same `𝔇` as the insertion-`α` metric
  obtain ⟨𝔇, h𝔇, hDeq⟩ : ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ (lqgXi γ) 𝔇 ∧
      ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧ ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -α * Real.log ‖x‖) u v := hD
  have hSat0 := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => (0 : ℝ)) hGFF
    (fun _ => continuous_const) (fun _ => measurable_const)
  have hbase : ∀ᵐ ω ∂P, ∀ u v, ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) u v) =
      weylScaling (𝔇 (hC ω)) (lqgXi γ) f u v := by
    filter_upwards [hSat0.ae_weylScaling] with ω hω u v
    have h := hω f hfcont u v
    simpa only [addFunPairing_zero_fun] using h
  have hLen0 : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    filter_upwards [hSat0.ae_isEuclideanLengthMetric] with ω hω
    simpa only [addFunPairing_zero_fun] using hω
  have hSat' := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ => f) hGFF
    (fun _ => hfcont) (fun _ => measurable_const)
  have hLen' : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) f)) :=
    hSat'.ae_isEuclideanLengthMetric
  have hDnn' : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ 𝔇 (addFunPairing (hC ω) f) u v :=
    hLen'.mono fun ω hω u v => nonneg_of_isEuclideanLengthMetric hω u v
  have hD'P : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ 𝔇 (addFunPairing (hC ω) f) u v ∧
      ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) u v) =
        weylScaling (𝔇 (addFunPairing (hC ω) f)) (lqgXi γ) (fun x => -(0 : ℝ) * Real.log ‖x‖) u v := by
    filter_upwards [hSat'.ae_weylScaling, hDnn'] with ω hω hnn u v
    refine ⟨hnn u v, ?_⟩
    have h := hω (fun _ => (0 : ℝ)) continuous_const u v
    simp only [addFunPairing_zero_fun, neg_zero, zero_mul] at h ⊢
    exact h
  have hD'mod : IsLQGMetricOfField P' γ (lqgXi γ) 0 (fun ω => addFunPairing (hC ω) f)
      (fun ω => 𝔇 (addFunPairing (hC ω) f)) :=
    ⟨𝔇, h𝔇, hP'P.ae_le hD'P⟩
  -- the zero-insertion statement, applied under the Cameron–Martin law
  have hz := hzero Ω P' (fun ω => addFunPairing (hC ω) f)
    (fun ω r z => hcirc ω r z + Real.circleAverage f z r) μ' (fun ω => 𝔇 (addFunPairing (hC ω) f))
    hGFF' hμ' hD'mod
  unfold PhysicalAt at hz
  simp only [pow_zero, one_mul] at hz
  have hzP := hPP'.ae_le hz
  -- decoders of the disc (`κ` for the measure, `m` for the metric)
  obtain ⟨κ, -, hκcal, -⟩ := hK c c r (2 * r) hγ0 hγ2 hr hr2 hcl hsub hnot
  obtain ⟨m, -, hm18, -⟩ := hR c c r (2 * r) hγ0 hγ2 hr hr2 hcl hsub hnot 𝔇 h𝔇
  obtain ⟨mm, hmm0, hmmm⟩ : ∃ mm : DecObs (ball c (2 * r)) → ℂ → ℂ → ℝ,
      (∀ obs x y, 0 ≤ mm obs x y) ∧ ∀ (obs : DecObs (ball c (2 * r))) (x y : ℂ)
        (h : (x, y) ∈ ball c (2 * r) ×ˢ ball c (2 * r)),
        ENNReal.ofReal (mm obs x y) = ENNReal.ofReal (m obs ⟨(x, y), h⟩) := by
    refine ⟨fun obs x y => if h : (x, y) ∈ ball c (2 * r) ×ˢ ball c (2 * r) then
      max (m obs ⟨(x, y), h⟩) 0 else 0, fun obs x y => ?_, fun obs x y h => ?_⟩
    · by_cases h : (x, y) ∈ ball c (2 * r) ×ˢ ball c (2 * r)
      · simp only [h, ↓reduceDIte]
        exact le_max_right _ _
      · simp only [h, ↓reduceDIte, le_refl]
    · simp only [h, ↓reduceDIte]
      rcases le_total (m obs ⟨(x, y), h⟩ : ℝ) 0 with h' | h'
      · rw [max_eq_right h', ENNReal.ofReal_of_nonpos h', ENNReal.ofReal_zero]
      · rw [max_eq_left h']
  -- calibration of `κ` and `mm` on the insertion-`α` model
  have hκα : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (κ (localMeanZeroObs α (ball c (2 * r)) (hC ω))).restrict (ball c (2 * r)) =
        ENNReal.ofReal a • (μ ω).restrict (ball c (2 * r)) :=
    hκcal α hα Ω P hC hcirc μ hGFF hμ
  have hint : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ ball c (2 * r), ∀ y ∈ ball c (2 * r),
      ENNReal.ofReal (mm (localMeanZeroObs α (ball c (2 * r)) (hC ω)) x y) =
        ENNReal.ofReal b * internalMetric (D ω) (ball c (2 * r)) x y := by
    filter_upwards [hm18 α hα Ω P hC hcirc hGFF, hDeq] with ω hω hDω
    obtain ⟨b, hb, hbm⟩ := hω
    refine ⟨b, hb, fun x hx y hy => ?_⟩
    have hxy : (x, y) ∈ ball c (2 * r) ×ˢ ball c (2 * r) := ⟨hx, hy⟩
    rw [hmmm _ x y hxy]
    have hfun : D ω = fun u v =>
        (weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun z => -α * Real.log ‖z‖) u v).toReal := by
      funext u v
      rw [← (hDω u v).2, ENNReal.toReal_ofReal (hDω u v).1]
    rw [hfun]
    exact hbm ⟨(x, y), hxy⟩
  have hDnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y := hDeq.mono fun ω h x y => (h x y).1
  have hLenα : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) :=
    HarmonicBalls.FirstPassS11iStep8LengthMetric.ae_isEuclideanLengthMetric_of_fieldAxioms
      (hLF Ω P γ (lqgXi γ) α hC hcirc) hGFF hγ0 hγ2 hα h𝔇 hDeq
  have hfitα := HarmonicBalls.FirstPassS11iStep8Fitting.ae_fitting_eventually_of_decoders α δ M
    (pinchOmegaGeom W Q δ) U V W T Q' Q c (2 * r) hC μ D κ mm hCC hU hκα
    (ae_of_all P fun ω x y => hmm0 _ x y) hDnn hLenα hint
  -- the zero-insertion side: same decoders, identical observations and internal metrics
  have hobs : ∀ ω, (fun φ : {φ : ℂ → ℝ // IsTestFunction (ball c (2 * r)) φ ∧ ∫ x, φ x = 0} =>
      fieldPairing 0 (addFunPairing (hC ω) f) φ.1) =
        localMeanZeroObs α (ball c (2 * r)) (hC ω) := by
    intro ω
    funext φ
    exact fieldPairing_shift_eq_on_disc φ.1 φ.2.1.2.2 hfα
  have hκ0 : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (κ (fun φ => fieldPairing 0 (addFunPairing (hC ω) f) φ.1)).restrict (ball c (2 * r)) =
        ENNReal.ofReal a • (μ' ω).restrict (ball c (2 * r)) := by
    filter_upwards [hκα, hmeas] with ω hκω hmω
    obtain ⟨a, ha, hωa⟩ := hκω
    refine ⟨a, ha, ?_⟩
    have hres : (μ' ω).restrict (ball c (2 * r)) = (μ ω).restrict (ball c (2 * r)) :=
      restrict_eq_of_subset_eq measurableSet_ball hmω
    rw [hobs ω, hres]
    exact hωa
  have hD'eq : ∀ᵐ ω ∂P, internalMetric (𝔇 (addFunPairing (hC ω) f)) (ball c (2 * r)) =
      internalMetric (D ω) (ball c (2 * r)) := by
    filter_upwards [hbase, hDeq, hLen0, hDnn'] with ω hbω hDω hLω hnn
    have hF : 𝔇 (addFunPairing (hC ω) f) = fun u v =>
        (weylScaling (𝔇 (hC ω)) (lqgXi γ) f u v).toReal := by
      funext u v
      rw [← hbω u v, ENNReal.toReal_ofReal (hnn u v)]
    have hG : D ω = fun u v =>
        (weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun z => -α * Real.log ‖z‖) u v).toReal := by
      funext u v
      rw [← (hDω u v).2, ENNReal.toReal_ofReal (hDω u v).1]
    rw [hF, hG]
    funext x y
    exact (internalMetric_shift_eq_on_disc (ξ := lqgXi γ) (α := α) hLω hfcont hfc hr2 hfα).symm
  have hint0 : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ ball c (2 * r), ∀ y ∈ ball c (2 * r),
      ENNReal.ofReal (mm (fun φ => fieldPairing 0 (addFunPairing (hC ω) f) φ.1) x y) =
        ENNReal.ofReal b * internalMetric (𝔇 (addFunPairing (hC ω) f)) (ball c (2 * r)) x y := by
    filter_upwards [hint, hD'eq] with ω hω heq
    obtain ⟨b, hb, hbx⟩ := hω
    refine ⟨b, hb, fun x hx y hy => ?_⟩
    rw [hobs ω, heq]
    exact hbx x hx y hy
  have hfit0 := HarmonicBalls.FirstPassS11iStep8Fitting.ae_fitting_eventually_of_decoders 0 δ M
    (pinchOmegaGeom W Q δ) U V W T Q' Q c (2 * r) (fun ω => addFunPairing (hC ω) f) μ'
    (fun ω => 𝔇 (addFunPairing (hC ω) f)) κ mm hCC hU hκ0 (ae_of_all P fun ω x y => hmm0 _ x y)
    hDnn' hLen' hint0
  -- the eventual certificate identity at every centre of the decoder disc
  have hiff : ∀ᵐ ω ∂P, ∀ z ∈ ball c (2 * r), ∀ᶠ n : ℕ in atTop,
      (CertificateEvent (μ' ω) (𝔇 (addFunPairing (hC ω) f)) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          ((2 : ℝ)⁻¹ ^ n) z ↔
        CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ n) z) := by
    filter_upwards [hfit0, hfitα] with ω h0 h1 z hz
    filter_upwards [h0 z hz, h1 z hz] with n e0 e1
    have e0' : CertificateEvent (κ (localMeanZeroObs α (ball c (2 * r)) (hC ω)))
        (mm (localMeanZeroObs α (ball c (2 * r)) (hC ω))) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ)⁻¹ ^ n) z ↔
        CertificateEvent (μ' ω) (𝔇 (addFunPairing (hC ω) f)) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          ((2 : ℝ)⁻¹ ^ n) z := by
      rw [← hobs ω]
      exact e0
    exact e0'.symm.trans e1
  -- transfer the window limit from `μ'` to `μ` on the decoder disc, then to the root ball
  filter_upwards [hzP, hiff, hmeas] with ω hzω hiffω hmω
  have hres : (μ' ω).restrict (ball c (2 * r)) = (μ ω).restrict (ball c (2 * r)) :=
    restrict_eq_of_subset_eq measurableSet_ball hmω
  have hA := ae_restrict_of_ae (s := ball c (2 * r)) hzω
  rw [hres] at hA
  have hB : ∀ᵐ z ∂(μ ω), z ∈ ball c (2 * r) → (z ∈ ball (0 : ℂ) 1 →
      WinLim (fun n : ℕ => CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ)⁻¹ ^ n) z) q) := by
    refine (ae_restrict_iff' measurableSet_ball).1 ?_
    filter_upwards [hA, ae_restrict_mem measurableSet_ball] with z hz hzs
    intro hz1
    exact (tendsto_window_iff_of_eventually_iff (hiffω z hzs) q).mp (hz hz1)
  filter_upwards [hB] with z hz hzr
  have hzd : z ∈ ball c (2 * r) := ball_subset_ball (by linarith) hzr
  exact hz hzd (hsub (ball_subset_closedBall hzd))

/-- **Insertion transfer at unit scale, universe 0.** If the zero-insertion physical frequency statement holds at
scale `2^0 = 1` for all models (`hzero`), then so does the insertion-`α` statement, for `α < lqgQ γ`. The
Cameron–Martin change of law (`CameronMartinGFFReweighting`), the existence of LQG measures
(`LQGMeasureExistence`), the non-atomicity of insertion-`α` measures (`LQGMeasureNonatomic`) and the decoder
inputs (`LocalMeasureKernelStmt`, `LocalMetricReplacementStmt`, `LQGMetricFieldAxiomsUnivFrozen`) enter as binders.
Universe `0`, since the metric axioms are stated for `Ω : Type`. -/
theorem allModelsAt_insertion_of_zero_k0 {γ α q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hCM : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{0})
    (hEx : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hNon : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α hC hcirc)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hLF : LQGMetricFieldAxiomsUnivFrozen.{0})
    (hzero : AllModelsAt.{0} γ (lqgXi γ) 0 q U V W T Q' Q δ M 0) :
    AllModelsAt.{0} γ (lqgXi γ) α q U V W T Q' Q δ M 0 := by
  intro Ω _ P hC hcirc μ D hGFF hμ hD
  classical
  have hPprob : IsProbabilityMeasure P := isProbabilityMeasure_of_isWholePlaneGFF hGFF
  have hU : U ⊆ closedBall 0 7 := by
    intro z hz
    have h2 : dist z 0 < 2 := (hgeom.U_subset hz).1
    exact mem_closedBall.2 (by linarith)
  have hCC := FirstPassS11ap.certificateContainments_of_buffered hgeom
  have hNonω : ∀ᵐ ω ∂P, μ ω {0} = 0 :=
    (hNon Ω P hC hcirc hGFF hγ0 hγ2 hα μ hμ).mono fun ω h => h 0
  have hΦ : ∀ p : ℚ × ℚ × ℚ, HarmonicBalls.FirstPassS11iStep8Exhaustion.ValidBall p → ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (HarmonicBalls.FirstPassS11iStep8Exhaustion.ballCen p) (HarmonicBalls.FirstPassS11iStep8Exhaustion.ballRad p) →
      WinLim (fun n : ℕ => CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ)⁻¹ ^ n) z) q := fun p hp =>
    disc_transfer_k0 hγ0 hγ2 hα hCC hU hCM hEx hK hR hLF hzero hp.1 hp.2.1 (validBall_closedBall_sub hp)
      Ω P hC hcirc μ D hGFF hμ hD
  have hcov := HarmonicBalls.FirstPassS11iStep8Exhaustion.ae_forall_of_cover P μ
    (fun ω z => WinLim (fun n : ℕ => CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ)⁻¹ ^ n) z) q) hNonω hΦ
  unfold PhysicalAt
  simp only [pow_zero, one_mul]
  exact hcov

end HarmonicBalls.FirstPassS11iInsertionTransfer

#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.tendsto_window_iff_of_eventually_iff
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.exists_log_cutoff_avoid_zero
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.restrict_eq_withDensity_of_off_zero
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.zeroInsertion_shift_eq_insertion_on_disc
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.internalMetric_shift_eq_on_disc
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.fieldPairing_shift_eq_on_disc
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.disc_transfer_k0
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.allModelsAt_insertion_of_zero_k0
