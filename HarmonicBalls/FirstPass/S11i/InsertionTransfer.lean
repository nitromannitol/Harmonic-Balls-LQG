import HarmonicBalls.FirstPass.S11i.Step8PhysReduction
import HarmonicBalls.FirstPass.S11r.LogSingularCutoff
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived
import HarmonicBalls.FirstPass.S11asWeyl
import HarmonicBalls.FirstPass.S11r.RootedLocality

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

end HarmonicBalls.FirstPassS11iInsertionTransfer

#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.tendsto_window_iff_of_eventually_iff
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.exists_log_cutoff_avoid_zero
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.restrict_eq_withDensity_of_off_zero
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.zeroInsertion_shift_eq_insertion_on_disc
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.internalMetric_shift_eq_on_disc
#print axioms HarmonicBalls.FirstPassS11iInsertionTransfer.fieldPairing_shift_eq_on_disc
