import HarmonicBalls.FirstPass.S11i.HzoomUnitBallDecoders
import HarmonicBalls.FirstPass.S8c.WeylOffOriginDerived
import HarmonicBalls.FirstPass.S11d.Dyadic
import HarmonicBalls.Proofs.GFF.BackgroundChargeParameter

/-!
# The fitting identity `hfit` of the doubled-disc inputs (fp-S11i-hzoom-scale-e, n4)

For a valid ball `p` (root disc `ball c r`, decoder disc `ball c (2 r)`):

* `kernelF_unrooted`: the unrooted clause of the finite decoder kernel `κF_p` (exists_finite_localMeasureKernel).
* `goodObs`: the good set `H_good` of the metric decoder (observations whose decoder is a length metric).
* `ae_obs_mem_good`: the physical observation lies in `H_good` almost surely (B3 `ae_markedObs_mem_modificationSet`,
  rooted length property `rootedLengthProperty`, positivity `hPos` on a dyadic square in the root disc).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal Classical
open ProbabilityTheory
open HarmonicBalls.FirstPassS11iStep8Exhaustion
open HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders

namespace HarmonicBalls.FirstPassS11iHzoomUnitBallFit

universe u

/-- The unrooted clause of the finite decoder kernel `κF_p` (first clause of `LocalMeasureKernelStmt`, through
`exists_finite_localMeasureKernel`). -/
lemma kernelF_unrooted {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂) {p : ℚ × ℚ × ℚ}
    (hp : ValidBall p) :
    IsFiniteKernel (kernelF hγ0 hγ2 hK p) ∧
    ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (kernelF hγ0 hγ2 hK p (localMeanZeroObs α (ball (ballCen p) (2 * ballRad p)) (hC ω))).restrict
            (ball (ballCen p) (2 * ballRad p)) =
          ENNReal.ofReal a • (μ ω).restrict (ball (ballCen p) (2 * ballRad p)) := by
  obtain ⟨hr, hcl, hunit, h0⟩ := validBall_facts hp
  have hex := FirstPassS11ahFinite.exists_finite_localMeasureKernel
    (hK (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p)) hγ0 hγ2 hr (by linarith) hcl hunit h0
  have hk : kernelF hγ0 hγ2 hK p = Classical.choose hex := by
    simp only [kernelF, hp, dite_true]
  rw [hk]
  exact ⟨(Classical.choose_spec hex).1, (Classical.choose_spec hex).2.1⟩

/-- The good set of the metric decoder: the observations whose decoder on `ball c (2 r)` is a length metric. -/
def goodObs {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ) :
    Set (FirstPassS11ahFinite.LocalObs (ballCen p) (2 * ballRad p)) :=
  {ℓ | FirstPassS11ah.IsLengthMetricOn (ball (ballCen p) (2 * ballRad p))
      (FirstPassS11ah.decoderOn (ball (ballCen p) (2 * ballRad p)) (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p ℓ))}

/-- The metric replacement `metricCont` of a valid ball is `Classical.choose` of `LocalMetricReplacementStmt`. -/
lemma metricCont_eq {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) {p : ℚ × ℚ × ℚ} (hp : ValidBall p) :
    metricCont hγ0 hγ2 hR 𝔇 h𝔇 p = Classical.choose (hR (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p) hγ0 hγ2
      (validBall_facts hp).1 (by linarith [(validBall_facts hp).1]) (validBall_facts hp).2.1
      (validBall_facts hp).2.2.1 (validBall_facts hp).2.2.2 𝔇 h𝔇) := by
  simp only [metricCont, hp, dite_true]

/-- **The physical observation lies in the good set** (`hfit`, chat 238 section 3, "Why B3 enters here"). -/
theorem ae_obs_mem_good {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hPos : HarmonicBalls.LQGMeasureSquarePositiveFrozen.{0})
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ) (hNon : ∀ᵐ ω ∂P, μ ω {0} = 0)
    (p : ℚ × ℚ × ℚ) (hp : ValidBall p) :
    ∀ᵐ ω ∂P, (fun φ : {φ : ℂ → ℝ // IsTestFunction (ball (ballCen p) (2 * ballRad p)) φ ∧ ∫ x, φ x = 0} =>
        fieldPairing 0 (hC ω) φ.1) ∈ goodObs hγ0 hγ2 hR 𝔇 h𝔇 p := by
  obtain ⟨hr, hcl, hunit, h0⟩ := validBall_facts hp
  have hr2 : (0 : ℝ) < 2 * ballRad p := by linarith
  have hα : (0 : ℝ) < lqgQ γ := lqgQ_pos hγ0
  have hspec := Classical.choose_spec (hR (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p) hγ0 hγ2 hr hr2
    hcl hunit h0 𝔇 h𝔇)
  have hmc := metricCont_eq hγ0 hγ2 hR 𝔇 h𝔇 hp
  have hmeas : Measurable (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p) := by
    rw [hmc]
    exact hspec.1
  have hH : MeasurableSet (goodObs hγ0 hγ2 hR 𝔇 h𝔇 p) :=
    FirstPassS11ahLocalObsHaeGood.hGood_of_measurable hr2 hmeas
  -- rooted clause (20) at insertion 0, for the model
  have hid := hspec.2.2 0 hα Ω P hC hcirc hG
  rw [← hmc] at hid
  have hrooted := FirstPassS11ah.rootedLengthProperty hG h𝔇 hfr hγ0 hγ2 hα hcl h0 (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p) hid
  have hrefH : ∀ᵐ z ∂(volume.restrict (ball (ballCen p) (ballRad p))), ∀ᵐ ω ∂P,
      (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2 ∈ goodObs hγ0 hγ2 hR 𝔇 h𝔇 p :=
    hrooted
  -- B3: the marked observations lie in the good set almost surely
  have hmark := HarmonicBalls.FirstPassS11iStep8MarkedMem.ae_markedObs_mem_modificationSet
    (hWeyl := localLQGInsertionWeylOffOrigin_derived) γ 0 hγ0 hγ2 hα hcl hunit μ μ hA10 hG hμ hμ hNon hNon hH hrefH
  -- positivity of the mass of the root disc (hPos on a dyadic square inside it)
  obtain ⟨_, S₂, _, hS₂, _, hS₂U⟩ := HarmonicBalls.exists_closedDyadicSquare_pair (isOpen_ball : IsOpen (ball (ballCen p) (ballRad p)))
    (mem_ball_self hr)
  have hpos := hPos γ 0 hγ0 hγ2 hα Ω P hC hcirc μ hG hμ S₂ hS₂
  filter_upwards [hmark, hpos] with ω hω hωpos
  have hne : (μ ω).restrict (ball (ballCen p) (ballRad p)) ≠ 0 := by
    intro h0'
    have h1 : (μ ω).restrict (ball (ballCen p) (ballRad p)) univ = 0 := by rw [h0']; rfl
    rw [Measure.restrict_apply_univ] at h1
    have h2 := measure_mono (μ := μ ω) hS₂U
    exact absurd (h2.trans_eq h1) (not_le.2 hωpos)
  have : (ae ((μ ω).restrict (ball (ballCen p) (ballRad p)))).NeBot := ae_neBot.2 hne
  obtain ⟨z, hz⟩ := hω.exists
  exact hz

/-- A real identity from an `ENNReal.ofReal` identity, when a vanishing `e` forces a vanishing `m`. -/
lemma real_eq_of_ofReal_eq {m e b : ℝ} (hb : 0 < b) (he : 0 ≤ e) (hsep : e = 0 → m = 0)
    (h : ENNReal.ofReal m = ENNReal.ofReal (b * e)) : m = b * e := by
  have hm : 0 ≤ m := by
    by_contra hneg
    have hneg' : m < 0 := not_le.1 hneg
    have h0 : ENNReal.ofReal m = 0 := ENNReal.ofReal_of_nonpos hneg'.le
    rw [h0] at h
    have hle : b * e ≤ 0 := ENNReal.ofReal_eq_zero.1 h.symm
    have he0 : e = 0 := le_antisymm (by nlinarith) he
    have := hsep he0
    linarith
  exact (ENNReal.ofReal_eq_ofReal_iff hm (mul_nonneg hb.le he)).1 h

/-- The root disc lies in the closed unit-scale window: `U ⊆ closedBall 0 7` (from the buffered geometry). -/
lemma subset_closedBall_of_buffered {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ) : U ⊆ closedBall 0 7 := by
  intro x hx
  have hxV : x ∈ V := FirstPassS11i.BufferedGeom.closure_U_subset hgeo (subset_closure hx)
  have hxW : x ∈ W := FirstPassS11i.BufferedGeom.closure_V_subset hgeo (subset_closure hxV)
  exact (FirstPassS11ap.certificateContainments_of_buffered hgeo).W_thick
    (self_subset_thickening (by linarith [hgeo.delta_pos]) W hxW)

/-- **The fitting identity `hfit`** (chat 238 section 3, on the doubled disc, with the metric index of the rulings).
For a whole-plane model with LQG metric `𝔇` (`hD`: the a.s. identity of `D`), almost surely, for every root `z` in
`ball c r`, eventually in `n`, the decoded certificate event (kernel `ballKernel`, metric `ballMetric`) and the physical
one (`μ`, `D`) agree. -/
theorem ae_eventually_ballFit {γ ξ δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hPos : HarmonicBalls.LQGMeasureSquarePositiveFrozen.{0})
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ) (hNon : ∀ᵐ ω ∂P, μ ω {0} = 0)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -0 * Real.log ‖x‖) u v)
    (p : ℚ × ℚ × ℚ) (hp : ValidBall p) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (ballCen p) (2 * ballRad p), ∀ᶠ n : ℕ in atTop,
      (FirstPassS11i.CertificateEvent (ballKernel hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1))
          (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (fun φ => fieldPairing 0 (hC ω) φ.1))
          (pinchOmegaGeom W Q δ) U V W T Q' Q δ M (FirstPassS11ah.certScale n) z ↔
        FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          (FirstPassS11ah.certScale n) z) := by
  classical
  obtain ⟨hr, hcl, hunit, h0⟩ := validBall_facts hp
  have hr2 : (0 : ℝ) < 2 * ballRad p := by linarith
  have hα : (0 : ℝ) < lqgQ γ := lqgQ_pos hγ0
  have hBo : IsOpen (ball (ballCen p) (2 * ballRad p)) := isOpen_ball
  obtain ⟨hfinK, hK1⟩ := kernelF_unrooted hγ0 hγ2 hK hp
  have hmc := metricCont_eq hγ0 hγ2 hR 𝔇 h𝔇 hp
  have hspec := Classical.choose_spec (hR (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p) hγ0 hγ2 hr hr2
    hcl hunit h0 𝔇 h𝔇)
  have hM1 := hspec.2.1 0 hα Ω P hC hcirc hG
  rw [← hmc] at hM1
  have hKa := hK1 0 hα Ω P hC hcirc μ hG hμ
  have hgood := ae_obs_mem_good hγ0 hγ2 hR h𝔇 hfr hPos hG hμ hA10 hNon p hp
  have hEuc := FirstPassS11ah.ae_isEuclideanLengthMetric_of_lqg h𝔇 hG
  have hUsub := subset_closedBall_of_buffered hgeo
  have hCC := FirstPassS11ap.certificateContainments_of_buffered hgeo
  filter_upwards [hKa, hM1, hgood, hD, hEuc] with ω hκω hbω hgoodω hDω hEω
  obtain ⟨a, ha, hκa⟩ := hκω
  obtain ⟨b, hb, hmb⟩ := hbω
  have hκa' : (kernelF hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1)).restrict
      (ball (ballCen p) (2 * ballRad p)) = ENNReal.ofReal a • (μ ω).restrict (ball (ballCen p) (2 * ballRad p)) := hκa
  have hgoodω' : FirstPassS11ah.IsLengthMetricOn (ball (ballCen p) (2 * ballRad p))
      (FirstPassS11ah.decoderOn (ball (ballCen p) (2 * ballRad p))
        (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p (fun φ => fieldPairing 0 (hC ω) φ.1))) := hgoodω
  -- the weight of the physical metric is the metric itself
  have hfun : (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -0 * Real.log ‖z‖) u v).toReal) = D ω := by
    funext u v
    rw [← (hDω u v).2, ENNReal.toReal_ofReal (hDω u v).1]
  unfold localMeanZeroObs at hmb
  rw [hfun] at hmb
  have hnn : ∀ x y, 0 ≤ 𝔇 (hC ω) x y := fun x y => by
    have h1 := hEω.triangle x y x
    rw [hEω.self_eq_zero, hEω.symm y x] at h1
    linarith
  have hDeq : D ω = 𝔇 (hC ω) := by
    funext u v
    have hzero : weylScaling (𝔇 (hC ω)) ξ (fun x => -0 * Real.log ‖x‖) u v = ENNReal.ofReal (𝔇 (hC ω) u v) := by
      have hf : (fun x : ℂ => -(0 : ℝ) * Real.log ‖x‖) = fun _ => 0 := by
        funext x
        simp
      rw [hf]
      exact hEω.weylScaling_zero ξ u v
    exact (ENNReal.ofReal_eq_ofReal_iff (hDω u v).1 (hnn u v)).1 ((hDω u v).2.trans hzero)
  have hEucD : IsEuclideanLengthMetric (D ω) := by
    rw [hDeq]
    exact hEω
  -- the decoded metric is `b · D` on the small closed balls of the root (no-shortcut radius `ρ`)
  have hdecEq : ∀ z ∈ ball (ballCen p) (2 * ballRad p), ∃ ρ : ℝ, 0 < ρ ∧ closedBall z ρ ⊆ ball (ballCen p) (2 * ballRad p) ∧
      ∀ x ∈ closedBall z ρ, ∀ y ∈ closedBall z ρ,
        ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (fun φ => fieldPairing 0 (hC ω) φ.1) x y = b * D ω x y := by
    intro z hz
    obtain ⟨ρ, hρ, hρsub, hρeq⟩ := FirstPassS11at.eq_internalMetric_on_small_ball_at hEucD hBo hz
    refine ⟨ρ, hρ, hρsub, fun x hx y hy => ?_⟩
    have hxB : x ∈ ball (ballCen p) (2 * ballRad p) := hρsub hx
    have hyB : y ∈ ball (ballCen p) (2 * ballRad p) := hρsub hy
    have hgd : ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (fun φ => fieldPairing 0 (hC ω) φ.1) x y =
        FirstPassS11ah.decoderOn (ball (ballCen p) (2 * ballRad p))
          (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p (fun φ => fieldPairing 0 (hC ω) φ.1)) x y := by
      unfold ballMetric
      simp only [hgoodω', ↓reduceIte]
    have hdq : FirstPassS11ah.decoderOn (ball (ballCen p) (2 * ballRad p))
          (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p (fun φ => fieldPairing 0 (hC ω) φ.1)) x y =
        metricCont hγ0 hγ2 hR 𝔇 h𝔇 p (fun φ => fieldPairing 0 (hC ω) φ.1) ⟨(x, y), Set.mk_mem_prod hxB hyB⟩ := by
      simp only [FirstPassS11ah.decoderOn, Set.mk_mem_prod hxB hyB, dite_true]
    rw [hgd, hdq]
    refine real_eq_of_ofReal_eq hb (hDω x y).1 ?_ ?_
    · intro hzero
      have hxy : x = y := hEucD.eq_of_eq_zero x y hzero
      rw [← hdq, hxy]
      exact hgoodω'.self_eq_zero y hyB
    · rw [hmb ⟨(x, y), Set.mk_mem_prod hxB hyB⟩]
      dsimp only
      rw [← hρeq x hx y hy, ← ENNReal.ofReal_mul hb.le]
  -- the normalized kernel of the root disc has the same measure as the physical one, up to a positive scalar
  have hxfin : (kernelF hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1)) (ball (ballCen p) (2 * ballRad p)) ≠ ⊤ :=
    ne_top_of_le_ne_top (Kernel.bound_lt_top _).ne (Kernel.measure_le_bound _ _ _)
  have hsum0 : 1 + (kernelF hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1))
      (ball (ballCen p) (2 * ballRad p)) ≠ 0 := by
    simp
  have hsum : 1 + (kernelF hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1))
      (ball (ballCen p) (2 * ballRad p)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hxfin⟩
  have hs0 : (1 + (kernelF hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1))
      (ball (ballCen p) (2 * ballRad p)))⁻¹ * ENNReal.ofReal a ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.2 hsum) (ENNReal.ofReal_pos.2 ha).ne'
  have hstop : (1 + (kernelF hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1))
      (ball (ballCen p) (2 * ballRad p)))⁻¹ * ENNReal.ofReal a ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hsum0) ENNReal.ofReal_ne_top
  have hBK : (ballKernel hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1)).restrict
      (ball (ballCen p) (2 * ballRad p)) =
      ENNReal.ofReal ((((1 + (kernelF hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1))
        (ball (ballCen p) (2 * ballRad p)))⁻¹ * ENNReal.ofReal a)).toReal) •
        (μ ω).restrict (ball (ballCen p) (2 * ballRad p)) := by
    have h1 : ballKernel hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1) =
        (1 + (kernelF hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1))
          (ball (ballCen p) (2 * ballRad p)))⁻¹ • (kernelF hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1)).restrict
            (ball (ballCen p) (2 * ballRad p)) :=
      FirstPassS11iStep8Modified.discNormalizedKernel_apply _ _ _
    rw [h1, Measure.restrict_smul, Measure.restrict_restrict_of_subset subset_rfl, hκa', smul_smul,
      ENNReal.ofReal_toReal hstop]
  have hpos : 0 < ((1 + (kernelF hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1))
      (ball (ballCen p) (2 * ballRad p)))⁻¹ * ENNReal.ofReal a).toReal :=
    ENNReal.toReal_pos hs0 hstop
  -- the fitting identity, root by root
  intro z hz
  obtain ⟨ρ, hρ, hρsub, hdz⟩ := hdecEq z hz
  have hev : ∀ᶠ n : ℕ in atTop, 7 * FirstPassS11ah.certScale n < ρ := by
    have ht : Tendsto (fun n : ℕ => 7 * FirstPassS11ah.certScale n) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 7
      simpa [FirstPassS11ah.certScale] using h
    exact ht.eventually (gt_mem_nhds hρ)
  filter_upwards [hev] with n hn
  have hsub : closedBall z (7 * FirstPassS11ah.certScale n) ⊆ closedBall z ρ :=
    closedBall_subset_closedBall hn.le
  have hsubB := hsub.trans hρsub
  have hr_n : 0 < FirstPassS11ah.certScale n := by
    unfold FirstPassS11ah.certScale
    positivity
  have hμn : (ballKernel hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1)).restrict
      (closedBall z (7 * FirstPassS11ah.certScale n)) =
      (ENNReal.ofReal ((((1 + (kernelF hγ0 hγ2 hK p (fun φ => fieldPairing 0 (hC ω) φ.1))
        (ball (ballCen p) (2 * ballRad p)))⁻¹ * ENNReal.ofReal a)).toReal) • μ ω).restrict
        (closedBall z (7 * FirstPassS11ah.certScale n)) := by
    rw [← Measure.restrict_restrict_of_subset hsubB, hBK, Measure.restrict_smul,
      Measure.restrict_restrict_of_subset hsubB, Measure.restrict_smul]
  have hDn : Set.EqOn (Function.uncurry (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (fun φ => fieldPairing 0 (hC ω) φ.1)))
      (Function.uncurry (fun x y => b * D ω x y))
      (closedBall z (7 * FirstPassS11ah.certScale n) ×ˢ closedBall z (7 * FirstPassS11ah.certScale n)) := by
    intro q hq
    exact hdz q.1 (hsub hq.1) q.2 (hsub hq.2)
  exact certificateEvent_of_restrict_scalar_at _ (μ ω) _ (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
    (FirstPassS11ah.certScale n) z hpos hb hCC hUsub hr_n hμn hDn

end HarmonicBalls.FirstPassS11iHzoomUnitBallFit

#print axioms HarmonicBalls.FirstPassS11iHzoomUnitBallFit.ae_obs_mem_good
#print axioms HarmonicBalls.FirstPassS11iHzoomUnitBallFit.real_eq_of_ofReal_eq
