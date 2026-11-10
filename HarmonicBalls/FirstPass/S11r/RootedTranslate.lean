import HarmonicBalls.FirstPass.S11h.WeylShiftUniv
import HarmonicBalls.FirstPass.S11at.Producers
import HarmonicBalls.FirstPass.S11c.TranslateField11_7
import HarmonicBalls.FirstPass.S11c.CoordRooted11_7
import HarmonicBalls.Steps.Sec11.WeylLocality
import HarmonicBalls.Steps.Sec11.WeylHomeomorph
import HarmonicBalls.Steps.Sec11.WeylScalingOrder
import HarmonicBalls.Steps.Sec11.WeylMetricConstantScaling
import HarmonicBalls.Steps.Sec11.InternalMetricHomeomorph
import HarmonicBalls.Steps.Sec11.MetricConstantScaling
import HarmonicBalls.Steps.Sec11.PinchNormalizedLocalEvent

/-!
# The rooted Weyl metric at translated points (the metric clause `hLoc` of Lemma 11.13)

For a whole-plane field `h^ℂ = hC ω` with circle averages `hcirc`, a root `z ≠ 0`, the rooted Weyl metric
`rootedWeylMetric 𝔇 ξ γ hC z ω` is the Weyl scaling of `𝔇 (h^ℂ)` by `-γ log|· - z| + γ log max(1,|·|)`.
Translating by `z` and normalising the field at `z` (`S11c.translatedPairing`, circle average `c = hcirc ω 1 z`),
the translated rooted metric equals `e^{ξ c}` times the Weyl scaling of the centred metric by the continuous weight
`γ log max(1,|· + z|)`. This weight vanishes on the preimage of a window `B ⊆ B₁(0)`, so on that window the
internal metrics agree up to `e^{ξ c}` (Steps A-D of the chat 235 ruling; Bou-Rabee-Gwynne, arXiv:2208.11795,
Fact 2.2 I-IV, corrected draft lines 418-457, and Fact 2.2 III for the continuous outer weight, line 445).

Frozen inputs (existing, none new): `LQGMetricFieldAxiomsUnivFrozen` (I), `LQGMetricSatisfiesAxiomsUnivFrozen`
(IV coordinate change; III for random continuous shifts), `LQGMetricLengthUnivFrozen`,
`RootedPhysicalMetricContinuousAtInsertionFrozen`, `WeylMetricCompositionContinuousOuterFrozen`,
`LQGMetricExponentPositive`.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

universe u

/-- The rooted Weyl metric of clause (20) of `LocalMetricReplacementStmt` at background `0`: the real part of the Weyl
scaling of `𝔇 (hC ω)` by the rooted weight `-γ log|· - z| + γ log max(1,|·|)`. -/
noncomputable def rootedWeylMetric (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ γ : ℝ) {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ)
    (z : ℂ) (ω : Ω) : ℂ → ℂ → ℝ :=
  fun u v => (weylScaling (𝔇 (hC ω)) ξ
    (fun w => -(0 : ℝ) * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) u v).toReal

/-- The centred Weyl metric of the translated normalised field at insertion `γ` (background `α₀ = γ`): the real metric
of `IsLQGMetricOfField P γ ξ γ (translatedPairing hC hcirc z)`. -/
noncomputable def centredWeylMetric (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ γ : ℝ) {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (ω : Ω) : ℂ → ℂ → ℝ :=
  fun u v => (weylScaling (𝔇 (S11c.translatedPairing hC hcirc z ω)) ξ (fun x => -γ * Real.log ‖x‖) u v).toReal

/-! ### Deterministic helpers -/

theorem nonneg_of_isEuclideanLengthMetric' {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) :
    0 ≤ D x y := by
  have h := hD.triangle x y x
  rw [hD.self_eq_zero, hD.symm y x] at h
  linarith

/-- A length metric admits, between any two points, a path of finite `D`-length. -/
theorem exists_path_pathLength_lt_top {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) :
    ∃ P : Path x y, pathLength D P < ⊤ := by
  have hlt : internalMetric D univ x y < ⊤ := by
    rw [← hD.ofReal_eq_internalMetric x y]
    exact ENNReal.ofReal_lt_top
  obtain ⟨P, hP⟩ := iInf_lt_iff.mp hlt
  obtain ⟨-, hP2⟩ := iInf_lt_iff.mp hP
  exact ⟨P, hP2⟩

/-- Weyl scaling of a length metric by a continuous weight is finite everywhere. -/
theorem weylScaling_ne_top_of_continuous' {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ : ℝ) {f : ℂ → ℝ}
    (hf : Continuous f) (x y : ℂ) : weylScaling D ξ f x y ≠ ⊤ := by
  obtain ⟨P, hP⟩ := exists_path_pathLength_lt_top hD x y
  exact (weylScaling_pathLength_ne_top_of_range hD ξ (O := univ) hf.continuousOn P (fun t => mem_univ _) hP).1

/-- Translation invariance of the length-metric property. -/
theorem isEuclideanLengthMetric_addRight' {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z : ℂ) :
    IsEuclideanLengthMetric (fun x y => D (x + z) (y + z)) := by
  refine
    { self_eq_zero := fun x => hD.self_eq_zero _
      eq_of_eq_zero := fun x y h => add_right_cancel (hD.eq_of_eq_zero _ _ h)
      symm := fun x y => hD.symm _ _
      triangle := fun x y w => hD.triangle _ _ _
      isOpen_iff := ?_
      ofReal_eq_internalMetric := ?_ }
  · intro U
    have hS : IsOpen U ↔ IsOpen ((fun w => w - z) ⁻¹' U) := by
      constructor
      · intro h
        exact h.preimage (continuous_id.sub continuous_const)
      · intro h
        have hpre : (fun w : ℂ => w + z) ⁻¹' ((fun w : ℂ => w - z) ⁻¹' U) = U := by
          ext w
          simp
        have := h.preimage (f := fun w : ℂ => w + z) (by fun_prop)
        rwa [hpre] at this
    rw [hS, hD.isOpen_iff]
    constructor
    · intro h x hx
      obtain ⟨ε, hε, hball⟩ := h (x + z) (by simpa using hx)
      refine ⟨ε, hε, fun w hw => ?_⟩
      have := hball (w + z) hw
      simpa using this
    · intro h p hp
      obtain ⟨ε, hε, hball⟩ := h (p - z) hp
      refine ⟨ε, hε, fun q hq => ?_⟩
      have := hball (q - z) (by simpa using hq)
      simpa using this
  · intro x y
    show ENNReal.ofReal (D (x + z) (y + z)) = internalMetric (fun a b => D (a + z) (b + z)) univ x y
    rw [hD.ofReal_eq_internalMetric]
    have h := internalMetric_comp_homeomorph D (Homeomorph.addRight z) univ x y
    rw [Set.image_univ, Homeomorph.range_coe] at h
    exact h.symm

/-! ### The main metric identity -/

theorem addFunPairing_zero' (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
  funext φ
  simp [addFunPairing]

/-- At `r = 1` the affine pullback of the field is the normalised translate plus the circle average constant. -/
theorem affinePullback_one_eq_translated {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ)
    (ω : Ω) :
    affinePullbackPairing (hC ω) 1 z =
      addFunPairing (S11c.translatedPairing hC hcirc z ω) (fun _ => hcirc ω 1 z) := by
  funext φ
  have hfun : (fun y : ℂ => φ ((y - z) / ((1 : ℝ) : ℂ))) = fun y => φ (y - z) := by
    funext y
    simp
  simp only [affinePullbackPairing, addFunPairing, S11c.translatedPairing, hfun, one_pow, inv_one, one_mul,
    integral_const_mul]
  ring

/-- **Lemma 11.13, metric clause (`hLoc`, V_z form).** Let `z ≠ 0` be a root and `hD1 : closedBall c₂ r₂ ⊆ ball 0 1`.
Almost surely in `ω`, the rooted Weyl metric at translated points is the internal metric of the centred metric
`centredWeylMetric` on the preimage `(· + z)⁻¹' ball c₂ r₂`, up to the factor `exp (ξ · hcirc ω 1 z)`. -/
theorem ae_rootedWeylMetric_internalMetric_translate
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {c₂ : ℂ} {r₂ : ℝ} (hD1 : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hXi : LQGMetricExponentPositive) (hField : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hU : LQGMetricSatisfiesAxiomsUnivFrozen.{u}) (hLenFr : LQGMetricLengthUnivFrozen.{u})
    (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    (hComp : WeylMetricCompositionContinuousOuterFrozen) {z : ℂ} (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ, x + z ∈ ball c₂ r₂ → y + z ∈ ball c₂ r₂ →
      internalMetric (rootedWeylMetric 𝔇 ξ γ hC z ω) (ball c₂ r₂) (x + z) (y + z) =
        ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 z)) *
          internalMetric (centredWeylMetric 𝔇 ξ γ hC hcirc z ω) ((fun u => u + z) ⁻¹' ball c₂ r₂) x y := by
  have hγlt : γ < lqgQ γ := S11c.gamma_lt_lqgQ hγ0 hγ2
  have hQpos : (0 : ℝ) < lqgQ γ := lt_trans hγ0 hγlt
  have hξ : 0 < ξ := hXi γ ξ 𝔇 hγ0 hγ2 h𝔇
  have hGT := S11c.isWholePlaneGFF_translate hG z
  have hshift := ae_wholePlane_weylScaling_shift_univ hU P γ ξ (S11c.translatedPairing hC hcirc z)
    (S11c.translatedCircle hcirc z) 𝔇 h𝔇 hGT (fun ω _ => hcirc ω 1 z) (fun ω => continuous_const)
    (fun _ => hG.measurable_circle 1 z one_pos)
  have hSat := hU γ ξ 𝔇 h𝔇 Ω P hC hcirc (fun _ _ => 0) hG (fun ω => continuous_const) (fun _ => measurable_const)
  have hIV := hSat.coordChange 1 one_pos z
  have hI := (hField Ω P γ ξ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z) hGT
    hγ0 hγ2 hγlt 𝔇 h𝔇).1
  have hLen := FirstPassS11atProducers.rootedWeylMetric_ae_isEuclideanLengthMetric hLenFr hField hRootFr P γ ξ 0
    hC hcirc hG 𝔇 h𝔇 hγ0 hγ2 hQpos hz
  filter_upwards [hshift, hIV, hI, hLen] with ω hsh hiv hi hlen
  -- Notation on the fixed fibre
  set T := S11c.translatedPairing hC hcirc z ω with hT
  set c : ℝ := hcirc ω 1 z with hc
  set D : ℂ → ℂ → ℝ := 𝔇 T with hD_def
  have hD : IsEuclideanLengthMetric D := hsh.1
  have hBlen : IsEuclideanLengthMetric (𝔇 (addFunPairing T (fun _ => c))) := hsh.2.1
  have hBW := hsh.2.2.2.1
  -- the field identity at translated points
  have hIVω : ∀ x y : ℂ, 𝔇 (hC ω) (x + z) (y + z) = 𝔇 (addFunPairing T (fun _ => c)) x y := by
    intro x y
    have h := hiv x y
    simp only [Complex.ofReal_one, one_mul, addFunPairing_zero', Real.log_one, mul_zero] at h
    rw [affinePullback_one_eq_translated hC hcirc z ω] at h
    exact h
  -- the constant Weyl shift of the field
  have hBfun : ∀ x y : ℂ, 𝔇 (addFunPairing T (fun _ => c)) x y = Real.exp (ξ * c) * D x y := by
    intro x y
    have h2 : weylScaling D ξ (fun _ => c) x y =
        ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (D x y) := by
      have h := weylScaling_add_const D ξ c (fun _ => 0) x y
      have h0 : weylScaling D ξ (fun _ => (0 : ℝ)) x y = ENNReal.ofReal (D x y) := hD.weylScaling_zero ξ x y
      simp only [zero_add] at h
      rw [h, h0]
    refine (ENNReal.ofReal_eq_ofReal_iff (nonneg_of_isEuclideanLengthMetric' hBlen x y)
      (mul_nonneg (Real.exp_pos _).le (nonneg_of_isEuclideanLengthMetric' hD x y))).mp ?_
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← h2]
    exact hBW x y
  -- the continuous outer weight and the inner singular weight
  have hgc : ContinuousOn (fun x : ℂ => -γ * Real.log ‖x‖) {x : ℂ | x ≠ 0} :=
    continuousOn_const.mul (Real.continuousOn_log.comp continuous_norm.continuousOn
      (fun x hx => norm_ne_zero_iff.mpr hx))
  have hqc : Continuous (fun x : ℂ => γ * Real.log (max 1 ‖x + z‖)) :=
    continuous_const.mul (Continuous.log (continuous_const.max (continuous_norm.comp (continuous_id.add continuous_const)))
      (fun x => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'))
  have hCl : IsEuclideanLengthMetric (centredWeylMetric 𝔇 ξ γ hC hcirc z ω) := hi.2
  have hfinW : ∀ x y : ℂ, weylScaling D ξ (fun x : ℂ => -γ * Real.log ‖x‖) x y ≠ ⊤ :=
    fun x y => (hi.1 x y).ne
  have hcomp : ∀ u v : ℂ, weylScaling (centredWeylMetric 𝔇 ξ γ hC hcirc z ω) ξ
      (fun x : ℂ => γ * Real.log (max 1 ‖x + z‖)) u v =
      weylScaling D ξ (fun x : ℂ => -γ * Real.log ‖x‖ + γ * Real.log (max 1 ‖x + z‖)) u v :=
    fun u v => hComp ξ hξ D (fun x : ℂ => -γ * Real.log ‖x‖) (fun x : ℂ => γ * Real.log (max 1 ‖x + z‖))
      hD hgc hqc hfinW u v
  -- the rooted weight at translated points
  set W0 : ℂ → ℝ := fun w => -(0 : ℝ) * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖) with hW0
  have hfunR : (fun x y : ℂ => 𝔇 (hC ω) (x + z) (y + z)) = fun x y => Real.exp (ξ * c) * D x y :=
    funext fun x => funext fun y => (hIVω x y).trans (hBfun x y)
  have hgfun : (fun x : ℂ => W0 (x + z)) =
      fun x : ℂ => -γ * Real.log ‖x‖ + γ * Real.log (max 1 ‖x + z‖) := by
    funext x
    simp only [hW0, add_sub_cancel_right]
    ring
  have R1 : ∀ u v : ℂ, rootedWeylMetric 𝔇 ξ γ hC z ω (u + z) (v + z) =
      Real.exp (ξ * c) * (weylScaling (centredWeylMetric 𝔇 ξ γ hC hcirc z ω) ξ
        (fun x : ℂ => γ * Real.log (max 1 ‖x + z‖)) u v).toReal := by
    intro u v
    have key : weylScaling (𝔇 (hC ω)) ξ W0 (u + z) (v + z) =
        weylScaling (fun x y : ℂ => Real.exp (ξ * c) * D x y) ξ
          (fun x : ℂ => -γ * Real.log ‖x‖ + γ * Real.log (max 1 ‖x + z‖)) u v := by
      rw [← hgfun, ← hfunR]
      exact (weylScaling_comp_homeomorph (𝔇 (hC ω)) ξ W0 (Homeomorph.addRight z) u v).symm
    show (weylScaling (𝔇 (hC ω)) ξ W0 (u + z) (v + z)).toReal = _
    rw [key, IsEuclideanLengthMetric.weylScaling_const_mul hD (Real.exp_pos _) ξ _ u v, ← hcomp u v,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  -- the real metric E' (window-free) and its length property
  set E' : ℂ → ℂ → ℝ := fun u v => (weylScaling (centredWeylMetric 𝔇 ξ γ hC hcirc z ω) ξ
    (fun x : ℂ => γ * Real.log (max 1 ‖x + z‖)) u v).toReal with hE'
  have hRlen : IsEuclideanLengthMetric (fun x y : ℂ => (weylScaling (𝔇 (hC ω)) ξ W0 x y).toReal) := hlen
  have hexp : Real.exp (-(ξ * c)) * Real.exp (ξ * c) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hE'len : IsEuclideanLengthMetric E' := by
    have h1 := (isEuclideanLengthMetric_addRight' hRlen z).const_mul (Real.exp_pos (-(ξ * c)))
    have hfun' : E' = fun x y : ℂ => Real.exp (-(ξ * c)) *
        (fun x y : ℂ => (weylScaling (𝔇 (hC ω)) ξ W0 x y).toReal) (x + z) (y + z) := by
      funext u v
      show E' u v = Real.exp (-(ξ * c)) * (weylScaling (𝔇 (hC ω)) ξ W0 (u + z) (v + z)).toReal
      have hR : (weylScaling (𝔇 (hC ω)) ξ W0 (u + z) (v + z)).toReal = Real.exp (ξ * c) * E' u v := R1 u v
      rw [hR, ← mul_assoc, hexp, one_mul]
    rw [hfun']
    exact h1
  -- finiteness, Step C on the window V
  have hfinC : ∀ u v : ℂ, weylScaling (centredWeylMetric 𝔇 ξ γ hC hcirc z ω) ξ
      (fun x : ℂ => γ * Real.log (max 1 ‖x + z‖)) u v ≠ ⊤ :=
    fun u v => weylScaling_ne_top_of_continuous' hCl ξ hqc u v
  have hEscale : ∀ u v : ℂ, ENNReal.ofReal (E' u v) = weylScaling (centredWeylMetric 𝔇 ξ γ hC hcirc z ω) ξ
      (fun x : ℂ => γ * Real.log (max 1 ‖x + z‖)) u v :=
    fun u v => ENNReal.ofReal_toReal (hfinC u v)
  have hFscale : ∀ u v : ℂ, ENNReal.ofReal (centredWeylMetric 𝔇 ξ γ hC hcirc z ω u v) =
      weylScaling (centredWeylMetric 𝔇 ξ γ hC hcirc z ω) ξ (fun _ => (0 : ℝ)) u v :=
    fun u v => (hCl.weylScaling_zero ξ u v).symm
  set V : Set ℂ := (fun u => u + z) ⁻¹' ball c₂ r₂ with hV
  have hVo : IsOpen V := isOpen_ball.preimage (continuous_id.add continuous_const)
  have hfg : ∀ w ∈ V, (fun x : ℂ => γ * Real.log (max 1 ‖x + z‖)) w = (fun _ => (0 : ℝ)) w := by
    intro w hw
    have h1 : ‖w + z‖ < 1 :=
      mem_ball_zero_iff.mp (hD1 (ball_subset_closedBall (show w + z ∈ ball c₂ r₂ from hw)))
    simp [max_eq_left h1.le]
  have hStepC : ∀ x y : ℂ, internalMetric E' V x y =
      internalMetric (centredWeylMetric 𝔇 ξ γ hC hcirc z ω) V x y :=
    fun x y => IsEuclideanLengthMetric.internalMetric_weylScaling_eq_of_eqOn hCl hE'len hCl ξ _ _
      hEscale hFscale hVo hfg x y
  -- assemble: translate the internal metric back, then scale
  intro x y _ _
  have hfunE : (fun a b : ℂ => rootedWeylMetric 𝔇 ξ γ hC z ω (a + z) (b + z)) =
      fun a b : ℂ => Real.exp (ξ * c) * E' a b :=
    funext fun a => funext fun b => R1 a b
  have himg : (Homeomorph.addRight z) '' V = ball c₂ r₂ :=
    (Homeomorph.addRight z).surjective.image_preimage (ball c₂ r₂)
  have hcm := internalMetric_comp_homeomorph (rootedWeylMetric 𝔇 ξ γ hC z ω) (Homeomorph.addRight z) V x y
  rw [himg] at hcm
  rw [show (fun a b : ℂ => rootedWeylMetric 𝔇 ξ γ hC z ω ((Homeomorph.addRight z) a) ((Homeomorph.addRight z) b)) =
      fun a b : ℂ => Real.exp (ξ * c) * E' a b from hfunE] at hcm
  rw [internalMetric_const_mul E' (Real.exp_pos _) V x y, hStepC x y] at hcm
  exact hcm.symm

end HarmonicBalls
