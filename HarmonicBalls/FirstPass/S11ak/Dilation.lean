import HarmonicBalls.FirstPass.S11ak.Scaling
import HarmonicBalls.FirstPass.S11v.Affine
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11ak.RandomConstant
import HarmonicBalls.FirstPass.S11r.LocalMetricReplacement

/-! # The dilated normalised field for the punctured-ball decoder (fp-S11ak, owner z6)

For `R > 0` the dilated, normalised whole-plane field `g(w) = h^ℂ(R w) - h^ℂ_R(0)` (CHATGPT-lh-R4-R5.md §R5a,
"Explicit dilation proof") is again a whole-plane GFF (`WholePlaneGFFAffineInvariance`, Proposed `LQG.lean:53`,
derived in `S11v/Affine.lean`). Its mean-zero observations on the disk `ball (c/R) (r/R)` are the rescaled
mean-zero observations of `h^ℂ` on `ball c r` (`fieldPairing_dilate`).

This file proves the deterministic and GFF-level parts, and the transport of the local metric replacement (n2's
`LocalMetricReplacementStmt`, on the disks of `ball 0 1`) to the disks of `ball 0 R` (`localMetricReplacement_dilate`, the
hypothesis `hLoc` of `S11ac.metricDecoder_punctured_ball`). The metric identity for the dilated field is the Type-`u` affine
Weyl identity `ae_weylScaling_affinePullback_circle_universe` (`RandomConstant.lean`), with the random constant
`hcirc(R,0) + Q log R`.
-/

namespace HarmonicBalls.S11ak

open MeasureTheory Set Filter Metric

universe u

/-- The pairing of the dilated normalised field: `φ ↦ R⁻² hC(φ(·/R)) - c₀ ∫ φ`, with `c₀` the circle average
`h^ℂ_R(0)` (`dilCirc` is its circle-average process). -/
noncomputable def dilPairing (R : ℝ) (hC : (ℂ → ℝ) → ℝ) (c₀ : ℝ) : (ℂ → ℝ) → ℝ :=
  fun φ => (R ^ 2)⁻¹ * hC (fun y => φ (y / (R : ℂ))) - c₀ * ∫ x, φ x

/-- The circle-average process of the dilated normalised field: `(r, z) ↦ h^ℂ_{Rr}(Rz) - h^ℂ_R(0)`. -/
noncomputable def dilCirc (R : ℝ) (hcirc : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => hcirc (R * r) (R * z) - hcirc R 0

/-- The dilated normalised field is a whole-plane GFF (`WholePlaneGFFAffineInvariance` at `a = R`, `b = 0`). -/
theorem isWholePlaneGFF_dilate {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {R : ℝ} (hR : 0 < R) :
    IsWholePlaneGFF P (fun ω => dilPairing R (hC ω) (hcirc ω R 0)) (fun ω => dilCirc R (hcirc ω)) := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hA := HarmonicBalls.wholePlaneGFFAffineInvariance_derived P hC hcirc hG (R : ℂ) hR0 0
  have hnorm : ‖(R : ℂ)‖ = R := by simp [abs_of_pos hR]
  simp only [hnorm, sub_zero, add_zero] at hA
  exact hA

/-- The pairing identity behind the coordinate change: the pulled-back field `h^ℂ(R·) + Q log R` is the dilated
normalised field plus the random constant `c₀ + Q log R`. -/
theorem addFunPairing_affine_eq_dilPairing (R : ℝ) (hC : (ℂ → ℝ) → ℝ) (c₀ Q : ℝ) :
    HarmonicBalls.addFunPairing (HarmonicBalls.affinePullbackPairing hC R 0) (fun _ => Q * Real.log R) =
      HarmonicBalls.addFunPairing (dilPairing R hC c₀) (fun _ => c₀ + Q * Real.log R) := by
  funext φ
  simp only [HarmonicBalls.addFunPairing, HarmonicBalls.affinePullbackPairing, dilPairing, sub_zero,
    integral_const_mul]
  ring

/-- Mean-zero observations of the dilated field on `ball (c/R) (r/R)` are rescaled observations of `h^ℂ` on
`ball c r`, with the factor `R⁻²`. -/
theorem localMeanZeroObs_dilate (hC : (ℂ → ℝ) → ℝ) {R : ℝ} (hR : 0 < R) (c : ℂ) (r α c₀ : ℝ)
    (φ : {φ : ℂ → ℝ // IsTestFunction (ball (c / (R : ℂ)) (r / R)) φ ∧ ∫ x, φ x = 0}) :
    localMeanZeroObs α (ball (c / (R : ℂ)) (r / R)) (dilPairing R hC c₀) φ =
      (R ^ 2)⁻¹ * localMeanZeroObs α (ball c r) hC
        ⟨fun y => φ.1 (y / (R : ℂ)), isTestFunction_div_ball hR φ.2.1,
          integral_div_ofReal_eq_zero hR φ.1 φ.2.2⟩ := by
  unfold localMeanZeroObs
  exact fieldPairing_dilate hC hR α c₀ φ.1 φ.2.1.1.continuous φ.2.1.2.1 φ.2.2

/-- The image of the disk `ball c r` under `z ↦ R z` is `ball (R c) (R r)`; equivalently `z ∈ ball (c/R) (r/R)` iff
`R z ∈ ball c r` (`R > 0`). -/
theorem mem_ball_div_iff_smul {c : ℂ} {r R : ℝ} (hR : 0 < R) (z : ℂ) :
    z ∈ ball (c / (R : ℂ)) (r / R) ↔ (R : ℂ) * z ∈ ball c r := by
  simp only [Metric.mem_ball, dist_eq_norm]
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hz : (R : ℂ) * z - c = (R : ℂ) * (z - c / (R : ℂ)) := by
    rw [mul_sub, mul_div_cancel₀ c hR0]
  rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, lt_div_iff₀ hR, mul_comm]

/-! ### Transport of the local metric replacement to the dilated disks (fp-S11ak, owner z6)

`hN2` (`LocalMetricReplacementStmt`) is stated on disks in `ball 0 1`. For `R > 0` and a disk `ball c₂ r₂ ⊆ ball 0 R`, the
rescaled disk `ball (c₂/R) (r₂/R)` lies in `ball 0 1`. The decoder `m'` of the rescaled disk, applied to the mean-zero
observation of the dilated normalised field `R⁻² h(·/R) - h^ℂ_R(0)`, equals `R⁻²` times the observation of `h` on the
original disk (`localMeanZeroObs_dilate`); its Weyl scaling is the Weyl scaling of `h` at `(R·, R·)` up to a positive
constant (`ae_weylScaling_affinePullback_circle_universe`, `internalMetric_const_mul_comp_smul`). -/

/-- Mean-zero test functions on the rescaled disk, pulled back to the original disk by `φ ↦ φ(·/R)`. -/
noncomputable def dilTest {R : ℝ} (hR : 0 < R) (c : ℂ) (r : ℝ)
    (φ : {φ : ℂ → ℝ // IsTestFunction (ball (c / (R : ℂ)) (r / R)) φ ∧ ∫ x, φ x = 0}) :
    {φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} :=
  ⟨fun y => φ.1 (y / (R : ℂ)), isTestFunction_div_ball hR φ.2.1, integral_div_ofReal_eq_zero hR φ.1 φ.2.2⟩

/-- The observation of the dilated field on the rescaled disk, as a function of an observation `ℓ` of `h` on the original
disk: `φ ↦ R⁻² ℓ(φ(·/R))`. -/
noncomputable def dilObs {R : ℝ} (hR : 0 < R) (c : ℂ) (r : ℝ)
    (ℓ : {φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ)
    (φ : {φ : ℂ → ℝ // IsTestFunction (ball (c / (R : ℂ)) (r / R)) φ ∧ ∫ x, φ x = 0}) : ℝ :=
  (R ^ 2)⁻¹ * ℓ (dilTest hR c r φ)

/-- The closed rescaled disk: `z ∈ closedBall (c/R) (r/R)` iff `R z ∈ closedBall c r` (`R > 0`). -/
theorem mem_closedBall_div_iff_smul {c : ℂ} {r R : ℝ} (hR : 0 < R) (z : ℂ) :
    z ∈ closedBall (c / (R : ℂ)) (r / R) ↔ (R : ℂ) * z ∈ closedBall c r := by
  simp only [Metric.mem_closedBall, dist_eq_norm]
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hz : (R : ℂ) * z - c = (R : ℂ) * (z - c / (R : ℂ)) := by
    rw [mul_sub, mul_div_cancel₀ c hR0]
  rw [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le, le_div_iff₀ hR, mul_comm]

/-- The affine pullback of `T` by `R` shifted by the random constant `Q log R - (c₀ + Q log R)` is the dilated normalised
pairing `dilPairing R T c₀` (the constant `-c₀`). -/
theorem addFunPairing_affinePullback_eq_dilPairing (R : ℝ) (T : (ℂ → ℝ) → ℝ) (c₀ Q : ℝ) :
    HarmonicBalls.addFunPairing (HarmonicBalls.affinePullbackPairing T R 0)
        (fun _ => Q * Real.log R - (c₀ + Q * Real.log R)) = dilPairing R T c₀ := by
  funext φ
  have h : Q * Real.log R - (c₀ + Q * Real.log R) = -c₀ := by ring
  simp only [HarmonicBalls.addFunPairing, HarmonicBalls.affinePullbackPairing, dilPairing, sub_zero, h, neg_mul,
    integral_neg, integral_const_mul]
  ring

/-- The observation of the dilated field is the dilated observation (`localMeanZeroObs_dilate`, as a function). -/
theorem dilObs_localMeanZeroObs (hC : (ℂ → ℝ) → ℝ) {R : ℝ} (hR : 0 < R) (c : ℂ) (r : ℝ) (α c₀ : ℝ) :
    dilObs hR c r (localMeanZeroObs α (ball c r) hC) =
      localMeanZeroObs α (ball (c / (R : ℂ)) (r / R)) (dilPairing R hC c₀) := by
  funext φ
  exact (localMeanZeroObs_dilate hC hR c r α c₀ φ).symm

/-- The rescaling `p ↦ p/R` of a product disk, as a continuous map of the subtypes. -/
noncomputable def dilPointMap {R : ℝ} (hR : 0 < R) (c : ℂ) (r : ℝ) :
    C(↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)),
      ↥(ball (c / (R : ℂ)) (r / R) ×ˢ ball (c / (R : ℂ)) (r / R) : Set (ℂ × ℂ))) where
  toFun p := ⟨((p.1.1 / (R : ℂ)), (p.1.2 / (R : ℂ))), by
    have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    exact ⟨(mem_ball_div_iff_smul hR _).2 (by rw [mul_div_cancel₀ _ hR0]; exact p.2.1),
      (mem_ball_div_iff_smul hR _).2 (by rw [mul_div_cancel₀ _ hR0]; exact p.2.2)⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

/-- **Local metric replacement on the disks of `ball 0 R`** (fp-S11ak, owner z6). From `hN2` (the local metric replacement
on the disks of `ball 0 1`) and the dilation by `R > 0`, the local metric replacement on the disks of `ball 0 R` holds: this
is the hypothesis `hLoc` of `S11ac.metricDecoder_punctured_ball`. -/
theorem localMetricReplacement_dilate {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} (hR : 0 < R)
    (hN2 : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ)
    (h1 : 0 < r₁) (h2 : 0 < r₂) (h3 : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h4 : closedBall c₂ r₂ ⊆ ball (0 : ℂ) R)
    (h5 : (0 : ℂ) ∉ closedBall c₂ r₂) :
    ∃ m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) →
        ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ,
      Measurable m ∧ ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
          ENNReal.ofReal (m (localMeanZeroObs α (ball c₂ r₂) (hC ω)) p) =
            ENNReal.ofReal b * internalMetric
              (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
              (ball c₂ r₂) p.1.1 p.1.2 := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hsub1 : closedBall (c₁ / (R : ℂ)) (r₁ / R) ⊆ ball (c₂ / (R : ℂ)) (r₂ / R) := by
    intro z hz
    rw [mem_closedBall_div_iff_smul hR] at hz
    exact (mem_ball_div_iff_smul hR z).2 (h3 hz)
  have hsub2 : closedBall (c₂ / (R : ℂ)) (r₂ / R) ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    have hz' := h4 ((mem_closedBall_div_iff_smul hR z).1 hz)
    have := (mem_ball_div_iff_smul (c := 0) (r := R) hR z).2 hz'
    simpa [div_self hR.ne'] using this
  have h5' : (0 : ℂ) ∉ closedBall (c₂ / (R : ℂ)) (r₂ / R) := by
    intro h
    apply h5
    have := (mem_closedBall_div_iff_smul hR 0).1 h
    simpa using this
  have hS := hN2 (c₁ / (R : ℂ)) (c₂ / (R : ℂ)) (r₁ / R) (r₂ / R)
  unfold LocalMetricReplacementStmt at hS
  obtain ⟨m', hm', h18', -⟩ := hS hγ hγ2 (div_pos h1 hR) (div_pos h2 hR) hsub1 hsub2 h5' 𝔇 h𝔇
  have hdil : Measurable (fun ℓ => dilObs hR c₂ r₂ ℓ) :=
    Measurable.of_eval (fun φ' => measurable_const.mul (measurable_pi_apply _))
  have hmeas : Measurable (fun ℓ => (m' (dilObs hR c₂ r₂ ℓ)).comp (dilPointMap hR c₂ r₂)) :=
    (ContinuousMap.continuous_precomp (Z := ℝ) (dilPointMap hR c₂ r₂)).measurable.comp (hm'.comp hdil)
  refine ⟨fun ℓ => (m' (dilObs hR c₂ r₂ ℓ)).comp (dilPointMap hR c₂ r₂), hmeas,
    fun α hα Ω _ P _ hC hcirc hG => ?_⟩
  have h18d := h18' α hα Ω P (fun ω => dilPairing R (hC ω) (hcirc ω R 0)) (fun ω => dilCirc R (hcirc ω))
    (isWholePlaneGFF_dilate hG hR)
  have hW := ae_weylScaling_affinePullback_circle_universe h𝔇 hG hR (lqgQ γ * Real.log R) α
  filter_upwards [h18d, hW] with ω hω hWω
  obtain ⟨b, hb, hb'⟩ := hω
  simp only [addFunPairing_affinePullback_eq_dilPairing] at hWω
  have hκpos : 0 < Real.exp (-(ξ * (hcirc ω R 0 + lqgQ γ * Real.log R - α * Real.log R))) := Real.exp_pos _
  refine ⟨b * Real.exp (-(ξ * (hcirc ω R 0 + lqgQ γ * Real.log R - α * Real.log R))), mul_pos hb hκpos, fun p => ?_⟩
  have hmet : (fun u v => (weylScaling (𝔇 (dilPairing R (hC ω) (hcirc ω R 0))) ξ
        (fun z => -α * Real.log ‖z‖) u v).toReal) =
      fun u v => Real.exp (-(ξ * (hcirc ω R 0 + lqgQ γ * Real.log R - α * Real.log R))) *
        (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) ((R : ℂ) * u) ((R : ℂ) * v)).toReal := by
    funext u v
    rw [hWω u v, ENNReal.toReal_mul, ENNReal.toReal_ofReal hκpos.le]
  have hkey : internalMetric
      (fun u v => Real.exp (-(ξ * (hcirc ω R 0 + lqgQ γ * Real.log R - α * Real.log R))) *
        (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) ((R : ℂ) * u) ((R : ℂ) * v)).toReal)
      (ball (c₂ / (R : ℂ)) (r₂ / R)) (dilPointMap hR c₂ r₂ p).1.1 (dilPointMap hR c₂ r₂ p).1.2 =
      ENNReal.ofReal (Real.exp (-(ξ * (hcirc ω R 0 + lqgQ γ * Real.log R - α * Real.log R)))) *
        internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
          (ball c₂ r₂) p.1.1 p.1.2 := by
    have h := internalMetric_const_mul_comp_smul
      (fun x y => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal) hκpos hR.ne'
      (ball (c₂ / (R : ℂ)) (r₂ / R)) (ball c₂ r₂) (fun z => mem_ball_div_iff_smul hR z)
      (p.1.1 / (R : ℂ)) (p.1.2 / (R : ℂ))
    rw [mul_div_cancel₀ _ hR0, mul_div_cancel₀ _ hR0] at h
    exact h
  have hp' := hb' (dilPointMap hR c₂ r₂ p)
  show ENNReal.ofReal ((m' (dilObs hR c₂ r₂ (localMeanZeroObs α (ball c₂ r₂) (hC ω))))
      (dilPointMap hR c₂ r₂ p)) = _
  rw [dilObs_localMeanZeroObs (hC ω) hR c₂ r₂ α (hcirc ω R 0), hp', hmet, hkey, ENNReal.ofReal_mul hb.le]
  ring

end HarmonicBalls.S11ak
