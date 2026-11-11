import HarmonicBalls.Proofs.Sec11.CanonicalPairingShift
import HarmonicBalls.Steps.Sec11.WeylLocality
import HarmonicBalls.Steps.Sec11.WeylMetricConstantScaling

/-! # Locally constant shifts of field and metric

The local field modulo constants is unchanged by any function constant on the
observation set. The corresponding deterministic Weyl metric comparison
uses only the length-metric and Weyl identities. The imported Cameron–Martin
results use Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- A function constant on the observation set has zero pairing with every
local zero-integral test. -/
theorem integral_mul_localZeroMeanTest_eq_zero {U : Set ℂ} {g : ℂ → ℝ} {c : ℝ}
    (hg : ∀ x ∈ U, g x = c) (φ : LocalZeroMeanTest U) :
    (∫ x, g x * φ.1 x) = 0 := by
  have heq : (fun x => g x * φ.1 x) = fun x => c * φ.1 x := by
    funext x
    by_cases hx : x ∈ U
    · rw [hg x hx]
    · have hz : φ.1 x = 0 := by
        by_contra hn
        exact hx (φ.2.1.2.2 (subset_closure hn))
      simp [hz]
  rw [heq, integral_const_mul, φ.2.2, mul_zero]

/-- A locally constant function acts as the identity on the canonical local
field modulo constants. -/
theorem localModConstPairingShift_eq_self_of_eqOn {U : Set ℂ} {g : ℂ → ℝ} {c : ℝ}
    (hg : ∀ x ∈ U, g x = c) (v : LocalZeroMeanTest U → ℝ) :
    localModConstPairingShift U g v = v := by
  funext φ
  simp only [localModConstPairingShift, integral_mul_localZeroMeanTest_eq_zero hg φ, add_zero]

/-- Every decoder of the field modulo constants is exactly invariant under a
locally constant background shift, without any law or measurability assumption. -/
theorem localModConstPairings_observable_eq_of_eqOn
    {Ω E : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    {U : Set ℂ} {g : ℂ → ℝ} {c : ℝ} (hg : ∀ x ∈ U, g x = c)
    (F : (LocalZeroMeanTest U → ℝ) → E) (ω : Ω) :
    F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U ω) =
      F (localModConstPairings α hC U ω) := by
  congr 1
  funext φ
  simp only [localModConstPairings, fieldPairing, addFunPairing,
    integral_mul_localZeroMeanTest_eq_zero hg φ, add_zero]

/-- If a Weyl weight is constant on an open set, internal distances there
scale by the corresponding deterministic constant, even though ambient
minimizing paths may leave the set. -/
theorem IsEuclideanLengthMetric.internalMetric_weylScaling_eq_of_constOn
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ : ℝ)
    (g : ℂ → ℝ) {c : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hg : ∀ x ∈ U, g x = c)
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ g x y).toReal))
    (hscale : ∀ x y, ENNReal.ofReal (weylScaling D ξ g x y).toReal =
      weylScaling D ξ g x y) (x y : ℂ) :
    internalMetric (fun x y => (weylScaling D ξ g x y).toReal) U x y =
      ENNReal.ofReal (Real.exp (ξ * c)) * internalMetric D U x y := by
  let a : ℝ := Real.exp (ξ * c)
  have ha : 0 < a := Real.exp_pos _
  have hF : IsEuclideanLengthMetric (fun x y => a * D x y) := hD.const_mul ha
  have hFscale : ∀ x y, ENNReal.ofReal (a * D x y) =
      weylScaling D ξ (fun _ => c) x y := by
    intro x y
    have hw := weylScaling_add_const D ξ c 0 x y
    simp only [Pi.zero_apply, zero_add] at hw
    rw [hw, hD.weylScaling_zero]
    exact ENNReal.ofReal_mul ha.le
  rw [hD.internalMetric_weylScaling_eq_of_eqOn hE hF ξ g (fun _ => c)
    hscale hFscale hU hg x y, internalMetric_const_mul D ha]

/-- A density constant on a measurable set scales its mass by that constant. -/
theorem withDensity_apply_of_constantOn {μ : Measure ℂ} {w : ℂ → ℝ≥0∞}
    {a : ℝ≥0∞} {U B : Set ℂ} (hB : MeasurableSet B) (hBU : B ⊆ U)
    (hw : ∀ x ∈ U, w x = a) :
    (μ.withDensity w) B = a * μ B := by
  rw [withDensity_apply _ hB]
  calc
    _ = ∫⁻ _ in B, a ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hB] with x hx
      exact hw x (hBU hx)
    _ = _ := setLIntegral_const _ _

/-- Normalizing by a reference mass removes a positive finite density that is
constant on both the reference set and the observed set. -/
theorem normalized_withDensity_apply_of_constantOn
    {μ : Measure ℂ} {w : ℂ → ℝ≥0∞} {a : ℝ≥0∞} {U B R : Set ℂ}
    (hB : MeasurableSet B) (hR : MeasurableSet R) (hBU : B ⊆ U) (hRU : R ⊆ U)
    (hw : ∀ x ∈ U, w x = a) (ha0 : a ≠ 0) (hatop : a ≠ ∞) :
    (((μ.withDensity w) R)⁻¹ • μ.withDensity w) B =
      ((μ R)⁻¹ • μ) B := by
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    withDensity_apply_of_constantOn hR hRU hw,
    withDensity_apply_of_constantOn hB hBU hw,
    ENNReal.mul_inv (a := a) (b := μ R) (Or.inl ha0) (Or.inl hatop)]
  calc
    _ = (μ R)⁻¹ * (a⁻¹ * a) * μ B := by ac_rfl
    _ = (μ R)⁻¹ * μ B := by rw [ENNReal.inv_mul_cancel ha0 hatop, mul_one]

/-- Under a locally constant Weyl shift, the normalized local metric and
mass agree with their unshifted values. The metric normalization is adjusted
by the inverse local Weyl factor. -/
theorem normalized_localMetricMeasure_weyl_eq_of_constOn
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ γ : ℝ)
    (g : ℂ → ℝ) {c : ℝ} {U V B R : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U)
    (hg : ∀ x ∈ U, g x = c)
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ g x y).toReal))
    (hscale : ∀ x y, ENNReal.ofReal (weylScaling D ξ g x y).toReal =
      weylScaling D ξ g x y) (x y : ℂ) (b : ℝ≥0∞) (μ : Measure ℂ)
    (hB : MeasurableSet B) (hR : MeasurableSet R) (hBU : B ⊆ U) (hRU : R ⊆ U) :
    let a := ENNReal.ofReal (Real.exp (ξ * c))
    let w : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (γ * g z))
    (b * a⁻¹ * internalMetric (fun x y => (weylScaling D ξ g x y).toReal) V x y,
      (((μ.withDensity w) R)⁻¹ • μ.withDensity w) B) =
      (b * internalMetric D V x y, ((μ R)⁻¹ • μ) B) := by
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * c))
  have ha0 : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hatop : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hm := hD.internalMetric_weylScaling_eq_of_constOn ξ g hV
    (fun z hz => hg z (hVU hz)) hE hscale x y
  dsimp only
  rw [hm]
  congr 1
  · calc
      _ = b * ((a⁻¹ * a) * internalMetric D V x y) := by ac_rfl
      _ = _ := by rw [ENNReal.inv_mul_cancel ha0 hatop, one_mul]
  · apply normalized_withDensity_apply_of_constantOn hB hR hBU hRU
    · intro z hz
      rw [hg z hz]
    · exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    · exact ENNReal.ofReal_ne_top

/-- A common local decoder is geometrically correct after a locally constant
Weyl shift whenever it is correct before the shift. -/
theorem local_decoder_weyl_eq_of_constOn
    {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ γ : ℝ)
    (g : ℂ → ℝ) {c : ℝ} {U V B R : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U)
    (hg : ∀ x ∈ U, g x = c)
    (hE : IsEuclideanLengthMetric (fun x y => (weylScaling D ξ g x y).toReal))
    (hscale : ∀ x y, ENNReal.ofReal (weylScaling D ξ g x y).toReal =
      weylScaling D ξ g x y) (x y : ℂ) (b : ℝ≥0∞) (μ : Measure ℂ)
    (hB : MeasurableSet B) (hR : MeasurableSet R) (hBU : B ⊆ U) (hRU : R ⊆ U)
    (F : (LocalZeroMeanTest U → ℝ) → (ℝ≥0∞ × ℝ≥0∞))
    (hF : F (localModConstPairings α hC U ω) =
      (b * internalMetric D V x y, ((μ R)⁻¹ • μ) B)) :
    let a := ENNReal.ofReal (Real.exp (ξ * c))
    let w : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (γ * g z))
    F (localModConstPairings α (fun ω => addFunPairing (hC ω) g) U ω) =
      (b * a⁻¹ * internalMetric (fun x y => (weylScaling D ξ g x y).toReal) V x y,
        (((μ.withDensity w) R)⁻¹ • μ.withDensity w) B) := by
  rw [localModConstPairings_observable_eq_of_eqOn α hC hg F ω, hF]
  exact (normalized_localMetricMeasure_weyl_eq_of_constOn hD ξ γ g hV hVU hg
    hE hscale x y b μ hB hR hBU hRU).symm




end HarmonicBalls
