import HarmonicBalls.FirstPass.S11s.Covariance
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly

/-!
# Iterated zoom-in of the canonical decoders

Step 7 of the rooted local rescaling (`FirstPass/S11as.lean`, `RootedLocalRescaling`). The one-step covariance of the frozen
canonical decoders under the zoom-in by `1/2` (`ae_covariance_canonical`, `FirstPass/S11s/Covariance.lean`) is iterated `n`
times: `dilOp^[n] L` is the canonical pairing of the whole-plane model zoomed in by `2^{-n}` about `0`, and its decoded
measure and metric are the constant multiples of `(Dμ L).map (· / (1/2)^n)` and of `Dd L ((1/2)^n ·) ((1/2)^n ·)`,
with `L = alphaCanon α hC ω`.

Inputs: the frozen canonical identification `LQGCanonicalIdentificationStmt` at `α₀ := α` in universe `0`
(`FirstPass/S11n.lean:61`), and the a.s. pairing homogeneity `hhom` of the model (GAP A, a hypothesis). The affine
invariance of the whole-plane GFF is the proved theorem `wholePlaneGFFAffineInvariance_proved` (not assumed).
Universe `0`: the one-step covariance is stated for `Ω : Type`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace FirstPassS11asZoom

/-- The zoom-in pairing `normDilatePairing T s (1/2)` is homogeneous when `T` is: the dilation `dilateTest 1` is linear on
test functions and `∫ c k = c ∫ k`. -/
theorem pairingHomogeneous_normDilatePairing_half {T : (ℂ → ℝ) → ℝ} (hT : PairingHomogeneous T) (s : ℝ) :
    PairingHomogeneous (normDilatePairing T s (1 / 2)) := by
  intro c k hk
  obtain ⟨h1, h2, h3⟩ := hk
  have hck : IsTestFunction (univ : Set ℂ) (fun y => c * k y) :=
    ⟨contDiff_const.mul h1, h2.mul_left, subset_univ _⟩
  have hdk : IsTestFunction (univ : Set ℂ) (dilateTest 1 k) :=
    isTestFunction_dilateTest ⟨h1, h2, h3⟩ 1
  have hdc : dilateTest 1 (fun y => c * k y) = fun y => c * dilateTest 1 k y := by
    funext y
    simp only [dilateTest]
    ring
  have e1 := normDilatePairing_half hT s (fun y => c * k y) hck
  have e2 := normDilatePairing_half hT s k ⟨h1, h2, h3⟩
  have e3 := hT c (dilateTest 1 k) hdk
  rw [e1, e2, hdc, e3, integral_const_mul]
  ring

/-- **Iterated one-step covariance of the canonical decoders (almost surely).** For a whole-plane GFF model `(hC, hcirc)`
with LQG measure `μ` and LQG metric `D` at insertion `α`, almost surely, with `L = alphaCanon α hC ω` and `a, b > 0`:
`Dμ (dilOp^[n] L) = a • (Dμ L).map (· / (1/2)^n)` and `Dd (dilOp^[n] L) u v = b * Dd L ((1/2)^n u) ((1/2)^n v)`.
Induction on `n`; each step applies `ae_covariance_canonical` to the zoomed model. -/
theorem ae_decoders_dilOp_iterate {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {γ ξ α : ℝ} (hγ : 0 < γ)
    {Dμ : S11n.CanonSpace → Measure ℂ} {Dd : S11n.CanonSpace → ℂ → ℂ → ℝ}
    (hid : S11n.LQGCanonicalIdentificationStmt.{0} γ ξ α Dμ Dd) (n : ℕ) :
    ∀ (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → (∀ᵐ ω ∂P, PairingHomogeneous (hC ω)) →
      IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
      ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        Dμ (dilOp^[n] (alphaCanon α hC ω))
            = ENNReal.ofReal a • (Dμ (alphaCanon α hC ω)).map (fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) ∧
        ∀ u v : ℂ, Dd (dilOp^[n] (alphaCanon α hC ω)) u v
            = b * Dd (alphaCanon α hC ω) ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * u) ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * v) := by
  induction n with
  | zero =>
    intro hC hcirc μ D _ _ _ _
    refine ae_of_all _ (fun ω => ⟨1, 1, one_pos, one_pos, ?_, fun u v => ?_⟩)
    · simp
    · simp
  | succ n ih =>
    intro hC hcirc μ D hG hhom hμ hD
    have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
    have hstep := ae_covariance_canonical P hγ hG hAff hhom hμ hD hid
    have hG' := isWholePlaneGFF_affinePullback hG hAff
    have hμ' := ae_isLQGMeasureOfField_affinePullback P hγ hG hμ
    have hD' := ae_isLQGMetricOfField_affinePullback P hG hD
    have hhom' : ∀ᵐ ω ∂P, PairingHomogeneous (normDilatePairing (hC ω) (hcirc ω (1 / 2) 0) (1 / 2)) := by
      filter_upwards [hhom] with ω hω
      exact pairingHomogeneous_normDilatePairing_half hω _
    have hih := ih _ _ _ _ hG' hhom' hμ' hD'
    have hgn : Measurable (fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) := by fun_prop
    have hg1 : Measurable (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) := by fun_prop
    have hcomp : ((fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) ∘ (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)))
        = fun w : ℂ => w / (((1 / 2 : ℝ) ^ (n + 1) : ℝ) : ℂ) := by
      funext w
      simp only [Function.comp_apply]
      rw [div_div]
      congr 1
      push_cast
      ring
    have key : ∀ x : ℂ, ((1 / 2 : ℝ) : ℂ) * ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * x)
        = ((((1 / 2 : ℝ) ^ (n + 1) : ℝ)) : ℂ) * x := by
      intro x
      push_cast
      ring
    filter_upwards [hstep, hih, hhom] with ω h1 h2 hω
    obtain ⟨a₀, b₀, ha₀, hb₀, hmeas₀, hmet₀⟩ := h1
    obtain ⟨a₁, b₁, ha₁, hb₁, hmeas₁, hmet₁⟩ := h2
    have hT := dilOp_alphaCanon_eq α hC (fun ω' => hcirc ω' (1 / 2) 0) ω hω
    rw [hT] at hmeas₀ hmet₀
    refine ⟨a₁ * a₀, b₁ * b₀, mul_pos ha₁ ha₀, mul_pos hb₁ hb₀, ?_, ?_⟩
    · rw [Function.iterate_succ_apply, hT, hmeas₁, hmeas₀, Measure.map_smul _ hgn.aemeasurable,
        Measure.map_map hgn hg1, smul_smul, ← ENNReal.ofReal_mul ha₁.le, hcomp]
    · intro u v
      rw [Function.iterate_succ_apply, hT, hmet₁ u v, hmet₀ _ _, key u, key v]
      ring

/-- **Decoded measure at scale `2^n`, undone.** The measure of `RootedLocalRescaling` (`μC.map (· / 2^n)`) of the decoded
zoomed measure `a • μL.map (· / (1/2)^n)` is `a • μL`. -/
theorem map_div_two_pow_decoded (μL : Measure ℂ) (a : ℝ≥0∞) (n : ℕ) :
    ((a • μL.map (fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ))).map
        (fun w : ℂ => w / (((2 : ℝ) ^ n : ℝ) : ℂ))) = a • μL := by
  have hm1 : Measurable (fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ)) := by fun_prop
  have hm2 : Measurable (fun w : ℂ => w / (((2 : ℝ) ^ n : ℝ) : ℂ)) := by fun_prop
  have h1 : (((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * (((2 : ℝ) ^ n : ℝ) : ℂ) = 1 := by
    push_cast
    rw [← mul_pow]
    norm_num
  have hcomp : ((fun w : ℂ => w / (((2 : ℝ) ^ n : ℝ) : ℂ)) ∘
      (fun w : ℂ => w / (((1 / 2 : ℝ) ^ n : ℝ) : ℂ))) = id := by
    funext w
    simp only [Function.comp_apply, id_eq]
    rw [div_div, h1, div_one]
  rw [Measure.map_smul _ hm2.aemeasurable, Measure.map_map hm2 hm1, hcomp, Measure.map_id]

/-- **Decoded metric at scale `2^n`, undone.** If `Dn u v = b * DL ((1/2)^n u) ((1/2)^n v)`, then the metric at the scaled
points `(2^n x, 2^n y)` is `b * DL x y`: this is the form in which the metric of `RootedLocalRescaling` is compared. -/
theorem decoded_metric_two_pow {Dn DL : ℂ → ℂ → ℝ} {b : ℝ} {n : ℕ}
    (h : ∀ u v : ℂ, Dn u v = b * DL ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * u) ((((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * v))
    (x y : ℂ) :
    Dn ((((2 : ℝ) ^ n : ℝ) : ℂ) * x) ((((2 : ℝ) ^ n : ℝ) : ℂ) * y) = b * DL x y := by
  have h1 : (((1 / 2 : ℝ) ^ n : ℝ) : ℂ) * (((2 : ℝ) ^ n : ℝ) : ℂ) = 1 := by
    push_cast
    rw [← mul_pow]
    norm_num
  rw [h]
  congr 2
  · rw [← mul_assoc, h1, one_mul]
  · rw [← mul_assoc, h1, one_mul]

end FirstPassS11asZoom

end HarmonicBalls
