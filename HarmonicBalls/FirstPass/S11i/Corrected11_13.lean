import HarmonicBalls.FirstPass.S11i.Assembly13

/-!
# Lemma 11.13 (corrected): `firstPass_11_13_corrected` (first pass fp-S11i-11-13c, owner n3)

`firstPass_11_13_corrected` proves `CorrectedLemma11_13Stmt` (`FirstPass/S11i/Faithful.lean`, paper form: no geometry clause;
the component clause `insert 0 (sphere 0 5) ⊆ pinchOmegaGeom W Q δ₀` of corrected paper lines 3180-3200 is derived from the
buffered geometry by `FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom` where it is needed).

Named input (one hypothesis): `hStep8`, `Step8IdentificationStmt`, the exists-E form (decision of fp-S11i-11-13c, item 2): for
every buffered geometry and `0 < γ < 2`, `α₀ < Q(γ)`, `M > 0`, there is a Lemma 11.12 event `E` at the insertion `γ`
(`PinchEventGammaStmt`) for which the Step 8 identification holds (`Step8IdentityStmt`). The Lemma 11.12 slice is not needed
for this form; `firstPass_11_12_corrected` is used only by the reduction of `hStep8` (not yet written).

Routing: Steps 1-2 are the content of `E` and `q` in `Step8IdentityStmt`; Steps 3, 9-11 are inside
`correctedLemma11_13_of_gamma_identity` (`Assembly13.lean`); Steps 4-8 (decoded-to-physical identification, n4, n1, Step 8 of the
zoom family) are the content of `Step8IdentityStmt`.

Ostar. `Step8IdentityStmt` and `GammaZoomIdentityStmt` use the paper's `Ostar = pinchOmegaGeom W Q δ` (corrected lines 3180-3191),
with `η = δ`, so the locality `FirstPassS11ap.certificateEvent_pinch_congr` discharges the containments.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- **Step 8 identification of Lemma 11.13 for one Lemma 11.12 event (named input; Blocker 1 of fp-S11i-11-13).** For a
Lemma 11.12 event `E` at the insertion `γ`: the probability `q` of `{h^γ|_{B₇} ∈ E}` is the same in every whole-plane model at
`γ`, and in every whole-plane model at `α₀` a zoom family `μk, Dk` at dyadic scales `2^k` has window certificate frequencies
(for the paper's `Ostar = pinchOmegaGeom W Q δ`, `η = δ`) converging, almost surely and for `μk`-almost every `w ∈ B₁(0)`, to
`q`. Source: corrected paper, proof of `lemma:mu_h-pinch-bad`, Step 8 (lines 3848-3930); the decoded-to-physical identification
is `CertificateIdentification` (`FirstPass/S11i/Identification.lean`, `CHATGPT-n3-identification.md` §5). -/
def Step8IdentityStmt (γ ξ α₀ : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ)
    (E : Set (ModConstTestPairings (ball (0 : ℂ) 7))) : Prop :=
  ∃ q : ℝ,
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ ξ γ hC D →
      (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal = q) ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∃ (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ),
        (∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
          μk k ω = ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) ∧
          ∀ x y : ℂ, Dk k ω x y = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * x) ((((2 : ℝ) ^ k : ℝ) : ℂ) * y)) ∧
        ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), w ∈ ball (0 : ℂ) 1 →
          Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
            FirstPassS11i.windowCert (pinchOmegaGeom W Q δ) U V W T Q' Q δ M μk Dk k ω n w}.ncard : ℝ) / (N : ℝ))
            atTop (𝓝 q)

/-- The named input of `firstPass_11_13_corrected`, exists-E form (`fp-S11i-11-13c`, decision 2): on every buffered geometry
and every `0 < γ < 2`, `α₀ < Q(γ)`, `M > 0`, there is a Lemma 11.12 event `E` at `γ` satisfying `Step8IdentityStmt`. -/
def Step8IdentificationStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  ∀ γ ξ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaStmt.{u} U T Q' Q γ ξ M E ∧
    Step8IdentityStmt.{u} γ ξ α₀ U V W T Q' Q δ₀ M E

/-- **Lemma 11.13 (corrected), first pass.** `CorrectedLemma11_13Stmt` from the named input `hStep8` (with the frozen and
Proposed inputs `hAx`, `hMeas` of `correctedLemma11_13_of_gamma_identity`). The density is `δ = min (q/4) (1/2)`. -/
theorem firstPass_11_13_corrected
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hMeas : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ γ hC hcirc)
    (hStep8 : Step8IdentificationStmt.{u}) :
    CorrectedLemma11_13Stmt.{u} := by
  refine correctedLemma11_13_of_gamma_identity hAx hMeas ?_
  intro U V W T Q' Q δ₀ hgeom γ ξ α₀ M hγ0 hγ2 hα hM
  obtain ⟨E, hPG, h8⟩ := hStep8 U V W T Q' Q δ₀ hgeom γ ξ α₀ M hγ0 hγ2 hα hM
  unfold GammaZoomIdentityStmt
  exact ⟨E, hPG, h8⟩

/-- The Lemma 11.12 event at the canonical exponent `ξ = lqgXi γ`: `PinchEventGammaStmt` (`Assembly13.lean:120`) with
`ξ = lqgXi γ`. The source file is unchanged. -/
def PinchEventGammaCanonicalStmt (U T Q' Q : Set ℂ) (γ M : ℝ)
    (E : Set (ModConstTestPairings (ball (0 : ℂ) 7))) : Prop :=
  PinchEventGammaStmt.{u} U T Q' Q γ (lqgXi γ) M E

/-- `Step8IdentityStmt` at the canonical exponent `ξ = lqgXi γ`. -/
def Step8IdentityCanonicalStmt (γ α₀ : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ)
    (E : Set (ModConstTestPairings (ball (0 : ℂ) 7))) : Prop :=
  Step8IdentityStmt.{u} γ (lqgXi γ) α₀ U V W T Q' Q δ M E

/-- Step 8 identification at the canonical exponent: for every buffered geometry, `0 < γ < 2`, `α₀ < Q(γ)` and `M > 0`
there is a Lemma 11.12 event `E` at `γ` (`PinchEventGammaCanonicalStmt`) satisfying `Step8IdentityCanonicalStmt`. -/
def Step8IdentificationCanonicalStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  ∀ γ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaCanonicalStmt.{u} U T Q' Q γ M E ∧
    Step8IdentityCanonicalStmt.{u} γ α₀ U V W T Q' Q δ₀ M E

/-- Part (c) of the Step 8 identification at the canonical exponent: a Lemma 11.12 event `E` at `γ`, for every buffered
geometry, `0 < γ < 2` and `M > 0`. Closed in `Closure/Sec11.lean` (`closure_11_13_canonical`) by the closed corrected
Lemma 11.12 (`closure_11_12`, through `pinchEventGamma_exists`, `Step8Event.lean`). -/
def Step8PinchEventCanonicalStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  ∀ γ M : ℝ, 0 < γ → γ < 2 → 0 < M →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaCanonicalStmt.{u} U T Q' Q γ M E

/-- Part (d) of the Step 8 identification at the canonical exponent: the rooted/marked/zoom identity
`Step8IdentityCanonicalStmt` (Step 8 of the corrected proof of `lemma:mu_h-pinch-bad`, corrected lines 3848-3930) for a
Lemma 11.12 event `E` at `γ`. The premise is the conclusion of part (c), so (c) and (d) together are equivalent to
`Step8IdentificationCanonicalStmt` (`step8Identification_canonical_of_split`). This is the only named input left open. -/
def Step8IdentityGivenPinchEventCanonicalStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  ∀ γ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
  (∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaCanonicalStmt.{u} U T Q' Q γ M E) →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaCanonicalStmt.{u} U T Q' Q γ M E ∧
    Step8IdentityCanonicalStmt.{u} γ α₀ U V W T Q' Q δ₀ M E

/-- The split is exact: parts (c) and (d) together give `Step8IdentificationCanonicalStmt`. -/
theorem step8Identification_canonical_of_split (hPE : Step8PinchEventCanonicalStmt.{u})
    (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u}) : Step8IdentificationCanonicalStmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM
  exact hId U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM (hPE U V W T Q' Q δ₀ hgeom γ M hγ0 hγ2 hM)

/-- **Lemma 11.13 (canonical), first pass.** `CorrectedLemma11_13CanonicalStmt` from the two named inputs `hPE` (part (c),
the Lemma 11.12 event) and `hId` (part (d), the Step 8 identity). The model
`(Ω, P, hC, hcirc, μ, D)` is fixed before the density, and the density is `δ = min (q/4) (1/2)`, where `q` is the common
probability of the Lemma 11.12 event in every γ-model (`Step8IdentityCanonicalStmt`, first conjunct). The probability
normalisation of `P` comes from `FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF`. -/
theorem firstPass_11_13_canonical
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hMeas : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ γ hC hcirc)
    (hPE : Step8PinchEventCanonicalStmt.{u}) (hId : Step8IdentityGivenPinchEventCanonicalStmt.{u}) :
    CorrectedLemma11_13CanonicalStmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ hγ0 hγ2 hα M hM Ω inst P hC hcirc μ D hG hμ hDm
  obtain ⟨E, hPG, h8⟩ :=
    step8Identification_canonical_of_split hPE hId U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM
  obtain ⟨-, hW⟩ := hPG
  obtain ⟨q, hqeq, hfreq⟩ := h8
  have : IsProbabilityMeasure P := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG
  obtain ⟨μg, Dg, hμg, hDg⟩ :=
    FirstPassS11iGamma.gammaModel_of_alpha0Model hAx hMeas hγ0 hγ2 Ω P hC hcirc hG D hDm
  obtain ⟨-, hpos, -⟩ := hW Ω P hC hcirc μg Dg hG hμg hDg
  have hq : 0 < q := by
    rw [← hqeq Ω P hC hcirc μg Dg hG hμg hDg]
    exact ENNReal.toReal_pos hpos.ne' (measure_ne_top P _)
  refine ⟨min (q / 4) (1 / 2), ⟨lt_min (div_pos hq (by norm_num)) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩, ?_⟩
  obtain ⟨μk, Dk, hsc, hstep⟩ := hfreq Ω P hC hcirc μ D hG hμ hDm
  exact (FirstPassS11i.CertAssemble.pinch_window_ae_buffered (hAx γ (lqgXi γ) α₀ Ω P hC hcirc) hG hγ0 hγ2 hα hDm
    hgeom hq μk Dk hsc hstep).mono fun ω hω => hω.mono fun z hz => hz.mono fun N hN =>
      le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg N)) hN

end HarmonicBalls

#print axioms HarmonicBalls.firstPass_11_13_corrected
#print axioms HarmonicBalls.firstPass_11_13_canonical
