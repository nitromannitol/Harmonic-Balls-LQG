import HarmonicBalls.FirstPass.S11i.CertAssemble
import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.S11i.CertificateCanonical
import HarmonicBalls.FirstPass.S11af

/-!
# Lemma 11.13 (corrected): conditional assembly from the Step 12 identity (fp-S11i, owner n3)

Route A (`notes/n3.md`): `FirstPassS11i.CertAssemble.pinch_window_ae_buffered` gives, almost surely and for `μ`-a.e. `z`,
the pinch-window count bound `q/4 * N ≤ #{n ∈ [N+1, 2N] : pinchPointEvent ...}` from the zoom-family window frequency
(Step 12 of the corrected proof of `lemma:mu_h-pinch-bad`). This file assembles `CorrectedLemma11_13Stmt` from that input.

Named inputs (neither frozen nor proved here):
* `hAx`: `LQGMetricFieldAxioms` (Proposed, Fact 2.2 I-IV; operator-approved), used only for the Euclidean length property.
* `hZ` (`ZoomIdentityStmt`, NEW, Step 12 of Lemma 11.13): for the Lemma 11.12 event `E` (`PinchEventWitnessStmt`, the body
  of `CorrectedLemma11_12Stmt` for one set `E`), the zoom-family window frequency converges almost surely to the probability
  `P(E^{α₀}(M))`, in every whole-plane model. Proved here, not assumed: the positivity `0 < P(E)`, the finiteness of `P(E)`
  (`FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF`), and the model independence of `P(E)`
  (`prob_ballRestrict_alphaCanon_indep`), so that the density `δ` is one number for all models.

Source of the identity: corrected paper, `paper/lqg_harmonic_ball-corrected.tex`, eq. `s11-pinch:eq:dyadic-frequency`
(line 3832), proof of `lemma:mu_h-pinch-bad` lines 3848-3930. Open point (Q1, `notes/n3.md`): that the identity holds for
the Lemma 11.12 event `E` as produced by the paper's construction is the NEW input; it is not checked in Lean.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

universe u

/-- The body of `CorrectedLemma11_12Stmt` (Faithful.lean:56) for one fixed set `E` of test pairings, at the parameters
`γ ξ M` and the geometry `U T Q' Q`: the event `{localModConstField α ∈ E}` is measurable in the Section 6 sigma-algebra of
fields modulo constants, has positive probability in every whole-plane model, and implies the pinch-point event a.s. -/
def PinchEventWitnessStmt (U T Q' Q : Set ℂ) (γ ξ M : ℝ)
    (E : Set (ModConstTestPairings (ball (0 : ℂ) 7))) : Prop :=
  MeasurableSet E ∧
  ∀ α : ℝ, α < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
    MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball (0 : ℂ) 7)]
      {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    0 < P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    ∀ᵐ ω ∂P, localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E →
      pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0

/-- **SUPERSEDED (2026-11-10, Q1 answer §3.2).** Its target `P(E^{α₀}(M))` is the α₀-insertion probability, but the answer
says the frequency limit is `p_γ(M)`, the γ-insertion probability. Do not use this hypothesis; use `GammaZoomIdentityStmt`.

**Step 12 of Lemma 11.13 (NEW named input).** For the buffered geometry `U V W T Q' Q` with buffer `δ`, the insertion
`α₀`, `γ`, `ξ` and `M`: there are a Lemma 11.12 event `E` (`PinchEventWitnessStmt`) and an open set `Ostar` with `0 ∈ Ostar`
and `sphere 0 5 ⊆ Ostar` such that, for every whole-plane model, there is a zoom family `μk, Dk` at dyadic scales `2^k` (the
scaling shape of `ae_hscale_dyadic`) whose window certificate frequency converges, for every `k`, almost surely and for
`μk`-almost every `w` in `B₁(0)`, to the probability `P(E^{α₀}(M))`. -/
def ZoomIdentityStmt (γ ξ α₀ : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) : Prop :=
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventWitnessStmt.{u} U T Q' Q γ ξ M E ∧
  ∃ Ostar : Set ℂ, IsOpen Ostar ∧ (0 : ℂ) ∈ Ostar ∧ sphere (0 : ℂ) 5 ⊆ Ostar ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∃ (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ),
        (∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
          μk k ω = ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) ∧
          ∀ x y : ℂ, Dk k ω x y = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * x) ((((2 : ℝ) ^ k : ℝ) : ℂ) * y)) ∧
        ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), w ∈ ball (0 : ℂ) 1 →
          Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
            FirstPassS11i.windowCert Ostar U V W T Q' Q δ M μk Dk k ω n w}.ncard : ℝ) / (N : ℝ)) atTop
            (𝓝 (P {ω | localModConstField α₀ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal)

/-- SUPERSEDED by `correctedLemma11_13_of_gamma_identity` below (its hypothesis `ZoomIdentityStmt` has the wrong target).

**Lemma 11.13 (corrected), conditional on the Step 12 identity.** The density is `δ = min (q/4) (1/2)` with
`q = P(E^{α₀}(M)) > 0`. The number `q` does not depend on the model: two whole-plane models give the same probability of
the canonical event (`prob_ballRestrict_alphaCanon_indep`). If no whole-plane model exists at `(γ, ξ, α₀)`, the conclusion is
vacuous and `δ = 1/2` is taken. -/
theorem correctedLemma11_13_of_identity
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hZ : ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
      ∀ γ ξ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
        ZoomIdentityStmt.{u} γ ξ α₀ U V W T Q' Q δ₀ M) :
    CorrectedLemma11_13Stmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ ξ hγ0 hγ2 hα M hM
  obtain ⟨E, hWit, Ostar, -, -, -, hfreq⟩ := hZ U V W T Q' Q δ₀ hgeom γ ξ α₀ M hγ0 hγ2 hα hM
  obtain ⟨hEm, hW⟩ := hWit
  by_cases hmod : ∃ (Ω : Type u) (inst : MeasurableSpace Ω) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc ∧ IsLQGMeasureOfField P γ α₀ hcirc μ ∧ IsLQGMetricOfField P γ ξ α₀ hC D
  · obtain ⟨Ω₀, inst₀, P₀, hC₀, hcirc₀, μ₀, D₀, hG₀, hμ₀, hD₀⟩ := hmod
    have : IsProbabilityMeasure P₀ := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG₀
    obtain ⟨-, hpos, -⟩ := hW α₀ hα Ω₀ P₀ hC₀ hcirc₀ μ₀ D₀ hG₀ hμ₀ hD₀
    obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (P₀ {ω | localModConstField α₀ hC₀ (ball (0 : ℂ) 7) ω ∈ E}).toReal :=
      ⟨_, rfl⟩
    have hq : 0 < q := by
      rw [hqdef]
      exact ENNReal.toReal_pos hpos.ne' (measure_ne_top P₀ _)
    refine ⟨min (q / 4) (1 / 2), ⟨lt_min (div_pos hq (by norm_num)) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩, ?_⟩
    intro Ω inst P hC hcirc μ D hG hμ hD
    have : IsProbabilityMeasure P := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG
    have hP : P {ω | localModConstField α₀ hC (ball (0 : ℂ) 7) ω ∈ E} =
        P₀ {ω | localModConstField α₀ hC₀ (ball (0 : ℂ) 7) ω ∈ E} := by
      have h := S11iCert.prob_ballRestrict_alphaCanon_indep hG hG₀ α₀ E hEm
      simpa only [S11iCert.ballRestrict_alphaCanon_eq] using h
    obtain ⟨μk, Dk, hsc, hstep⟩ := hfreq Ω P hC hcirc μ D hG hμ hD
    rw [hP, ← hqdef] at hstep
    exact (FirstPassS11i.CertAssemble.pinch_window_ae_buffered (hAx γ ξ α₀ Ω P hC hcirc) hG hγ0 hγ2 hα hD hgeom hq
      μk Dk hsc hstep).mono fun ω hω => hω.mono fun z hz => hz.mono fun N hN =>
        le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg N)) hN
  · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    intro Ω inst P hC hcirc μ D hG hμ hD
    exact (hmod ⟨Ω, inst, P, hC, hcirc, μ, D, hG, hμ, hD⟩).elim

/-- **Lemma 11.12 event at the insertion `γ` (slice of `PinchEventWitnessStmt`).** `E` is measurable, has positive probability
at the insertion `γ` in every whole-plane model, and implies the pinch-point event almost surely. Only the insertion `γ` is
used (the positivity of `certificate_canonical_pos`, `CertificateCanonical.lean:70`). -/
def PinchEventGammaStmt (U T Q' Q : Set ℂ) (γ ξ M : ℝ)
    (E : Set (ModConstTestPairings (ball (0 : ℂ) 7))) : Prop :=
  MeasurableSet E ∧
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ ξ γ hC D →
    MeasurableSet[Section6.fieldSigmaAlgebraModConst γ hC (ball (0 : ℂ) 7)]
      {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    0 < P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    ∀ᵐ ω ∂P, localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E →
      pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0

/-- **Step 12 of Lemma 11.13 at the insertion `γ` (NEW named input; Q1 answer 2026-11-10 02:53 UTC, §3.2 and §5).** There are a
Lemma 11.12 event `E` at `γ` (`PinchEventGammaStmt`) and a number `q` that is its canonical probability `P(A_E) = p_γ(M)` in
every whole-plane model at the insertion `γ`, and an open set `Ostar` with `0 ∈ Ostar` and `sphere 0 5 ⊆ Ostar`, such that for
every whole-plane model at the insertion `α₀` there is a zoom family `μk, Dk` at dyadic scales `2^k` whose window certificate
frequency converges, for every `k`, almost surely and for `μk`-almost every `w` in `B₁(0)`, to `q`. -/
def GammaZoomIdentityStmt (γ ξ α₀ : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) : Prop :=
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaStmt.{u} U T Q' Q γ ξ M E ∧
  ∃ q : ℝ,
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ ξ γ hC D →
      (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal = q) ∧
    ∃ Ostar : Set ℂ, IsOpen Ostar ∧ (0 : ℂ) ∈ Ostar ∧ sphere (0 : ℂ) 5 ⊆ Ostar ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
        ∃ (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ),
          (∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
            μk k ω = ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) ∧
            ∀ x y : ℂ, Dk k ω x y = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * x) ((((2 : ℝ) ^ k : ℝ) : ℂ) * y)) ∧
          ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), w ∈ ball (0 : ℂ) 1 →
            Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
              FirstPassS11i.windowCert Ostar U V W T Q' Q δ M μk Dk k ω n w}.ncard : ℝ) / (N : ℝ)) atTop
              (𝓝 q)

/-- **Lemma 11.13 (corrected), conditional on the Step 12 identity at the insertion `γ`.** The density is `δ = min (q/4) (1/2)`
with `q = p_γ(M) > 0`; the positivity is the canonical positivity at `γ` in a γ-model. The hypothesis `hγM` is an explicit
NEW input, not yet source-checked: a whole-plane model at the insertion `γ` for the same `ξ` exists whenever one exists at some
insertion `α₀ < Q` (the existence that `certificate_canonical_pos` takes as `hmodel`). If no model exists at `(γ, ξ, α₀)`, the
conclusion is vacuous and `δ = 1/2` is taken. -/
theorem correctedLemma11_13_of_gamma_identity
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hγM : ∀ (γ ξ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
      (∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc ∧ IsLQGMeasureOfField P γ α₀ hcirc μ ∧ IsLQGMetricOfField P γ ξ α₀ hC D) →
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc ∧ IsLQGMeasureOfField P γ γ hcirc μ ∧ IsLQGMetricOfField P γ ξ γ hC D)
    (hZ : ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
      ∀ γ ξ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
        GammaZoomIdentityStmt.{u} γ ξ α₀ U V W T Q' Q δ₀ M) :
    CorrectedLemma11_13Stmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ ξ hγ0 hγ2 hα M hM
  obtain ⟨E, ⟨-, hW⟩, q, hqeq, Ostar, -, -, -, hfreq⟩ :=
    hZ U V W T Q' Q δ₀ hgeom γ ξ α₀ M hγ0 hγ2 hα hM
  by_cases hmod : ∃ (Ω : Type u) (inst : MeasurableSpace Ω) (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc ∧ IsLQGMeasureOfField P γ α₀ hcirc μ ∧ IsLQGMetricOfField P γ ξ α₀ hC D
  · obtain ⟨Ωg, instg, Pg, hCg, hcircg, μg, Dg, hGg, hμg, hDg⟩ := hγM γ ξ α₀ hγ0 hγ2 hα hmod
    have : IsProbabilityMeasure Pg := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hGg
    obtain ⟨-, hpos, -⟩ := hW Ωg Pg hCg hcircg μg Dg hGg hμg hDg
    have hq : 0 < q := by
      rw [← hqeq Ωg Pg hCg hcircg μg Dg hGg hμg hDg]
      exact ENNReal.toReal_pos hpos.ne' (measure_ne_top Pg _)
    refine ⟨min (q / 4) (1 / 2), ⟨lt_min (div_pos hq (by norm_num)) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩, ?_⟩
    intro Ω inst P hC hcirc μ D hG hμ hD
    obtain ⟨μk, Dk, hsc, hstep⟩ := hfreq Ω P hC hcirc μ D hG hμ hD
    exact (FirstPassS11i.CertAssemble.pinch_window_ae_buffered (hAx γ ξ α₀ Ω P hC hcirc) hG hγ0 hγ2 hα hD hgeom hq
      μk Dk hsc hstep).mono fun ω hω => hω.mono fun z hz => hz.mono fun N hN =>
        le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg N)) hN
  · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    intro Ω inst P hC hcirc μ D hG hμ hD
    exact (hmod ⟨Ω, inst, P, hC, hcirc, μ, D, hG, hμ, hD⟩).elim

end HarmonicBalls

#print axioms HarmonicBalls.correctedLemma11_13_of_gamma_identity
#print axioms HarmonicBalls.correctedLemma11_13_of_identity
