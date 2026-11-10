import HarmonicBalls.FirstPass.S11i.Assembly13
import HarmonicBalls.FirstPass.S11m.Corrected11_12

/-!
# Lemma 11.13 (corrected): `firstPass_11_13_corrected` (first pass fp-S11i-11-13b, owner n3)

`firstPass_11_13_corrected` proves `CorrectedLemma11_13Stmt` (`FirstPass/S11i/Faithful.lean`), whose geometry clause
`insert 0 (sphere 0 5) ⊆ pinchOmegaGeom W Q δ₀` (corrected paper lines 3180-3200) is the operator decision on Blocker 2
(the same clause as in `CorrectedLemma11_12Stmt`; `IsBufferedPinchGeometry` is unchanged).

Named inputs (hypotheses here, not proved here):
* `hAx`, `hMeas`: `LQGMetricFieldAxioms` (Fact 2.2 I-IV) and `LQGMeasureExistence`; Proposed, operator source-check pending.
* `hCert`: `PinchLocalCertificateStmt` (z4, `FirstPass/S11m/Corrected11_12.lean:40`), the local certificate input of Lemma 11.12.
* `hXi`: `LQGMetricExponentPositive` (frozen, `FirstPass/Frozen/S11j.lean:105`).
* `hStep8`: `Step8IdentificationStmt` (Blocker 1: the Step 8 identification of the zoom family, `Step8IdentityStmt`).

Routing. Steps 1-2 (the event `E` at `γ` and its probability): `E` is the Lemma 11.12 event at the insertion `γ`, taken
from the α = γ slice of `firstPass_11_12_corrected` (which carries `hOmega`). Steps 3, 9-11 are inside
`correctedLemma11_13_of_gamma_identity` (`Assembly13.lean`). Steps 4-7 (n4 local measurability and the a.s. modification
of q3; n1 rooted identification) have no separate hypothesis yet: they belong to the Step 8 identification and are split out
of `Step8IdentityStmt` when they land.

Open point for the operator: `Step8IdentificationStmt` quantifies over EVERY Lemma 11.12 event `E` at `γ`
(`PinchEventGammaStmt`), so the identification is assumed for the event produced by `firstPass_11_12_corrected`, not only
for the event constructed in the paper. If the paper's identification holds for one constructed event only, the hypothesis
should become `∃ E, PinchEventGammaStmt E ∧ Step8IdentityStmt …` (then the Step 1-2 slice is not needed).
-/

universe u

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- **Step 8 identification of Lemma 11.13 for one Lemma 11.12 event (named input; Blocker 1 of fp-S11i-11-13b).** For a
Lemma 11.12 event `E` at the insertion `γ` (`PinchEventGammaStmt`): the probability `q` of `{h^γ|_{B₇} ∈ E}` is the same in
every whole-plane model at `γ`, and there is an open set `Ostar ∋ 0` with `sphere 0 5 ⊆ Ostar` such that in every
whole-plane model at `α₀` a zoom family `μk, Dk` at dyadic scales `2^k` has window certificate frequencies converging, almost
surely and for `μk`-almost every `w ∈ B₁(0)`, to `q` (the γ-insertion target of `GammaZoomIdentityStmt`; Step 8 of the
corrected proof of `lemma:mu_h-pinch-bad`, corrected paper lines 3848-3930). -/
def Step8IdentityStmt (γ ξ α₀ : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ)
    (E : Set (ModConstTestPairings (ball (0 : ℂ) 7))) : Prop :=
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

/-- The named input of `firstPass_11_13_corrected`: the Step 8 identification (`Step8IdentityStmt`) for every Lemma 11.12
event `E` at the insertion `γ`, on every buffered geometry with the component clause. -/
def Step8IdentificationStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ₀ →
  ∀ γ ξ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
  ∀ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), PinchEventGammaStmt.{u} U T Q' Q γ ξ M E →
  Step8IdentityStmt.{u} γ ξ α₀ U V W T Q' Q δ₀ M E

/-- **Lemma 11.13 (corrected), first pass.** `CorrectedLemma11_13Stmt` from the named inputs `hAx`, `hMeas`, `hCert`, `hXi`
and `hStep8` (see the module docstring). The density is `δ = min (q/4) (1/2)` with `q = P(E^γ(M)) > 0`. -/
theorem firstPass_11_13_corrected
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hMeas : ∀ (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ γ hC hcirc)
    (hCert : PinchLocalCertificateStmt.{u}) (hXi : LQGMetricExponentPositive)
    (hStep8 : Step8IdentificationStmt.{u}) :
    CorrectedLemma11_13Stmt.{u} := by
  refine correctedLemma11_13_of_gamma_identity hAx hMeas ?_
  intro U V W T Q' Q δ₀ hgeom hOmega γ ξ α₀ M hγ0 hγ2 hα hM
  obtain ⟨E, hEm, hE⟩ :=
    firstPass_11_12_corrected hAx hCert hXi U V W T Q' Q δ₀ hgeom hOmega γ ξ hγ0 hγ2 M hM
  have hγQ : γ < lqgQ γ := by
    unfold lqgQ
    have h : γ / 2 < 2 / γ := by
      rw [div_lt_div_iff₀ (by norm_num) hγ0]
      nlinarith
    linarith
  have hPG : PinchEventGammaStmt.{u} U T Q' Q γ ξ M E := by
    refine ⟨hEm, ?_⟩
    intro Ω _ P hC hcirc μ D hgff hμ hD
    exact hE γ hγQ Ω P hC hcirc μ D hgff hμ hD
  unfold GammaZoomIdentityStmt
  exact ⟨E, hPG, hStep8 U V W T Q' Q δ₀ hgeom hOmega γ ξ α₀ M hγ0 hγ2 hα hM E hPG⟩

end HarmonicBalls

#print axioms HarmonicBalls.firstPass_11_13_corrected
