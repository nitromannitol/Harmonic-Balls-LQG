import Mathlib
import HarmonicBalls.FirstPass.S11i.Step8TransferDilation
import HarmonicBalls.FirstPass.S11i.AlphaCanonical
import HarmonicBalls.FirstPass.S11i.Step8CanonicalFailure
import HarmonicBalls.FirstPass.S11n
import HarmonicBalls.Defs.LQGMetric

/-!
# Identification of the physical failure event with the canonical one (Step 8, section 8 of the n3-hT route)

Route: notes/fp-gaps/CHATGPT-n3-hT.md, section 8 ("why this really gives the physical failure event").
On the canonical-identification conull set (`LQGCanonicalIdentificationStmt`, FirstPass/S11n.lean:61), the physical LQG
measure and LQG metric are positive rescalings of their canonical counterparts:
`μ ω = ofReal a • Dμ (alphaCanon α₀ hC ω)` and `D ω = b * Dd (alphaCanon α₀ hC ω)` with `a, b > 0`.
`CertificateEvent` is invariant under such rescalings (`window_count_ofReal_smul_eq`, Step8TransferDilation.lean), so the
unit-scale window frequencies agree for every `N`.

The identification `LQGCanonicalIdentificationStmt` is a hypothesis here, not a proved statement.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise

namespace HarmonicBalls.FirstPassS11iStep8Transfer

universe u

open FirstPassS11i HarmonicBalls

/-- **Unit-scale window frequency of the certificate event (Step 8).** At the point `z` and the scale index `N`, the
proportion `#{n : N + 1 ≤ n ≤ 2N | CertificateEvent μ D … (2⁻¹ ^ n) z} / N` of the window scales `2^{-n}` at which the
certificate holds. This is the sequence whose limit defines the physical failure event. -/
noncomputable def unitScaleWindowFreq (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (z : ℂ) (N : ℕ) : ℝ :=
  (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      CertificateEvent μ D Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ)

/-- **Scaling invariance of the unit-scale window frequency.** For `a, b > 0`, the pair `(ofReal a • μ, b * D)` has the same
unit-scale window frequency as `(μ, D)`, at every `z` and every `N`. Reduces to the set identity
`window_count_ofReal_smul_eq` (Step8TransferDilation.lean), which rests on `certificateEvent_ofReal_smul_iff`. -/
theorem unitScaleWindowFreq_ofReal_smul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (μ : Measure ℂ) (D : ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (z : ℂ) (N : ℕ) :
    unitScaleWindowFreq (ENNReal.ofReal a • μ) (fun x y => b * D x y) Ostar U V W T Q' Q η M z N =
      unitScaleWindowFreq μ D Ostar U V W T Q' Q η M z N := by
  unfold unitScaleWindowFreq
  rw [window_count_ofReal_smul_eq ha hb μ Ostar U V W T Q' Q η M z N]

/-- **Identification of the physical failure frequencies with the canonical ones (Step 8, section 8).** Assume the
canonical identification `hId : LQGCanonicalIdentificationStmt` (FirstPass/S11n.lean:61) for the decoders `Dμ`, `Dd`.
For a whole-plane GFF model with `IsLQGMeasureOfField P γ α₀ hcirc μ` and `IsLQGMetricOfField P γ ξ α₀ hC D`, almost surely,
for every point `z` and every `N`, the unit-scale window frequency of the physical pair `(μ ω, D ω)` equals that of the
canonical pair `(Dμ (alphaCanon α₀ hC ω), Dd (alphaCanon α₀ hC ω))`. -/
theorem unitScaleWindowFreq_ae_eq_canonical (γ ξ α₀ : ℝ)
    (Dμ : HarmonicBalls.S11n.CanonSpace → Measure ℂ) (Dd : HarmonicBalls.S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hId : HarmonicBalls.S11n.LQGCanonicalIdentificationStmt.{u} γ ξ α₀ Dμ Dd)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (N : ℕ),
      unitScaleWindowFreq (μ ω) (D ω) Ostar U V W T Q' Q η M z N =
        unitScaleWindowFreq (Dμ (alphaCanon α₀ hC ω)) (Dd (alphaCanon α₀ hC ω)) Ostar U V W T Q' Q η M z N := by
  filter_upwards [hId Ω P hC hcirc μ D hGFF hμ hD] with ω hω
  obtain ⟨a, b, ha, hb, hμω, hDω⟩ := hω
  have hDfun : D ω = fun x y => b * Dd (alphaCanon α₀ hC ω) x y :=
    funext fun x => funext fun y => hDω x y
  intro z N
  rw [hμω, hDfun]
  exact unitScaleWindowFreq_ofReal_smul ha hb (Dμ (alphaCanon α₀ hC ω)) (Dd (alphaCanon α₀ hC ω))
    Ostar U V W T Q' Q η M z N

/-- **Physical failure event as the canonical one (Step 8, section 8).** Let `Φ` send each model's pairing `hC ω` to the
canonical point `alphaCanon α₀ hC ω` (hypothesis `hΦ`). Almost surely, for every root `z`, the physical unit-scale window
frequency of `(μ ω, D ω)` fails to converge to `q` exactly when `(hC ω, z)` lies in the canonical failure set
`canonicalFailure` (Step8CanonicalFailure.lean). -/
theorem unitScaleWindowFreq_not_tendsto_iff_canonicalFailure (γ ξ α₀ q : ℝ)
    (Dμ : HarmonicBalls.S11n.CanonSpace → Measure ℂ) (Dd : HarmonicBalls.S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hId : HarmonicBalls.S11n.LQGCanonicalIdentificationStmt.{u} γ ξ α₀ Dμ Dd)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (Φ : ((ℂ → ℝ) → ℝ) → HarmonicBalls.S11n.CanonSpace) (hΦ : ∀ ω, Φ (hC ω) = alphaCanon α₀ hC ω) :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      (¬ Tendsto (fun N : ℕ => unitScaleWindowFreq (μ ω) (D ω) Ostar U V W T Q' Q η M z N) atTop (𝓝 q)) ↔
        (hC ω, z) ∈ canonicalFailure Dμ Dd Ostar U V W T Q' Q η M q Φ := by
  filter_upwards [unitScaleWindowFreq_ae_eq_canonical γ ξ α₀ Dμ Dd hId P hC hcirc μ D hGFF hμ hD
    Ostar U V W T Q' Q η M] with ω hω
  intro z
  have hfun : (fun N : ℕ => unitScaleWindowFreq (μ ω) (D ω) Ostar U V W T Q' Q η M z N) =
      fun N : ℕ => canonicalWindowFreq Dμ Dd Ostar U V W T Q' Q η M (Φ (hC ω)) z N := by
    funext N
    rw [hΦ ω]
    exact hω z N
  change (¬ Tendsto (fun N : ℕ => unitScaleWindowFreq (μ ω) (D ω) Ostar U V W T Q' Q η M z N) atTop
      (𝓝 q)) ↔
    ¬ Tendsto (fun N : ℕ => canonicalWindowFreq Dμ Dd Ostar U V W T Q' Q η M (Φ (hC ω)) z N) atTop (𝓝 q)
  rw [hfun]

end HarmonicBalls.FirstPassS11iStep8Transfer
